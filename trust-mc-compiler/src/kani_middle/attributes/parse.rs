// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Attribute parsing utilities for Kani/trust_mc attributes.
//!
//! This module contains:
//! - Attribute value extraction (`expect_key_string_value`, `expect_single`, `expect_no_args`)
//! - Attribute argument parsing (`parse_unwind`, `parse_solver`, `parse_integer`, `parse_paths`, `parse_key_values`)
//! - Unstable attribute support (`UnstableAttribute`, `UnstableAttrParseError`)
//! - Syn/pretty helpers (`attr_kind`, `syn_attr`, `pretty_type_path`)
//! - Public API helpers (`is_proof_harness`, `has_kani_attribute`)

use super::KaniAttributeKind;

use std::collections::BTreeMap;
use std::str::FromStr;

use quote::ToTokens;
use rustc_ast::{LitKind, MetaItem, MetaItemKind};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::AttrArgs;
use rustc_hir::Attribute;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance as InstanceStable;
use rustc_public::rustc_internal;
use rustc_session::Session;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{PathSegment, TypePath};
use trust_mc_metadata::SolverOption;

use tracing::{debug, trace};

/// An efficient check for the existence for a particular [`KaniAttributeKind`].
/// Unlike querying [`KaniAttributes`] this method builds no new heap data
/// structures and has short circuiting.
pub(super) fn has_kani_attribute<F: Fn(KaniAttributeKind) -> bool>(
    tcx: TyCtxt,
    def_id: DefId,
    predicate: F,
) -> bool {
    tcx.get_all_attrs(def_id).iter().filter_map(|a| attr_kind(tcx, a)).any(predicate)
}

/// Same as [`KaniAttributes::is_proof_harness`] but more efficient because less
/// attribute parsing is performed.
pub(crate) fn is_proof_harness(tcx: TyCtxt, instance: InstanceStable) -> bool {
    let def_id = rustc_internal::internal(tcx, instance.def.def_id());
    has_kani_attribute(tcx, def_id, |a| {
        matches!(a, KaniAttributeKind::Proof | KaniAttributeKind::ProofForContract)
    })
}

/// Expect the contents of this attribute to be of the format #[attribute =
/// "value"] and return the `"value"`.
pub(super) fn expect_key_string_value(
    sess: &Session,
    attr: &Attribute,
) -> Result<rustc_span::Symbol, ErrorGuaranteed> {
    let span = attr.span();
    let AttrArgs::Eq { expr, .. } = &attr.get_normal_item().args else {
        return Err(sess
            .dcx()
            .span_err(span, "Expected attribute of the form #[attr = \"value\"]"));
    };
    let maybe_str = expr.kind.str();
    if let Some(str) = maybe_str {
        Ok(str)
    } else {
        Err(sess.dcx().span_err(span, "Expected literal string as right hand side of `=`"))
    }
}

#[allow(clippy::panic)] // Internal validation - panics indicate compiler bugs
pub(super) fn expect_single<'tcx>(
    tcx: TyCtxt,
    kind: KaniAttributeKind,
    attributes: &Vec<&'tcx Attribute>,
) -> &'tcx Attribute {
    let attr = attributes.first().unwrap_or_else(|| {
        panic!("expected at least one attribute {} in {attributes:?}", kind.as_ref())
    });
    if attributes.len() > 1 {
        tcx.dcx().span_err(
            attr.span(),
            format!("only one '#[kani::{}]' attribute is allowed per harness", kind.as_ref()),
        );
    }
    attr
}

/// Attribute used to mark a Kani lib API unstable.
#[derive(Debug)]
pub(super) struct UnstableAttribute {
    /// The feature identifier.
    pub(super) feature: String,
    /// A link to the stabilization tracking issue.
    pub(super) issue: String,
    /// A user friendly message that describes the reason why this feature is marked as unstable.
    pub(super) reason: String,
}

#[derive(Debug)]
pub(super) struct UnstableAttrParseError<'a> {
    /// The reason why the parsing failed.
    reason: String,
    /// The attribute being parsed.
    attr: &'a Attribute,
}

impl UnstableAttrParseError<'_> {
    /// Report the error in a friendly format.
    pub(super) fn report(&self, tcx: TyCtxt) -> ErrorGuaranteed {
        tcx.dcx()
            .struct_span_err(
                self.attr.span(),
                format!("failed to parse `#[kani::unstable_feature]`: {}", self.reason),
            )
            .with_note(format!(
                "expected format: #[kani::unstable_feature({}, {}, {})]",
                r#"feature="<IDENTIFIER>""#, r#"issue="<ISSUE>""#, r#"reason="<DESCRIPTION>""#
            ))
            .emit()
    }
}

/// Try to parse an unstable attribute into an `UnstableAttribute`.
impl<'a> TryFrom<&'a Attribute> for UnstableAttribute {
    type Error = UnstableAttrParseError<'a>;
    fn try_from(attr: &'a Attribute) -> Result<Self, Self::Error> {
        let build_error = |reason: String| Self::Error { reason, attr };
        let args = parse_key_values(attr).map_err(build_error)?;
        let invalid_keys = args
            .iter()
            .filter_map(|(key, _)| {
                (!matches!(key.as_str(), "feature" | "issue" | "reason")).then_some(key)
            })
            .cloned()
            .collect::<Vec<_>>();

        if !invalid_keys.is_empty() {
            Err(build_error(format!("unexpected argument `{}`", invalid_keys.join("`, `"))))
        } else {
            let get_val = |name: &str| {
                args.get(name).cloned().ok_or(build_error(format!("missing `{name}` field")))
            };
            Ok(UnstableAttribute {
                feature: get_val("feature")?,
                issue: get_val("issue")?,
                reason: get_val("reason")?,
            })
        }
    }
}

pub(super) fn expect_no_args(tcx: TyCtxt, kind: KaniAttributeKind, attr: &Attribute) {
    if !attr.is_word() {
        tcx.dcx()
            .struct_span_err(attr.span(), format!("unexpected argument for `{}`", kind.as_ref()))
            .with_help("remove the extra argument")
            .emit();
    }
}

/// Return the unwind value from the given attribute.
pub(super) fn parse_unwind(tcx: TyCtxt, attr: &Attribute) -> Option<u32> {
    // Get Attribute value and if it's not none, assign it to the metadata
    match parse_integer(attr) {
        None => {
            // There are no integers or too many arguments given to the attribute
            tcx.dcx().span_err(
                attr.span(),
                "invalid argument for `unwind` attribute, expected an integer",
            );
            None
        }
        Some(unwind_integer_value) => {
            if let Ok(val) = unwind_integer_value.try_into() {
                Some(val)
            } else {
                tcx.dcx().span_err(attr.span(), "value above maximum permitted value - u32::MAX");
                None
            }
        }
    }
}

pub(super) fn parse_solver(tcx: TyCtxt, attr: &Attribute) -> Option<SolverOption> {
    // REFACTORING: Validation could move to `kani_macros` for earlier errors.
    // Upstream: <https://github.com/model-checking/kani/issues/2192>
    //
    // Trade-offs:
    // - Current (here): Validation during kani_middle analysis has access to
    //   TyCtxt for richer diagnostics and cross-attribute checks.
    // - Alternative (macros): Earlier errors at macro expansion, but limited
    //   context (proc_macro API only, no type information).
    //
    // Decision: Keep validation here. The #[kani::solver] attribute validation
    // benefits from TyCtxt access for potential future cross-checks with other
    // Kani attributes. Moving to macros would fragment validation logic.
    // Part of #1358.
    const ATTRIBUTE: &str = "#[kani::solver]";
    let invalid_arg_err = |attr: &Attribute| {
        tcx.dcx().span_err(
            attr.span(),
            format!("invalid argument for `{ATTRIBUTE}` attribute, expected one of the supported solvers (e.g. `kissat`) or a SAT solver binary (e.g. `bin=\"<SAT_SOLVER_BINARY>\"`)"),
        )
    };

    let attr_args = attr.meta_item_list().expect("attribute should have meta item list");
    if attr_args.len() != 1 {
        tcx.dcx().span_err(
            attr.span(),
            format!(
                "the `{ATTRIBUTE}` attribute expects a single argument. Got {} arguments.",
                attr_args.len()
            ),
        );
        return None;
    }
    let attr_arg = &attr_args[0];
    let Some(meta_item) = attr_arg.meta_item() else {
        invalid_arg_err(attr);
        return None;
    };
    let ident = meta_item.ident().expect("meta item should have ident");
    let ident_str = ident.as_str();
    match &meta_item.kind {
        MetaItemKind::Word => {
            let solver = SolverOption::from_str(ident_str);
            if let Ok(solver) = solver {
                Some(solver)
            } else {
                tcx.dcx().span_err(attr.span(), format!("unknown solver `{ident_str}`"));
                None
            }
        }
        MetaItemKind::NameValue(lit) if ident_str == "bin" && lit.kind.is_str() => {
            Some(SolverOption::Binary(lit.symbol.to_string()))
        }
        _ => {
            // external enum: MetaItemKind
            invalid_arg_err(attr);
            None
        }
    }
}

/// Extracts the integer value argument from the attribute provided
/// For example, `unwind(8)` return `Some(8)`
fn parse_integer(attr: &Attribute) -> Option<u128> {
    // Vector of meta items , that contain the arguments given the attribute
    let attr_args = attr.meta_item_list()?;
    // Only extracts one integer value as argument
    if attr_args.len() == 1 {
        let x = attr_args[0].lit()?;
        match x.kind {
            LitKind::Int(y, ..) => Some(y.get()),
            _ => None, // external enum: LitKind
        }
    }
    // Return none if there are no attributes or if there's too many attributes
    else {
        None
    }
}

/// Extracts a vector with the path arguments of an attribute.
///
/// Emits an error if it couldn't convert any of the arguments and return an empty vector.
pub(super) fn parse_paths(tcx: TyCtxt, attr: &Attribute) -> Result<Vec<TypePath>, syn::Error> {
    let syn_attr = syn_attr(tcx, attr);
    let parser = Punctuated::<TypePath, syn::Token![,]>::parse_terminated;
    let paths = syn_attr.parse_args_with(parser)?;
    Ok(paths.into_iter().collect())
}

/// Parse the arguments of the attribute into a (key, value) map.
fn parse_key_values(attr: &Attribute) -> Result<BTreeMap<String, String>, String> {
    trace!(list=?attr.meta_item_list(), ?attr, "parse_key_values");
    let args = attr.meta_item_list().ok_or("malformed attribute input")?;
    args.iter()
        .map(|arg| match arg.meta_item() {
            Some(MetaItem { path: key, kind: MetaItemKind::NameValue(val), .. }) => Ok((
                key.segments.first().expect("path should have segments").ident.to_string(),
                val.symbol.to_string(),
            )),
            _ => Err(format!(
                // non-enum: Option<MetaItem>
                r#"expected "key = value" pair, but found `{}`"#,
                rustc_ast_pretty::pprust::meta_list_item_to_string(arg)
            )),
        })
        .collect()
}

/// If the attribute is named `kanitool::name` or `trust_mctool::name`, this extracts `name`
pub(super) fn attr_kind(tcx: TyCtxt, attr: &Attribute) -> Option<KaniAttributeKind> {
    if let Attribute::Unparsed(normal) = attr {
        let segments = &normal.path.segments;
        let tool_name = segments.first().map(rustc_span::Ident::as_str);
        if matches!(tool_name, Some("kanitool") | Some("trust_mctool")) {
            let ident_str = segments[1..]
                .iter()
                .map(rustc_span::Ident::as_str)
                .intersperse("::")
                .collect::<String>();
            KaniAttributeKind::try_from(ident_str.as_str())
                .inspect_err(|&err| {
                    debug!(?err, "attr_kind_failed");
                    tcx.dcx().span_err(attr.span(), format!("unknown attribute `{ident_str}`"));
                })
                .ok()
        } else {
            None
        }
    } else {
        None
    }
}

/// Parse an attribute using `syn`.
///
/// This provides a user-friendly interface to manipulate than the internal compiler AST.
pub(super) fn syn_attr(tcx: TyCtxt, attr: &Attribute) -> syn::Attribute {
    let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
    let parser = syn::Attribute::parse_outer;
    parser
        .parse_str(&attr_str)
        .expect("failed to parse attribute")
        .pop()
        .expect("attribute should not be empty")
}

/// Return a more user-friendly string for path by trying to remove unneeded whitespace.
///
/// `quote!()` and `TokenString::to_string()` introduce unnecessary space around separators.
/// This happens because these methods end up using TokenStream display, which has no
/// guarantees on the format printed.
/// <https://doc.rust-lang.org/proc_macro/struct.TokenStream.html#impl-Display-for-TokenStream>
///
/// E.g.: The path `<[char; 10]>::foo` printed with token stream becomes `< [ char ; 10 ] > :: foo`.
/// while this function turns this into `<[char ; 10]>::foo`.
///
/// Thus, this can still be improved to handle the `qself.ty`.
///
/// We also don't handle path segments, but users shouldn't pass generic arguments to our
/// attributes.
pub(super) fn pretty_type_path(path: &TypePath) -> String {
    fn segments_str<'a, I>(segments: I) -> String
    where
        I: IntoIterator<Item = &'a PathSegment>,
    {
        // We don't bother with path arguments for now since users shouldn't provide them.
        let parts: Vec<_> =
            segments.into_iter().map(|segment| segment.to_token_stream().to_string()).collect();
        parts.join("::")
    }
    let leading = if path.path.leading_colon.is_some() { "::" } else { "" };
    if let Some(qself) = &path.qself {
        let pos = qself.position;
        let qself_str = qself.ty.to_token_stream().to_string();
        if pos == 0 {
            format!("<{qself_str}>::{}", segments_str(&path.path.segments))
        } else {
            let before = segments_str(path.path.segments.iter().take(pos));
            let after = segments_str(path.path.segments.iter().skip(pos));
            format!("<{qself_str} as {before}>::{after}")
        }
    } else {
        format!("{leading}{}", segments_str(&path.path.segments))
    }
}

#[cfg(test)]
mod tests {
    use super::pretty_type_path;
    use syn::TypePath;

    fn parse(s: &str) -> TypePath {
        syn::parse_str::<TypePath>(s).expect("valid TypePath literal")
    }

    #[test]
    fn simple_path() {
        assert_eq!(pretty_type_path(&parse("foo::bar::baz")), "foo::bar::baz");
    }

    #[test]
    fn single_segment() {
        assert_eq!(pretty_type_path(&parse("MyType")), "MyType");
    }

    #[test]
    fn leading_colon() {
        assert_eq!(pretty_type_path(&parse("::std::vec::Vec")), "::std::vec::Vec");
    }

    #[test]
    fn qself_position_zero() {
        // <[char; 10]>::foo — qself.position == 0 branch
        // Note: `to_token_stream` inserts space around `;` in array types
        assert_eq!(pretty_type_path(&parse("<[char; 10]>::foo")), "<[char ; 10]>::foo");
    }

    #[test]
    fn qself_as_trait() {
        // <T as std::fmt::Display>::fmt — qself.position > 0 branch
        assert_eq!(
            pretty_type_path(&parse("<T as std::fmt::Display>::fmt")),
            "<T as std::fmt::Display>::fmt"
        );
    }

    #[test]
    fn no_leading_colon() {
        let result = pretty_type_path(&parse("std::vec::Vec"));
        assert!(!result.starts_with("::"), "should not start with ::");
    }
}
