// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::parse::UnstableAttribute;

use std::collections::BTreeMap;

use quote::ToTokens;
use rustc_public::crate_def::Attribute as AttributeStable;
use rustc_public::{CrateDef, Symbol as SymbolStable};
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::{Expr, ExprLit, Lit, MetaNameValue, Token};

fn stable_expr_to_string(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Lit(ExprLit { lit: Lit::Str(lit), .. }) => Some(lit.value()),
        Expr::Lit(ExprLit { lit: Lit::Int(lit), .. }) => Some(lit.base10_digits().to_owned()),
        _ => None,
    }
}

fn parse_stable_key_values(attr: &AttributeStable) -> Result<BTreeMap<String, String>, String> {
    let attribute = syn_attr_stable(attr);
    let syn::Meta::List(list) = &attribute.meta else {
        return Err("malformed attribute input".to_owned());
    };
    let parser = Punctuated::<MetaNameValue, Token![,]>::parse_terminated;
    let args = parser.parse2(list.tokens.clone()).map_err(|err| err.to_string())?;
    args.into_iter()
        .map(|arg| {
            let key =
                arg.path.get_ident().map(std::string::ToString::to_string).ok_or_else(|| {
                    format!("expected identifier key in `{}`", arg.path.to_token_stream())
                })?;
            let value = stable_expr_to_string(&arg.value).ok_or_else(|| {
                format!(
                    "expected string or integer literal for `{key}`, but found `{}`",
                    arg.value.to_token_stream()
                )
            })?;
            Ok((key, value))
        })
        .collect()
}

fn parse_stable_unstable_attribute(attr: &AttributeStable) -> Result<UnstableAttribute, String> {
    let args = parse_stable_key_values(attr)?;
    let invalid_keys = args
        .iter()
        .filter_map(|(key, _)| {
            (!matches!(key.as_str(), "feature" | "issue" | "reason")).then_some(key)
        })
        .cloned()
        .collect::<Vec<_>>();

    if !invalid_keys.is_empty() {
        return Err(format!("unexpected argument `{}`", invalid_keys.join("`, `")));
    }

    let get_val =
        |name: &str| args.get(name).cloned().ok_or_else(|| format!("missing `{name}` field"));
    Ok(UnstableAttribute {
        feature: get_val("feature")?,
        issue: get_val("issue")?,
        reason: get_val("reason")?,
    })
}

pub(crate) fn stable_tool_unstable_attrs<T: CrateDef>(
    def: T,
) -> Vec<Result<UnstableAttribute, String>> {
    let tool_paths =
        [["kanitool".into(), "unstable".into()], ["trust_mctool".into(), "unstable".into()]];
    tool_paths
        .into_iter()
        .flat_map(|tool_path| def.tool_attrs(&tool_path))
        .map(|attr| parse_stable_unstable_attribute(&attr))
        .collect()
}

fn syn_attr_stable(attr: &AttributeStable) -> syn::Attribute {
    let parser = syn::Attribute::parse_outer;
    parser
        .parse_str(attr.as_str())
        .expect("failed to parse attribute")
        .pop()
        .expect("attribute should not be empty")
}

pub(crate) fn fn_marker<T: CrateDef>(def: T) -> Option<String> {
    let fn_marker: [SymbolStable; 2] = ["kanitool".into(), "fn_marker".into()];
    let marker = def.tool_attrs(&fn_marker).pop()?;
    let attribute = syn_attr_stable(&marker);
    let meta_name = attribute.meta.require_name_value().ok()?;
    let Expr::Lit(ExprLit { lit: Lit::Str(lit_str), .. }) = &meta_name.value else {
        return None;
    };
    Some(lit_str.value())
}
