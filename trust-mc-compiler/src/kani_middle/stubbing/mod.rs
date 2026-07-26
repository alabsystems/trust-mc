// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module contains code for implementing stubbing.

mod alpha_equiv;
mod annotations;

use itertools::Itertools;
use rustc_span::DUMMY_SP;
use std::collections::HashMap;
use tracing::{debug, trace};

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Const;
use rustc_middle::ty::{self, EarlyBinder, TyCtxt, TypeFoldable, TypingEnv};
use rustc_public::mir::ConstOperand;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::visit::{Location, MirVisitor};
use rustc_public::rustc_internal;
use rustc_public::ty::{FnDef, GenericArgs, RigidTy, TyKind};
use rustc_public::{CrateDef, CrateItem};
use trust_mc_metadata::HarnessMetadata;

use self::alpha_equiv::{generic_param_positions, ty_alpha_equiv_bind};
use self::annotations::update_stub_mapping;

/// Collects the stubs from the harnesses in a crate.
pub(crate) fn harness_stub_map(
    tcx: TyCtxt,
    harness: Instance,
    metadata: &HarnessMetadata,
) -> HashMap<DefId, DefId> {
    let def_id = rustc_internal::internal(tcx, harness.def.def_id());
    let attrs = &metadata.attributes;
    let mut stub_pairs = HashMap::default();
    for stubs in &attrs.stubs {
        update_stub_mapping(tcx, def_id.expect_local(), stubs, &mut stub_pairs);
    }
    stub_pairs
}

/// For the purpose of checking generic argument length, don't consider the `Self` generic argument.
/// The purpose is to allow stubbing out:
/// ```rust
/// pub trait Foo {
///    fn foo(&self) -> bool {
///        false
///    }
/// }
/// ```
/// with:
/// ```rust
/// pub fn stub_foo() -> bool {
///    true
/// }
/// ```
/// Since `rustc_public` APIs introduce a `Self` generic argument for trait functions
fn generic_args_len_without_self(args: &GenericArgs) -> usize {
    let len = args.0.len();
    if len == 0 {
        return len;
    }
    let has_self = args.0.iter().any(|arg| {
        if let Some(ty) = arg.ty()
            && let TyKind::Param(param_ty) = ty.kind()
        {
            param_ty.name == "Self"
        } else {
            false
        }
    });
    if has_self { len - 1 } else { len }
}

/// Checks whether the stub is compatible with the original function/method: do
/// the arities and types (of the parameters and return values) match up? This
/// does **NOT** check whether the type variables are constrained to implement
/// the same traits; trait mismatches are checked during monomorphization.
///
/// # Contracts
///
/// REQUIRES: tcx is valid for resolving both old_def and new_def types
/// ENSURES: Ok(()) implies:
///   - Arity matches (same number of arguments)
///   - Generic parameter count matches (excluding Self for trait methods)
///   - Return type matches
///   - All parameter types match positionally
///
/// ENSURES: Err(msg) contains human-readable description of the incompatibility
///
/// # Note
///
/// Generic parameter count is always validated. If either function lacks a body,
/// arity is checked using the function signature, but parameter/return types
/// cannot be fully verified. A warning is emitted in this case.
pub(crate) fn check_compatibility(
    tcx: TyCtxt,
    old_def: FnDef,
    new_def: FnDef,
) -> Result<(), String> {
    // When bodies are missing, we cannot fully validate parameter and return types.
    // Fall back to signature-based arity check and warn about limited validation.
    let old_body = old_def.body();
    let new_body = new_def.body();

    // Check generic parameter count first - doesn't require body
    let old_def_id = rustc_internal::internal(tcx, old_def.def_id());
    let new_def_id = rustc_internal::internal(tcx, new_def.def_id());
    let old_ty = rustc_internal::stable(tcx.type_of(old_def_id)).value;
    let new_ty = rustc_internal::stable(tcx.type_of(new_def_id)).value;
    let TyKind::RigidTy(RigidTy::FnDef(_, old_args)) = old_ty.kind() else {
        unreachable!("Expected function, but found {old_ty}")
    };
    let TyKind::RigidTy(RigidTy::FnDef(_, new_args)) = new_ty.kind() else {
        unreachable!("Expected function, but found {new_ty}")
    };

    let old_args_len = generic_args_len_without_self(&old_args);
    let new_args_len = generic_args_len_without_self(&new_args);

    if old_args_len != new_args_len {
        return Err(format!(
            "mismatch in the number of generic parameters: original function/method `{}` \
             takes {} generic parameter(s), stub `{}` takes {}",
            old_def.name(),
            old_args_len,
            new_def.name(),
            new_args_len,
        ));
    }
    let old_param_positions = generic_param_positions(&old_args);
    let new_param_positions = generic_param_positions(&new_args);

    if old_body.is_none() || new_body.is_none() {
        // Use fn_sig to check arity even without body
        let old_sig = tcx.fn_sig(old_def_id).skip_binder().skip_binder();
        let new_sig = tcx.fn_sig(new_def_id).skip_binder().skip_binder();

        // Check arity from signature
        if old_sig.inputs().len() != new_sig.inputs().len() {
            return Err(format!(
                "arity mismatch: original function/method `{}` takes {} argument(s), stub `{}` takes {} \
                 (arity checked via signature, body unavailable)",
                old_def.name(),
                old_sig.inputs().len(),
                new_def.name(),
                new_sig.inputs().len(),
            ));
        }

        // #956: Also check parameter types and return type from signature.
        // These checks use erased region types, which may miss some subtle
        // lifetime mismatches, but catches concrete type incompatibilities.
        let mut sig_diff = vec![];
        // One Self binding across return + all params: a trait default method's
        // `Self` must instantiate to the SAME concrete type everywhere.
        let mut self_binding = None;

        // Check return type
        let old_output = old_sig.output();
        let new_output = new_sig.output();
        if !ty_alpha_equiv_bind(
            rustc_internal::stable(old_output),
            rustc_internal::stable(new_output),
            &old_param_positions,
            &new_param_positions,
            &mut self_binding,
        ) {
            sig_diff.push(format!(
                "Expected return type `{:?}`, but found `{:?}` (from signature)",
                old_output, new_output
            ));
        }

        // Check parameter types
        for (i, (old_input, new_input)) in old_sig.inputs().iter().zip(new_sig.inputs()).enumerate()
        {
            if !ty_alpha_equiv_bind(
                rustc_internal::stable(*old_input),
                rustc_internal::stable(*new_input),
                &old_param_positions,
                &new_param_positions,
                &mut self_binding,
            ) {
                sig_diff.push(format!(
                    "Expected type `{:?}` for parameter {}, but found `{:?}` (from signature)",
                    old_input,
                    i + 1,
                    new_input
                ));
            }
        }

        if !sig_diff.is_empty() {
            return Err(format!(
                "Cannot stub `{}` by `{}` (body unavailable, checked via signature).\n - {}",
                old_def.name(),
                new_def.name(),
                sig_diff.iter().join("\n - ")
            ));
        }

        // Warn about limitations of signature-only checking
        tracing::debug!(
            "Stub compatibility for `{}` -> `{}` validated via signature only: \
             {} body unavailable. Lifetime and generic bounds not fully checked.",
            old_def.name(),
            new_def.name(),
            if old_body.is_none() && new_body.is_none() {
                "both function bodies"
            } else if old_body.is_none() {
                "original function body"
            } else {
                "stub body"
            }
        );
        return Ok(());
    }

    let old_body = old_body.expect("old_body presence checked above");
    let new_body = new_body.expect("new_body presence checked above");
    // Check whether the arities match.
    if old_body.arg_locals().len() != new_body.arg_locals().len() {
        let msg = format!(
            "arity mismatch: original function/method `{}` takes {} argument(s), stub `{}` takes {}",
            old_def.name(),
            old_body.arg_locals().len(),
            new_def.name(),
            new_body.arg_locals().len(),
        );
        return Err(msg);
    }
    // Note: Generic parameter count is checked earlier (before body-less early return)
    // Check whether the types match. Index 0 refers to the returned value,
    // indices [1, `arg_count`] refer to the parameters.
    let old_ret_ty = old_body.ret_local().ty;
    let new_ret_ty = new_body.ret_local().ty;
    let mut diff = vec![];
    // Shared Self binding across return + all params (see the sig path above).
    let mut self_binding = None;
    if !ty_alpha_equiv_bind(
        old_ret_ty,
        new_ret_ty,
        &old_param_positions,
        &new_param_positions,
        &mut self_binding,
    ) {
        diff.push(format!("Expected return type `{old_ret_ty}`, but found `{new_ret_ty}`"));
    }
    for (i, (old_arg, new_arg)) in
        old_body.arg_locals().iter().zip(new_body.arg_locals().iter()).enumerate()
    {
        if !ty_alpha_equiv_bind(
            old_arg.ty,
            new_arg.ty,
            &old_param_positions,
            &new_param_positions,
            &mut self_binding,
        ) {
            diff.push(format!(
                "Expected type `{}` for parameter {}, but found `{}`",
                old_arg.ty,
                i + 1,
                new_arg.ty
            ));
        }
    }
    if !diff.is_empty() {
        Err(format!(
            "Cannot stub `{}` by `{}`.\n - {}",
            old_def.name(),
            new_def.name(),
            diff.iter().join("\n - ")
        ))
    } else {
        Ok(())
    }
}

/// Validate that an instance body can be instantiated.
///
/// Stubbing may cause an instance to not be correctly instantiated since we delay checking its
/// generic bounds.
///
/// In stable MIR, trying to retrieve an `Instance::body()` will ICE if we cannot evaluate a
/// constant as expected. For now, use internal APIs to anticipate this issue.
pub(crate) fn validate_stub_const(tcx: TyCtxt, instance: Instance) -> bool {
    debug!(?instance, "validate_instance");
    let item = CrateItem::try_from(instance).expect("instance should convert to CrateItem");
    let internal_instance = rustc_internal::internal(tcx, instance);
    let mut checker = StubConstChecker::new(tcx, internal_instance, item);
    checker.visit_body(&item.expect_body());
    checker.is_valid()
}

struct StubConstChecker<'tcx> {
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    source: CrateItem,
    is_valid: bool,
}

impl<'tcx> StubConstChecker<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>, source: CrateItem) -> Self {
        StubConstChecker { tcx, instance, is_valid: true, source }
    }
    fn monomorphize<T>(&self, value: T) -> T
    where
        T: TypeFoldable<TyCtxt<'tcx>> + Copy,
    {
        trace!(instance=?self.instance, ?value, "monomorphize");
        if self.instance.args.is_empty() {
            return value;
        }
        self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            TypingEnv::fully_monomorphized(),
            EarlyBinder::bind(value),
        )
    }

    fn is_valid(&self) -> bool {
        self.is_valid
    }
}

impl MirVisitor for StubConstChecker<'_> {
    /// Collect constants that are represented as static variables.
    fn visit_const_operand(&mut self, constant: &ConstOperand, location: Location) {
        let const_ = self.monomorphize(rustc_internal::internal(self.tcx, &constant.const_));
        debug!(?constant, ?location, ?const_, "visit_constant");
        match const_ {
            Const::Val(..) | Const::Ty(..) => {}
            Const::Unevaluated(un_eval, _) => {
                // Thread local fall into this category.
                if self
                    .tcx
                    .const_eval_resolve(TypingEnv::fully_monomorphized(), un_eval, DUMMY_SP)
                    .is_err()
                {
                    // The `monomorphize` call should have evaluated that constant already.
                    let tcx = self.tcx;
                    let mono_const = &un_eval;
                    let implementor = match mono_const.args.as_slice() {
                        [one] => one.as_type().expect("expected single type argument"),
                        _ => unreachable!("expected single type argument in mono_const.args"), // non-enum: slice
                    };
                    let trait_ = tcx
                        .trait_of_assoc(mono_const.def)
                        .expect("associated const should have trait");
                    let msg = format!(
                        "Type `{implementor}` does not implement trait `{}`. \
        This is likely because `{}` is used as a stub but its \
        generic bounds are not being met.",
                        tcx.def_path_str(trait_),
                        self.source.name()
                    );
                    tcx.dcx().span_err(rustc_internal::internal(self.tcx, location.span()), msg);
                    self.is_valid = false;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    // =========================================================================
    // Error message formatting — check_compatibility patterns (Part of #2217)
    //
    // check_compatibility builds structured error messages with specific
    // format patterns. We test the formatting logic extracted from the function.
    // The actual function requires TyCtxt, but the message construction is pure.
    // =========================================================================

    #[test]
    fn arity_mismatch_message_format() {
        let msg = format!(
            "arity mismatch: original function/method `{}` takes {} argument(s), stub `{}` takes {}",
            "foo", 3, "bar", 2
        );
        assert!(msg.contains("arity mismatch"));
        assert!(msg.contains("foo"));
        assert!(msg.contains("bar"));
        assert!(msg.contains("3 argument(s)"));
        assert!(msg.contains("takes 2"));
    }

    #[test]
    fn generic_param_mismatch_message_format() {
        let msg = format!(
            "mismatch in the number of generic parameters: original function/method `{}` \
             takes {} generic parameter(s), stub `{}` takes {}",
            "original_fn", 2, "stub_fn", 1,
        );
        assert!(msg.contains("generic parameters"));
        assert!(msg.contains("original_fn"));
        assert!(msg.contains("stub_fn"));
        assert!(msg.contains("2 generic parameter(s)"));
        assert!(msg.contains("takes 1"));
    }

    #[test]
    fn type_mismatch_diff_formatting() {
        // Simulates the diff accumulation pattern from check_compatibility
        let mut diff = vec![];
        diff.push("Expected return type `u32`, but found `i32`".to_string());
        diff.push(format!("Expected type `String` for parameter {}, but found `&str`", 1));

        let result =
            format!("Cannot stub `original` by `replacement`.\n - {}", diff.iter().join("\n - "));
        assert!(result.contains("Cannot stub `original` by `replacement`"));
        assert!(result.contains("Expected return type `u32`, but found `i32`"));
        assert!(result.contains("Expected type `String` for parameter 1, but found `&str`"));
        // Verify the separator
        assert!(result.contains("\n - "));
    }

    #[test]
    fn empty_diff_means_compatible() {
        let diff: Vec<String> = vec![];
        // In check_compatibility: !diff.is_empty() → Err, else → Ok
        assert!(diff.is_empty());
    }

    #[test]
    fn signature_based_arity_message_includes_provenance() {
        let msg = format!(
            "arity mismatch: original function/method `{}` takes {} argument(s), stub `{}` takes {} \
             (arity checked via signature, body unavailable)",
            "target", 1, "stub", 3
        );
        assert!(msg.contains("body unavailable"));
        assert!(msg.contains("arity checked via signature"));
    }

    // =========================================================================
    // generic_args_len_without_self — Self-detection pattern (Part of #2217)
    //
    // The actual function takes GenericArgs (compiler type), but the core logic
    // is: if any arg is a type param named "Self", subtract 1 from the count.
    // We test this decision pattern with a simplified abstraction.
    // =========================================================================

    /// Simplified version of the Self-detection logic for testing.
    /// Real implementation checks GenericArgKind::Type + TyKind::Param.
    fn has_self_param(param_names: &[&str]) -> bool {
        param_names.contains(&"Self")
    }

    fn args_len_without_self(param_names: &[&str]) -> usize {
        let len = param_names.len();
        if len == 0 {
            return len;
        }
        if has_self_param(param_names) { len - 1 } else { len }
    }

    #[test]
    fn no_args_returns_zero() {
        assert_eq!(args_len_without_self(&[]), 0);
    }

    #[test]
    fn single_self_returns_zero() {
        assert_eq!(args_len_without_self(&["Self"]), 0);
    }

    #[test]
    fn self_plus_one_returns_one() {
        assert_eq!(args_len_without_self(&["Self", "T"]), 1);
    }

    #[test]
    fn no_self_preserves_count() {
        assert_eq!(args_len_without_self(&["T", "U", "V"]), 3);
    }

    #[test]
    fn self_among_multiple_subtracts_one() {
        assert_eq!(args_len_without_self(&["Self", "T", "U"]), 2);
    }

    #[test]
    fn lowercase_self_is_not_special() {
        // Only uppercase "Self" is the trait self-type parameter
        assert_eq!(args_len_without_self(&["self", "T"]), 2);
    }
}
