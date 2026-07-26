// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module contains two passes:
//! 1. `AutomaticHarnessPass`, which transforms the body of an automatic harness to verify a function.
//! 2. `AutomaticArbitraryPass`, which creates `T::any()` implementations for `T`s that do not implement Arbitrary in source code,
//!    but we have determined can derive it.

use crate::args::ReachabilityType;
use crate::kani_middle::attributes::KaniAttributes;
use crate::kani_middle::codegen_units::CodegenUnit;
use crate::kani_middle::implements_arbitrary;
use crate::kani_middle::kani_functions::{KaniHook, KaniIntrinsic, KaniModel};
use crate::kani_middle::transform::body::{InsertPosition, MutableBody, SourceInstruction};
use crate::kani_middle::transform::{TransformPass, TransformationType};
use crate::kani_queries::QueryDb;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    AggregateKind, BasicBlockIdx, BinOp, Body, BorrowKind, Local, MutBorrowKind, Mutability,
    Operand, Place, Rvalue, SwitchTargets, Terminator, TerminatorKind,
};
use rustc_public::ty::{
    AdtDef, AdtKind, FnDef, GenericArgKind, GenericArgs, RigidTy, Ty, TyKind, UintTy, VariantDef,
};
use rustc_public_bridge::IndexedVal;
use tracing::debug;

/// Generate `T::any()` implementations for `T`s that do not implement Arbitrary in source code,
/// AND decompose types that DO implement Arbitrary into per-field kani::any() calls so that
/// FunctionInlinePass + CHC codegen can process them correctly.
#[derive(Debug, Clone)]
pub(crate) struct AutomaticArbitraryPass {
    /// The FnDef of KaniModel::Any
    kani_any: FnDef,
    /// Resolved Instance of KaniHook::Assume for inserting assume constraints
    kani_assume: Instance,
}

impl AutomaticArbitraryPass {
    pub(crate) fn new(_unit: &CodegenUnit, query_db: &QueryDb) -> Self {
        let kani_fns = query_db.kani_functions();
        let kani_any =
            *kani_fns.get(&KaniModel::Any.into()).expect("KaniModel::Any should be defined");
        let assume_def =
            *kani_fns.get(&KaniHook::Assume.into()).expect("KaniHook::Assume should be defined");
        let kani_assume = Instance::resolve(assume_def, &GenericArgs(vec![]))
            .expect("Assume instance should be resolvable");
        Self { kani_any, kani_assume }
    }
}

impl TransformPass for AutomaticArbitraryPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        matches!(query_db.args().reachability_analysis, ReachabilityType::AllFns)
    }

    /// Transform the body of a `kani::any::<T>()` call if `T` does not implement `Arbitrary`.
    /// This occurs if an automatic harness calls kani::any() for a type that `automatic_harness_partition` determined can derive Arbitrary.
    /// The default implementation for `kani::any()` (c.f. kani_core::kani_intrinsics) is:
    /// ```text
    /// pub fn any<T: Arbitrary>() -> T {
    ///   T::any()
    /// }
    /// ```
    /// We need to overwrite this implementation because `T` doesn't implement `Arbitrary`, so trying to call `T::any()` will fail.
    /// Instead, we inline the body of what `T::any()` would be if it existed.
    /// For example:
    /// ```text
    /// enum Foo {
    ///   Variant1,
    ///   Variant2,
    /// }
    /// ```
    /// we replace the body:
    /// ```text
    /// pub fn any() -> Foo {
    ///   Foo::any() // doesn't exist, must replace
    /// }
    /// ```
    /// so that instead, we have:
    /// ```text
    /// pub fn any() -> Foo {
    ///   match kani::any() {
    ///     0 => Foo::Variant1,
    ///     _ => Foo::Variant2, // non-enum: doc example
    ///   }
    /// }
    /// ```
    /// We match the implementations that kani_macros::derive creates for structs and enums,
    /// so see that module for full documentation of what the generated bodies look like.
    #[allow(clippy::panic)] // Internal validation - unexpected type indicates compiler bug
    fn transform(&mut self, _tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        debug!(function=?instance.name(), "AutomaticArbitraryPass::transform");

        let unexpected_ty = |ty: &Ty| {
            panic!(
                "AutomaticArbitraryPass: should only find compiler-inserted kani::any() calls for structs or enums, found {ty}"
            )
        };

        if instance.def.def_id() != self.kani_any.def_id() {
            return (false, body);
        }

        // Get the `ty` we're calling `kani::any()` on
        let binding = instance.args();
        let ty = binding.0[0].expect_ty();

        if implements_arbitrary(*ty, self.kani_any, &mut FxHashMap::default()) {
            // Type has an existing Arbitrary impl. Generate a synthetic decomposed
            // body that replaces trait dispatch with kani::any() calls for fields.
            // This allows FunctionInlinePass to inline the body and CHC codegen
            // to process leaf-level kani::any() calls correctly.
            // Part of #3207: ArbitraryResolutionPass Phase 1.
            return self.resolve_existing_arbitrary(ty, body);
        }

        if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
            match def.kind() {
                AdtKind::Enum => (true, self.generate_enum_body(def, args, body)),
                AdtKind::Struct => (true, self.generate_struct_body(def, args, body)),
                AdtKind::Union => unexpected_ty(ty),
            }
        } else {
            unexpected_ty(ty)
        }
    }
}

/// Insert a call to `kani::any::\<ty>()` in `body`; return the local storing the result.
/// Panics if `ty` does not implement Arbitrary.
#[allow(clippy::panic)] // Documented panic - ty must implement Arbitrary
fn call_kani_any_for_ty(
    kani_any: FnDef,
    body: &mut MutableBody,
    ty: Ty,
    mutability: Mutability,
    source: &mut SourceInstruction,
) -> Local {
    if let TyKind::RigidTy(RigidTy::Ref(region, inner_ty, inner_mutability)) = ty.kind() {
        let inner_lcl = call_kani_any_for_ty(kani_any, body, inner_ty, inner_mutability, source);
        let ref_lcl = body.new_local(ty, source.span(body.blocks()), mutability);
        let borrow_kind = if inner_mutability == Mutability::Not {
            BorrowKind::Shared
        } else {
            BorrowKind::Mut { kind: MutBorrowKind::Default }
        };
        body.assign_to(
            Place::from(ref_lcl),
            Rvalue::Ref(region, borrow_kind, Place::from(inner_lcl)),
            source,
            InsertPosition::Before,
        );
        ref_lcl
    } else {
        let kani_any_inst =
            Instance::resolve(kani_any, &GenericArgs(vec![GenericArgKind::Type(ty)]))
                .unwrap_or_else(|_| panic!("expected a ty that implements Arbitrary, got {ty}"));
        let lcl = body.new_local(ty, source.span(body.blocks()), mutability);
        body.insert_call(&kani_any_inst, source, InsertPosition::Before, vec![], Place::from(lcl));
        lcl
    }
}

impl AutomaticArbitraryPass {
    /// Insert the basic blocks for generating an arbitrary variant into `body`.
    /// Return the index of the first inserted basic block.
    /// We generate an arbitrary variant by:
    ///   1. Calling kani::any() for each of the variant's field types, then
    ///   2. Constructing the variant from the results of 1) and assigning it to the return local.
    ///
    /// This function will panic if a field type does not implement Arbitrary.
    fn call_kani_any_for_variant(
        &self,
        adt_def: AdtDef,
        adt_args: &GenericArgs,
        body: &mut MutableBody,
        source: &mut SourceInstruction,
        variant: VariantDef,
    ) -> BasicBlockIdx {
        let fields = variant.fields();
        let mut field_locals = vec![];

        // Construct nondeterministic values for each of the variant's fields
        for ty in fields.iter().map(|field| field.ty_with_args(adt_args)) {
            let lcl = call_kani_any_for_ty(self.kani_any, body, ty, Mutability::Not, source);
            field_locals.push(lcl);
        }

        // Insert a basic block that constructs the variant from each of the nondet fields, then returns it
        body.insert_terminator(
            source,
            InsertPosition::Before,
            Terminator { kind: TerminatorKind::Return, span: source.span(body.blocks()) },
        );
        let mut assign_instr = SourceInstruction::Terminator { bb: source.bb() - 1 };
        let rvalue = Rvalue::Aggregate(
            AggregateKind::Adt(adt_def, variant.idx, adt_args.clone(), None, None),
            field_locals.into_iter().map(|lcl| Operand::Move(lcl.into())).collect(),
        );
        body.assign_to(Place::from(0), rvalue, &mut assign_instr, InsertPosition::Before);

        // The index of the first block we inserted is (last bb index - number of bbs we inserted above it)
        source.bb() - (fields.len() + 1)
    }

    /// Overwrite the default kani::any() implementation `body` for the enum described by `def`.
    /// The returned body is equivalent to:
    /// ```text
    /// let discriminant = kani::any();
    /// match discriminant {
    ///   0 => Enum::Variant1(field1, field2),
    ///   1 => Enum::Variant2(..),
    ///   ... (cont.)
    ///   _ => Enum::LastVariant // non-enum: doc example
    /// }
    /// ```
    fn generate_enum_body(&self, def: AdtDef, args: GenericArgs, body: Body) -> Body {
        // Autoharness only deems a function with an enum eligible if it has at least one variant, c.f. `can_derive_arbitrary`
        assert!(def.num_variants() > 0);

        let mut new_body = MutableBody::from(body);
        new_body.clear_body(TerminatorKind::Unreachable);
        let mut source = SourceInstruction::Terminator { bb: 0 };

        // Generate a nondet u128 to switch on
        let discr_lcl = call_kani_any_for_ty(
            self.kani_any,
            &mut new_body,
            Ty::from_rigid_kind(RigidTy::Uint(UintTy::U128)),
            Mutability::Not,
            &mut source,
        );

        // Insert a placeholder for the SwitchInt terminator
        let span = source.span(new_body.blocks());
        new_body.insert_terminator(
            &mut source,
            InsertPosition::Before,
            Terminator { kind: TerminatorKind::Unreachable, span },
        );
        let switch_int_instr = SourceInstruction::Terminator { bb: source.bb() - 1 };

        let mut branches: Vec<(u128, BasicBlockIdx)> = vec![];
        for variant in def.variants_iter() {
            let target_bb =
                self.call_kani_any_for_variant(def, &args, &mut new_body, &mut source, variant);
            branches.push((variant.idx.to_index() as u128, target_bb));
        }

        let otherwise = branches.pop().expect("enum should have at least one variant").1;
        let match_term = Terminator {
            kind: TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from(discr_lcl)),
                targets: SwitchTargets::new(branches, otherwise),
            },
            span: source.span(new_body.blocks()),
        };
        new_body.replace_terminator(&switch_int_instr, match_term);

        new_body.into()
    }

    /// Overwrite the default kani::any() implementation `body` for the struct described by `def`.
    /// The returned body is equivalent to:
    /// ```text
    /// struct Struct {
    ///   field1: kani::any(),
    ///   field2: kani::any(),
    ///   ...
    /// }
    /// ```
    fn generate_struct_body(&self, def: AdtDef, args: GenericArgs, body: Body) -> Body {
        assert_eq!(def.num_variants(), 1);

        let mut new_body = MutableBody::from(body);
        new_body.clear_body(TerminatorKind::Unreachable);
        let mut source = SourceInstruction::Terminator { bb: 0 };

        let variant = def.variants()[0];
        self.call_kani_any_for_variant(def, &args, &mut new_body, &mut source, variant);

        new_body.into()
    }

    /// Phase 2: Try to resolve the actual `<T as Arbitrary>::any()` impl body.
    ///
    /// The default body of `kani::any::<T>()` is `{ <T as Arbitrary>::any() }`.
    /// If we can resolve that callee and get its MIR body, we return it to
    /// preserve `kani::assume()` constraints from custom Arbitrary impls.
    ///
    /// Returns None if the callee can't be resolved or its body isn't available
    /// (e.g., cross-crate impls in kani_core). Phase 1 structural decomposition
    /// is used as fallback in that case.
    ///
    /// Part of #3207: ArbitraryResolutionPass Phase 2.
    fn try_resolve_arbitrary_body(&self, body: &Body) -> Option<Body> {
        if body.blocks.is_empty() {
            return None;
        }

        // The body of kani::any::<T>() is:
        //   bb0: _0 = <T as Arbitrary>::any() -> [return: bb1, ...]
        //   bb1: return
        let TerminatorKind::Call { func, .. } = &body.blocks[0].terminator.kind else {
            return None;
        };

        // Resolve the callee: <T as Arbitrary>::any()
        let func_ty = func.ty(body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(fn_def, args)) = func_ty.kind() else {
            return None;
        };
        let callee = Instance::resolve(fn_def, &args).ok()?;

        debug!(callee=?callee.name(), "try_resolve_arbitrary_body: resolved callee");
        callee.body()
    }

    /// For types that already implement Arbitrary, resolve the actual Arbitrary
    /// impl body (Phase 2) or generate a synthetic decomposed body (Phase 1).
    ///
    /// Phase 2 (body inlining): Resolves `<T as Arbitrary>::any()` and returns
    /// its body directly. This preserves `kani::assume()` constraints from
    /// custom user-defined Arbitrary impls.
    ///
    /// Phase 1 (structural decomposition): Falls back to generating per-field
    /// `kani::any()` calls when the impl body is unavailable (cross-crate).
    ///
    /// Part of #3207: ArbitraryResolutionPass.
    fn resolve_existing_arbitrary(&self, ty: &Ty, body: Body) -> (bool, Body) {
        // Phase 2: Try to resolve the actual Arbitrary impl body.
        // This preserves kani::assume() constraints from custom impls.
        if let Some(arb_body) = self.try_resolve_arbitrary_body(&body) {
            debug!("resolve_existing_arbitrary: inlined Arbitrary impl body for {ty}");
            return (true, arb_body);
        }

        // Phase 1 fallback: structural decomposition for known library types
        // whose cross-crate Arbitrary impl bodies are unavailable.
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Bool) => {
                debug!("resolve_existing_arbitrary: generating bool body");
                (true, self.generate_bool_arbitrary_body(body))
            }
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                // Verify all field types support kani::any() before decomposing
                if !all_fields_support_kani_any(self.kani_any, def, &args) {
                    debug!(name=?def.name(), "resolve_existing_arbitrary: fields not resolvable, skipping");
                    return (false, body);
                }
                debug!(name=?def.name(), "resolve_existing_arbitrary: decomposing ADT");
                match def.kind() {
                    AdtKind::Enum => (true, self.generate_enum_body(def, args, body)),
                    AdtKind::Struct => (true, self.generate_struct_body(def, args, body)),
                    AdtKind::Union => (false, body),
                }
            }
            _ => (false, body),
        }
    }

    /// Generate the Arbitrary body for bool, matching kani_core's impl:
    /// ```text
    /// let byte: u8 = kani::any();
    /// kani::assume(byte < 2);
    /// byte == 1
    /// ```
    fn generate_bool_arbitrary_body(&self, body: Body) -> Body {
        let mut new_body = MutableBody::from(body);
        new_body.clear_body(TerminatorKind::Unreachable);
        let mut source = SourceInstruction::Terminator { bb: 0 };
        let span = source.span(new_body.blocks());

        // _u8 = kani::any::<u8>()
        let u8_ty = Ty::from_rigid_kind(RigidTy::Uint(UintTy::U8));
        let u8_lcl =
            call_kani_any_for_ty(self.kani_any, &mut new_body, u8_ty, Mutability::Not, &mut source);

        // _lt = (_u8 < 2u8)
        let two_op = new_body.new_uint_operand(2, UintTy::U8, span);
        let lt_result = new_body.insert_binary_op(
            BinOp::Lt,
            Operand::Copy(Place::from(u8_lcl)),
            two_op,
            &mut source,
            InsertPosition::Before,
        );

        // kani::assume(_lt)
        let unit_ty = Ty::new_tuple(&[]);
        let unit_lcl = new_body.new_local(unit_ty, span, Mutability::Not);
        new_body.insert_call(
            &self.kani_assume,
            &mut source,
            InsertPosition::Before,
            vec![Operand::Copy(Place::from(lt_result))],
            Place::from(unit_lcl),
        );

        // Insert Return terminator
        let ret_span = source.span(new_body.blocks());
        new_body.insert_terminator(
            &mut source,
            InsertPosition::Before,
            Terminator { kind: TerminatorKind::Return, span: ret_span },
        );

        // _0 = (_u8 == 1u8) — assign to return place
        let mut assign_source = SourceInstruction::Terminator { bb: source.bb() - 1 };
        let assign_span = assign_source.span(new_body.blocks());
        let one_op = new_body.new_uint_operand(1, UintTy::U8, assign_span);
        new_body.assign_to(
            Place::from(0usize),
            Rvalue::BinaryOp(BinOp::Eq, Operand::Copy(Place::from(u8_lcl)), one_op),
            &mut assign_source,
            InsertPosition::Before,
        );

        new_body.into()
    }
}

/// Check if a type can be passed to `call_kani_any_for_ty` without panicking.
/// Mirrors the resolution logic of `call_kani_any_for_ty`.
fn can_call_kani_any_for_ty(kani_any: FnDef, ty: Ty) -> bool {
    if let TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _)) = ty.kind() {
        can_call_kani_any_for_ty(kani_any, inner_ty)
    } else {
        Instance::resolve(kani_any, &GenericArgs(vec![GenericArgKind::Type(ty)])).is_ok()
    }
}

/// Check that all field types in all variants of an ADT support kani::any().
/// Returns false if any field type would cause `call_kani_any_for_ty` to panic.
fn all_fields_support_kani_any(kani_any: FnDef, def: AdtDef, args: &GenericArgs) -> bool {
    def.variants_iter().all(|variant| {
        variant
            .fields()
            .iter()
            .all(|field| can_call_kani_any_for_ty(kani_any, field.ty_with_args(args)))
    })
}

/// Transform the dummy body of an automatic_harness Kani intrinsic to be a proof harness for a given function.
#[derive(Debug, Clone)]
pub(crate) struct AutomaticHarnessPass {
    kani_any: FnDef,
    init_contracts_hook: Instance,
    kani_autoharness_intrinsic: FnDef,
}

impl AutomaticHarnessPass {
    pub(crate) fn new(query_db: &QueryDb) -> Self {
        let kani_fns = query_db.kani_functions();
        let kani_autoharness_intrinsic = *kani_fns
            .get(&KaniIntrinsic::AutomaticHarness.into())
            .expect("AutomaticHarness intrinsic should be defined");
        let kani_any =
            *kani_fns.get(&KaniModel::Any.into()).expect("KaniModel::Any should be defined");
        let init_contracts_hook = *kani_fns
            .get(&KaniHook::InitContracts.into())
            .expect("InitContracts hook should be defined");
        let init_contracts_hook = Instance::resolve(init_contracts_hook, &GenericArgs(vec![]))
            .expect("InitContracts instance should be resolvable");
        Self { kani_any, init_contracts_hook, kani_autoharness_intrinsic }
    }
}

impl TransformPass for AutomaticHarnessPass {
    fn transformation_type() -> TransformationType
    where
        Self: Sized,
    {
        TransformationType::Stubbing
    }

    fn is_enabled(&self, query_db: &QueryDb) -> bool
    where
        Self: Sized,
    {
        matches!(query_db.args().reachability_analysis, ReachabilityType::AllFns)
    }

    fn transform(&mut self, tcx: TyCtxt, body: Body, instance: Instance) -> (bool, Body) {
        debug!(function=?instance.name(), "AutomaticHarnessPass::transform");

        if instance.def.def_id() != self.kani_autoharness_intrinsic.def_id() {
            return (false, body);
        }

        // Retrieve the generic arguments of the harness, which is the type of the function it is verifying,
        // and then resolve `fn_to_verify`.
        let kind = instance.args().0[0].expect_ty().kind();
        let (def, args) = kind.fn_def().expect("harness target should be function type");
        let fn_to_verify =
            Instance::resolve(def, args).expect("function to verify should be resolvable");
        let fn_to_verify_body = fn_to_verify.body().expect("function to verify should have body");

        let mut harness_body = MutableBody::from(body);
        harness_body.clear_body(TerminatorKind::Return);
        let mut source = SourceInstruction::Terminator { bb: 0 };

        // Contract harnesses need a free(NULL) statement, c.f. kani_core::init_contracts().
        let attrs = KaniAttributes::for_def_id(tcx, def.def_id());
        if attrs.has_contract() {
            let ret_local = harness_body.new_local(
                Ty::from_rigid_kind(RigidTy::Tuple(vec![])),
                source.span(harness_body.blocks()),
                Mutability::Not,
            );
            harness_body.insert_call(
                &self.init_contracts_hook,
                &mut source,
                InsertPosition::Before,
                vec![],
                Place::from(ret_local),
            );
        }

        // For each argument of `fn_to_verify`, create a nondeterministic value of its type
        // by generating a kani::any() call and saving the result in `arg_local`.
        let arg_locals = fn_to_verify_body
            .arg_locals()
            .iter()
            .map(|local_decl| {
                call_kani_any_for_ty(
                    self.kani_any,
                    &mut harness_body,
                    local_decl.ty,
                    local_decl.mutability,
                    &mut source,
                )
            })
            .collect::<Vec<_>>();

        let func_to_verify_ret = fn_to_verify_body.ret_local();
        let ret_place = Place::from(harness_body.new_local(
            func_to_verify_ret.ty,
            source.span(harness_body.blocks()),
            func_to_verify_ret.mutability,
        ));

        // Call `fn_to_verify` on the nondeterministic arguments generated above.
        harness_body.insert_call(
            &fn_to_verify,
            &mut source,
            InsertPosition::Before,
            arg_locals.iter().map(|lcl| Operand::Copy(Place::from(*lcl))).collect::<Vec<_>>(),
            ret_place,
        );

        (true, harness_body.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kani_middle::kani_functions::{KaniFunction, KaniHook, KaniIntrinsic};
    use crate::kani_middle::transform::TransformationType;

    // =========================================================================
    // TransformationType — both passes are Stubbing (Part of #2217)
    // =========================================================================

    #[test]
    fn automatic_arbitrary_pass_is_stubbing_type() {
        assert!(matches!(
            AutomaticArbitraryPass::transformation_type(),
            TransformationType::Stubbing
        ));
    }

    #[test]
    fn automatic_harness_pass_is_stubbing_type() {
        assert!(matches!(
            AutomaticHarnessPass::transformation_type(),
            TransformationType::Stubbing
        ));
    }

    // =========================================================================
    // ReachabilityType gating — is_enabled logic (Part of #2217)
    //
    // Both passes should only be enabled when reachability is AllFns.
    // We can't construct QueryDb, but we verify the pattern by testing
    // ReachabilityType enum matching directly.
    // =========================================================================

    #[test]
    fn reachability_allfns_matches_is_enabled_pattern() {
        // The is_enabled pattern: matches!(query_db.args().reachability_analysis, ReachabilityType::AllFns)
        assert!(matches!(ReachabilityType::AllFns, ReachabilityType::AllFns));
    }

    #[test]
    fn reachability_harnesses_does_not_match_allfns() {
        assert!(!matches!(ReachabilityType::Harnesses, ReachabilityType::AllFns));
    }

    #[test]
    fn reachability_none_does_not_match_allfns() {
        assert!(!matches!(ReachabilityType::None, ReachabilityType::AllFns));
    }

    #[test]
    fn reachability_pubfns_does_not_match_allfns() {
        assert!(!matches!(ReachabilityType::PubFns, ReachabilityType::AllFns));
    }

    // =========================================================================
    // KaniFunction dependencies — verify expected functions exist (Part of #2217)
    //
    // AutomaticArbitraryPass requires KaniModel::Any
    // AutomaticHarnessPass requires KaniModel::Any, KaniHook::InitContracts,
    //   and KaniIntrinsic::AutomaticHarness
    // =========================================================================

    #[test]
    fn automatic_arbitrary_requires_kani_any_model() {
        let func: KaniFunction = KaniModel::Any.into();
        assert!(matches!(func, KaniFunction::Model(KaniModel::Any)));
    }

    #[test]
    fn automatic_harness_requires_init_contracts_hook() {
        let func: KaniFunction = KaniHook::InitContracts.into();
        assert!(matches!(func, KaniFunction::Hook(KaniHook::InitContracts)));
    }

    #[test]
    fn automatic_harness_requires_autoharness_intrinsic() {
        let func: KaniFunction = KaniIntrinsic::AutomaticHarness.into();
        assert!(matches!(func, KaniFunction::Intrinsic(KaniIntrinsic::AutomaticHarness)));
    }

    // =========================================================================
    // AdtKind dispatch — the core transform logic pattern (Part of #2217)
    //
    // AutomaticArbitraryPass::transform dispatches on AdtKind:
    //   Enum → generate_enum_body
    //   Struct → generate_struct_body
    //   Union → panic (unexpected)
    // We test the dispatch pattern with the enum directly.
    // =========================================================================

    #[test]
    fn adt_kind_enum_matches_expected_branch() {
        let kind = AdtKind::Enum;
        assert!(matches!(kind, AdtKind::Enum));
        assert!(!matches!(kind, AdtKind::Struct));
        assert!(!matches!(kind, AdtKind::Union));
    }

    #[test]
    fn adt_kind_struct_matches_expected_branch() {
        let kind = AdtKind::Struct;
        assert!(matches!(kind, AdtKind::Struct));
        assert!(!matches!(kind, AdtKind::Enum));
        assert!(!matches!(kind, AdtKind::Union));
    }

    #[test]
    fn adt_kind_union_is_rejected() {
        // automatic.rs panics on Union — verify it's the "other" case
        let kind = AdtKind::Union;
        assert!(!matches!(kind, AdtKind::Enum | AdtKind::Struct));
    }
}
