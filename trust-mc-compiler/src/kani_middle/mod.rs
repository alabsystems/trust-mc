// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! This module contains code that are backend agnostic. For example, MIR analysis
//! and transformations.

use std::collections::HashSet;

use crate::kani_queries::QueryDb;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{def::DefKind, def_id::DefId as InternalDefId, def_id::LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::TerminatorKind;
use rustc_public::mir::mono::{Instance, MonoItem};
use rustc_public::rustc_internal;
use rustc_public::ty::{
    AdtDef, AdtKind, ExistentialPredicate, FnDef, GenericArgKind, GenericArgs, RigidTy,
    Span as SpanStable, Ty, TyKind,
};
use rustc_public::visitor::{Visitable, Visitor};
use rustc_public::{CrateDef, DefId};

use self::attributes::KaniAttributes;

pub(crate) mod abi;
pub(crate) mod analysis;
pub(crate) mod attributes;
pub(crate) mod codegen_units;
pub(crate) mod coercion;
pub(crate) mod kani_functions;
pub(crate) mod metadata;
pub(crate) mod points_to;
pub(crate) mod reachability;
#[cfg(test)]
mod reachability_test;
pub(crate) mod resolve;
pub(crate) mod simd_monomorphization;
pub(crate) mod stable_atomic_policy;
pub(crate) mod stubbing;
pub(crate) mod transform;
pub(crate) mod tuple_usage;
pub(crate) mod type_validity;
#[cfg(test)]
mod unstable_type_test;

/// Check that all crate items are supported and there's no misconfiguration.
/// This method will exhaustively print any error / warning and it will abort at the end if any
/// error was found.
pub(crate) fn check_crate_items(tcx: TyCtxt, ignore_asm: bool) {
    let krate = tcx.crate_name(LOCAL_CRATE);
    let mut all_stub_verified_targets = FxHashMap::default();
    let mut all_contract_targets = HashSet::new();

    for item in tcx.hir_free_items() {
        let def_id = item.owner_id.def_id.to_def_id();
        let (stub_verified_targets, contract_targets) =
            KaniAttributes::for_item(tcx, def_id).check_attributes();
        all_stub_verified_targets.extend(stub_verified_targets);
        all_contract_targets.extend(contract_targets);

        if tcx.def_kind(def_id) == DefKind::GlobalAsm {
            if !ignore_asm {
                let error_msg = format!(
                    "Crate {krate} contains global ASM, which is not supported by trust_mc. Rerun with \
                    `-Z unstable-options --ignore-global-asm` to suppress this error \
                    (**Verification results may be impacted**).",
                );
                tcx.dcx().err(error_msg);
            } else {
                tcx.dcx().warn(format!(
                    "Ignoring global ASM in crate {krate}. Verification results may be impacted.",
                ));
            }
        }
    }

    // Validate that all stub_verified targets have corresponding proof_for_contract harnesses
    for (stub_verified_target, span) in all_stub_verified_targets {
        if !all_contract_targets.contains(&stub_verified_target) {
            tcx.dcx().struct_span_err(
                span,
                format!(
                    "stub verified target `{}` does not have a corresponding `#[proof_for_contract]` harness",
                    stub_verified_target.name()
                ),
            ).with_help("verified stubs are meant to be sound abstractions for a function's behavior, so trust_mc enforces that proofs exist for the stub's contract")
            .emit();
        }
    }

    tcx.dcx().abort_if_errors();
}

/// Check that all given items are supported and there's no misconfiguration.
/// This method will exhaustively print any error / warning and it will abort at the end if any
/// error was found.
pub(crate) fn check_reachable_items(tcx: TyCtxt, queries: &QueryDb, items: &[MonoItem]) {
    // Avoid printing the same error multiple times for different instantiations of the same item.
    let mut def_ids = HashSet::new();
    let mut referenced_type_defs = HashSet::new();
    let reachable_functions: HashSet<DefId> = items
        .iter()
        .filter_map(|i| match i {
            MonoItem::Fn(instance) => Some(instance.def.def_id()),
            _ => None, // external enum: MonoItem
        })
        .collect();
    for item in items.iter().filter(|i| matches!(i, MonoItem::Fn(..) | MonoItem::Static(..))) {
        let def_id = match item {
            MonoItem::Fn(instance) => instance.def.def_id(),
            MonoItem::Static(def) => def.def_id(),
            MonoItem::GlobalAsm(_) => {
                unreachable!("GlobalAsm variant was excluded by filter(Fn | Static)")
            }
        };
        if !def_ids.contains(&def_id) {
            let attributes = KaniAttributes::for_def_id(tcx, def_id);
            // Check if any unstable attribute was reached.
            attributes.check_unstable_features(&queries.args().unstable_features);
            if let MonoItem::Fn(instance) = item
                && let Some(body) = instance.body()
            {
                for (_, local_decl) in body.local_decls() {
                    check_referenced_type_unstable_features(
                        tcx,
                        local_decl.ty,
                        &queries.args().unstable_features,
                        &mut referenced_type_defs,
                    );
                }
            }
            // Check whether all `proof_for_contract` targets are reachable
            attributes.check_proof_for_contract_reachability(&reachable_functions);
            def_ids.insert(def_id);
        }
    }
    // Replay rustc's monomorphization-time generic-SIMD-intrinsic checks
    // (E0511): rustc performs these during codegen of each reachable
    // instantiation, which trust-mc replaces — an ill-typed instantiation must
    // be a compile error here, never a verification verdict.
    simd_monomorphization::check_simd_intrinsic_monomorphizations(tcx, items);
    tcx.dcx().abort_if_errors();
}

fn check_referenced_type_unstable_features(
    tcx: TyCtxt,
    ty: Ty,
    enabled_features: &[String],
    visited_defs: &mut HashSet<DefId>,
) {
    struct UnstableTypeChecker<'tcx, 'a> {
        tcx: TyCtxt<'tcx>,
        enabled_features: &'a [String],
        visited_defs: &'a mut HashSet<DefId>,
    }

    impl Visitor for UnstableTypeChecker<'_, '_> {
        type Break = ();

        fn visit_ty(&mut self, ty: &Ty) -> std::ops::ControlFlow<Self::Break> {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                    let def_id = def.def_id();
                    if self.visited_defs.insert(def_id) {
                        let attributes = KaniAttributes::for_def_id(self.tcx, def_id);
                        let saw_raw_unstable = attributes.has_unstable_feature_attr();
                        attributes.check_unstable_features(self.enabled_features);
                        if !saw_raw_unstable {
                            attributes::check_stable_tool_unstable_features(
                                self.tcx,
                                def_id,
                                def,
                                self.enabled_features,
                            );
                        }
                    }
                }
                TyKind::RigidTy(RigidTy::Dynamic(preds, _)) => {
                    for pred in preds {
                        let def_id = match &pred.value {
                            ExistentialPredicate::Trait(trait_ref) => trait_ref.def_id.def_id(),
                            ExistentialPredicate::Projection(projection) => {
                                projection.def_id.def_id()
                            }
                            ExistentialPredicate::AutoTrait(_) => continue,
                        };
                        if self.visited_defs.insert(def_id) {
                            KaniAttributes::for_def_id(self.tcx, def_id)
                                .check_unstable_features(self.enabled_features);
                        }
                    }
                }
                _ => {}
            }
            ty.super_visit(self)
        }
    }

    let mut checker = UnstableTypeChecker { tcx, enabled_features, visited_defs };
    let _ = ty.visit(&mut checker);
}

#[cfg(test)]
fn referenced_unstable_type_defs(ty: Ty) -> Vec<DefId> {
    struct DefCollector {
        defs: Vec<DefId>,
    }

    impl Visitor for DefCollector {
        type Break = ();

        fn visit_ty(&mut self, ty: &Ty) -> std::ops::ControlFlow<Self::Break> {
            match ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, _)) => self.defs.push(def.def_id()),
                TyKind::RigidTy(RigidTy::Dynamic(preds, _)) => {
                    for pred in preds {
                        match &pred.value {
                            ExistentialPredicate::Trait(trait_ref) => {
                                self.defs.push(trait_ref.def_id.def_id());
                            }
                            ExistentialPredicate::Projection(projection) => {
                                self.defs.push(projection.def_id.def_id());
                            }
                            ExistentialPredicate::AutoTrait(_) => {}
                        }
                    }
                }
                _ => {}
            }
            ty.super_visit(self)
        }
    }

    let mut collector = DefCollector { defs: Vec::new() };
    let _ = ty.visit(&mut collector);
    collector.defs
}

/// Structure that represents the source location of a definition.
pub(crate) struct SourceLocation {
    pub(crate) filename: String,
    pub(crate) start_line: usize,
    pub(crate) end_line: usize,
}

impl SourceLocation {
    pub(crate) fn new(span: SpanStable) -> Self {
        let loc = span.get_lines();
        let filename = span.get_filename();
        let start_line = loc.start_line;
        let end_line = loc.end_line;
        SourceLocation { filename, start_line, end_line }
    }
}

/// Return whether `def_id` refers to a nested static allocation.
pub(crate) fn is_anon_static(tcx: TyCtxt, def_id: DefId) -> bool {
    let int_def_id = rustc_internal::internal(tcx, def_id);
    match tcx.def_kind(int_def_id) {
        rustc_hir::def::DefKind::Static { nested, .. } => nested,
        _ => false, // external enum: DefKind
    }
}

/// Try to convert an internal `DefId` to a `FnDef`.
pub(crate) fn stable_fn_def(tcx: TyCtxt, def_id: InternalDefId) -> Option<FnDef> {
    if let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
        rustc_internal::stable(tcx.type_of(def_id)).value.kind()
    {
        Some(def)
    } else {
        None
    }
}

/// Inspect a `kani::any<T>()` call to determine if `T: Arbitrary`
/// `kani_any_def` refers to a function that looks like:
/// ```rust
/// fn any<T: Arbitrary>() -> T {
///   T::any()
/// }
/// ```
/// So we select the terminator that calls T::kani::Arbitrary::any(), then try to resolve it to an Instance.
/// `T` implements Arbitrary iff we successfully resolve the Instance.
fn implements_arbitrary(
    ty: Ty,
    kani_any_def: FnDef,
    ty_arbitrary_cache: &mut FxHashMap<Ty, bool>,
) -> bool {
    if let Some(v) = ty_arbitrary_cache.get(&ty) {
        return *v;
    }

    if ty.kind().rigid().is_none() {
        return false;
    }

    if let TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _)) = ty.kind() {
        if let TyKind::RigidTy(RigidTy::Adt(..)) = inner_ty.kind() {
            return can_derive_arbitrary(inner_ty, kani_any_def, ty_arbitrary_cache);
        }
        return implements_arbitrary(inner_ty, kani_any_def, ty_arbitrary_cache);
    }

    let kani_any_body =
        Instance::resolve(kani_any_def, &GenericArgs(vec![GenericArgKind::Type(ty)]))
            .expect("should resolve kani_any instance")
            .body()
            .expect("kani_any instance should have a body");

    for bb in &kani_any_body.blocks {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            continue;
        };
        if let TyKind::RigidTy(RigidTy::FnDef(def, args)) =
            func.ty(kani_any_body.arg_locals()).expect("func operand should have valid type").kind()
        {
            let res = Instance::resolve(def, &args).is_ok();
            ty_arbitrary_cache.insert(ty, res);
            return res;
        }
    }
    false
}

/// Is `ty` a struct or enum whose fields/variants implement Arbitrary, or a reference to such a
/// type?
///
/// Decision tree (documented for testability — these decisions are exercised via
/// integration tests since the inputs require compiler types):
///   1. Non-ADT, non-reference → false
///   2. Reference → recurse via can_derive_arbitrary on inner type
///   3. ADT with any lifetime generic arg → false
///   4. Union → false
///   5. Enum with 0 variants → false
///   6. Enum/Struct → true iff all fields in all variants implement/can-derive Arbitrary
///      (ADT fields recurse via can_derive_arbitrary; non-ADT fields via implements_arbitrary)
fn can_derive_arbitrary(
    ty: Ty,
    kani_any_def: FnDef,
    ty_arbitrary_cache: &mut FxHashMap<Ty, bool>,
) -> bool {
    let mut variants_can_derive = |def: AdtDef, args: GenericArgs| {
        for variant in def.variants_iter() {
            let fields = variant.fields();
            let mut fields_impl_arbitrary = true;
            for ty in fields.iter().map(|field| field.ty_with_args(&args)) {
                if let TyKind::RigidTy(RigidTy::Adt(..)) = ty.kind() {
                    fields_impl_arbitrary &=
                        can_derive_arbitrary(ty, kani_any_def, ty_arbitrary_cache);
                } else {
                    fields_impl_arbitrary &=
                        implements_arbitrary(ty, kani_any_def, ty_arbitrary_cache);
                }
            }
            if !fields_impl_arbitrary {
                return false;
            }
        }
        true
    };

    if let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() {
        for arg in &args.0 {
            if let GenericArgKind::Lifetime(..) = arg {
                return false;
            }
        }

        match def.kind() {
            AdtKind::Enum => {
                // Enums with no variants cannot be instantiated
                if def.num_variants() == 0 {
                    return false;
                }
                variants_can_derive(def, args)
            }
            AdtKind::Struct => variants_can_derive(def, args),
            AdtKind::Union => false,
        }
    } else if let TyKind::RigidTy(RigidTy::Ref(_, inner_ty, _)) = ty.kind() {
        can_derive_arbitrary(inner_ty, kani_any_def, ty_arbitrary_cache)
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // =========================================================================
    // SourceLocation — pure data structure tests (Part of #2217)
    // =========================================================================

    #[test]
    fn source_location_fields_accessible() {
        let loc =
            SourceLocation { filename: "src/main.rs".to_string(), start_line: 10, end_line: 20 };
        assert_eq!(loc.filename, "src/main.rs");
        assert_eq!(loc.start_line, 10);
        assert_eq!(loc.end_line, 20);
    }

    #[test]
    fn source_location_single_line() {
        let loc = SourceLocation { filename: "lib.rs".to_string(), start_line: 42, end_line: 42 };
        assert_eq!(loc.start_line, loc.end_line);
    }

    #[test]
    fn source_location_empty_filename() {
        let loc = SourceLocation { filename: String::new(), start_line: 0, end_line: 0 };
        assert!(loc.filename.is_empty());
        assert_eq!(loc.start_line, 0);
    }

    #[test]
    fn source_location_multiline_span() {
        let loc = SourceLocation {
            filename: "trust_mc-compiler/src/kani_middle/mod.rs".to_string(),
            start_line: 100,
            end_line: 270,
        };
        assert!(loc.end_line > loc.start_line);
        assert_eq!(loc.end_line - loc.start_line, 170);
    }

    // =========================================================================
    // Module structure — verify submodule declarations exist (Part of #2217)
    // =========================================================================

    /// Verify that key public submodules are importable and contain expected types.
    /// If any submodule declaration is removed or renamed, this fails at compile time.
    #[test]
    fn submodule_declarations_consistent() {
        // Each module is imported and one public type is referenced to suppress
        // unused-import warnings while proving the module path compiles.
        assert!(!std::any::type_name::<super::abi::LayoutOf>().is_empty());
        assert!(!std::any::type_name::<super::attributes::KaniAttributes>().is_empty());
        assert!(!std::any::type_name::<super::coercion::CoercionBase>().is_empty());
        assert!(!std::any::type_name::<super::kani_functions::KaniFunction>().is_empty());
        assert!(!std::any::type_name::<super::reachability::CallGraph>().is_empty());
    }
}
