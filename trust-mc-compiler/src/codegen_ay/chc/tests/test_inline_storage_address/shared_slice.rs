// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Actual source/encoder controls. These prepare no solver verdict.
use super::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::ptr_repr::PtrRepr;
use rustc_public::ty::Ty;

const VIEW_DEPENDENCY: &str = r#"
#![allow(dead_code,unused_assignments)]
#[repr(C)] pub struct Pair { pub first:u64, pub second:u64 }
impl Pair {
 #[inline(never)] pub fn first_view(&self)->&[u64] { std::slice::from_ref(&self.first) }
 #[inline(never)] pub fn second_view(&self)->&[u64] { let field=&self.second; std::slice::from_ref(field) }
 #[inline(never)] pub fn effectful_view(&self)->&[u64] { std::hint::black_box(self.first); std::slice::from_ref(&self.second) }
 #[inline(never)] pub fn shadow_view(&self)->&[u64] { shadow::from_ref(&self.second) }
}
mod shadow { #[inline(never)] pub fn from_ref(value:&u64)->&[u64] { std::slice::from_ref(value) } }
pub mod alloc { pub mod vec {
 #[repr(C)] pub struct Vec<T> { pub value:T, pub other:usize }
 impl<T> Vec<T> { #[inline(never)] pub fn as_slice(&self)->&[T] { std::slice::from_ref(&self.value) } }
} }
"#;
const VIEW_SOURCE: &str = r#"
#![allow(dead_code,unused_assignments)]
extern crate external_vec_lookalike;
use external_vec_lookalike::Pair;
use external_vec_lookalike::alloc::vec::Vec as ForeignVec;
pub fn cargo_native() { let value=ForeignVec{value:3u64,other:7}; assert!(value.as_slice()[0]==3); }
pub fn first() { let value=Pair{first:3,second:7}; let view=value.first_view(); assert!(view[0]==3); }
pub fn second() { let value=Pair{first:3,second:7}; let view=value.second_view(); let alias=view; assert!(alias[0]==7); }
pub fn current() { let mut value=Pair{first:3,second:7}; value.second=9; let view=value.second_view(); assert!(view[0]==9); }
pub fn same_value_owners() { let a=Pair{first:3,second:7}; let b=Pair{first:3,second:7}; let one=a.second_view(); let two=b.second_view(); assert!(one[0]==two[0]); }
pub fn retargeted() { let a=Pair{first:3,second:7}; let b=Pair{first:3,second:9}; let mut view=a.second_view(); view=b.second_view(); assert!(view[0]==9); }
pub fn exposed() { let value=Pair{first:3,second:7}; let view=value.second_view(); let _slot=&raw const view; assert!(view[0]==7); }
pub fn effectful() { let value=Pair{first:3,second:7}; let view=value.effectful_view(); assert!(view[0]==7); }
pub fn shadowed() { let value=Pair{first:3,second:7}; let view=value.shadow_view(); assert!(view[0]==7); }
pub fn escaped() -> &'static[u64] { let value=Pair{first:3,second:7}; let view=value.second_view(); unsafe{ std::mem::transmute(view) } }
"#;

fn with_context<F>(callback: F)
where
    F: for<'tcx> FnOnce(crate::codegen_ay::context::AYCtx<'tcx, 'static>) + Send,
{
    crate::codegen_ay::context::with_test_ay_ctx_for_external_source(
        VIEW_DEPENDENCY,
        VIEW_SOURCE,
        &["-Cpanic=abort", "-Zmir-enable-passes=-RemoveStorageMarkers", "-Zinline-mir=no"],
        callback,
    );
}

fn dispatch<'a>(
    body: &'a Body,
    bb: usize,
    constraints: &'a [Expr],
    modified: &'a HashSet<usize>,
    from: &'a RelationApp,
) -> DispatchCallContext<'a> {
    let TerminatorKind::Call { func, args, destination, target, .. } =
        &body.blocks[bb].terminator.kind
    else {
        panic!("actual call")
    };
    DispatchCallContext {
        bb_idx: bb,
        func,
        args,
        destination,
        target,
        from_app: from,
        stmt_constraints: constraints,
        modified_locals: modified,
        callee_path: None,
    }
}
fn from(context: &ChcCtx<'_, '_>, bb: usize) -> RelationApp {
    let relation = context.block_relations.get(&bb).unwrap();
    RelationApp::new(
        relation,
        context
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect(),
    )
}
fn callee(tcx: TyCtxt<'_>, instance: Instance, label: &str) -> Body {
    let body = crate::kani_middle::transform::walker_transformed_body(tcx, instance)
        .expect("actual walker-selected body");
    retain_storage_body(&format!("shared_slice_{label}_callee"), &body);
    body
}
fn folded(value: &Expr) -> Expr {
    trust_mc_core::chc_const_prop::eval::try_eval_to_const(value).unwrap_or_else(|| value.clone())
}

fn scalar_at(mut image: &Expr, address: &Expr) -> Option<Expr> {
    while let ExprValue::Store { array, index, value } = image.value() {
        // Stores can carry a concatenated object and offset. Resolve only
        // concrete addresses and retain the most recent matching write.
        let concrete = folded(index);
        if !matches!(concrete.value(), ExprValue::BitVecConst { .. }) {
            return None;
        }
        if &concrete == address {
            return Some(folded(value));
        }
        image = array;
    }
    None
}

#[test]
fn native_shared_one_slice_preserves_field_layout_alias_and_current_typed_memory() {
    with_context(|ctx| {
        for (host, method, offset, expected) in [
            ("cargo_native", "as_slice", 0, 3),
            ("first", "first_view", 0, 3),
            ("second", "second_view", 8, 7),
            ("current", "second_view", 8, 9),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, host).callee_body().unwrap();
            retain_storage_body(&format!("shared_slice_{host}_host"), &body);
            let mut context = ChcCtx::new(ctx.tcx, &body, host, mem_config());
            context.declare_block_relations();
            let sites: Vec<_> = (0..body.blocks.len())
                .filter_map(|bb| {
                    let (instance, args) = resolve_call(&body, bb)?;
                    instance.def.name().ends_with(method).then_some((bb, instance, args))
                })
                .collect();
            assert_eq!(sites.len(), 1);
            let (bb, instance, _) = sites[0];
            assert_eq!(bb, 0, "current scalar store precedes the first real getter");
            let (constraints, _, modified, _) = context.encode_block_statements(bb);
            let image = context
                .heap_state
                .get_store_chain(&ChcCtx::type_key_for_ty(Ty::from_rigid_kind(RigidTy::Uint(
                    UintTy::U64,
                ))))
                .expect("actual prefix encoded the current scalar type array")
                .clone();
            let from = from(&context, bb);
            let call = dispatch(&body, bb, &constraints, &modified, &from);
            let callee = callee(ctx.tcx, instance, host);
            if host == "first" {
                context.with_inline_walk_frame(&callee, |context| {
                    assert!(
                        !context.try_inline_storage_address(&call, &callee, instance),
                        "frame-local numbers cannot borrow host storage authority"
                    );
                });
                context.with_inline_walk_write_mark(|context| {
                    assert!(
                        !context.try_inline_storage_address(&call, &callee, instance),
                        "an outer walk scope cannot use host storage authority"
                    );
                });
            }
            let before = context.sound_fallback_count();
            let before_rules = context.vc.rules.len();
            let addresses = context.heap_state.local_addresses.clone();
            assert!(
                context.try_inline_storage_address(&call, &callee, instance),
                "actual native view route required: {host}: {callee:#?}"
            );
            assert_eq!(context.sound_fallback_count(), before);
            assert_eq!(
                context.heap_state.local_addresses, addresses,
                "one-element view creates no allocation"
            );
            let dest = call.destination.local;
            assert!(!context.ref_resolution.const_ref_values.contains_key(&dest));
            assert!(
                !context.ref_resolution.ref_targets.contains_key(&dest),
                "scalar storage must not become an array target"
            );
            assert_eq!(
                context.ref_resolution.subslice_len.get(&dest),
                Some(&Expr::bitvec_const(1u64, 64))
            );
            let (_, destination) = context.resolve_destination(dest).unwrap();
            let actual = context.vc.rules[before_rules..]
                .iter()
                .flat_map(|rule| &rule.body.constraints)
                .find_map(|constraint| match constraint.value() {
                    ExprValue::Eq(left, right) if left == &destination => Some(right.clone()),
                    _ => None,
                })
                .expect("actual emitted fat-pointer result equality");
            let repr = PtrRepr::classify(&actual).unwrap();
            assert_eq!(folded(repr.metadata().unwrap().as_expr()), Expr::bitvec_const(1u64, 64));
            let pointer = folded(repr.data().as_expr());
            let (object, actual_offset) = ChcCtx::try_extract_constant_addr(&pointer).unwrap();
            assert_eq!(actual_offset, offset);
            let owner = context
                .heap_state
                .local_idx_for_obj_id(object)
                .expect("original live caller allocation");
            assert_eq!(body.locals()[owner].ty.layout().unwrap().shape().size.bytes(), 16);
            assert_eq!(
                scalar_at(&image, &pointer),
                Some(Expr::bitvec_const(expected, 64)),
                "{host}: current scalar field, including the real pre-view write"
            );
            assert_eq!(folded(&context.known_stack_addr_expr(dest).unwrap()), pointer);
            assert!(context.stack_local_is_live(owner) == Some(true));
        }
        let body = find_instance_by_suffix(ctx.tcx, "same_value_owners").callee_body().unwrap();
        let mut context = ChcCtx::new(ctx.tcx, &body, "same_value_owners", mem_config());
        context.declare_block_relations();
        let mut objects = BTreeSet::new();
        let mut calls = 0;
        for bb in 0..body.blocks.len() {
            let Some((instance, _)) = resolve_call(&body, bb) else { continue };
            if !instance.def.name().ends_with("second_view") {
                continue;
            }
            install_call_liveness(&mut context, bb);
            let from = from(&context, bb);
            let constraints = [];
            let modified = HashSet::new();
            let call = dispatch(&body, bb, &constraints, &modified, &from);
            let callee =
                crate::kani_middle::transform::walker_transformed_body(ctx.tcx, instance).unwrap();
            assert!(context.try_inline_storage_address(&call, &callee, instance));
            let pointer = context.known_stack_addr_expr(call.destination.local).unwrap();
            let (object, offset) = ChcCtx::try_extract_constant_addr(&pointer).unwrap();
            assert_eq!(offset, 8);
            objects.insert(object);
            calls += 1;
        }
        assert_eq!((calls, objects.len()), (2, 2), "equal scalar values retain distinct owners");
    });
}

#[test]
fn native_shared_one_slice_preserves_an_actual_copy_without_copy_prop() {
    // Default MIR coalesces `view` and `alias` into the same local. Keep
    // the normal behavior control above unchanged and separately require a
    // real compiler-produced copy; do not manufacture an assignment in MIR.
    const COPY_FLAGS: &[&str] = &[
        "-Cpanic=abort",
        "-Zmir-enable-passes=-RemoveStorageMarkers,-CopyProp",
        "-Zinline-mir=no",
    ];
    crate::codegen_ay::context::with_test_ay_ctx_for_external_source(
        VIEW_DEPENDENCY,
        VIEW_SOURCE,
        COPY_FLAGS,
        |ctx| {
            retain_storage_artifact(
                "shared_slice_copy_configuration",
                "txt",
                &COPY_FLAGS.join("\n"),
            );
            let body = find_instance_by_suffix(ctx.tcx, "second").callee_body().unwrap();
            retain_storage_body("shared_slice_copy_host", &body);
            let sites: Vec<_> = (0..body.blocks.len())
                .filter_map(|bb| {
                    let (instance, _) = resolve_call(&body, bb)?;
                    instance.def.name().ends_with("second_view").then_some((bb, instance))
                })
                .collect();
            assert_eq!(sites.len(), 1);
            let (bb, instance) = sites[0];
            assert_eq!(bb, 0);
            let TerminatorKind::Call { destination, target: Some(target), .. } =
                &body.blocks[bb].terminator.kind
            else {
                panic!("actual getter return edge required")
            };
            let copies: Vec<_> = body.blocks[*target]
                .statements
                .iter()
                .filter_map(|statement| {
                    let StatementKind::Assign(
                        lhs,
                        rustc_public::mir::Rvalue::Use(Operand::Copy(source), ..),
                    ) = &statement.kind
                    else {
                        return None;
                    };
                    if !lhs.projection.is_empty()
                        || !source.projection.is_empty()
                        || source.local != destination.local
                        || lhs.local == source.local
                    {
                        return None;
                    }
                    let ty = source.ty(body.locals()).ok()?;
                    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, _))
                        if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(_))))
                    .then_some(lhs.local)
                })
                .collect();
            assert_eq!(copies.len(), 1, "actual shared-slice copy producer required: {body:#?}");
            let alias = copies[0];
            let consumed =
                body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
                    let StatementKind::Assign(
                        _,
                        rustc_public::mir::Rvalue::Use(Operand::Copy(source), ..),
                    ) = &statement.kind
                    else {
                        return false;
                    };
                    source.local == alias
                        && matches!(
                            source.projection.as_slice(),
                            [
                                ProjectionElem::Deref,
                                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                            ]
                        )
                });
            assert!(consumed, "the copied slice must feed the actual scalar read: {body:#?}");

            let mut context = ChcCtx::new(ctx.tcx, &body, "second_copy", mem_config());
            context.declare_block_relations();
            let (constraints, _, modified, _) = context.encode_block_statements(bb);
            let scalar_key =
                ChcCtx::type_key_for_ty(Ty::from_rigid_kind(RigidTy::Uint(UintTy::U64)));
            let image = context
                .heap_state
                .get_store_chain(&scalar_key)
                .expect("actual scalar storage before the getter")
                .clone();
            let from = from(&context, bb);
            let call = dispatch(&body, bb, &constraints, &modified, &from);
            let callee = callee(ctx.tcx, instance, "copy");
            let before = context.sound_fallback_count();
            let allocations = context.heap_state.local_addresses.clone();
            assert!(context.try_inline_storage_address(&call, &callee, instance));
            let pointer = folded(&context.known_stack_addr_expr(destination.local).unwrap());
            let (object, offset) = ChcCtx::try_extract_constant_addr(&pointer).unwrap();
            assert_eq!(offset, 8);
            let owner = context.heap_state.local_idx_for_obj_id(object).unwrap();

            let (_, _, modified, _) = context.encode_block_statements(*target);
            assert!(modified.contains(&alias), "encode the actual compiler-produced copy");
            assert_eq!(context.sound_fallback_count(), before);
            assert_eq!(
                context.heap_state.local_addresses, allocations,
                "a copy creates no allocation"
            );
            assert_eq!(
                context.ref_resolution.subslice_len.get(&alias),
                Some(&Expr::bitvec_const(1u64, 64))
            );
            assert_eq!(folded(&context.known_stack_addr_expr(alias).unwrap()), pointer);
            assert!(!context.ref_resolution.const_ref_values.contains_key(&alias));
            assert!(!context.ref_resolution.ref_targets.contains_key(&alias));
            assert!(
                !context.heap_state.is_array_modified(&scalar_key),
                "the encoded copy keeps the source scalar memory unchanged"
            );
            assert_eq!(scalar_at(&image, &pointer), Some(Expr::bitvec_const(7u64, 64)));
            assert_eq!(context.stack_local_is_live(owner), Some(true));
        },
    );
}

#[test]
fn native_shared_one_slice_refuses_escapes_retargeted_slots_effects_and_foreign_helpers() {
    with_context(|ctx| {
        for (host, method, expected) in [
            ("retargeted", "second_view", 2),
            ("exposed", "second_view", 1),
            ("effectful", "effectful_view", 1),
            ("shadowed", "shadow_view", 1),
            ("escaped", "second_view", 1),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, host).callee_body().unwrap();
            let mut context = ChcCtx::new(ctx.tcx, &body, host, mem_config());
            context.declare_block_relations();
            let mut calls = 0;
            for bb in 0..body.blocks.len() {
                let Some((instance, _)) = resolve_call(&body, bb) else { continue };
                if !instance.def.name().ends_with(method) {
                    continue;
                }
                install_call_liveness(&mut context, bb);
                let from = from(&context, bb);
                let constraints = [];
                let modified = HashSet::new();
                let call = dispatch(&body, bb, &constraints, &modified, &from);
                let callee =
                    crate::kani_middle::transform::walker_transformed_body(ctx.tcx, instance)
                        .unwrap();
                let before = context.sound_fallback_count();
                assert!(
                    !context.try_inline_storage_address(&call, &callee, instance),
                    "unsupported shared view must not gain storage authority: {host}"
                );
                if host != "shadowed" {
                    assert!(
                        context.sound_fallback_count() > before,
                        "qualified native view attempt retains explicit refusal: {host}"
                    );
                }
                assert!(
                    !context.ref_resolution.const_ref_values.contains_key(&call.destination.local)
                );
                calls += 1;
            }
            assert_eq!(calls, expected, "actual negative call sites required: {host}");
        }
    });
}
