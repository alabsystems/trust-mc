// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::{BinOp, FlowRules, StaticView, Tracked, memory_of_constant};
use super::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::rules::codegen_rules_entry::CodegenRulesEntry;
use crate::codegen_ay::chc::{ChcConfig, ChcCtx};
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use rustc_public::mir::{Body, Operand, Rvalue, StatementKind};

const SOURCE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    pub fn compound() -> &'static (u8, Option<bool>) { &(9, None) }
    pub fn other() -> &'static (u8, Option<bool>) { &(7, None) }
    pub fn padded() -> &'static (u64, u8) { &(123, 5) }
    pub fn relocation() -> &'static (&'static u8,) { &(&7,) }
    const UNINIT: core::mem::MaybeUninit<u8> = core::mem::MaybeUninit::uninit();
    pub fn uninit() -> &'static core::mem::MaybeUninit<u8> { &UNINIT }
    pub fn raw() -> u8 {
        let value = &(9u8, None::<bool>);
        assert!(value.1.is_none());
        unsafe { *core::ptr::addr_of!(value.1).cast::<u8>() }
    }
    pub fn nested_raw() -> u8 {
        let value = &(123u64, (9u8, None::<bool>));
        assert!(value.1.1.is_none());
        unsafe { *core::ptr::addr_of!(value.1.1).cast::<u8>() }
    }
    pub fn raw_read_method() -> u8 {
        let value = &(9u8, None::<bool>);
        unsafe { core::ptr::addr_of!(value.1).cast::<u8>().read() }
    }
    fn cast(_: *const Option<bool>, other: *const u8) -> *const u8 { other }
    fn unknown(_: *const u8, other: *const u8) -> *const u8 { other }
    fn unknown_mixed(_: *const u8, other: *const Option<bool>) -> *const u8 { other as *const u8 }
    pub fn custom_cast() -> u8 {
        let value = &(9u8, None::<bool>);
        unsafe { *cast(core::ptr::addr_of!(value.1), &7u8) }
    }
    pub fn opaque_byte() -> u8 {
        let value = &(9u8, None::<bool>);
        let p = core::ptr::addr_of!(value.1).cast::<u8>();
        unsafe { *unknown(p, &7u8) }
    }
    pub fn opaque_mixed() -> u8 {
        let value = &(9u8, None::<bool>);
        let p = core::ptr::addr_of!(value.1).cast::<u8>();
        unsafe { *unknown_mixed(p, core::ptr::addr_of!(value.1)) }
    }
    pub fn aggregate_byte(other: *const u8) -> u8 {
        let value = &(9u8, None::<bool>);
        let p = core::ptr::addr_of!(value.1).cast::<u8>();
        let pair = (p, other);
        unsafe { *pair.1 }
    }
    pub fn borrowed_byte() -> u8 {
        let value = &(9u8, None::<bool>);
        let p = core::ptr::addr_of!(value.1).cast::<u8>();
        let borrowed = &p;
        unsafe { (borrowed as *const *const u8 as *const u8).read() }
    }
    pub fn rewritten_byte(choose: bool, other: *const u8) -> u8 {
        let value = &(9u8, None::<bool>);
        let mut p = core::ptr::addr_of!(value.1).cast::<u8>();
        if choose { p = other; }
        unsafe { *p }
    }
    pub fn indirect_cast(f: fn(*const Option<bool>) -> *const u8) -> u8 {
        let value = &(9u8, None::<bool>);
        unsafe { *f(core::ptr::addr_of!(value.1)) }
    }
    static mut LIVE: (u8, Option<bool>) = (9, None);
    pub fn live_raw() -> u8 {
        unsafe { *core::ptr::addr_of!(LIVE.1).cast::<u8>() }
    }
"#;

fn constant(body: &Body) -> (Origin, Ty) {
    body.blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(_, Rvalue::Use(op @ Operand::Constant(c), ..)) =
                &statement.kind
            else {
                return None;
            };
            let (id, true) = memory_of_constant(op)? else { return None };
            let TyKind::RigidTy(RigidTy::Ref(_, ty, _)) = c.const_.ty().kind() else {
                return None;
            };
            Some((Origin::Memory { id, static_image: false }, ty))
        })
        .expect("one promoted constant reference")
}

fn byte_ty() -> Ty {
    Ty::unsigned_ty(UintTy::U8)
}

fn view(origin: Origin, whole: Ty, offset: u64) -> StaticView {
    StaticView::Seeded {
        whole,
        view: whole,
        sort: None,
        at_base: offset == 0,
        holds_static_pointers: false,
        origin: Some(origin),
        direct: true,
        const_offset: Some(offset),
        byte_view: false,
    }
}

#[test]
fn exact_native_byte_requires_the_registered_entry_seed() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "compound").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "compound", ChcConfig::default());
        chc.note_extra_read_type(byte_ty());
        chc.declare_block_relations();
        let offset = LayoutOf::new(whole).field_offset(1).unwrap() as u64;
        assert!(StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
        let saved = chc.ref_resolution.const_ref_memory_inits.clone();
        chc.ref_resolution.object_seeding_closed = false;
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
        chc.ref_resolution.object_seeding_closed = true;
        chc.ref_resolution
            .const_ref_memory_inits
            .retain(|(key, _, _, _, at)| &**key != "u8" || *at != offset);
        chc.ref_resolution.object_seeding_closed = false;
        chc.close_object_seeding();
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
        chc.ref_resolution.const_ref_memory_inits = saved;
        chc.ref_resolution.object_seeding_closed = false;
        chc.close_object_seeding();
        let array = chc.heap_state.type_arrays.remove("u8").unwrap();
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
        chc.heap_state.type_arrays.insert("u8".into(), array);
        for (key, _, value, _, at) in &mut chc.ref_resolution.const_ref_memory_inits {
            if &**key == "u8" && *at == offset {
                *value = Expr::bitvec_const(0u8, 8);
            }
        }
        chc.ref_resolution.object_seeding_closed = false;
        chc.close_object_seeding();
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
    });
}

#[test]
fn a_matching_byte_appended_after_closure_is_not_entry_evidence() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "compound").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "compound", ChcConfig::default());
        chc.note_extra_read_type(byte_ty());
        chc.declare_block_relations();
        let offset = LayoutOf::new(whole).field_offset(1).unwrap() as u64;
        let index = chc
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .position(|(key, _, _, _, at)| &**key == "u8" && *at == offset)
            .unwrap();
        let seed = chc.ref_resolution.const_ref_memory_inits.remove(index);
        chc.ref_resolution.object_seeding_closed = false;
        chc.close_object_seeding();
        let frozen = chc.ref_resolution.const_ref_entry_byte_seeds.clone();
        chc.ref_resolution.const_ref_memory_inits.push(seed);
        // Re-closing cannot promote a late seed into entry evidence.
        chc.close_object_seeding();
        assert_eq!(chc.ref_resolution.const_ref_entry_byte_seeds, frozen);
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
    });
}

#[test]
fn a_byte_array_registered_after_closure_is_not_entry_evidence() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "compound").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "compound", ChcConfig::default());
        chc.note_extra_read_type(byte_ty());
        chc.declare_block_relations();
        let offset = LayoutOf::new(whole).field_offset(1).unwrap() as u64;
        let array = chc.heap_state.type_arrays.remove("u8").unwrap();
        chc.ref_resolution.object_seeding_closed = false;
        chc.close_object_seeding();
        assert!(chc.ref_resolution.const_ref_entry_byte_seeds.is_empty());
        chc.heap_state.type_arrays.insert("u8".into(), array);
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
    });
}

#[test]
fn offset_authority_survives_only_identical_locations() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "compound").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let chc = ChcCtx::new(ctx.tcx, &body, "compound", ChcConfig::default());
        let rules = StaticRules { ctx: &chc, track_consts: true };
        let offset = rules
            .const_tuple_field_offset(
                whole,
                1,
                match whole.kind() {
                    TyKind::RigidTy(RigidTy::Tuple(fields)) => fields[1],
                    _ => unreachable!(),
                },
                Some(0),
            )
            .unwrap();
        assert_eq!(offset as usize, LayoutOf::new(whole).field_offset(1).unwrap());
        let value = view(origin, whole, 0);
        assert_eq!(value.join(&value), value);
        assert!(matches!(
            value.join(&view(origin, whole, offset)),
            StaticView::Seeded { const_offset: None, .. }
        ));
        let other = find_instance_by_suffix(ctx.tcx, "other").callee_body().unwrap();
        assert!(matches!(
            value.join(&view(constant(&other).0, whole, 0)),
            StaticView::Seeded { const_offset: None, .. }
        ));
        assert!(matches!(
            rules.arith(Some(&BinOp::Offset), value, None),
            Some(StaticView::Seeded { const_offset: None, .. })
        ));
        assert_eq!(rules.const_tuple_field_offset(whole, 1, byte_ty(), Some(0)), None);
        let TyKind::RigidTy(RigidTy::Tuple(fields)) = whole.kind() else { unreachable!() };
        assert_eq!(rules.const_tuple_field_offset(whole, 1, fields[1], Some(u64::MAX)), None);
        assert!(!rules.seeded_const_byte(Some(Origin::Consts), Some(0), byte_ty()));
        assert!(!rules.seeded_const_byte(Some(origin), None, byte_ty()));
        assert!(!rules.seeded_const_byte(Some(origin), Some(u64::MAX), byte_ty()));
        assert!(matches!(
            rules.view_change(view(origin, whole, 0), Ty::new_tuple(&[])),
            StaticView::Seeded { const_offset: None, .. }
        ));
        // The existing equal-sort value route cannot confer native-byte
        // authority on a later cast: the new fact is independent of sorts.
        assert!(matches!(
            rules.view_change(
                view(origin, Ty::unsigned_ty(UintTy::U32), 0),
                Ty::from_rigid_kind(RigidTy::Char)
            ),
            StaticView::Seeded { const_offset: None, .. }
        ));
    });
}

#[test]
fn initialized_data_not_padding_or_relocations_establishes_byte_views() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["padded", "relocation", "uninit"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (origin, _) = constant(&body);
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.note_extra_read_type(byte_ty());
            chc.declare_block_relations();
            let Origin::Memory { id, .. } = origin else { unreachable!() };
            let (bytes, _) = target_bytes(ctx.tcx, &TargetKey::Memory(id)).unwrap();
            let uninitialized = (0..bytes.len())
                .find(|at| bytes.read_uint_at(*at, 1).is_none())
                .expect("fixture has native padding, relocation or uninitialized bytes");
            assert!(
                !StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
                    Some(origin),
                    Some(uninitialized as u64),
                    byte_ty()
                ),
                "{name}"
            );
        }
    });
}

#[test]
fn compound_native_byte_scan_is_precise_and_mutable_static_scan_stays_refused() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, unseeded) in [
            ("raw", false),
            ("nested_raw", false),
            ("raw_read_method", false),
            ("live_raw", true),
            ("custom_cast", true),
            ("opaque_byte", true),
            ("opaque_mixed", true),
            ("aggregate_byte", true),
            ("borrowed_byte", true),
            ("rewritten_byte", true),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            assert_eq!(
                !chc.static_unseeded_view_read_blocks(&body, false).is_empty(),
                unseeded,
                "{name}"
            );
        }
    });
}

#[test]
fn a_native_read_method_with_a_byte_entry_seed_is_precise() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "raw_read_method").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "raw_read_method", ChcConfig::default());
        chc.declare_block_relations();
        let Origin::Memory { id, .. } = origin else { unreachable!() };
        let obj = chc.global_object(&TargetKey::Memory(id)).unwrap().obj_id;
        let offset = LayoutOf::new(whole).field_offset(1).unwrap() as u64;
        assert_eq!(
            chc.ref_resolution.const_ref_entry_byte_seeds.get(&(obj, offset)),
            Some(&Some(Expr::bitvec_const(2u8, 8)))
        );
        assert!(StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
        assert!(chc.static_unseeded_view_read_blocks(&body, false).is_empty());
    });
}

#[test]
fn entry_byte_evidence_survives_actual_bb0_replay() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "raw_read_method").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let mut chc = ChcCtx::new(
            ctx.tcx,
            &body,
            "raw_read_method",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc.declare_block_relations();
        let offset = LayoutOf::new(whole).field_offset(1).unwrap() as u64;
        assert!(StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
        chc.declare_error_relation();
        chc.emit_entry_rule();
        chc.seed_promoted_const_store_chains_for_bb0(0);
        assert!(chc.ref_resolution.const_ref_memory_inits.is_empty());
        assert!(StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
        assert!(chc.static_unseeded_view_read_blocks(&body, false).is_empty());
    });
}

#[test]
fn conflicting_byte_entry_seeds_never_establish_authority() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "compound").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "compound", ChcConfig::default());
        chc.note_extra_read_type(byte_ty());
        chc.declare_block_relations();
        let offset = LayoutOf::new(whole).field_offset(1).unwrap() as u64;
        let mut conflicting = chc
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .find(|(key, _, _, _, at)| &**key == "u8" && *at == offset)
            .unwrap()
            .clone();
        conflicting.2 = Expr::bitvec_const(0u8, 8);
        chc.ref_resolution.const_ref_memory_inits.push(conflicting);
        chc.ref_resolution.object_seeding_closed = false;
        chc.close_object_seeding();
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
    });
}

#[test]
fn a_new_byte_cell_cannot_be_pushed_after_entry_closes() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "compound").callee_body().unwrap();
        let (origin, whole) = constant(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "compound", ChcConfig::default());
        chc.declare_block_relations();
        let Origin::Memory { id, .. } = origin else { unreachable!() };
        let obj = chc.global_object(&TargetKey::Memory(id)).unwrap().obj_id;
        let offset = LayoutOf::new(whole).field_offset(1).unwrap() as u64;
        assert!(!chc.ref_resolution.const_ref_entry_byte_seeds.contains_key(&(obj, offset)));
        let (bytes, _) = target_bytes(ctx.tcx, &TargetKey::Memory(id)).unwrap();
        let byte = bytes.read_uint_at(offset as usize, 1).unwrap();
        let before = chc.ref_resolution.const_ref_memory_inits.clone();
        let debt = chc.diagnostics.sound_havoc_drop.get();
        chc.push_const_memory_inits(vec![(
            "u8".into(),
            Sort::bitvec(8),
            Expr::bitvec_const(byte, 8),
            obj,
            offset,
        )]);
        assert_eq!(chc.ref_resolution.const_ref_memory_inits, before);
        assert!(chc.diagnostics.sound_havoc_drop.get() > debt);
        assert!(!StaticRules { ctx: &chc, track_consts: true }.seeded_const_byte(
            Some(origin),
            Some(offset),
            byte_ty()
        ));
    });
}

#[test]
fn native_cast_identity_refuses_user_targets_indirection_and_unit_stubs() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "raw_read_method").callee_body().unwrap();
        let chc = ChcCtx::new(ctx.tcx, &body, "native_cast_identity", ChcConfig::default());
        let rules = StaticRules { ctx: &chc, track_consts: true };
        let callee_type = |body: &Body| {
            body.blocks
                .iter()
                .find_map(|block| {
                    let rustc_public::mir::TerminatorKind::Call { func, .. } =
                        &block.terminator.kind
                    else {
                        return None;
                    };
                    func.ty(body.locals()).ok()
                })
                .unwrap()
        };
        let native = callee_type(&body);
        assert!(rules.native_pointer_cast(Some(native), "cast"));
        for name in ["custom_cast", "indirect_cast"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            assert!(!rules.native_pointer_cast(Some(callee_type(&body)), "cast"), "{name}");
        }
        let TyKind::RigidTy(RigidTy::FnDef(def, _)) = native.kind() else { unreachable!() };
        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            std::collections::HashMap::from([(def, def)]),
        );
        assert!(!rules.native_pointer_cast(Some(native), "cast"));
    });
}
