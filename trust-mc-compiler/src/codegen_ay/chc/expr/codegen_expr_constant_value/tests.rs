// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::callee_body::CalleeBody;
use crate::codegen_ay::chc::ChcConfig;
use crate::codegen_ay::chc::rules::codegen_rules_entry::CodegenRulesEntry;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::shared::const_pointer::ConstWindow;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::{Body, Operand, Rvalue, StatementKind};

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn some() -> &'static (usize, Option<usize>) { &(1, Some(3)) }
    pub fn none() -> &'static (usize, Option<usize>) { &(7, None) }
    pub fn nested() -> &'static (bool, (u8, Option<(u16, bool)>)) {
        &(true, (5, Some((257, false))))
    }
    pub fn niche_some() -> &'static (u8, Option<bool>) { &(9, Some(true)) }
    pub fn niche_none() -> &'static (u8, Option<bool>) { &(9, None) }
    pub fn compound_none_raw() -> u8 {
        let value = &(9u8, None::<bool>);
        unsafe { *core::ptr::addr_of!(value.1).cast::<u8>() }
    }
    pub fn direct_none_raw() -> u8 {
        const RAW: *const u8 = &None::<bool> as *const Option<bool> as *const u8;
        unsafe { *RAW }
    }
    pub fn character() -> &'static (u8, Option<char>) { &(9, Some('é')) }
    pub fn option_tuple() -> &'static Option<(u16, bool)> { &Some((257, false)) }
    pub fn option_tuple_none() -> &'static Option<(u16, bool)> { &None }
    pub fn option_singleton() -> &'static Option<(u16,)> { &Some((257,)) }
    pub fn option_nested() -> &'static Option<Option<u16>> { &Some(Some(257)) }
    pub fn reordered() -> &'static (u8, u64) { &(5, 0x123456789abcdef0) }
    pub fn padded() -> &'static (i128, u8) { &(-123, 5) }
    pub fn scalar() -> &'static u64 { &0x123456789abcdef0 }
    pub fn bad_bool() -> &'static u8 { &2 }
    pub fn bad_char() -> &'static u32 { &0xd800 }
    pub fn pointer_slot() -> &'static (&'static u8,) { &(&7,) }
    const UNINIT: core::mem::MaybeUninit<u64> = core::mem::MaybeUninit::uninit();
    pub fn uninit() -> &'static core::mem::MaybeUninit<u64> { &UNINIT }
    pub mod lookalike {
        pub enum Option<T> { None, Some(T) }
    }
    pub fn unsupported() -> &'static (u8, lookalike::Option<u64>) {
        &(1, lookalike::Option::Some(3))
    }
"#;

fn fixture_window(tcx: TyCtxt<'_>, name: &str) -> (Body, Ty, ConstWindow) {
    let body = find_instance_by_suffix(tcx, name).callee_body().unwrap();
    let (ty, window) = body
        .blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(_, Rvalue::Use(Operand::Constant(c), ..)) = &statement.kind
            else {
                return None;
            };
            let ty = match c.const_.ty().kind() {
                TyKind::RigidTy(RigidTy::Ref(_, ty, _) | RigidTy::RawPtr(ty, _)) => ty,
                _ => return None,
            };
            let bytes = const_pointer::const_bytes(&c.const_)?;
            let (_, window) = const_pointer::fixed_pointee(tcx, &bytes, 0, ty)?;
            Some((ty, window))
        })
        .unwrap_or_else(|| panic!("promoted constant reference fixture {name}"));
    (body, ty, window)
}

fn fields(value: &Expr) -> &[Expr] {
    let ay_bindings::ExprValue::DatatypeConstructor { args, .. } = value.value() else {
        panic!("expected datatype constructor: {value}");
    };
    args
}

fn scalar(value: &Expr, expected: u128) {
    let ay_bindings::ExprValue::BitVecConst { value, .. } = value.value() else {
        panic!("expected scalar: {value}");
    };
    assert_eq!(value.to_string(), expected.to_string());
}

fn is_some(value: &Expr, expected: bool) {
    let ay_bindings::ExprValue::DatatypeConstructor { constructor_name, args, .. } = value.value()
    else {
        panic!("expected Option constructor: {value}");
    };
    assert_eq!(constructor_name.starts_with("Some_"), expected);
    assert_eq!(args.len(), usize::from(expected));
}

#[test]
fn promoted_tuple_options_decode_real_tag_payload_offsets_and_nested_values() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["some", "none", "nested", "niche_some", "niche_none", "character"] {
            let (body, ty, window) = fixture_window(ctx.tcx, name);
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let sort = ChcCtx::translate_ty(ty).unwrap();
            let value = chc.read_const_safe_value(&window, 0, ty, &sort, 0).unwrap();
            let values = fields(&value);
            match name {
                "some" => {
                    scalar(&values[0], 1);
                    is_some(&values[1], true);
                    scalar(&fields(&values[1])[0], 3);
                }
                "none" => {
                    scalar(&values[0], 7);
                    is_some(&values[1], false);
                }
                "nested" => {
                    assert_eq!(values[0], Expr::bool_const(true));
                    let nested = fields(&values[1]);
                    scalar(&nested[0], 5);
                    is_some(&nested[1], true);
                    let payload = fields(&fields(&nested[1])[0]);
                    scalar(&payload[0], 257);
                    assert_eq!(payload[1], Expr::bool_const(false));
                }
                "niche_some" => {
                    is_some(&values[1], true);
                    assert_eq!(fields(&values[1])[0], Expr::bool_const(true));
                }
                "niche_none" => is_some(&values[1], false),
                "character" => {
                    is_some(&values[1], true);
                    scalar(&fields(&values[1])[0], 'é' as u128);
                }
                _ => unreachable!(),
            }
        }
    });
}

#[test]
fn tuple_layout_order_and_padding_do_not_change_initialized_field_values() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["reordered", "padded"] {
            let (body, ty, window) = fixture_window(ctx.tcx, name);
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let sort = ChcCtx::translate_ty(ty).unwrap();
            let value = chc.read_const_safe_value(&window, 0, ty, &sort, 0).unwrap();
            let values = fields(&value);
            if name == "reordered" {
                scalar(&values[0], 5);
                scalar(&values[1], 0x123456789abcdef0);
            } else {
                scalar(&values[0], (-123i128) as u128);
                scalar(&values[1], 5);
            }
        }
    });
}

#[test]
fn malformed_or_unsupported_safe_value_windows_refuse_without_inventing_bytes() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let (body, ty, window) = fixture_window(ctx.tcx, "scalar");
        let chc = ChcCtx::new(ctx.tcx, &body, "scalar", ChcConfig::default());
        let sort = ChcCtx::translate_ty(ty).unwrap();
        assert!(chc.read_const_safe_value(&window, 0, ty, &Sort::bitvec(32), 0).is_none());
        let truncated = window.sub_window(0, window.len() - 1).unwrap();
        assert!(chc.read_const_safe_value(&truncated, 0, ty, &sort, 0).is_none());
        let (_, _, uninit) = fixture_window(ctx.tcx, "uninit");
        assert!(chc.read_const_safe_value(&uninit, 0, ty, &sort, 0).is_none());
        assert!(chc.read_const_safe_value(&window, 0, ty, &sort, MAX_VALUE_DEPTH + 1).is_none());
        let (_, _, pointer) = fixture_window(ctx.tcx, "pointer_slot");
        assert!(chc.read_const_safe_value(&pointer, 0, ty, &sort, 0).is_none());
        let (_, _, invalid_bool) = fixture_window(ctx.tcx, "bad_bool");
        let bool_ty = Ty::from_rigid_kind(RigidTy::Bool);
        assert!(chc.read_const_safe_value(&invalid_bool, 0, bool_ty, &Sort::bool(), 0).is_none());
        let (_, _, invalid_char) = fixture_window(ctx.tcx, "bad_char");
        let char_ty = Ty::from_rigid_kind(RigidTy::Char);
        assert!(
            chc.read_const_safe_value(&invalid_char, 0, char_ty, &Sort::bitvec(32), 0).is_none()
        );
        let (_, unsupported, bytes) = fixture_window(ctx.tcx, "unsupported");
        let unsupported_sort = ChcCtx::translate_ty(unsupported).unwrap();
        assert!(!chc.const_safe_value_supported(unsupported, 0));
        assert!(chc.read_const_safe_value(&bytes, 0, unsupported, &unsupported_sort, 0).is_none());
    });
}

#[test]
fn declaration_and_expression_paths_share_the_typed_tuple_decoder() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in [
            "some",
            "none",
            "nested",
            "niche_some",
            "niche_none",
            "option_tuple",
            "option_tuple_none",
            "option_singleton",
            "option_nested",
        ] {
            let (body, ty, window) = fixture_window(ctx.tcx, name);
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            let sort = ChcCtx::translate_ty(ty).unwrap();
            let expected = chc.read_const_safe_value(&window, 0, ty, &sort, 0).unwrap();
            assert!(chc.ref_resolution.const_ref_values.values().any(|value| value == &expected));
            for statement in body.blocks.iter().flat_map(|block| &block.statements) {
                if let StatementKind::Assign(_, Rvalue::Use(Operand::Constant(c), ..)) =
                    &statement.kind
                    && matches!(c.const_.ty().kind(), TyKind::RigidTy(RigidTy::Ref(..)))
                {
                    assert_eq!(chc.translate_constant_referent(c), Some(expected.clone()));
                }
            }
            assert_eq!(chc.diagnostics.sound_havoc_drop.get(), 0, "{name}");
        }
    });
}

#[test]
fn safe_window_seeds_whole_compounds_and_active_fields_transactionally() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["some", "none"] {
            let (body, ty, window) = fixture_window(ctx.tcx, name);
            let chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            let mut seeds = Vec::new();
            let site = InitSite { obj_id: 99, base: 13 };
            chc.decode_const_safe_window(&window, ty, &mut seeds, site).unwrap();
            let layout = LayoutOf::new(ty);
            let TyKind::RigidTy(RigidTy::Tuple(fields)) = ty.kind() else { panic!("tuple") };
            let root_key = ChcCtx::type_key_for_ty(ty);
            assert!(
                seeds.iter().any(|(key, sort, _, object, at)| {
                    key.as_ref() == root_key.as_ref()
                        && *sort == chc.elem_sort_for_memory_array(ty)
                        && *object == 99
                        && *at == 13
                }),
                "the 24-byte whole tuple must not be omitted"
            );
            let option_ty = fields[1];
            let option_base = 13 + layout.field_offset(1).unwrap() as u64;
            let option_key = ChcCtx::type_key_for_ty(option_ty);
            assert!(seeds.iter().any(|(key, sort, _, object, at)| {
                key.as_ref() == option_key.as_ref()
                    && *sort == chc.elem_sort_for_memory_array(option_ty)
                    && *object == 99
                    && *at == option_base
            }));
            let payload_at =
                option_base + LayoutOf::new(option_ty).variant_field_offset(1, 0).unwrap() as u64;
            assert_eq!(
                seeds.iter().any(|(_, _, _, object, at)| *object == 99 && *at == payload_at),
                name == "some",
                "only an active Some payload has a field cell"
            );
        }
        // The existing memory codec cannot retain a separate Option tag when
        // its entire bit width is already occupied by the payload. Decode the
        // native value, but preserve refusal rather than seed a lossy image.
        let (body, ty, window) = fixture_window(ctx.tcx, "character");
        let chc = ChcCtx::new(ctx.tcx, &body, "character", ChcConfig::default());
        let sort = ChcCtx::translate_ty(ty).unwrap();
        assert!(chc.read_const_safe_value(&window, 0, ty, &sort, 0).is_some());
        let mut seeds = Vec::new();
        assert!(
            chc.decode_const_safe_window(&window, ty, &mut seeds, InitSite { obj_id: 99, base: 0 })
                .is_none()
        );
        assert!(seeds.is_empty(), "a refused nested image must not leave partial seeds");
    });
}

#[test]
fn unsupported_tuple_reference_retains_contents_and_expression_debt() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let (body, _, _) = fixture_window(ctx.tcx, "unsupported");
        let mut chc = ChcCtx::new(ctx.tcx, &body, "unsupported", ChcConfig::default());
        chc.declare_block_relations();
        assert!(chc.diagnostics.sound_havoc_drop.get() > 0);
        assert!(chc.ref_resolution.const_ref_values.is_empty());
        for statement in body.blocks.iter().flat_map(|block| &block.statements) {
            if let StatementKind::Assign(_, Rvalue::Use(Operand::Constant(c), ..)) = &statement.kind
                && matches!(c.const_.ty().kind(), TyKind::RigidTy(RigidTy::Ref(..)))
            {
                assert!(chc.translate_constant_referent(c).is_none());
            }
        }
        assert!(chc.diagnostics.const_translation_drop.get() > 0);
    });
}

fn has_conjunct(expr: &Expr, expected: &Expr) -> bool {
    expr == expected
        || matches!(expr.value(), ay_bindings::ExprValue::And(children)
        if children.iter().any(|child| has_conjunct(child, expected)))
}

#[test]
fn niche_none_entry_keeps_typed_and_native_raw_cells_distinct() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let name = "compound_none_raw";
        let (body, ty, window) = fixture_window(ctx.tcx, name);
        let TyKind::RigidTy(RigidTy::Tuple(field_tys)) = ty.kind() else { panic!("tuple") };
        let option_ty = field_tys[1];
        let option_offset = LayoutOf::new(ty).field_offset(1).unwrap() as u64;
        assert_eq!(LayoutOf::new(option_ty).size_of(), Some(1));
        let native = window.read_uint_at(option_offset as usize, 1).unwrap();
        assert_eq!(native, 2, "native oracle for the admitted seal's Option<bool>::None");
        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let mut chc = ChcCtx::new(ctx.tcx, &body, name, config);
        chc.declare_block_relations();
        let sort = ChcCtx::translate_ty(ty).unwrap();
        let expected = chc.read_const_safe_value(&window, 0, ty, &sort, 0).unwrap();
        let local = *chc
            .ref_resolution
            .const_ref_values
            .iter()
            .find(|(_, value)| **value == expected)
            .unwrap()
            .0;
        let object = chc.ref_resolution.const_ref_objects[&local];
        let at = object.offset + option_offset;
        let option_key = ChcCtx::type_key_for_ty(option_ty);
        assert_ne!(option_key.as_ref(), "u8");
        let seeds = &chc.ref_resolution.const_ref_memory_inits;
        let typed = seeds
            .iter()
            .find(|(key, _, _, obj, offset)| {
                key.as_ref() == option_key.as_ref() && *obj == object.obj_id && *offset == at
            })
            .unwrap()
            .clone();
        let raw = seeds
            .iter()
            .find(|(key, _, _, obj, offset)| {
                key.as_ref() == "u8" && *obj == object.obj_id && *offset == at
            })
            .unwrap()
            .clone();
        assert_eq!(typed.1, Sort::bitvec(8));
        scalar(&raw.2, native);
        // The canonical Option cell selects zero for None. Its tag tester is
        // false on this exact decoded None constructor; it is not raw byte2.
        let ay_bindings::ExprValue::Ite { cond, else_expr, .. } = typed.2.value() else {
            panic!("expected canonical tagged Option memory encoding");
        };
        let ay_bindings::ExprValue::DatatypeTester { constructor_name, expr, .. } = cond.value()
        else {
            panic!("expected the Option payload tag tester")
        };
        let ay_bindings::ExprValue::DatatypeConstructor { constructor_name: actual, args, .. } =
            expr.value()
        else {
            panic!("expected decoded Option None")
        };
        assert!(args.is_empty());
        assert_ne!(constructor_name, actual);
        scalar(else_expr, 0);
        assert_eq!(chc.diagnostics.sound_havoc_drop.get(), 0);
        chc.declare_error_relation();
        chc.emit_entry_rule();
        for (key, element_sort, value, obj, offset) in [typed, raw] {
            assert_eq!(chc.heap_state.type_arrays[key.as_ref()].1, element_sort);
            let array = Expr::var(
                names::mem_array_name(name, &key).as_ref(),
                Sort::array(crate::codegen_ay::types::ptr_sort(), element_sort),
            );
            let base = crate::codegen_ay::chc::decl::global_objects::object_base_for(obj);
            let address = if offset == 0 {
                base
            } else {
                base.bvadd(Expr::bitvec_const(offset, crate::codegen_ay::types::POINTER_WIDTH))
            };
            let expected_constraint = array.select(address).eq(value);
            assert!(
                chc.vc
                    .rules
                    .iter()
                    .filter(|rule| rule.body.relation.is_none())
                    .flat_map(|rule| &rule.body.constraints)
                    .any(|constraint| has_conjunct(constraint, &expected_constraint)),
                "entry must retain the independent {key} cell at the same native address"
            );
        }
        assert_eq!(chc.diagnostics.sound_havoc_drop.get(), 0);
    });
}

#[test]
fn niche_none_raw_view_discovered_after_entry_retains_refusal() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let (body, _, _) = fixture_window(ctx.tcx, "niche_none");
        let mut chc = ChcCtx::new(ctx.tcx, &body, "niche_none", ChcConfig::default());
        chc.declare_block_relations();
        let late_ty = Ty::unsigned_ty(rustc_public::ty::UintTy::U16);
        assert!(!chc.ref_resolution.extra_read_types.contains(&late_ty));
        assert!(!chc.ref_resolution.seeded_object_types.iter().any(|(_, ty)| *ty == late_ty));
        assert!(!chc.ref_resolution.object_read_types.is_empty());
        chc.declare_error_relation();
        chc.emit_entry_rule();
        assert!(chc.ref_resolution.object_seeding_closed);
        let before_seeds = chc.ref_resolution.const_ref_memory_inits.clone();
        let before_debt = chc.diagnostics.sound_havoc_drop.get();
        chc.note_extra_read_type(late_ty);
        assert!(chc.diagnostics.sound_havoc_drop.get() > before_debt);
        assert_eq!(chc.ref_resolution.const_ref_memory_inits, before_seeds);
        assert!(!chc.ref_resolution.seeded_object_types.iter().any(|(_, ty)| *ty == late_ty));
    });
}

#[test]
fn direct_raw_constant_decodes_its_native_scalar_window() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let name = "direct_none_raw";
        let (body, ty, window) = fixture_window(ctx.tcx, name);
        assert_eq!(ty, Ty::unsigned_ty(rustc_public::ty::UintTy::U8));
        assert_eq!(window.read_uint_at(0, 1), Some(2));
        let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
        chc.declare_block_relations();
        let expected = Expr::bitvec_const(2u8, 8);
        assert!(chc.ref_resolution.const_ref_values.values().any(|value| value == &expected));
        for statement in body.blocks.iter().flat_map(|block| &block.statements) {
            if let StatementKind::Assign(_, Rvalue::Use(Operand::Constant(c), ..)) = &statement.kind
                && matches!(c.const_.ty().kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))
            {
                assert_eq!(chc.translate_constant_referent(c), Some(expected.clone()));
            }
        }
        assert!(chc.ref_resolution.const_ref_memory_inits.iter().any(
            |(key, sort, value, _, _)| key.as_ref() == "u8"
                && *sort == Sort::bitvec(8)
                && value == &expected
        ));
        assert_eq!(chc.diagnostics.sound_havoc_drop.get(), 0);
    });
}
