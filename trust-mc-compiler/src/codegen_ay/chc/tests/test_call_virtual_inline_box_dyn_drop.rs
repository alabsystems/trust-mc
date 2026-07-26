// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused Box<dyn> inline drop identity tests.

use super::common::*;
use crate::codegen_ay::chc::call::codegen_call_virtual_inline::translate_virtual_body_inline;
use crate::codegen_ay::chc::call::unprojected_inline_drop_arg_base_local_for_test;
use crate::codegen_ay::chc::rules::codegen_rules_helpers::CodegenRulesHelpers;
use crate::codegen_ay::types::POINTER_WIDTH;
use rustc_public::mir::TerminatorKind;
use std::collections::HashMap;

fn find_drop_in_place_args(
    body: &rustc_public::mir::Body,
    chc_ctx: &mut ChcCtx<'_, '_>,
) -> Vec<rustc_public::mir::Operand> {
    body.blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            TerminatorKind::Call { func, args, .. } => chc_ctx
                .resolve_callee_path(func)
                .filter(|path| path.contains("drop_in_place"))
                .map(|_| args.clone()),
            _ => None,
        })
        .expect("expected explicit drop_in_place call")
}

fn find_box_drop_place(
    body: &rustc_public::mir::Body,
    chc_ctx: &ChcCtx<'_, '_>,
) -> rustc_public::mir::Place {
    body.blocks
        .iter()
        .find_map(|block| match &block.terminator.kind {
            TerminatorKind::Drop { place, .. } => {
                let drop_ty = place.ty(body.locals()).ok().map(|ty| chc_ctx.resolve_body_ty(ty))?;
                <ChcCtx<'_, '_> as CodegenRulesHelpers>::is_box_ty(drop_ty).then(|| place.clone())
            }
            _ => None,
        })
        .expect("expected Box drop terminator")
}

#[test]
fn test_inline_box_dyn_projected_drop_arg_does_not_use_container_local() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]

        pub trait DynDropProbe {
            fn val(&self) -> u32;
        }

        pub struct Impl(u32);
        impl DynDropProbe for Impl {
            fn val(&self) -> u32 { self.0 }
        }

        pub struct Holder {
            pub field: Box<dyn DynDropProbe>,
            pub other: Box<dyn DynDropProbe>,
        }

        pub unsafe fn drop_projected_box_dyn_field(holder: &mut Holder) {
            unsafe { std::ptr::drop_in_place(&mut holder.field); }
        }
        "#,
        |ctx| {
            let fn_name = "drop_projected_box_dyn_field";
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
            let args = find_drop_in_place_args(&body, &mut chc_ctx);
            let first_arg = args.first().expect("drop_in_place self arg");

            match first_arg {
                rustc_public::mir::Operand::Copy(place)
                | rustc_public::mir::Operand::Move(place) => {
                    assert!(
                        place.projection.is_empty(),
                        "probe should exercise an unprojected temporary ref arg, got {place:?}"
                    );
                }
                _ => panic!("drop_in_place arg should be a place operand, got {first_arg:?}"),
            }

            assert_eq!(
                unprojected_inline_drop_arg_base_local_for_test(&body, first_arg),
                None,
                "projected Box<dyn> field drops must not reuse the containing Holder local alloc id"
            );
        },
    );
}

#[test]
fn test_inline_box_dyn_dealloc_ignores_outer_known_alloc_id_collision() {
    with_test_ay_ctx_for_source(
        r#"
        #![allow(dead_code)]

        pub trait DynDropProbe {
            fn val(&self) -> u32;
        }

        pub struct Impl(u32);
        impl DynDropProbe for Impl {
            fn val(&self) -> u32 { self.0 }
        }

        pub fn outer_body_for_collision_seed(x: u32) -> u32 { x }

        pub fn inline_box_dyn_arg_drop(_boxed: Box<dyn DynDropProbe>) {}
        "#,
        |ctx| {
            let outer_instance = find_instance_by_suffix(ctx.tcx, "outer_body_for_collision_seed");
            let outer_body = outer_instance.body().expect("outer function body");
            let inline_instance = find_instance_by_suffix(ctx.tcx, "inline_box_dyn_arg_drop");
            let inline_body = inline_instance.body().expect("inline function body");
            let mut chc_ctx = ChcCtx::new(
                ctx.tcx,
                &outer_body,
                "outer_body_for_collision_seed",
                ChcConfig::default(),
            );

            let drop_place = find_box_drop_place(&inline_body, &chc_ctx);
            let wrong_caller_obj_id = 0xDEAD_u32;
            chc_ctx.known_alloc_ids.insert(drop_place.local, wrong_caller_obj_id);

            let real_inline_obj_id = 0x1234_u32;
            let inline_box_ptr =
                Expr::bitvec_const((real_inline_obj_id as u128) << 32, POINTER_WIDTH);
            let result = translate_virtual_body_inline(
                &mut chc_ctx,
                &inline_body,
                &[inline_box_ptr],
                0,
                &HashMap::new(),
                Some(inline_instance),
                0,
            );

            assert!(result.is_some(), "inline Box<dyn> drop body should translate");
            let dealloc_text = chc_ctx
                .heap_state
                .pending_checks
                .iter()
                .chain(chc_ctx.heap_state.pending_updates.iter())
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
                .to_lowercase();
            assert!(dealloc_text.contains("obj_valid"), "expected inline dealloc effects");
            assert!(
                !dealloc_text.contains("#x0000dead"),
                "inline drop must not read caller known_alloc_ids using callee local numbers: \
                 {dealloc_text}"
            );
        },
    );
}
