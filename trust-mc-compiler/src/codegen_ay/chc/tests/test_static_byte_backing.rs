// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for static byte backing metadata used by CHC slice/string lowering.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::args::{Arguments, ChcTrackLevel};
use crate::codegen_ay::codegen_function::codegen_function_with_body;
use crate::codegen_ay::emit_chc;
use rustc_public::mir::{Operand, TerminatorKind};

const CONST_STATIC_SLICE_AS_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]

    const LUT: &'static [u8] = b"ab";

    pub fn const_static_slice_as_ptr() -> u8 {
        let ptr = LUT.as_ptr();
        unsafe { *ptr }
    }
"#;

const STATIC_STR_AS_BYTES_SOURCE: &str = r#"
    #![allow(dead_code)]

    static STATIC: [&str; 1] = ["FOO"];

    pub fn static_str_as_bytes() -> u8 {
        let x = STATIC[0];
        let bytes = x.as_bytes();
        bytes[0]
    }
"#;

const STATIC_STR_AS_BYTES_ASSERT_SOURCE: &str = r#"
    #![allow(dead_code)]

    static STATIC: [&str; 1] = ["FOO"];

    pub fn static_str_as_bytes_asserts() {
        let x = STATIC[0];
        let bytes = x.as_bytes();
        assert!(bytes.len() == 3);
        assert!(bytes[0] == b'F');
        assert!(bytes[1] == b'O');
        assert!(bytes[2] == b'O');
    }
"#;

/// `slice::as_ptr` over a `const &'static [u8]` must carry the byte-array
/// backing onto the raw-pointer result so `*ptr` does not become select-any.
#[test]
fn test_const_static_slice_as_ptr_propagates_byte_backing() {
    with_test_ay_ctx_for_source(CONST_STATIC_SLICE_AS_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "const_static_slice_as_ptr");
        let body = instance.body().expect("body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "const_static_slice_as_ptr", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (receiver, destination) = body
            .blocks
            .iter()
            .find_map(|bb| {
                let TerminatorKind::Call { func, args, destination, .. } = &bb.terminator.kind
                else {
                    return None;
                };
                let path = chc_ctx.resolve_callee_path(func)?;
                if !path.contains("as_ptr") {
                    return None;
                }
                let receiver = match args.first()? {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        place.clone()
                    }
                    _ => return None,
                };
                Some((Operand::Copy(receiver), destination.local))
            })
            .expect("expected slice::as_ptr call");

        let Operand::Copy(receiver_place) = &receiver else { unreachable!() };
        assert!(
            chc_ctx.ref_resolution.const_ref_values.contains_key(&receiver_place.local),
            "slice::as_ptr receiver _{} should have const byte backing",
            receiver_place.local
        );

        assert!(
            chc_ctx.ref_resolution.const_ref_values.contains_key(&destination),
            "declaration pre-pass should propagate const byte backing to slice::as_ptr destination _{destination}"
        );
        assert!(
            chc_ctx.ref_resolution.subslice_offset.contains_key(&destination),
            "declaration pre-pass should give slice::as_ptr destination _{destination} a zero byte offset"
        );
    });
}

/// Static `&str` values flowing through `str::as_bytes` should pre-seed the
/// returned byte slice with concrete backing bytes before block translation.
#[test]
fn test_static_str_as_bytes_precollects_byte_backing() {
    with_test_ay_ctx_for_source(STATIC_STR_AS_BYTES_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "static_str_as_bytes");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "static_str_as_bytes", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_paths = Vec::new();
        let as_bytes_dest = body.blocks.iter().find_map(|bb| {
            let TerminatorKind::Call { func, destination, .. } = &bb.terminator.kind else {
                return None;
            };
            let path = chc_ctx.resolve_callee_path(func)?;
            call_paths.push(path.to_owned());
            path.contains("as_bytes").then_some(destination.local)
        });

        let dest = as_bytes_dest.unwrap_or_else(|| {
            panic!("expected str::as_bytes call, saw call paths: {call_paths:?}")
        });
        assert!(
            chc_ctx.ref_resolution.const_ref_values.contains_key(&dest),
            "str::as_bytes destination _{dest} should carry static string byte backing; calls: {:?}; const_ref values: {:?}; subslice_len values: {:?}; static inits: {:?}",
            call_paths,
            chc_ctx
                .ref_resolution
                .const_ref_values
                .iter()
                .map(|(local, expr)| (*local, expr.to_string()))
                .collect::<Vec<_>>(),
            chc_ctx
                .ref_resolution
                .subslice_len
                .iter()
                .map(|(local, expr)| (*local, expr.to_string()))
                .collect::<Vec<_>>(),
            chc_ctx
                .ref_resolution
                .static_memory_inits
                .iter()
                .map(|(ty, sort, value, addr)| {
                    (ty.to_string(), sort.to_string(), value.to_string(), addr.to_string())
                })
                .collect::<Vec<_>>()
        );
        assert!(
            chc_ctx.ref_resolution.subslice_len.contains_key(&dest),
            "str::as_bytes destination _{dest} should carry static string length"
        );
    });
}

/// The scalar slice-index call over static `str::as_bytes` should select from
/// the concrete byte backing instead of falling through to typed-memory
/// select-any placeholders.
#[test]
fn test_static_str_as_bytes_index_uses_const_backing() {
    with_test_ay_ctx_for_source(STATIC_STR_AS_BYTES_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "static_str_as_bytes");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "static_str_as_bytes",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let smt = emit_chc(&vc).to_string();

        assert!(
            !smt.lines().any(|line| {
                line.contains("_static_str_as_bytes_0__out") && line.contains("mem_u8_select_any")
            }),
            "static str::as_bytes index result should not fall back to select-any memory reads:\n{smt}"
        );
        assert!(
            smt.contains("#x46"),
            "static str::as_bytes indexing should carry the concrete 'F' byte:\n{smt}"
        );
    });
}

#[test]
fn test_static_str_as_bytes_asserts_use_const_backing() {
    with_test_ay_ctx_for_source(STATIC_STR_AS_BYTES_ASSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "static_str_as_bytes_asserts");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "static_str_as_bytes_asserts",
            ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let smt = emit_chc(&vc).to_string();

        assert!(
            !smt.lines().any(|line| line.contains("error") && line.contains("mem_u8_select_any")),
            "static str::as_bytes assertion failure rules should not depend on select-any memory reads:\n{smt}"
        );
    });
}

#[test]
fn test_static_str_as_bytes_final_pipeline_uses_const_backing() {
    with_test_ay_ctx_for_source(STATIC_STR_AS_BYTES_ASSERT_SOURCE, |ctx| {
        let mut ctx = ctx;
        ctx.config.use_chc = true;
        ctx.config.chc_track_level = ChcTrackLevel::Mem;
        ctx.queries.set_args(Arguments::default());

        let instance = find_instance_by_suffix(ctx.tcx, "static_str_as_bytes_asserts");
        let body = instance.body().expect("body");
        let name = instance.name();
        ctx.set_current_fn(instance);

        codegen_function_with_body(&mut ctx, instance, body, &name);
        let (_minimal, program) = ctx.split_emit_chc();
        let smt = program.to_string();

        assert!(
            !smt.lines().any(|line| line.contains("error") && line.contains("mem_u8_select_any")),
            "final static str::as_bytes assertion rules should not depend on select-any memory reads:\n{smt}"
        );
    });
}
