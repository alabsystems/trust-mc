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
const PROJECTED_STATIC_WINDOW_SOURCE: &str = r#"
    #![allow(dead_code, unused_assignments)]
    static WORDS: [&str; 2] = ["DECOY", "FOO"];
    static OTHER: [&str; 2] = ["OTHER", "BAR"];
    static BYTES: [u8; 5] = *b"xBARy";
    static WINDOWS: [&str; 1] = [unsafe {
        core::str::from_utf8_unchecked(core::slice::from_raw_parts(BYTES.as_ptr().add(1), 3))
    }];
    static mut LIVE_BYTES: [u8; 3] = *b"LIV";
    static LIVE_WINDOWS: [&str; 1] = [unsafe {
        core::str::from_utf8_unchecked(core::slice::from_raw_parts(
            core::ptr::addr_of!(LIVE_BYTES).cast::<u8>(), 3,
        ))
    }];
    pub fn second_element() -> u8 { WORDS[1].as_bytes()[0] }
    pub fn interior_window() -> u8 { WINDOWS[0].as_bytes()[0] }
    pub fn selected_pointer_identity() {
        let selected = WORDS[1];
        assert!(selected.as_ptr() == WORDS[1].as_ptr());
    }
    pub fn selected_pointer_distinct_bug() {
        let selected = WORDS[1];
        assert!(selected.as_ptr() == WORDS[0].as_ptr());
    }
    pub fn live_window() -> u8 { LIVE_WINDOWS[0].as_bytes()[0] }
    pub fn merged_static_source(condition: bool) -> u8 {
        let source = if condition { &WORDS } else { &OTHER };
        let copied = source;
        copied[1].as_bytes()[0]
    }
    pub fn copied_entry_source_then_reassign(mut source: &'static [&'static str; 2]) -> u8 {
        let copied = source;
        let result = copied[1].as_bytes()[0];
        source = &WORDS;
        core::hint::black_box(source);
        result
    }
    pub fn dynamic_index(index: usize) -> u8 { WORDS[index].as_bytes()[0] }
    pub fn entry_index_then_reassign(mut index: usize) -> u8 {
        let value = WORDS[index].as_bytes()[0];
        index = 0;
        core::hint::black_box(index);
        value
    }
    pub fn replaced_pointer_slot() -> u8 {
        let mut text = WORDS[1];
        { let slot = &mut text; *slot = "ZZZ"; }
        text.as_bytes()[0]
    }
"#;

// The decoded bytes are stores over an unconstrained tail. Declare that
// tail without constraining it: the selected bytes must hold for every tail.
fn projected_window_query_declarations(expr: &Expr) -> String {
    let mut variables = std::collections::BTreeMap::new();
    let mut stack = vec![expr];
    while let Some(value) = stack.pop() {
        if let ay_bindings::ExprValue::Var { name } = value.value() {
            variables.insert(name.clone(), value.sort().clone());
        }
        stack.extend(value.value().children());
    }
    variables.into_iter().map(|(name, sort)| format!("(declare-const {name} {sort})\n")).collect()
}

#[test]
fn test_projected_static_string_windows_precollect_exact_bytes() {
    with_test_ay_ctx_for_source(PROJECTED_STATIC_WINDOW_SOURCE, |ctx| {
        for (name, expected) in [("second_element", b"FOO"), ("interior_window", b"BAR")] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            let dest = body
                .blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind
                    else {
                        return None;
                    };
                    chc.resolve_callee_path(func)?
                        .ends_with("as_bytes")
                        .then_some(destination.local)
                })
                .expect("one str::as_bytes call");
            let bytes = chc.ref_resolution.const_ref_values.get(&dest).expect(name);
            let len = chc.ref_resolution.subslice_len.get(&dest).expect(name);
            assert_eq!(len, &Expr::bitvec_const(expected.len() as u128, 64), "{name}");
            let index_width = bytes.sort().array_sort().unwrap().index_sort.bitvec_width().unwrap();
            let same =
                expected.iter().enumerate().fold(Expr::bool_const(true), |same, (i, byte)| {
                    same.and(
                        bytes
                            .clone()
                            .select(Expr::bitvec_const(i as u128, index_width))
                            .eq(Expr::bitvec_const(*byte as u128, 8)),
                    )
                });
            let declarations = projected_window_query_declarations(&same);
            let query =
                format!("(set-logic QF_ABV)\n{declarations}(assert (not {same}))\n(check-sat)\n");
            assert_eq!(
                run_z3_on_smt2_with_timeout(&query, z3_test_timeout_secs_or(30)).unwrap(),
                "unsat",
                "{name}"
            );
        }
    });
}

#[test]
fn test_projected_static_string_windows_refuse_unstable_inputs() {
    with_test_ay_ctx_for_source(PROJECTED_STATIC_WINDOW_SOURCE, |ctx| {
        for name in [
            "live_window",
            "dynamic_index",
            "entry_index_then_reassign",
            "replaced_pointer_slot",
            "merged_static_source",
            "copied_entry_source_then_reassign",
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, ChcConfig::default());
            chc.declare_block_relations();
            let dest = body
                .blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind
                    else {
                        return None;
                    };
                    chc.resolve_callee_path(func)?
                        .ends_with("as_bytes")
                        .then_some(destination.local)
                })
                .expect("one str::as_bytes call");
            assert!(
                !chc.ref_resolution.const_ref_values.contains_key(&dest),
                "{name}: no fixed byte fact"
            );
            assert!(
                !chc.ref_resolution.subslice_len.contains_key(&dest),
                "{name}: no fixed length fact"
            );
        }
    });
}

#[test]
fn test_projected_static_pointer_slot_checks_actual_constant_index_bounds() {
    use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
    use rustc_public::ty::{RigidTy, TyKind};
    with_test_ay_ctx_for_source(PROJECTED_STATIC_WINDOW_SOURCE, |ctx| {
        for (offset, min_length, from_end, expected) in [
            (1, 1, true, true),
            (0, 3, false, false),
            (2, 1, false, false),
            (3, 1, true, false),
            (0, 1, true, false),
        ] {
            let mut body = find_instance_by_suffix(ctx.tcx, "second_element").body().unwrap();
            let local_tys: Vec<_> = body.locals().iter().map(|local| local.ty).collect();
            let mut changed = 0;
            for block in &mut body.blocks {
                for statement in &mut block.statements {
                    let StatementKind::Assign(
                        _,
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..),
                    ) = &mut statement.kind
                    else {
                        continue;
                    };
                    let pointee = match local_tys[place.local].kind() {
                        TyKind::RigidTy(
                            RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _),
                        ) => pointee,
                        _ => continue,
                    };
                    if !matches!(pointee.kind(), TyKind::RigidTy(RigidTy::Array(..)))
                        || place.projection.len() != 2
                        || !matches!(place.projection[0], ProjectionElem::Deref)
                        || !matches!(
                            place.projection[1],
                            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                        )
                    {
                        continue;
                    }
                    place.projection[1] =
                        ProjectionElem::ConstantIndex { offset, min_length, from_end };
                    changed += 1;
                }
            }
            assert_eq!(changed, 1, "the static array's single pointer load");
            let mut chc = ChcCtx::new(ctx.tcx, &body, "second_element", ChcConfig::default());
            chc.declare_block_relations();
            let dest = body
                .blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind
                    else {
                        return None;
                    };
                    chc.resolve_callee_path(func)?
                        .ends_with("as_bytes")
                        .then_some(destination.local)
                })
                .expect("one str::as_bytes call");
            assert_eq!(
                chc.ref_resolution.const_ref_values.contains_key(&dest),
                expected,
                "offset={offset} min_length={min_length} from_end={from_end}"
            );
            if expected {
                assert_eq!(
                    chc.ref_resolution.subslice_len.get(&dest),
                    Some(&Expr::bitvec_const(3u128, 64))
                );
                let value = chc.ref_resolution.const_ref_values.get(&dest).unwrap();
                let first = value.clone().select(Expr::bitvec_const(0u128, 64));
                let declarations = projected_window_query_declarations(&first);
                let query = format!(
                    "(set-logic QF_ABV)\n{declarations}(assert (not (= {first} {})))\n(check-sat)\n",
                    Expr::bitvec_const(b'F' as u128, 8)
                );
                assert_eq!(
                    run_z3_on_smt2_with_timeout(&query, z3_test_timeout_secs_or(30)).unwrap(),
                    "unsat"
                );
            }
        }
    });
}

#[test]
fn test_projected_static_string_pointer_identity_is_preserved() {
    with_test_ay_ctx_for_source(PROJECTED_STATIC_WINDOW_SOURCE, |ctx| {
        for (name, expected) in
            [("selected_pointer_identity", "unsat"), ("selected_pointer_distinct_bug", "sat")]
        {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            let vc = mir_to_chc(
                ctx.tcx,
                &body,
                name,
                ChcConfig { track_level: ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let query = emit_chc(&vc).to_string();
            assert_eq!(
                run_z3_on_smt2_with_timeout(&query, z3_test_timeout_secs_or(30)).unwrap(),
                expected,
                "{name}"
            );
        }
    });
}
