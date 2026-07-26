// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_dispatch_overapprox.rs` — over-approximation dispatch.
//!
//! Part of #2303 (codegen_call_dispatch_overapprox.rs, 111 LOC, zero dedicated coverage).
//! Covers dispatch paths exercised by `try_dispatch_call_overapprox`:
//! - `detect_kani_mem_stub` -> kani::mem helper stubs (is_aligned, valid_ptr)
//! - `detect_ub_panic_stub` -> UB checks, precondition checks, panic stubs
//! - `detect_fmt_stub` -> formatting stubs (unconstrained)
//!
//! Tests exercise the dispatch path:
//!   mir_to_chc -> generate_transition_rules -> codegen_call_terminator -> try_dispatch_call_overapprox

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::chc_call_context::DispatchCallContext;
use crate::codegen_ay::chc::codegen_call::CallTerminator;
use crate::codegen_ay::chc::take_inferable_summary_names_by_fn;
use crate::codegen_ay::emit_chc;

fn mir_to_chc_default(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    fn_name: &str,
) -> trust_mc_core::chc::ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig::default(),
    )
}

fn mir_to_chc_mem(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    fn_name: &str,
) -> trust_mc_core::chc::ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig {
            track_level: crate::args::ChcTrackLevel::Mem,
            ..crate::codegen_ay::chc::ChcConfig::default()
        },
    )
}

// =============================================================================
// Panic / assert — detect_ub_panic_stub (PanicError path)
// =============================================================================

const PANIC_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_panic_explicit() {
        panic!("test panic");
    }
"#;

/// panic!() should be detected and emit an error-headed rule.
#[test]
fn test_panic_generates_error_rule() {
    with_test_ay_ctx_for_source(PANIC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_panic_explicit");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_panic_explicit");

        assert_vc_structure(&vc, "probe_panic_explicit", body.blocks.len());

        // Panic should produce at least one error-headed rule
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "panic!() should emit error-headed rules for soundness"
        );
    });
}

const ASSERT_FALSE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_assert_false(x: u32) {
        assert!(x > 10);
    }
"#;

/// assert!() with condition should emit error-headed rules for the false branch.
#[test]
fn test_assert_generates_error_rule() {
    with_test_ay_ctx_for_source(ASSERT_FALSE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_assert_false");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_assert_false");

        assert_vc_structure(&vc, "probe_assert_false", body.blocks.len());

        // Assert failure path should produce error-headed rules
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "assert!() should emit error-headed rules for the failure branch"
        );
    });
}

// =============================================================================
// Unreachable — PanicUnreachable path (no successor)
// =============================================================================

const UNREACHABLE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_unreachable(x: u32) -> u32 {
        match x {
            0 => 1,
            1 => 2,
            _ => unreachable!(),
        }
    }
"#;

/// unreachable!() should be detected as PanicUnreachable — no successor emitted.
/// The unreachable path should NOT produce error-headed rules (it's infeasible by design).
#[test]
fn test_unreachable_generates_vc() {
    with_test_ay_ctx_for_source(UNREACHABLE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unreachable");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_unreachable");

        assert_vc_structure(&vc, "probe_unreachable", body.blocks.len());

        // unreachable!() in the default arm uses PanicUnreachable — no error() rule
        // should be emitted for that path (it's treated as dead code).
        // The match arms 0=>1, 1=>2 should produce constrained transition rules.
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(constrained, "match arms should produce constrained transition rules");
    });
}

// =============================================================================
// Overflow check — UB check stub (assume true)
// =============================================================================

const OVERFLOW_CHECK_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_overflow_check(a: u32, b: u32) -> u32 {
        a + b
    }
"#;

/// Arithmetic overflow check should produce valid VC with error-headed rules
/// for the overflow branch.
#[test]
fn test_overflow_check_generates_vc() {
    with_test_ay_ctx_for_source(OVERFLOW_CHECK_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_overflow_check");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_overflow_check");

        assert_vc_structure(&vc, "probe_overflow_check", body.blocks.len());

        // Overflow check should produce constrained transition rules (the add itself)
        let constrained = vc
            .rules
            .iter()
            .filter(|r| r.body.relation.is_some())
            .any(|r| !r.body.constraints.is_empty());
        assert!(
            constrained,
            "u32 addition with overflow check should produce constrained transition rules"
        );

        // bv32 sorts should appear in relations for the u32 operands and result
        let has_bv32 =
            vc.relations.iter().any(|r| r.arg_sorts.iter().any(|s| s.bitvec_width() == Some(32)));
        assert!(has_bv32, "u32 addition should have bv32 state vars");
    });
}

// =============================================================================
// Format stub — formatting calls are unconstrained (Part of #2196)
// =============================================================================

const FORMAT_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_format(x: u32) -> String {
        alloc::format!("{}", x)
    }
"#;

/// format!() should be dispatched as an unconstrained formatting stub.
/// The VC should have transition rules (fmt destination unconstrained).
#[test]
fn test_format_generates_vc() {
    with_test_ay_ctx_for_source(FORMAT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_format");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_format");

        assert_vc_structure(&vc, "probe_format", body.blocks.len());

        // format!() dispatches as a fmt stub with unconstrained destination.
        // The VC should still have transition rules connecting basic blocks.
        let transition_rules = vc.rules.iter().filter(|r| r.body.relation.is_some()).count();
        assert!(
            transition_rules >= 1,
            "format!() pipeline should produce at least 1 transition rule, got {transition_rules}"
        );
    });
}

// =============================================================================
// Combined: assert + panic path with multiple dispatch types
// =============================================================================

const COMBINED_ASSERT_RETURN_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_combined_assert_return(x: u32) -> u32 {
        assert!(x != 0, "x must not be zero");
        x + 1
    }
"#;

/// Combined assert + arithmetic exercises both panic stub and overflow check paths.
#[test]
fn test_combined_assert_return_generates_vc() {
    with_test_ay_ctx_for_source(COMBINED_ASSERT_RETURN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_combined_assert_return");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_combined_assert_return");

        assert_vc_structure(&vc, "probe_combined_assert_return", body.blocks.len());

        // Should have error-headed rules from the assert
        assert!(
            vc.rules.iter().any(|r| r.head.name == "error"),
            "Combined assert+return should emit error-headed rules"
        );

        // Should have more rules than a simple function due to multiple paths
        assert!(
            vc.rules.len() >= 3,
            "Combined function should produce at least 3 rules, got {}",
            vc.rules.len()
        );
    });
}

/// Multiple assertions in sequence should each produce error-headed rules.
const MULTI_ASSERT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_multi_assert(x: u32, y: u32) -> u32 {
        assert!(x > 0);
        assert!(y > 0);
        x + y
    }
"#;

#[test]
fn test_multi_assert_generates_multiple_error_rules() {
    with_test_ay_ctx_for_source(MULTI_ASSERT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_multi_assert");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_multi_assert");

        assert_vc_structure(&vc, "probe_multi_assert", body.blocks.len());

        let error_rule_count = vc.rules.iter().filter(|r| r.head.name == "error").count();
        // Two assert!() calls should produce at least 2 error paths
        assert!(
            error_rule_count >= 2,
            "Two assert!() calls should produce at least 2 error-headed rules, got {error_rule_count}",
        );
    });
}

const PACKED_KANI_MEM_SOURCE: &str = r#"
    #![allow(dead_code)]

    use core::ptr::addr_of;

    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn can_read_unaligned<T>(_ptr: *const T) -> bool {
                true
            }

            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool {
                true
            }
        }
    }

    #[repr(C, packed)]
    pub struct Packed {
        pub byte: u8,
        pub c: char,
    }

    pub fn probe_can_read_unaligned(packed: Packed) -> bool {
        kani::mem::can_read_unaligned(addr_of!(packed.c))
    }

    pub fn probe_can_dereference(packed: Packed) -> bool {
        kani::mem::can_dereference(addr_of!(packed.c))
    }
"#;

#[test]
fn test_can_read_unaligned_packed_char_avoids_kani_mem_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_read_unaligned");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_read_unaligned");

        assert_vc_structure(&vc, "probe_can_read_unaligned", body.blocks.len());
        assert_eq!(
            crate::codegen_ay::take_kani_mem_overapprox_count(),
            0,
            "packed char can_read_unaligned should no longer hit kani_mem_overapprox"
        );

        let has_char_validity = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().chain(rule.head.args.iter()).any(|constraint| {
                let rendered = constraint.to_string();
                (rendered.contains("55295")
                    || rendered.contains("D7FF")
                    || rendered.contains("d7ff"))
                    && (rendered.contains("57344")
                        || rendered.contains("E000")
                        || rendered.contains("e000"))
            })
        });
        assert!(
            has_char_validity,
            "packed char can_read_unaligned should carry Unicode scalar validity constraints"
        );
    });
}

#[test]
fn test_can_dereference_packed_char_avoids_kani_mem_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_dereference");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_dereference");

        assert_vc_structure(&vc, "probe_can_dereference", body.blocks.len());
        assert_eq!(
            crate::codegen_ay::take_kani_mem_overapprox_count(),
            0,
            "packed char can_dereference should no longer hit kani_mem_overapprox"
        );

        let has_alignment_check = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|constraint| constraint.to_string().contains("bvurem"))
        });
        assert!(
            has_alignment_check,
            "packed char can_dereference should retain the explicit alignment predicate"
        );
    });
}

/// Part of #4158: even when the destination local has no state index, overapprox
/// dispatch must still emit a transition rule instead of silently pruning the
/// successor edge.
#[test]
fn test_kani_mem_missing_dest_state_idx_emits_transition_rule() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_dereference");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_can_dereference", ChcConfig::default());
        chc_ctx.declare_block_relations();

        use rustc_public::mir::TerminatorKind;
        let (bb_idx, func, args, destination, target) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb_idx, block)| {
                let TerminatorKind::Call { func, args, destination, target, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                matches!(chc_ctx.detect_stub(func), Some(StubKind::KaniMemCanDereference))
                    .then_some((bb_idx, func, args, destination, target))
            })
            .expect("expected kani::mem::can_dereference call terminator");
        let target = target.expect("kani_mem call target");

        assert!(chc_ctx.state_var_mgr.local_to_state_idx.remove(&destination.local).is_some());
        assert!(chc_ctx.try_state_idx_for_local(destination.local).is_none());

        let from_app = RelationApp::new("__test_from", Vec::new());
        let modified_locals = HashSet::new();
        let stmt_constraints = [Expr::bool_const(true)];
        let before_rules = chc_ctx.vc.rules.len();
        let before_sound_fallback = chc_ctx.sound_fallback_count();

        let target_some = Some(target);
        let dcx = DispatchCallContext {
            bb_idx,
            func,
            args,
            destination,
            target: &target_some,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
            callee_path: None,
        };

        assert!(chc_ctx.codegen_call_terminator(&dcx));
        assert!(
            chc_ctx.sound_fallback_count() > before_sound_fallback,
            "missing-dest kani_mem dispatch should record at least one sound fallback"
        );
        let emitted = &chc_ctx.vc.rules[before_rules..];
        assert!(!emitted.is_empty());
        assert!(
            emitted.iter().any(|rule| rule.body.relation.is_some() && &*rule.head.name != "error")
        );
    });
}

// =============================================================================
// Full packed-mem address-form probes (Part of #3930)
//
// Mirrors the three address forms in tests/trust_mc/ValidValues/unaligned.rs:
//   addr_of!(packed)       — whole-struct pointer
//   addr_of!(packed.byte)  — byte-field pointer
//   addr_of!(packed.c)     — char-field pointer (already covered above)
// =============================================================================

const PACKED_KANI_MEM_FULL_SOURCE: &str = r#"
    #![allow(dead_code)]

    use core::ptr::addr_of;

    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn can_read_unaligned<T>(_ptr: *const T) -> bool {
                true
            }

            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool {
                true
            }
        }
    }

    #[repr(C, packed)]
    pub struct Packed {
        pub byte: u8,
        pub c: char,
    }

    pub fn probe_can_dereference_packed_whole(packed: Packed) -> bool {
        kani::mem::can_dereference(addr_of!(packed))
    }

    pub fn probe_can_dereference_packed_byte(packed: Packed) -> bool {
        kani::mem::can_dereference(addr_of!(packed.byte))
    }

    pub fn probe_can_dereference_packed_char(packed: Packed) -> bool {
        kani::mem::can_dereference(addr_of!(packed.c))
    }

    pub fn probe_can_read_unaligned_packed_whole(packed: Packed) -> bool {
        kani::mem::can_read_unaligned(addr_of!(packed))
    }

    pub fn probe_can_read_unaligned_packed_byte(packed: Packed) -> bool {
        kani::mem::can_read_unaligned(addr_of!(packed.byte))
    }

    pub fn probe_can_read_unaligned_packed_char(packed: Packed) -> bool {
        kani::mem::can_read_unaligned(addr_of!(packed.c))
    }
"#;

const PACKED_KANI_MEM_CONCRETE_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::ptr::addr_of;

    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn can_read_unaligned<T>(_ptr: *const T) -> bool {
                true
            }

            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool {
                true
            }
        }
    }

    #[repr(C, packed)]
    pub struct Packed {
        pub byte: u8,
        pub c: char,
    }

    #[repr(C)]
    pub struct NonPacked {
        pub byte: u8,
        pub c: char,
    }

    pub fn probe_can_dereference_nonpacked_whole_concrete() {
        let s = NonPacked { byte: 42, c: 'A' };
        assert!(kani::mem::can_dereference(addr_of!(s)));
    }

    pub fn probe_can_dereference_packed_whole_concrete() {
        let packed = Packed { byte: 42, c: 'A' };
        assert!(kani::mem::can_dereference(addr_of!(packed)));
    }

    pub fn probe_can_read_unaligned_packed_whole_concrete() {
        let packed = Packed { byte: 42, c: 'A' };
        assert!(kani::mem::can_read_unaligned(addr_of!(packed)));
    }
"#;

#[test]
fn test_can_dereference_packed_whole_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_FULL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_dereference_packed_whole");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_dereference_packed_whole");

        assert_vc_structure(&vc, "probe_can_dereference_packed_whole", body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        // Expose the exact count — if non-zero, the whole-struct path is the red form.
        assert_eq!(
            overapprox, 0,
            "packed whole-struct can_dereference should not hit kani_mem_overapprox (got {overapprox})"
        );
    });
}

#[test]
fn test_can_dereference_packed_byte_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_FULL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_dereference_packed_byte");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_dereference_packed_byte");

        assert_vc_structure(&vc, "probe_can_dereference_packed_byte", body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(
            overapprox, 0,
            "packed byte-field can_dereference should not hit kani_mem_overapprox (got {overapprox})"
        );
    });
}

#[test]
fn test_can_dereference_packed_char_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_FULL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_dereference_packed_char");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_dereference_packed_char");

        assert_vc_structure(&vc, "probe_can_dereference_packed_char", body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(
            overapprox, 0,
            "packed char-field can_dereference should not hit kani_mem_overapprox (got {overapprox})"
        );
    });
}

#[test]
fn test_can_read_unaligned_packed_whole_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_FULL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_read_unaligned_packed_whole");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_read_unaligned_packed_whole");

        assert_vc_structure(&vc, "probe_can_read_unaligned_packed_whole", body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(
            overapprox, 0,
            "packed whole-struct can_read_unaligned should not hit kani_mem_overapprox (got {overapprox})"
        );
    });
}

#[test]
fn test_can_read_unaligned_packed_byte_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_FULL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_read_unaligned_packed_byte");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_read_unaligned_packed_byte");

        assert_vc_structure(&vc, "probe_can_read_unaligned_packed_byte", body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(
            overapprox, 0,
            "packed byte-field can_read_unaligned should not hit kani_mem_overapprox (got {overapprox})"
        );
    });
}

#[test]
fn test_can_read_unaligned_packed_char_overapprox() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_FULL_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_can_read_unaligned_packed_char");
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_can_read_unaligned_packed_char");

        assert_vc_structure(&vc, "probe_can_read_unaligned_packed_char", body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(
            overapprox, 0,
            "packed char-field can_read_unaligned should not hit kani_mem_overapprox (got {overapprox})"
        );
    });
}

#[test]
fn test_mem_can_dereference_nonpacked_whole_concrete_is_safe() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_CONCRETE_SOURCE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_can_dereference_nonpacked_whole_concrete");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_mem(ctx.tcx, &body, "probe_can_dereference_nonpacked_whole_concrete");
        assert_vc_structure(
            &vc,
            "probe_can_dereference_nonpacked_whole_concrete",
            body.blocks.len(),
        );

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "VC should serialize to non-empty SMT-LIB2");
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

#[test]
fn test_mem_can_dereference_packed_whole_concrete_is_safe() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_CONCRETE_SOURCE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_can_dereference_packed_whole_concrete");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_mem(ctx.tcx, &body, "probe_can_dereference_packed_whole_concrete");
        assert_vc_structure(&vc, "probe_can_dereference_packed_whole_concrete", body.blocks.len());

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "VC should serialize to non-empty SMT-LIB2");
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

#[test]
fn test_mem_can_read_unaligned_packed_whole_concrete_is_safe() {
    with_test_ay_ctx_for_source(PACKED_KANI_MEM_CONCRETE_SOURCE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_can_read_unaligned_packed_whole_concrete");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_mem(ctx.tcx, &body, "probe_can_read_unaligned_packed_whole_concrete");
        assert_vc_structure(
            &vc,
            "probe_can_read_unaligned_packed_whole_concrete",
            body.blocks.len(),
        );

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "VC should serialize to non-empty SMT-LIB2");
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

// =============================================================================
// Defensive-branch invariants for overapprox dispatch partitioning
// =============================================================================

/// Overapprox dispatch has a defensive kani::mem fallback branch that should be
/// unreachable as long as the kani::mem stub partition remains exhaustive.
#[test]
fn test_kani_mem_stub_partition_is_exhaustive() {
    // Assume-true fallback stubs: must route to exactly one of assume_true XOR noop
    let assume_true_stubs = [StubKind::KaniMemAssertIsInitialized];

    for stub in assume_true_stubs {
        assert!(stub.is_kani_mem(), "{stub:?} must be classified as kani::mem");
        let assume_true = stub.is_kani_mem_assume_true();
        let noop = stub.is_kani_mem_noop();
        assert!(
            assume_true ^ noop,
            "{stub:?} must route to exactly one kani::mem sub-branch (assume_true={assume_true}, noop={noop})"
        );
    }

    // Explicit-dispatch stubs: have their own branches and must NOT fall through
    // to assume-true (Part of #3531, #3470, #4249)
    for stub in [
        StubKind::KaniMemCanDereference,
        StubKind::KaniMemCanWrite,
        StubKind::KaniMemCanReadUnaligned,
        StubKind::KaniMemIsPtrAligned,
        StubKind::KaniMemIsInbounds,
        StubKind::KaniMemSameAllocation,
    ] {
        assert!(stub.is_kani_mem(), "{stub:?} must be classified as kani::mem");
        assert!(
            !stub.is_kani_mem_assume_true(),
            "{stub:?} has an explicit dispatch branch and must not be in assume-true"
        );
    }
}

// =============================================================================
// &mut self inferable guard (Part of #3589, Part of #3348)
//
// Uses functions with >16 basic blocks so fn_inline rejects them and the calls
// fall through to the catch-all in codegen_call_primitive_cmp. Extern "Rust"
// functions are NOT usable here because is_foreign_call intercepts them before
// the catch-all.
// =============================================================================

/// Function with `&mut u32` first arg and >16 match arms (>16 effective blocks).
/// fn_inline rejects the callee body, so the call reaches the catch-all where
/// `has_mut_receiver` gates the inferable path.
const MUT_RECEIVER_COMPLEX_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn complex_mut(s: &mut u32, x: u32) -> u32 {
        match x {
            0 => { *s = s.wrapping_add(1); 10 }
            1 => { *s = s.wrapping_add(2); 11 }
            2 => { *s = s.wrapping_add(3); 12 }
            3 => { *s = s.wrapping_add(4); 13 }
            4 => { *s = s.wrapping_add(5); 14 }
            5 => { *s = s.wrapping_add(6); 15 }
            6 => { *s = s.wrapping_add(7); 16 }
            7 => { *s = s.wrapping_add(8); 17 }
            8 => { *s = s.wrapping_add(9); 18 }
            9 => { *s = s.wrapping_add(10); 19 }
            10 => { *s = s.wrapping_add(11); 20 }
            11 => { *s = s.wrapping_add(12); 21 }
            12 => { *s = s.wrapping_add(13); 22 }
            13 => { *s = s.wrapping_add(14); 23 }
            14 => { *s = s.wrapping_add(15); 24 }
            15 => { *s = s.wrapping_add(16); 25 }
            16 => { *s = s.wrapping_add(17); 26 }
            17 => { *s = s.wrapping_add(18); 27 }
            _ => { *s = s.wrapping_add(19); 28 }
        }
    }

    pub fn probe_mut_recv(s: &mut u32, x: u32) -> u32 {
        complex_mut(s, x)
    }
"#;

#[test]
fn test_mut_receiver_catchall_skips_inferable_predicate() {
    let _ = take_inferable_summary_names_by_fn();
    with_test_ay_ctx_for_source(MUT_RECEIVER_COMPLEX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_mut_recv");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_mut_recv");

        // The &mut receiver call should NOT produce any P_inf_ declarations
        // because has_mut_receiver returns true → inferable skipped.
        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|d| {
                if let trust_mc_core::decl::Decl::Fun { name, .. } = d {
                    if name.starts_with("P_inf_") { Some(name.as_str()) } else { None }
                } else {
                    None
                }
            })
            .collect();
        assert!(
            inferable_decls.is_empty(),
            "calls with &mut receiver should skip inferable predicates, \
             but found: {inferable_decls:?}"
        );

        let inferable_summary_names = take_inferable_summary_names_by_fn();
        assert!(
            inferable_summary_names.is_empty(),
            "calls with &mut receiver should not record inferable summary provenance, got: {inferable_summary_names:?}"
        );
    });
}

/// Same pattern but with value-type first arg (u32, not &mut). The inferable
/// constraint should be built because has_mut_receiver returns false.
const VALUE_ARG_COMPLEX_SOURCE: &str = r#"
    #![allow(dead_code)]

    fn complex_value(x: u32, y: u32) -> u32 {
        match y {
            0 => x.wrapping_add(1),
            1 => x.wrapping_add(2),
            2 => x.wrapping_add(3),
            3 => x.wrapping_add(4),
            4 => x.wrapping_add(5),
            5 => x.wrapping_add(6),
            6 => x.wrapping_add(7),
            7 => x.wrapping_add(8),
            8 => x.wrapping_add(9),
            9 => x.wrapping_add(10),
            10 => x.wrapping_add(11),
            11 => x.wrapping_add(12),
            12 => x.wrapping_add(13),
            13 => x.wrapping_add(14),
            14 => x.wrapping_add(15),
            15 => x.wrapping_add(16),
            16 => x.wrapping_add(17),
            17 => x.wrapping_add(18),
            _ => x.wrapping_add(19),
        }
    }

    pub fn probe_value_args(x: u32, y: u32) -> u32 {
        complex_value(x, y)
    }
"#;

#[test]
fn test_value_args_catchall_keeps_inferable_predicate() {
    let _ = take_inferable_summary_names_by_fn();
    with_test_ay_ctx_for_source(VALUE_ARG_COMPLEX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_value_args");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_value_args");

        // Value-type args (no &mut receiver) SHOULD produce P_inf_ declarations.
        // has_mut_receiver returns false (first arg is u32, not &mut T).
        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|d| {
                if let trust_mc_core::decl::Decl::Fun { name, .. } = d {
                    if name.starts_with("P_inf_") { Some(name.as_str()) } else { None }
                } else {
                    None
                }
            })
            .collect();
        assert!(
            !inferable_decls.is_empty(),
            "calls without &mut receiver should keep inferable predicates, \
             but no P_inf_ declarations found in VC"
        );

        let inferable_summary_names = take_inferable_summary_names_by_fn();
        let summaries = inferable_summary_names
            .get("probe_value_args")
            .expect("value-arg catch-all should record inferable provenance for the harness");
        assert!(
            !summaries.is_empty(),
            "value-arg catch-all should record at least one inferable summary name, got: {inferable_summary_names:?}"
        );
        assert!(
            summaries.keys().all(|name| name.starts_with("P_inf_")),
            "all recorded provenance entries must be inferable summary symbols, got: {summaries:?}"
        );
        assert!(
            summaries.keys().any(|name| name.contains("complex_value")),
            "value-arg catch-all should record the complex_value callee in inferable provenance, got: {summaries:?}"
        );
    });
}

/// Overapprox UB/panic dispatch has a defensive fallback branch that should be
/// unreachable as long as each UB/panic stub maps to one explicit sub-branch.
#[test]
fn test_ub_panic_stub_partition_is_exhaustive() {
    let ub_panic_stubs = [
        StubKind::UbCheckLanguageUb,
        StubKind::UbCheckMaybeIsAligned,
        StubKind::UbCheckMaybeIsNonoverlapping,
        StubKind::PreconditionCheck,
        StubKind::PanicUnreachable,
        StubKind::PanicError,
    ];

    for stub in ub_panic_stubs {
        assert!(stub.is_ub_panic(), "{stub:?} must be classified as ub/panic");
        let branch_hits = [
            stub.is_panic_error(),
            stub.is_panic_unreachable(),
            stub.is_ub_check_assume_true(),
            stub.is_ub_check_noop(),
        ]
        .into_iter()
        .filter(|hit| *hit)
        .count();
        assert_eq!(branch_hits, 1, "{stub:?} must route to exactly one UB/panic sub-branch");
    }
}
