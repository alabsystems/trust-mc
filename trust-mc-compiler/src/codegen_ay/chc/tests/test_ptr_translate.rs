// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Translation tests for CHC ptr intrinsic functions.
//!
//! Tests the actual SMT output of translate_ptr_add_call,
//! translate_ptr_write_call, and translate_ptr_read_call using
//! MIR-backed operands from compiled Rust source.
//!
//! Part of #2354: zero translation test coverage for ptr operations.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

// =============================================================================
// translate_ptr_add_call — pointer arithmetic translation
// =============================================================================

/// translate_ptr_add_call with real MIR operands should produce a bitvec result.
/// Exercises the ptr + count * sizeof(T) computation path.
#[test]
fn test_translate_ptr_add_returns_bitvec_result() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add(arr: &[u32; 4]) -> *const u32 {
            let p = arr.as_ptr();
            unsafe { p.add(2) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_add", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find PtrAdd call site in MIR
        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrAdd)
            {
                call_args = Some(args.clone());
                break;
            }
        }

        let args = call_args.expect("expected PtrAdd call terminator in probe_ptr_add MIR");
        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_ptr_add_call(&args, &modified);
        assert!(result.is_some(), "translate_ptr_add_call should return Some with valid MIR args");

        let result = result.unwrap();
        assert!(
            result.sort().is_bitvec(),
            "ptr.add result should be bitvec (pointer), got sort: {:?}",
            result.sort()
        );
    });
}

/// translate_ptr_add_call should produce a split-pointer recomposition (concat)
/// instead of a raw whole-pointer bvadd for 64-bit pointers.
///
/// Regression for #3921: whole-pointer bvadd lets symbolic arithmetic spill
/// from the offset lane into the object-id lane of the split-pointer model.
#[test]
fn test_translate_ptr_add_uses_split_pointer_concat() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_add_split(arr: &[u32; 4]) -> *const u32 {
            let p = arr.as_ptr();
            unsafe { p.add(2) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_add_split");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_add_split", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrAdd)
            {
                call_args = Some(args.clone());
                break;
            }
        }

        let args = call_args.expect("expected PtrAdd call terminator in probe_ptr_add_split MIR");
        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_ptr_add_call(&args, &modified);
        assert!(result.is_some(), "translate_ptr_add_call should return Some");

        let result = result.unwrap();
        let smt = result.to_string();

        // The result for 64-bit pointers must use concat (split-pointer
        // recomposition), not a top-level bvadd on the full 64-bit pointer.
        assert!(
            smt.contains("concat"),
            "ptr.add on 64-bit pointer should use split-pointer concat, got: {smt}"
        );
    });
}

/// Split-pointer step preserves obj_id lane in the encoding.
///
/// Regression for #3921: whole-pointer `bvadd` let symbolic arithmetic spill
/// from the offset lane into the object-id lane. The fix routes pointer offset
/// through `step_split_pointer`, which adds only to the lower 32-bit offset
/// lane and recombines with `concat`.
#[test]
fn test_split_pointer_step_preserves_obj_id_lane() {
    use crate::codegen_ay::chc::pointer_step::step_split_pointer;

    let obj_id = Expr::bitvec_const(0x42u128, 32);
    let offset = Expr::bitvec_const(0x100u128, 32);
    let ptr = obj_id.concat(offset);

    let byte_offset = Expr::bitvec_const(4u128, 64);
    let step = step_split_pointer(ptr, byte_offset);

    let smt = step.result.to_string();
    assert!(smt.contains("concat"), "split-pointer step should use concat recomposition: {smt}");

    let result_obj_id = step.result.clone().extract(63, 32);
    let result_obj_id_smt = result_obj_id.to_string();
    assert!(
        result_obj_id_smt.contains("#x00000042"),
        "obj_id lane should be preserved as-is: {result_obj_id_smt}"
    );

    let result_offset = step.result.extract(31, 0);
    let result_offset_smt = result_offset.to_string();
    assert!(
        result_offset_smt.contains("bvadd"),
        "offset lane should contain the addition: {result_offset_smt}"
    );

    assert!(step.same_object_ok.is_some(), "split-pointer step must surface same_object_ok");
}

/// Regression for #4029: `step_split_pointer` with a signed-negative byte_offset
/// must produce a `same_object_ok` predicate that evaluates to true when the
/// backward step stays within the same allocation.
#[test]
fn test_split_pointer_step_allows_negative_same_object_offset() {
    use crate::codegen_ay::chc::pointer_step::step_split_pointer;

    let obj_id = Expr::bitvec_const(0x42u128, 32);
    let offset = Expr::bitvec_const(0x100u128, 32);
    let ptr = obj_id.concat(offset);

    // byte_offset = -4 as signed 64-bit (two's complement: 0xFFFFFFFF_FFFFFFFC)
    let byte_offset = Expr::bitvec_const(0xFFFF_FFFF_FFFF_FFFCu128, 64);
    let step = step_split_pointer(ptr, byte_offset);

    let same_object_ok = step.same_object_ok.expect("split-pointer step must surface safety");

    // same_object_ok should be valid (true) for this in-bounds backward step.
    // Assert (not same_object_ok) is unsat.
    let smt = format!("(set-logic ALL)\n(assert (not {}))\n(check-sat)\n", same_object_ok);
    assert_z3_result(&smt, "unsat");

    // Result offset should be 0x100 - 4 = 0xFC.
    let expected_offset = Expr::bitvec_const(0xfcu128, 32);
    let result_offset = step.result.extract(31, 0);
    let offset_smt = format!(
        "(set-logic ALL)\n(assert (not (= {} {})))\n(check-sat)\n",
        result_offset, expected_offset
    );
    assert_z3_result(&offset_smt, "unsat");
}

/// Backward pointer steps within the same object use `step_split_pointer_sub`.
///
/// Regression for #3921 audit: backward (negative) offsets must go through
/// `step_split_pointer_sub` with the absolute byte count, not through
/// `step_split_pointer` with a signed-negative value. The latter's
/// `same_object_ok` predicate is unsound for negative offsets (#4029).
#[test]
fn test_split_pointer_sub_allows_backward_same_object_offset() {
    use crate::codegen_ay::chc::pointer_step::step_split_pointer_sub;

    let obj_id = Expr::bitvec_const(0x42u128, 32);
    let offset = Expr::bitvec_const(0x100u128, 32);
    let ptr = obj_id.concat(offset);

    // Step backward by 4 bytes using the sub helper.
    let byte_offset = Expr::bitvec_const(4u128, 64);
    let step = step_split_pointer_sub(ptr, byte_offset);

    let same_object_ok = step.same_object_ok.expect("split-pointer sub must surface safety");
    let expected_offset = Expr::bitvec_const(0xfcu128, 32);

    // same_object_ok should be valid (no underflow: 0x100 - 4 = 0xFC >= 0).
    let same_object_smt =
        format!("(set-logic ALL)\n(assert (not {}))\n(check-sat)\n", same_object_ok);
    assert_z3_result(&same_object_smt, "unsat");

    let result_offset = step.result.extract(31, 0);
    let offset_smt = format!(
        "(set-logic ALL)\n(assert (not (= {} {})))\n(check-sat)\n",
        result_offset, expected_offset
    );
    assert_z3_result(&offset_smt, "unsat");
}

// =============================================================================
// translate_ptr_write_call — memory store translation
// =============================================================================

/// translate_ptr_write_call with real MIR operands should return true,
/// indicating the memory store was modeled.
#[test]
fn test_translate_ptr_write_returns_true_on_success() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write() {
            let mut val: u32 = 0;
            let p = &mut val as *mut u32;
            unsafe { p.write(42) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_write", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find PtrWrite call site in MIR
        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrWrite)
            {
                call_args = Some(args.clone());
                break;
            }
        }

        let args = call_args.expect("expected PtrWrite call terminator in probe_ptr_write MIR");
        let modified: HashSet<usize> = HashSet::new();

        let result = chc_ctx.translate_ptr_write_call(&args, &modified);
        assert!(result, "translate_ptr_write_call should return true for valid ptr.write");
    });
}

/// ptr.write of a literal should preserve that literal through operand
/// translation and into the accumulated heap store chain.
///
/// Regression guard for #3677 triage: if the store chain drops `42` here, the
/// realloc-grow failure is already present before the realloc path runs.
#[test]
fn test_translate_ptr_write_preserves_literal_in_store_chain() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write_literal() {
            let mut val: u32 = 0;
            let p = &mut val as *mut u32;
            unsafe { p.write(42) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write_literal");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_ptr_write_literal", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrWrite)
            {
                call_args = Some(args.clone());
                break;
            }
        }

        let args = call_args.expect("expected PtrWrite call terminator in probe_ptr_write_literal");
        let modified: HashSet<usize> = HashSet::new();

        let value_expr = chc_ctx
            .translate_operand_with_modified(&args[1], &modified)
            .expect("ptr.write literal operand should translate");
        assert!(
            matches!(
                value_expr.value(),
                ExprValue::BitVecConst { value, width }
                    if *width == 32 && u64::try_from(value).ok() == Some(42)
            ),
            "ptr.write value operand should remain a bv32 literal 42, got {value_expr}"
        );

        let result = chc_ctx.translate_ptr_write_call(&args, &modified);
        assert!(result, "translate_ptr_write_call should succeed for ptr.write literal");

        let literal_smt = "#x0000002a";
        let has_literal_store = chc_ctx.heap_state.store_chains.values().any(|(_, expr)| {
            let smt = expr.to_string();
            smt.contains("store") && smt.contains(literal_smt)
        });
        assert!(
            has_literal_store,
            "ptr.write store chain should retain literal 42 in SMT form {literal_smt}"
        );
    });
}

/// PtrWrite should reuse known allocation IDs to store through a constant heap
/// address, so later loads can recover the same value at mem track.
#[test]
fn test_translate_ptr_write_uses_known_alloc_id_constant_addr() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_write_known_alloc_id() {
            let mut val: u32 = 0;
            let p = &mut val as *mut u32;
            unsafe { p.write(42) }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_write_known_alloc_id");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ptr_write_known_alloc_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrWrite)
            {
                call_args = Some(args.clone());
                break;
            }
        }

        let args =
            call_args.expect("expected PtrWrite call terminator in probe_ptr_write_known_alloc_id");
        let modified: HashSet<usize> = HashSet::new();
        let (rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)) =
            &args[0]
        else {
            panic!("PtrWrite operand should be a local place");
        };
        assert!(
            place.projection.is_empty(),
            "PtrWrite local should not carry projections in this probe"
        );

        let obj_id = 0xBEEF_u32;
        chc_ctx.known_alloc_ids.insert(place.local, obj_id);
        let ok = chc_ctx.translate_ptr_write_call(&args, &modified);
        assert!(ok, "translate_ptr_write_call should succeed for known alloc-id probe");

        let pointee_ty = args[0]
            .ty(body.locals())
            .ok()
            .and_then(ChcCtx::deref_pointee_ty)
            .expect("PtrWrite operand should dereference to u32");
        let const_addr = Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));
        let loaded = chc_ctx
            .load_from_memory(const_addr, pointee_ty)
            .expect("PtrWrite store should be recoverable through constant alloc-id address");
        let rendered = loaded.to_string();
        assert!(
            rendered.contains("#x0000002a"),
            "PtrWrite should store through the constant alloc-id address: {rendered}"
        );
    });
}

// =============================================================================
// translate_ptr_read_call — memory load translation
// =============================================================================

/// translate_ptr_read_call with real MIR operands should return an expression.
#[test]
fn test_translate_ptr_read_returns_some_expr() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_read() -> u32 {
            let val: u32 = 42;
            let p = &val as *const u32;
            unsafe { p.read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_read");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ptr_read", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find PtrRead call site in MIR
        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrRead)
            {
                call_args = Some(args.clone());
                break;
            }
        }

        let args = call_args.expect("expected PtrRead call terminator in probe_ptr_read MIR");
        let modified: HashSet<usize> = HashSet::new();

        let expr = chc_ctx
            .translate_ptr_read_call(&args, &modified)
            .expect("translate_ptr_read_call should return Some for u32 ptr.read");
        // ptr.read of u32 should produce a bitvec-32 expression
        assert!(
            expr.sort().is_bitvec(),
            "ptr.read result should be bitvec for u32, got: {:?}",
            expr.sort()
        );
        assert_eq!(
            expr.sort().bitvec_width(),
            Some(32),
            "ptr.read of u32 should produce bitvec-32"
        );
    });
}

/// PtrRead should reuse known allocation IDs to recover the constant heap
/// address family, mirroring store-side canonicalization.
#[test]
fn test_translate_ptr_read_uses_known_alloc_id_constant_addr() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub fn probe_ptr_read_known_alloc_id() -> u32 {
            let mut val: u32 = 0;
            let p = &mut val as *mut u32;
            unsafe { p.read() }
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ptr_read_known_alloc_id");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_ptr_read_known_alloc_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        chc_ctx.declare_block_relations();

        let mut call_args = None;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_ptr_memory)
                    == Some(StubKind::PtrRead)
            {
                call_args = Some(args.clone());
                break;
            }
        }

        let args =
            call_args.expect("expected PtrRead call terminator in probe_ptr_read_known_alloc_id");
        let modified: HashSet<usize> = HashSet::new();
        let (rustc_public::mir::Operand::Copy(place) | rustc_public::mir::Operand::Move(place)) =
            &args[0]
        else {
            panic!("PtrRead operand should be a local place");
        };
        assert!(
            place.projection.is_empty(),
            "PtrRead local should not carry projections in this probe"
        );

        let obj_id = 0xCAFE_u32;
        chc_ctx.known_alloc_ids.insert(place.local, obj_id);

        let pointee_ty = args[0]
            .ty(body.locals())
            .ok()
            .and_then(ChcCtx::deref_pointee_ty)
            .expect("PtrRead operand should dereference to u32");
        let const_addr = Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));
        chc_ctx.build_memory_store(const_addr, Expr::bitvec_const(42, 32), pointee_ty);

        let expr = chc_ctx
            .translate_ptr_read_call(&args, &modified)
            .expect("translate_ptr_read_call should succeed for known alloc-id probe");
        let rendered = expr.to_string();
        assert!(
            rendered.contains("#x0000002a"),
            "PtrRead should recover the constant-address store via known_alloc_ids: {rendered}"
        );
    });
}
