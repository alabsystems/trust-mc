// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Unit tests for check_values validity range logic.
//! Extracted from mod.rs (Part of #2204).

use super::*;
use crate::rustc_public_bridge::IndexedVal;
use rustc_public::abi::WrappingRange;
use rustc_public::mir::{BasicBlock, SwitchTargets, UnwindAction};
use rustc_public::target::MachineSize;
use rustc_public::ty::Span;

// =========================================================================
// range_contains tests (Part of #2190)
// Exercises all 4 match arms of range_contains(r1, r2, sz).
// =========================================================================

fn sz8() -> MachineSize {
    MachineSize::from_bits(8)
}
fn sz16() -> MachineSize {
    MachineSize::from_bits(16)
}

/// (no-wrap, no-wrap): r2 ⊆ r1 when r1.start <= r2.start && r1.end >= r2.end
#[test]
fn test_range_contains_nowrap_nowrap_subset() {
    let r1 = WrappingRange { start: 0, end: 255 };
    let r2 = WrappingRange { start: 10, end: 200 };
    assert!(range_contains(&r1, &r2, sz8()));
}

#[test]
fn test_range_contains_nowrap_nowrap_equal() {
    let r = WrappingRange { start: 5, end: 100 };
    assert!(range_contains(&r, &r, sz8()));
}

#[test]
fn test_range_contains_nowrap_nowrap_not_subset() {
    let r1 = WrappingRange { start: 10, end: 50 };
    let r2 = WrappingRange { start: 5, end: 100 };
    assert!(!range_contains(&r1, &r2, sz8()));
}

#[test]
fn test_range_contains_nowrap_nowrap_start_exceeds() {
    let r1 = WrappingRange { start: 20, end: 200 };
    let r2 = WrappingRange { start: 10, end: 100 };
    assert!(!range_contains(&r1, &r2, sz8()));
}

#[test]
fn test_range_contains_nowrap_nowrap_end_exceeds() {
    let r1 = WrappingRange { start: 0, end: 50 };
    let r2 = WrappingRange { start: 0, end: 100 };
    assert!(!range_contains(&r1, &r2, sz8()));
}

/// (wrap, wrap): both wrap around, containment by start/end comparison
#[test]
fn test_range_contains_wrap_wrap_subset() {
    // r1 wraps: [200, 255] ∪ [0, 50]
    // r2 wraps: [210, 255] ∪ [0, 30]
    let r1 = WrappingRange { start: 200, end: 50 };
    let r2 = WrappingRange { start: 210, end: 30 };
    assert!(range_contains(&r1, &r2, sz8()));
}

#[test]
fn test_range_contains_wrap_wrap_not_subset() {
    let r1 = WrappingRange { start: 210, end: 30 };
    let r2 = WrappingRange { start: 200, end: 50 };
    assert!(!range_contains(&r1, &r2, sz8()));
}

/// (wrap, no-wrap): wrapping r1 contains non-wrapping r2 if
/// r1.start <= r2.start OR r1.end >= r2.end
#[test]
fn test_range_contains_wrap_nowrap_low_end() {
    // r1 wraps: [200, 255] ∪ [0, 50], r2 = [10, 40]
    let r1 = WrappingRange { start: 200, end: 50 };
    let r2 = WrappingRange { start: 10, end: 40 };
    // r1.end(50) >= r2.end(40) → true
    assert!(range_contains(&r1, &r2, sz8()));
}

#[test]
fn test_range_contains_wrap_nowrap_high_end() {
    // r1 wraps: [200, 255] ∪ [0, 50], r2 = [210, 250]
    let r1 = WrappingRange { start: 200, end: 50 };
    let r2 = WrappingRange { start: 210, end: 250 };
    // r1.start(200) <= r2.start(210) → true
    assert!(range_contains(&r1, &r2, sz8()));
}

#[test]
fn test_range_contains_wrap_nowrap_gap() {
    // r1 wraps: [200, 255] ∪ [0, 50], r2 = [60, 190] (in the gap)
    let r1 = WrappingRange { start: 200, end: 50 };
    let r2 = WrappingRange { start: 60, end: 190 };
    // r1.start(200) <= r2.start(60)? No. r1.end(50) >= r2.end(190)? No. → false
    assert!(!range_contains(&r1, &r2, sz8()));
}

/// (no-wrap, wrap): non-wrapping r1 contains wrapping r2 only if r1 is full range
#[test]
fn test_range_contains_nowrap_wrap_full() {
    let r1 = WrappingRange { start: 0, end: 255 }; // full u8 range
    let r2 = WrappingRange { start: 200, end: 50 }; // wraps
    assert!(range_contains(&r1, &r2, sz8()));
}

#[test]
fn test_range_contains_nowrap_wrap_not_full() {
    let r1 = WrappingRange { start: 0, end: 200 }; // not full
    let r2 = WrappingRange { start: 200, end: 50 }; // wraps
    assert!(!range_contains(&r1, &r2, sz8()));
}

// =========================================================================
// ValidValueReq::is_full tests (Part of #2190)
// =========================================================================

#[test]
fn test_valid_value_req_is_full_true() {
    let req = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 0, end: 255 }),
    };
    assert!(req.is_full());
}

#[test]
fn test_valid_value_req_is_full_false() {
    let req = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 0, end: 200 }),
    };
    assert!(!req.is_full());
}

#[test]
fn test_valid_value_req_is_full_multiple_returns_false() {
    // Multiple variant always returns false from is_full
    let req = ValidValueReq {
        offset: 0,
        size: MachineSize::from_bits(32),
        valid_range: ValidityRange::Multiple([
            WrappingRange { start: 0, end: 0xD7FF },
            WrappingRange { start: 0xE000, end: 0x10FFFF },
        ]),
    };
    assert!(!req.is_full());
}

// =========================================================================
// ValidValueReq::contains tests (Part of #2190)
// =========================================================================

#[test]
fn test_contains_single_single_subset() {
    let outer = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 0, end: 255 }),
    };
    let inner = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 10, end: 200 }),
    };
    assert!(outer.contains(&inner));
}

#[test]
fn test_contains_single_single_not_subset() {
    let outer = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 10, end: 50 }),
    };
    let inner = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 5, end: 100 }),
    };
    assert!(!outer.contains(&inner));
}

#[test]
fn test_contains_multiple_single_first_covers() {
    // Multiple with two ranges, first range covers the single
    let outer = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Multiple([
            WrappingRange { start: 0, end: 0xD7FF },
            WrappingRange { start: 0xE000, end: 0xFFFF },
        ]),
    };
    let inner = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Single(WrappingRange { start: 100, end: 500 }),
    };
    assert!(outer.contains(&inner));
}

#[test]
fn test_contains_multiple_single_second_covers() {
    let outer = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Multiple([
            WrappingRange { start: 0, end: 100 },
            WrappingRange { start: 200, end: 65535 },
        ]),
    };
    let inner = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Single(WrappingRange { start: 300, end: 500 }),
    };
    assert!(outer.contains(&inner));
}

#[test]
fn test_contains_single_multiple_must_cover_both() {
    // Single must cover BOTH ranges of the Multiple
    let outer = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Single(WrappingRange { start: 0, end: 65535 }),
    };
    let inner = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Multiple([
            WrappingRange { start: 0, end: 0xD7FF },
            WrappingRange { start: 0xE000, end: 0xFFFF },
        ]),
    };
    assert!(outer.contains(&inner));
}

#[test]
fn test_contains_single_multiple_covers_only_one() {
    // Single covers only the first range of Multiple — should fail
    let outer = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Single(WrappingRange { start: 0, end: 0xDFFF }),
    };
    let inner = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Multiple([
            WrappingRange { start: 0, end: 0xD7FF },
            WrappingRange { start: 0xE000, end: 0xFFFF },
        ]),
    };
    assert!(!outer.contains(&inner));
}

// =========================================================================
// range_is_bool_like tests (task #76): the `bool` validity shape (one byte,
// 0..=1) must be recognized so a non-redirectable transmute fails closed
// instead of emitting a vacuous destination read-back check.
// =========================================================================

#[test]
fn test_range_is_bool_like_bool_shape() {
    let req = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 0, end: 1 }),
    };
    assert!(range_is_bool_like(&req));
}

#[test]
fn test_range_is_bool_like_rejects_nonzero_u8() {
    let req = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Single(WrappingRange { start: 1, end: 255 }),
    };
    assert!(!range_is_bool_like(&req));
}

#[test]
fn test_range_is_bool_like_rejects_wider_size() {
    // A 0..=1 range over 16 bits is not the bool shape.
    let req = ValidValueReq {
        offset: 0,
        size: sz16(),
        valid_range: ValidityRange::Single(WrappingRange { start: 0, end: 1 }),
    };
    assert!(!range_is_bool_like(&req));
}

#[test]
fn test_range_is_bool_like_rejects_multiple_ranges() {
    let req = ValidValueReq {
        offset: 0,
        size: sz8(),
        valid_range: ValidityRange::Multiple([
            WrappingRange { start: 0, end: 1 },
            WrappingRange { start: 3, end: 4 },
        ]),
    };
    assert!(!range_is_bool_like(&req));
}

// =========================================================================
// Precise array-source redirect cast fence.
// =========================================================================

#[test]
fn array_source_redirect_accepts_only_address_preserving_casts() {
    assert!(array_source_cast_preserves_address(&CastKind::PtrToPtr));
    assert!(array_source_cast_preserves_address(&CastKind::Subtype));

    for kind in [
        CastKind::PointerExposeAddress,
        CastKind::PointerWithExposedProvenance,
        CastKind::PointerCoercion(rustc_public::mir::PointerCoercion::Unsize),
        CastKind::IntToInt,
        CastKind::FloatToInt,
        CastKind::FloatToFloat,
        CastKind::IntToFloat,
        CastKind::FnPtrToPtr,
        CastKind::Transmute,
    ] {
        assert!(
            !array_source_cast_preserves_address(&kind),
            "{kind:?} must keep the original fail-closed dereference path"
        );
    }
}

// =========================================================================
// Array-source reaching-definition regressions (valid-value array redirect).
// =========================================================================

fn local_decl() -> LocalDecl {
    LocalDecl { ty: Ty::to_val(0), span: Span::to_val(0), mutability: Mutability::Mut }
}

fn assignment(local: Local, source: Local) -> Statement {
    Statement {
        kind: StatementKind::Assign(
            Place::from(local),
            Rvalue::Use(Operand::Copy(Place::from(source))),
        ),
        span: Span::to_val(0),
    }
}

fn basic_block(statements: Vec<Statement>, kind: TerminatorKind) -> BasicBlock {
    BasicBlock { statements, terminator: Terminator { kind, span: Span::to_val(0) } }
}

fn goto(target: BasicBlockIdx) -> TerminatorKind {
    TerminatorKind::Goto { target }
}

fn bool_switch(
    discr: Local,
    false_target: BasicBlockIdx,
    true_target: BasicBlockIdx,
) -> TerminatorKind {
    TerminatorKind::SwitchInt {
        discr: Operand::Copy(Place::from(discr)),
        targets: SwitchTargets::new(vec![(0, false_target)], true_target),
    }
}

fn mutable_body(blocks: Vec<BasicBlock>, local_count: usize, arg_count: usize) -> MutableBody {
    MutableBody::from(Body::new(
        blocks,
        vec![local_decl(); local_count],
        arg_count,
        Vec::new(),
        None,
        Span::to_val(0),
    ))
}

#[test]
fn array_source_declines_branch_dependent_argument_overwrite() {
    // Models a pointer argument whose caller-provided value reaches one branch,
    // while the other branch assigns it a pointer derived from a local array.
    // The statement is not the argument's unique definition: accepting it
    // would validate the local array even when the dereference uses the
    // caller's pointer.
    let body = mutable_body(
        vec![
            basic_block(Vec::new(), bool_switch(2, 2, 1)),
            basic_block(vec![assignment(1, 3)], goto(2)),
            basic_block(Vec::new(), TerminatorKind::Return),
        ],
        4,
        2,
    );

    assert!(
        unique_assignment_rhs(&body, 1).is_none(),
        "an argument's implicit caller definition must make a statement overwrite ambiguous",
    );
}

#[test]
fn array_source_declines_statement_and_call_destination_definitions() {
    // Models an if-expression whose local is assigned from an array-derived
    // pointer on one branch and is the destination of a pointer-returning call
    // on the other. Scanning statements alone sees one assignment, but the call
    // destination is a second reaching definition and must force fallback.
    let call = TerminatorKind::Call {
        func: Operand::Copy(Place::from(5)),
        args: Vec::new(),
        destination: Place::from(3),
        target: Some(3),
        unwind: UnwindAction::Terminate,
    };
    let body = mutable_body(
        vec![
            basic_block(Vec::new(), bool_switch(2, 2, 1)),
            basic_block(vec![assignment(3, 4)], goto(3)),
            basic_block(Vec::new(), call),
            basic_block(Vec::new(), TerminatorKind::Return),
        ],
        6,
        2,
    );

    assert!(
        unique_assignment_rhs(&body, 3).is_none(),
        "a call destination must count as a second reaching definition",
    );
}
