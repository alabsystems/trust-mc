// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A write through an interior pointer must never be silently dropped.
//!
//! `translate_stack_store` is keyed by the ALLOCA's `ValueId`. A store whose ptr
//! is `BorrowMut(GEP(alloca, k))` — what `&mut local.field` lowers to — misses the
//! precise `stack_cell`, and the `ValidBorrow` annotation then suppresses the
//! `MemoryAccessWithoutPreciseModel` fail-close. Before the interior-pointer
//! provenance fix the write was dropped with NO diagnostic while the alloca's cell
//! kept its PRE-store value, so the next `Load` read back the value the function
//! had just overwritten and every obligation over it was discharged against a
//! stale value. That is a false-PROVE generator, the worst state a verifier has.
//!
//! The modules below are the shape `trustc -Ztrust-dump=native-bundle` emits for
//!
//! ```ignore
//! pub struct S { pub a: u32, pub b: u32 }
//! pub fn f(seed: u32) -> u32 { let mut s = S { a: 1, b: seed };
//!                              let r = &mut s.a; *r = K; 100 / s.a }
//! ```
//!
//! The obligation is the divide-by-zero check on `s.a`, encoded as the reachability
//! of the `error` relation. With the seeded field (`1`) and the written constant
//! both literal, the whole error constraint folds to a constant, so each test can
//! read the verdict EXACTLY rather than diffing rule text: `Some(true)` = error
//! reachable (correctly refuted), `Some(false)` = error unreachable (PROVED),
//! `None` = the value went symbolic (havoc — sound, imprecise).

use trust_ir::inst::ICmpOp;
use trust_ir::value::FuncId;
use trust_ir::{Constant, FieldDef, ProofAnnotation, StructDef, StructRepr, Ty};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::chc::ChcVc;
use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;
use trust_mc_trust_bmc::{
    TranslateOptions, TrustIrChcDiagnostic, single_cell_alloca_rejection,
    stack_alloca_cell_accesses_match_type, stack_alloca_pointer_is_non_escaping,
    trust_ir_function_to_chc_translation_output,
};

/// How the pointer stored through is derived from the `s` alloca.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Target {
    /// `&mut s.a` — `BorrowMut(GEP(alloca, 0))`, the pervasive shape.
    FieldBorrow,
    /// `&mut s.a` with the field index computed, not constant — the offset is
    /// unknown, so the whole cell must be havoced rather than left stale.
    SymbolicLaneBorrow,
    /// `&mut s` — `BorrowMut(alloca)`, no `GEP` at all.
    WholeBorrow,
    /// A pointer with no provenance into the alloca, stored through AFTER the
    /// alloca's interior address escaped into a call. It may alias `s`.
    UnknownAfterEscape,
    /// A pointer with no provenance into the alloca and no escape anywhere: it
    /// provably cannot reach the cell, so the cell must stay precise.
    UnknownWithNoEscape,
    /// `sink(&mut s.a)` and NOTHING after it — the interior address escapes into a
    /// call and no store follows. The callee may write through it, so the readback
    /// must NOT see the seeded value. This is the pure call-invalidation case:
    /// `UnknownAfterEscape` above always appends a store, which is what triggered
    /// the only pre-existing consumer of `escaped_cell_bases`.
    CallEscapeNoStore,
}

struct Probe {
    vc: ChcVc,
    diagnostics: Vec<TrustIrChcDiagnostic>,
}

/// Build `f`, writing `written` into `s.a` through `target`, and translate it.
fn probe(target: Target, written: i128, valid_borrow: bool) -> Probe {
    let mut mb = ModuleBuilder::new("interior_ptr");
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "interior_ptr::S".to_string(),
        fields: vec![
            FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
            FieldDef { name: "b".into(), ty: Ty::U32, offset: Some(4) },
        ],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::Rust,
    });
    let sty = Ty::Struct(struct_id);
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    // A callee an interior pointer can escape into.
    let sink_ty = mb.add_func_type(vec![Ty::Ptr], vec![Ty::Unit]);
    let sink_id = mb.peek_next_func_id();
    {
        let mut sink = mb.function("sink", sink_ty);
        let sink_entry = sink.create_block();
        sink.switch_to_block(sink_entry);
        sink.set_entry(sink_entry);
        sink.add_block_param(sink_entry, Ty::Ptr);
        sink.ret(vec![]);
        sink.build();
    }

    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let seed = fb.add_block_param(entry, Ty::U32);

    // s = S { a: 1, b: seed }, spilled to the stack because its address is taken.
    let one = fb.const_value(Ty::U32, Constant::Int(1));
    let undef = fb.undef(sty.clone());
    let agg0 = fb.insert_field(sty.clone(), undef, 0, one);
    let agg1 = fb.insert_field(sty.clone(), agg0, 1, seed);
    let slot = fb.alloca(sty.clone());
    fb.store(sty.clone(), slot, agg1);

    let k = fb.const_value(Ty::U32, Constant::Int(written));
    let proofs = if valid_borrow { vec![ProofAnnotation::ValidBorrow] } else { Vec::new() };

    match target {
        Target::FieldBorrow => {
            let lane = fb.const_value(Ty::I64, Constant::Int(0));
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.store_proven(Ty::U32, borrow, k, proofs);
        }
        Target::SymbolicLaneBorrow => {
            // A lane index the translator cannot fold: `seed & 0` is 0 in fact, but
            // the GEP index is not a `BitVecConst`, so the offset is unknown.
            let mask = fb.const_value(Ty::U32, Constant::Int(0));
            let masked = fb.binop(trust_ir::inst::BinOp::And, Ty::U32, seed, mask);
            let lane = fb.zext(Ty::U32, Ty::I64, masked);
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.store_proven(Ty::U32, borrow, k, proofs);
        }
        Target::WholeBorrow => {
            // `*(&mut s) = S { a: K, b: seed }` — no GEP, the borrow IS the alloca.
            let undef2 = fb.undef(sty.clone());
            let n0 = fb.insert_field(sty.clone(), undef2, 0, k);
            let n1 = fb.insert_field(sty.clone(), n0, 1, seed);
            let borrow = fb.borrow_mut(slot);
            fb.store_proven(sty.clone(), borrow, n1, proofs);
        }
        Target::UnknownAfterEscape => {
            // `sink(&mut s.a)` — the interior address leaves the model...
            let lane = fb.const_value(Ty::I64, Constant::Int(0));
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.call_void(sink_id, vec![borrow]);
            // ...and this store is through a pointer that may be the escaped one.
            let opaque = fb.null_ptr();
            fb.store_proven(Ty::U32, opaque, k, proofs);
        }
        Target::UnknownWithNoEscape => {
            let opaque = fb.null_ptr();
            fb.store_proven(Ty::U32, opaque, k, proofs);
        }
        Target::CallEscapeNoStore => {
            // `sink(&mut s.a)` — and deliberately NO store afterwards.
            let lane = fb.const_value(Ty::I64, Constant::Int(0));
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.call_void(sink_id, vec![borrow]);
        }
    }

    // 100 / s.a — read back through the SAME alloca.
    let reloaded = fb.load(sty.clone(), slot);
    let a = fb.extract_field(Ty::U32, reloaded, 0);
    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, a, zero);
    let f = fb.const_value(Ty::Bool, Constant::Bool(false));
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, f);
    fb.assert(ok);
    fb.ret(vec![a]);
    fb.build();

    let module = mb.build();
    let out = trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(1),
        &TranslateOptions::default(),
    )
    .expect("f translates");
    Probe { vc: out.vc, diagnostics: out.diagnostics }
}

/// TrustIR GEP is `base + index * size_of(pointee_ty)`, not structural field
/// selection. In `{ u64, u32 }`, `gep u32 base, [1]` is byte offset 4, inside
/// the first field; it does NOT select the second field at byte offset 8.
///
/// The pre-fix lane mapper nevertheless saw `fields[1] == u32`, overwrote the
/// modeled second field with 7, and falsely proved the assertion below even
/// though the real second field remains zero. The sound fallback is to havoc
/// the cell because this heterogeneous byte offset has no exact aggregate lane.
fn heterogeneous_non_lane_gep_probe() -> Probe {
    let mut mb = ModuleBuilder::new("heterogeneous_interior_ptr");
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "heterogeneous_interior_ptr::S".to_string(),
        fields: vec![
            FieldDef { name: "wide".into(), ty: Ty::U64, offset: Some(0) },
            FieldDef { name: "divisor".into(), ty: Ty::U32, offset: Some(8) },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
    });
    let struct_ty = Ty::Struct(struct_id);
    let fn_ty = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("heterogeneous_gep", fn_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let wide = fb.const_value(Ty::U64, Constant::Int(0));
    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let undef = fb.undef(struct_ty.clone());
    let with_wide = fb.insert_field(struct_ty.clone(), undef, 0, wide);
    let aggregate = fb.insert_field(struct_ty.clone(), with_wide, 1, zero);
    let slot = fb.alloca(struct_ty.clone());
    fb.store(struct_ty.clone(), slot, aggregate);

    let one = fb.const_value(Ty::I64, Constant::Int(1));
    let byte_four = fb.gep(Ty::U32, slot, vec![one]);
    let borrowed = fb.borrow_mut(byte_four);
    let seven = fb.const_value(Ty::U32, Constant::Int(7));
    fb.store_proven(Ty::U32, borrowed, seven, vec![ProofAnnotation::ValidBorrow]);

    let reloaded = fb.load(struct_ty.clone(), slot);
    let divisor = fb.extract_field(Ty::U32, reloaded, 1);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, divisor, zero);
    let false_value = fb.const_value(Ty::Bool, Constant::Bool(false));
    let nonzero = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, false_value);
    fb.assert(nonzero);
    fb.ret(vec![divisor]);
    fb.build();

    let module = mb.build();
    let out = trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("heterogeneous GEP fixture translates");
    Probe { vc: out.vc, diagnostics: out.diagnostics }
}

/// Build a homogeneous `{ u32, u32 }` pair and attempt to write logical field 1
/// with `gep u32 [1]` (byte offset 4). The supplied layout decides whether that
/// address is evidence-grade field identity or must degrade to whole-cell havoc.
fn homogeneous_field_one_probe(
    name: &str,
    offsets: [Option<u64>; 2],
    size: Option<u64>,
    align: Option<u64>,
) -> Probe {
    let mut mb = ModuleBuilder::new(name);
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: format!("{name}::S"),
        fields: vec![
            FieldDef { name: "first".into(), ty: Ty::U32, offset: offsets[0] },
            FieldDef { name: "divisor".into(), ty: Ty::U32, offset: offsets[1] },
        ],
        size,
        align,
        repr: StructRepr::Rust,
    });
    let struct_ty = Ty::Struct(struct_id);
    let fn_ty = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("homogeneous_gep", fn_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let undef = fb.undef(struct_ty.clone());
    let with_first = fb.insert_field(struct_ty.clone(), undef, 0, zero);
    let aggregate = fb.insert_field(struct_ty.clone(), with_first, 1, zero);
    let slot = fb.alloca(struct_ty.clone());
    fb.store(struct_ty.clone(), slot, aggregate);

    let one = fb.const_value(Ty::I64, Constant::Int(1));
    let byte_four = fb.gep(Ty::U32, slot, vec![one]);
    let borrowed = fb.borrow_mut(byte_four);
    let seven = fb.const_value(Ty::U32, Constant::Int(7));
    fb.store_proven(Ty::U32, borrowed, seven, vec![ProofAnnotation::ValidBorrow]);

    let reloaded = fb.load(struct_ty.clone(), slot);
    let divisor = fb.extract_field(Ty::U32, reloaded, 1);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, divisor, zero);
    let false_value = fb.const_value(Ty::Bool, Constant::Bool(false));
    let nonzero = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, false_value);
    fb.assert(nonzero);
    fb.ret(vec![divisor]);
    fb.build();

    let module = mb.build();
    let out = trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("homogeneous GEP fixture translates");
    Probe { vc: out.vc, diagnostics: out.diagnostics }
}

/// Two logical fields alias the same four bytes. A write through the field-0
/// address changes BOTH observable field reads, so updating only logical field 0
/// would leave field 1 stale and could falsely prove `field1 == 0`.
fn overlapping_fields_probe() -> Probe {
    let mut mb = ModuleBuilder::new("overlapping_fields");
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "overlapping_fields::S".into(),
        fields: vec![
            FieldDef { name: "first".into(), ty: Ty::U32, offset: Some(0) },
            FieldDef { name: "alias".into(), ty: Ty::U32, offset: Some(0) },
        ],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::Rust,
    });
    let struct_ty = Ty::Struct(struct_id);
    let fn_ty = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("overlapping_gep", fn_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let undef = fb.undef(struct_ty.clone());
    let with_first = fb.insert_field(struct_ty.clone(), undef, 0, zero);
    let aggregate = fb.insert_field(struct_ty.clone(), with_first, 1, zero);
    let slot = fb.alloca(struct_ty.clone());
    fb.store(struct_ty.clone(), slot, aggregate);

    let index_zero = fb.const_value(Ty::I64, Constant::Int(0));
    let overlapping_address = fb.gep(Ty::U32, slot, vec![index_zero]);
    let borrowed = fb.borrow_mut(overlapping_address);
    let seven = fb.const_value(Ty::U32, Constant::Int(7));
    fb.store_proven(Ty::U32, borrowed, seven, vec![ProofAnnotation::ValidBorrow]);

    let reloaded = fb.load(struct_ty.clone(), slot);
    let alias = fb.extract_field(Ty::U32, reloaded, 1);
    let alias_still_zero = fb.icmp(ICmpOp::Eq, Ty::U32, alias, zero);
    fb.assert(alias_still_zero);
    fb.ret(vec![alias]);
    fb.build();

    let module = mb.build();
    let out = trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("overlapping-field fixture translates");
    Probe { vc: out.vc, diagnostics: out.diagnostics }
}

/// Constant-fold the `error`-head rules' constraints.
///
/// `Some(true)`  — the error is reachable on a constant path: the obligation is
///                 (correctly) refuted.
/// `Some(false)` — every error path folds to false: the obligation is PROVED.
/// `None`        — a constraint stayed symbolic: the value was havoced, so the
///                 solver decides. Sound, imprecise — never a false proof.
fn error_reachability(vc: &ChcVc) -> Option<bool> {
    let mut any_reachable = false;
    let mut saw_error_rule = false;
    for rule in &vc.rules {
        if rule.head.name.as_str() != "error" {
            continue;
        }
        saw_error_rule = true;
        let mut conjunction = Some(true);
        for constraint in rule.body.constraints.iter() {
            match try_eval_to_bool(constraint) {
                Some(true) => {}
                Some(false) => {
                    conjunction = Some(false);
                    break;
                }
                None => conjunction = None,
            }
        }
        match conjunction {
            Some(true) => any_reachable = true,
            Some(false) => {}
            None => return None,
        }
    }
    assert!(saw_error_rule, "the assert must emit an error rule");
    Some(any_reachable)
}

/// THE REGRESSION. Writing `0` through `&mut s.a` makes `100 / s.a` a genuine
/// divide-by-zero, so the error MUST be reachable. Before the fix the write was
/// dropped and the readback was the seeded `1`, folding the error constraint to
/// `false` — a false PROVE of a function that actually divides by zero.
#[test]
fn field_store_through_borrow_is_not_dropped() {
    let bad = probe(Target::FieldBorrow, 0, true);
    assert_eq!(
        error_reachability(&bad.vc),
        Some(true),
        "DROPPED WRITE: `*(&mut s.a) = 0` was not modeled, so the readback folded to the \
         PRE-store field value and the divide-by-zero obligation was falsely PROVED"
    );
    assert!(
        bad.diagnostics.is_empty(),
        "the write is modeled exactly, so nothing should fail closed: {:?}",
        bad.diagnostics
    );
}

/// The other side of the same coin: a write that FIXES the divisor must be
/// believed, so the obligation still proves. Guards against "fix" by blanket
/// havoc, which would leave this `None` instead of `Some(false)`.
#[test]
fn field_store_through_borrow_is_modeled_precisely() {
    let good = probe(Target::FieldBorrow, 7, true);
    assert_eq!(
        error_reachability(&good.vc),
        Some(false),
        "`*(&mut s.a) = 7` must be modeled at the field lane, so the divisor is 7"
    );
    assert!(good.diagnostics.is_empty(), "{:?}", good.diagnostics);
}

/// A matching non-I8 field type is not enough to turn TrustIR byte arithmetic
/// into field identity. Heterogeneous aggregates must fail closed by havocing.
#[test]
fn heterogeneous_non_i8_gep_does_not_update_a_rederived_field_lane() {
    let probe = heterogeneous_non_lane_gep_probe();
    assert_eq!(
        error_reachability(&probe.vc),
        None,
        "`gep u32` index 1 into `{{u64,u32}}` is byte offset 4, not field 1; an exact field-1 update falsely proves the zero-divisor assertion"
    );
    assert!(
        probe.diagnostics.is_empty(),
        "the owned cell was soundly invalidated; no unsupported rule is needed: {:?}",
        probe.diagnostics
    );
}

/// Complete, non-overlapping layout evidence keeps the intended direct lane
/// precise: byte offset 4 is exactly the second u32 field.
#[test]
fn explicit_matching_layout_updates_the_proved_field_lane() {
    let probe = homogeneous_field_one_probe(
        "explicit_matching_layout",
        [Some(0), Some(4)],
        Some(8),
        Some(4),
    );
    assert_eq!(
        error_reachability(&probe.vc),
        Some(false),
        "declared byte offset 4 uniquely identifies field 1"
    );
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
}

/// Homogeneous field types are not layout evidence. With field 1 declared at
/// byte 8, `gep u32 [1]` lands at byte 4 (padding), so updating field 1 would
/// falsely prove the assertion.
#[test]
fn explicit_offset_mismatch_havocs_instead_of_updating_a_field() {
    let probe = homogeneous_field_one_probe(
        "explicit_offset_mismatch",
        [Some(0), Some(8)],
        Some(12),
        Some(4),
    );
    assert_eq!(
        error_reachability(&probe.vc),
        None,
        "a raw byte offset in padding must not be reinterpreted as logical field 1"
    );
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
}

/// `offset: null` is absence of authority, not permission to assume declaration
/// order. Even a homogeneous pair must degrade to havoc without layout evidence.
#[test]
fn missing_struct_layout_havocs_instead_of_assuming_field_identity() {
    let probe = homogeneous_field_one_probe("missing_layout", [None, None], None, None);
    assert_eq!(
        error_reachability(&probe.vc),
        None,
        "missing field offsets cannot authorize an exact derived-pointer update"
    );
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
}

/// Exact logical-lane replacement is unsound when another declared field aliases
/// the written bytes. The whole aggregate must be invalidated.
#[test]
fn overlapping_declared_fields_havoc_instead_of_leaving_a_sibling_stale() {
    let probe = overlapping_fields_probe();
    assert_eq!(
        error_reachability(&probe.vc),
        None,
        "overlapping field 1 must not retain its pre-write zero after field 0 is written"
    );
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
}

/// A `BorrowMut` straight off the alloca (no `GEP`) carries the same provenance.
#[test]
fn whole_cell_store_through_borrow_is_not_dropped() {
    assert_eq!(
        error_reachability(&probe(Target::WholeBorrow, 0, true).vc),
        Some(true),
        "`*(&mut s) = S {{ a: 0, .. }}` was dropped: the readback is stale"
    );
    assert_eq!(
        error_reachability(&probe(Target::WholeBorrow, 7, true).vc),
        Some(false),
        "`*(&mut s) = S {{ a: 7, .. }}` must be modeled exactly"
    );
}

/// An unknown offset cannot be written at a lane, but it also cannot be dropped:
/// the cell is havoced, so the readback is unconstrained and the obligation is
/// left to the solver (`None`) instead of being proved from a stale value.
#[test]
fn symbolic_lane_store_havocs_rather_than_going_stale() {
    for written in [0, 7] {
        assert_eq!(
            error_reachability(&probe(Target::SymbolicLaneBorrow, written, true).vc),
            None,
            "a store at an unknown offset into `s` must havoc the cell (write {written})"
        );
    }
}

/// A store through an unknown pointer, made after `&mut s.a` escaped into a call,
/// may alias `s`. It must invalidate the cell — not be dropped while the cell
/// keeps its pre-store value.
#[test]
fn unknown_store_after_an_address_escape_invalidates_the_cell() {
    assert_eq!(
        error_reachability(&probe(Target::UnknownAfterEscape, 0, true).vc),
        None,
        "the escaped interior address may be this store's target, so `s` must be havoced"
    );
}

/// The precision floor: with no escape anywhere, an unknown store provably cannot
/// reach the cell, so the cell stays precise and the obligation still proves. This
/// is what keeps the fix from degenerating into "havoc everything on any store".
#[test]
fn unknown_store_with_no_escape_leaves_the_cell_precise() {
    assert_eq!(
        error_reachability(&probe(Target::UnknownWithNoEscape, 0, true).vc),
        Some(false),
        "nothing aliases `s`, so `s.a` is still the seeded 1 and the divisor is nonzero"
    );
}

/// THE CALL-INVALIDATION ORACLE. `sink(&mut s.a)` with no store after it. The callee
/// may write any value through the escaped interior pointer, so the readback of `s.a`
/// must be a havoc and `s.a != 0` must NOT prove.
///
/// If this reads `Some(false)`, the translator proved the assertion from the value that
/// was in the cell BEFORE the call — a stale read, and a completed false proof.
///
/// THIS ORACLE IS LOAD-BEARING, AND THAT IS MEASURED, NOT ASSUMED. It was vacuous while
/// `translate_alloca`'s coarse whole-function escape guard demoted every escaping cell —
/// the havoc came from the guard. Now that the guard is narrowed to admit
/// `StackCellEscape::IntoCallsOnly`, commenting out the single
/// `invalidate_cells_escaping_into_call` call in `translate_node` makes THIS test, and
/// only this test, fail: 12 passed / 1 failed. That failure is the translator proving
/// `s.a != 0` from the value the cell held BEFORE the call — the exact false proof the
/// narrowing would have shipped had the two halves been landed in the other order.
#[test]
fn call_escape_without_a_following_store_invalidates_the_cell() {
    assert_eq!(
        error_reachability(&probe(Target::CallEscapeNoStore, 0, true).vc),
        None,
        "the callee may write through the escaped `&mut s.a`, so `s.a` must be havoced"
    );
}

/// `ValidBorrow` asserts the BORROW is valid, never that the WRITE was modeled.
/// Whether it is present must not change what the cell holds afterwards.
#[test]
fn valid_borrow_annotation_does_not_change_the_modeled_write() {
    for target in [Target::FieldBorrow, Target::WholeBorrow] {
        for written in [0, 7] {
            let annotated = probe(target, written, true);
            let bare = probe(target, written, false);
            assert_eq!(
                error_reachability(&annotated.vc),
                error_reachability(&bare.vc),
                "`ValidBorrow` changed the modeled value of the write (write {written})"
            );
        }
    }
}

// ===========================================================================
// THE CROSS-BLOCK PROJECTED-READ ORACLE
//
// `aggregate_cell_hazards_stay_fail_closed` pins that a `FieldProjected` cell is REFUSED
// by both admission lanes, which is what keeps the 181-row aggregate slice of the
// `store_/load_in_other_block` bucket (221 rows at R59) unpromotable. But that pin checks
// REJECTION only, and its fixture DISCARDS the GEP result (`let _addr = fb.gep(..)`), so
// nothing anywhere exercises a projected READ or checks what the model would COMPUTE if
// the cell were promoted.
//
// Widening promotion therefore cannot be justified by the existing suite — it would swap
// a conservative alias rule for an unverified correctness claim. These are the missing
// oracles. They are TESTS, so they cannot introduce a false proof; they can only reveal
// whether the hazard is modelled.
//
// The shape is the hazard itself, not a weaker cousin: the cell is written in BOTH arms
// of a branch and read back THROUGH A GEP in the join — the block that CONSUMES the
// threaded value. That is exactly where a stale or fabricated leaf would surface.
// ===========================================================================

/// `{ u64, u64 }` written in both arms, field 0 read back via `GEP` in the join block.
/// `then_a`/`else_a` are what each arm stores into field 0.
fn cross_block_projected(then_a: i128, else_a: i128) -> ChcVc {
    let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let mut mb = ModuleBuilder::new("cross_block_projected_read");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let mut fb = mb.function("projected_join", ft);

    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    let join = fb.create_block();
    fb.set_entry(entry);

    fb.switch_to_block(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let cell = fb.alloca(pair.clone());
    fb.condbr(cond, then_block, vec![], else_block, vec![]);

    for (blk, a) in [(then_block, then_a), (else_block, else_a)] {
        fb.switch_to_block(blk);
        let av = fb.const_value(Ty::U64, Constant::Int(a));
        let bv = fb.const_value(Ty::U64, Constant::Int(7));
        let undef = fb.undef(pair.clone());
        let p0 = fb.insert_field(pair.clone(), undef, 0, av);
        let p1 = fb.insert_field(pair.clone(), p0, 1, bv);
        fb.store(pair.clone(), cell, p1);
        fb.br(join, vec![]);
    }

    // THE JOIN: field 0 read back THROUGH a GEP, in the block consuming the threaded
    // value. This is the `FieldProjected` hazard actually exercised.
    fb.switch_to_block(join);
    let lane = fb.const_value(Ty::I64, Constant::Int(0));
    let field_ptr = fb.gep(Ty::U64, cell, vec![lane]);
    let a = fb.load(Ty::U64, field_ptr);
    let zero = fb.const_value(Ty::U64, Constant::Int(0));
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U64, a, zero);
    let f = fb.const_value(Ty::Bool, Constant::Bool(false));
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, f);
    fb.assert(ok);
    fb.ret(vec![a]);
    fb.build();

    let module = mb.build();
    // This builder makes exactly ONE function, so it is id 0 — unlike `probe()` above,
    // whose `sink` callee occupies 0 and whose subject is 1.
    trust_ir_function_to_chc_translation_output(&module, FuncId::new(0), &TranslateOptions::default())
        .expect("projected_join translates")
        .vc
}

/// BASELINE / ACCEPTANCE TARGET. Field 0 is the SAME nonzero constant on both paths, so
/// `a != 0` is genuinely TRUE. Today the cell is unpromoted (its pointer feeds a `GEP`),
/// the join's projected read havocs, and the obligation is NOT proved.
///
/// A correct widening must turn this into `Some(false)` — WITHOUT changing the tripwire
/// below. That pair is the acceptance criterion for touching
/// `aggregate_cell_hazards_stay_fail_closed`.
#[test]
fn cross_block_projected_read_is_unproved_while_the_cell_is_unpromoted() {
    assert_eq!(
        error_reachability(&cross_block_projected(1, 1)),
        None,
        "baseline: unpromoted cell => the join's projected read havocs => not proved"
    );
}

/// THE FALSE-PROOF TRIPWIRE, and why the target above is not sufficient alone.
///
/// The `else` arm stores ZERO into field 0, so `a != 0` is genuinely FALSE on that path.
/// No model may prove it — not today's havoc, not a future promoted per-leaf model. A
/// widening that makes this report `Some(false)` is threading only ONE arm's leaf into
/// the join and is UNSOUND.
#[test]
fn a_zero_storing_arm_must_never_let_the_projected_read_prove() {
    assert_ne!(
        error_reachability(&cross_block_projected(1, 0)),
        Some(false),
        "FALSE PROOF: else arm stores 0 into field 0, so `a != 0` must not be provable"
    );
}

/// DIAGNOSTIC for the 181-row cross-block bucket: WHICH condition refuses the oracle's
/// cell? Lifting the GEP disqualification alone left the projected read unproved, so a
/// further blocker exists and this names it rather than leaving it to inference.
#[test]
fn why_is_the_cross_block_projected_cell_refused() {
    let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let mut mb = ModuleBuilder::new("diag");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let mut fb = mb.function("projected_join", ft);
    let (entry, t, e, join) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let cell = fb.alloca(pair.clone());
    fb.condbr(cond, t, vec![], e, vec![]);
    for blk in [t, e] {
        fb.switch_to_block(blk);
        let av = fb.const_value(Ty::U64, Constant::Int(1));
        let bv = fb.const_value(Ty::U64, Constant::Int(7));
        let u = fb.undef(pair.clone());
        let p0 = fb.insert_field(pair.clone(), u, 0, av);
        let p1 = fb.insert_field(pair.clone(), p0, 1, bv);
        fb.store(pair.clone(), cell, p1);
        fb.br(join, vec![]);
    }
    fb.switch_to_block(join);
    let lane = fb.const_value(Ty::I64, Constant::Int(0));
    let fp = fb.gep(Ty::U64, cell, vec![lane]);
    let a = fb.load(Ty::U64, fp);
    fb.ret(vec![a]);
    fb.build();
    let module = mb.build();
    let function = &module.functions[0];

    let rejection = single_cell_alloca_rejection(&module, function, cell, &pair);
    println!(
        "CROSS-BLOCK DIAGNOSTIC: lane1={:?} lane2={:?}  non_escaping={} ty_match={}",
        rejection.as_ref().map(|r| r.block_local.kind()),
        rejection.as_ref().map(|r| r.promoted.kind()),
        stack_alloca_pointer_is_non_escaping(function, cell),
        stack_alloca_cell_accesses_match_type(function, cell, &pair),
    );
}
