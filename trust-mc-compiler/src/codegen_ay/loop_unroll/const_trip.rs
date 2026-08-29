// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constant-trip-count analysis: derive a per-body unwind bound for loops whose
//! iteration count is statically computable.
//!
//! # Why this exists
//!
//! With no user unwind hint the effective depth is 1 (`compiler_interface.rs`:
//! `args.unwind.or(harness.unwind_value).or(args.default_unwind).unwrap_or(1)`).
//! `unroll_cfg_loops` then cuts the last copy's back-edge into an unwinding
//! assertion, so EVERYTHING AFTER the loop is reachable only through paths the
//! truncation removed and post-loop checks come back UNREACHABLE. Kani's default
//! is CBMC *complete* unwinding, so a constant-trip loop is fully unrolled there
//! and post-loop checks get real verdicts.
//!
//! Raising the default globally is the wrong fix: memory is already bounded
//! (`MAX_EXPANDED_BLOCKS`, `MAX_TOTAL_BLOCKS`), but a deeper unroll is a strictly
//! bigger solver query. So the bound is DERIVED per body, exactly like the
//! existing `variadic_unroll_depth` precedent in `codegen_function.rs`.
//!
//! # What it derives
//!
//! A concrete forward simulation of the body's control flow from `bb0`, with an
//! abstract store that holds only values it can compute exactly (`Val`) and `⊤`
//! for everything else. A branch on `⊤` stops the simulation. For every natural
//! loop header the simulation records the smallest `unwind_depth` at which no
//! header visit is truncated (see `remap_target`: at `iter == unwind_depth`
//! *every* in-loop target of the header diverts to the fail block).
//!
//! * A header that branches itself (`while c { .. }`) leaves the loop from the
//!   header on its final visit, and that edge is out-of-loop, so `n` body
//!   executions need `unwind_depth == n`.
//! * A header that only computes the condition and `goto`s the block that
//!   branches — how an indexed `for` loop lowers — has an IN-loop successor on
//!   every visit, its last one included, so it needs `n + 1`. Once the final
//!   header copy is not truncated, the out-of-loop exit edge can sit any number
//!   of blocks further down the loop body: `remap_target` only truncates edges
//!   whose source is the header.
//!
//! # Why a wrong answer is safe
//!
//! * The derived bound only ever RAISES the depth — it is combined with
//!   `.max()`, never used on its own, so it can never model fewer iterations
//!   than today.
//! * Unrolling stays fail-closed: an exhausted back-edge becomes an
//!   unwinding-assertion ERROR edge. A bound that is too small FAILS LOUDLY
//!   instead of proving anything vacuously. Nothing here may be used with
//!   unwinding assertions disabled — `derive_const_trip_unroll_depth` is only
//!   called when they are on (see `codegen_function.rs`).
//! * Anything not modelled exactly derives NOTHING for the affected loop
//!   (fail open to today's behaviour), never a guess.

use super::cfg::Cfg;
use super::dominators::find_loop_headers;
use super::unroll::natural_loop;
use rustc_public::mir::{
    AggregateKind, BinOp, Body, CastKind, ConstOperand, Local, Operand, Place, ProjectionElem,
    Rvalue, Statement, StatementKind, TerminatorKind, UnOp,
};
use rustc_public::ty::{AdtKind, ConstantKind, RigidTy, Ty, TyConstKind, TyKind};
use std::collections::HashMap;
use trust_mc_codegen_shared::IntoOption;
use trust_mc_codegen_types::types::{int_ty_to_bitvec_width, uint_ty_to_bitvec_width};

/// Hard cap on simulated basic-block transitions. A body that has not reached a
/// terminal state within this many steps derives whatever it has completed and
/// stops (see `SimOutcome::Bailed`).
const MAX_SIM_STEPS: usize = 200_000;

/// Hard cap on the derived depth. Above this the unroll is a solver-time
/// pessimisation rather than a fix, so we derive nothing and leave today's
/// behaviour (a loud unwinding-assertion failure) in place.
const CONST_TRIP_DEPTH_CAP: u32 = 64;

/// A value the simulator can represent exactly. Anything else is `⊤` (absent).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Val {
    Bool(bool),
    /// `bits` is the value's unsigned two's-complement representation, already
    /// masked to `width`. `signed` selects the comparison/shift semantics.
    Int {
        bits: u128,
        width: u32,
        signed: bool,
    },
}

impl Val {
    /// The bit pattern a `SwitchInt` case value is compared against, and the
    /// width the case value must be masked to first.
    ///
    /// MIR stores a signed case value sign-extended to the full `u128` (e.g.
    /// `Ordering::Less == -1` appears as `u128::MAX`), so comparing raw against
    /// this value's masked bits would silently miss the branch and send the
    /// simulation down `otherwise`. Same masking as `terminator.rs`.
    fn switch_bits(self) -> (u128, u32) {
        match self {
            Val::Bool(b) => (u128::from(b), 8),
            Val::Int { bits, width, .. } => (bits, width),
        }
    }
}

fn mask(width: u32) -> u128 {
    if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
}

fn truncate(bits: u128, width: u32) -> u128 {
    bits & mask(width)
}

/// Reinterpret a masked bit pattern as a signed value.
fn to_signed(bits: u128, width: u32) -> i128 {
    if width >= 128 {
        bits as i128
    } else if bits & (1u128 << (width - 1)) != 0 {
        (bits as i128) - (1i128 << width)
    } else {
        bits as i128
    }
}

/// Width/signedness for the integer-like scalar types the simulator models.
fn int_shape(ty: Ty) -> Option<(u32, bool)> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(int_ty)) => Some((int_ty_to_bitvec_width(int_ty), true)),
        TyKind::RigidTy(RigidTy::Uint(uint_ty)) => Some((uint_ty_to_bitvec_width(uint_ty), false)),
        _ => None,
    }
}

/// Read a MIR constant operand, if it is a scalar this simulator models.
fn const_val(c: &ConstOperand) -> Option<Val> {
    let mir_const = &c.const_;
    let ty = mir_const.ty();
    let alloc = match mir_const.kind() {
        ConstantKind::Allocated(alloc) => alloc.clone(),
        ConstantKind::Ty(ty_const) => match ty_const.kind() {
            TyConstKind::Value(_, alloc) => alloc.clone(),
            _ => return None,
        },
        _ => return None,
    };
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool) => Some(Val::Bool(alloc.read_bool().into_option()?)),
        TyKind::RigidTy(RigidTy::Int(int_ty)) => {
            let width = int_ty_to_bitvec_width(int_ty);
            let v = alloc.read_int().into_option()?;
            Some(Val::Int { bits: truncate(v as u128, width), width, signed: true })
        }
        TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
            let width = uint_ty_to_bitvec_width(uint_ty);
            let v = alloc.read_uint().into_option()?;
            Some(Val::Int { bits: truncate(v, width), width, signed: false })
        }
        _ => None,
    }
}

/// The part of a place the store can address: a local, optionally one field.
///
/// `CheckedBinaryOp` writes a `(T, bool)` tuple that MIR immediately reads back
/// as `(_5.0: i32)` / `(_5.1: bool)`, so single-level field addressing is the
/// minimum needed to follow an ordinary `+=` in a loop body.
type Slot = (Local, Option<u32>);

fn place_slot(place: &Place) -> Option<Slot> {
    match place.projection.as_slice() {
        [] => Some((place.local, None)),
        [ProjectionElem::Field(idx, _)] => Some((place.local, Some(*idx as u32))),
        _ => None,
    }
}

/// The abstract store. Absent key == `⊤` (unknown).
#[derive(Default)]
struct Store {
    vals: HashMap<Slot, Val>,
}

impl Store {
    fn get(&self, place: &Place, poisoned: &[bool]) -> Option<Val> {
        let slot = place_slot(place)?;
        if poisoned.get(slot.0).copied().unwrap_or(true) {
            return None;
        }
        self.vals.get(&slot).copied()
    }

    /// Forget everything known about `local` (all of its slots).
    fn kill_local(&mut self, local: Local) {
        self.vals.retain(|(l, _), _| *l != local);
    }

    /// Write `val` (or `⊤` when `None`) to `place`.
    fn write(&mut self, place: &Place, val: Option<Val>) {
        match place_slot(place) {
            Some((local, None)) => {
                // A whole-local write invalidates every field view of it.
                self.kill_local(local);
                if let Some(v) = val {
                    self.vals.insert((local, None), v);
                }
            }
            Some((local, Some(idx))) => {
                // A field write leaves the whole-local view stale.
                self.vals.remove(&(local, None));
                match val {
                    Some(v) => {
                        self.vals.insert((local, Some(idx)), v);
                    }
                    None => {
                        self.vals.remove(&(local, Some(idx)));
                    }
                }
            }
            // Deref/index writes: we cannot tell what was written, so forget the
            // whole base local. (Its pointee, if it is a local, is poisoned.)
            None => self.kill_local(place.local),
        }
    }
}

/// Whether an aggregate's operands land in the same field slots a later read
/// addresses them by.
///
/// Structs and tuples qualify: operand `i` is `FieldIdx` `i`, and MIR reads the
/// value back with the bare `Field(i)` projection that `place_slot` models.
/// Enums do not — the read goes through a `Downcast` that `place_slot` refuses,
/// so recording the fields could only ever be read back under the WRONG variant.
/// Unions do not — `Field` there reinterprets the same bytes. Arrays, closures,
/// coroutines and raw pointers are not one-level-field-addressable at all.
fn aggregate_is_field_addressable(kind: &AggregateKind) -> bool {
    match kind {
        AggregateKind::Tuple => true,
        // A struct has exactly one variant, so the variant index is necessarily
        // zero; `active_field` is `Some` only for a union initialiser.
        AggregateKind::Adt(def, _, _, _, active_field) => {
            def.kind() == AdtKind::Struct && active_field.is_none()
        }
        _ => false,
    }
}

/// Locals whose address is taken anywhere in the body can be mutated through a
/// pointer the simulator does not track, so their values are never trusted.
fn poisoned_locals(body: &Body) -> Vec<bool> {
    let mut poisoned = vec![false; body.locals().len()];
    let mut poison = |local: Local| {
        if let Some(slot) = poisoned.get_mut(local) {
            *slot = true;
        }
    };
    for block in body.blocks.iter() {
        for stmt in &block.statements {
            if let StatementKind::Assign(dest, rvalue) = &stmt.kind {
                // A write that goes through a projection we cannot address is
                // handled by `Store::write`; here we only care about aliasing.
                if dest.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
                    poison(dest.local);
                }
                match rvalue {
                    Rvalue::Ref(_, _, place)
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::CopyForDeref(place) => poison(place.local),
                    _ => {}
                }
            }
        }
    }
    poisoned
}

/// Evaluate a binary operation on two modelled values.
///
/// Returns `None` whenever the exact result is not representable by `Val` or
/// would be UB/overflow — the simulation then stores `⊤`, which is safe.
fn eval_binop(op: BinOp, a: Val, b: Val) -> Option<Val> {
    // Comparisons are defined on bools too.
    if let (Val::Bool(x), Val::Bool(y)) = (a, b) {
        return match op {
            BinOp::Eq => Some(Val::Bool(x == y)),
            BinOp::Ne => Some(Val::Bool(x != y)),
            BinOp::BitAnd => Some(Val::Bool(x && y)),
            BinOp::BitOr => Some(Val::Bool(x || y)),
            BinOp::BitXor => Some(Val::Bool(x != y)),
            _ => None,
        };
    }
    let (
        Val::Int { bits: ab, width: aw, signed: asg },
        Val::Int { bits: bb, width: bw, signed: bsg },
    ) = (a, b)
    else {
        return None;
    };

    // Shifts are the one operation whose operand types legitimately differ.
    if matches!(op, BinOp::Shl | BinOp::ShlUnchecked | BinOp::Shr | BinOp::ShrUnchecked) {
        let shift = to_signed(bb, bw);
        if shift < 0 || shift >= i128::from(aw) {
            // Overflowing shift: Rust reports it, so this is not an execution
            // we need to count. Model it as unknown.
            return None;
        }
        let shift = shift as u32;
        let out = match op {
            BinOp::Shl | BinOp::ShlUnchecked => truncate(ab << shift, aw),
            _ if asg => truncate((to_signed(ab, aw) >> shift) as u128, aw),
            _ => ab >> shift,
        };
        return Some(Val::Int { bits: out, width: aw, signed: asg });
    }

    // Everything else requires matching operand shapes.
    if aw != bw || asg != bsg {
        return None;
    }
    let width = aw;
    let signed = asg;

    let ordering =
        if signed { to_signed(ab, width).cmp(&to_signed(bb, width)) } else { ab.cmp(&bb) };
    match op {
        BinOp::Eq => return Some(Val::Bool(ab == bb)),
        BinOp::Ne => return Some(Val::Bool(ab != bb)),
        BinOp::Lt => return Some(Val::Bool(ordering.is_lt())),
        BinOp::Le => return Some(Val::Bool(ordering.is_le())),
        BinOp::Gt => return Some(Val::Bool(ordering.is_gt())),
        BinOp::Ge => return Some(Val::Bool(ordering.is_ge())),
        _ => {}
    }

    let bits = if signed {
        let x = to_signed(ab, width);
        let y = to_signed(bb, width);
        let exact: i128 = match op {
            BinOp::Add | BinOp::AddUnchecked => x.checked_add(y)?,
            BinOp::Sub | BinOp::SubUnchecked => x.checked_sub(y)?,
            BinOp::Mul | BinOp::MulUnchecked => x.checked_mul(y)?,
            BinOp::Div => x.checked_div(y)?,
            BinOp::Rem => x.checked_rem(y)?,
            BinOp::BitAnd => x & y,
            BinOp::BitOr => x | y,
            BinOp::BitXor => x ^ y,
            _ => return None,
        };
        // Reject anything that does not fit the type: that execution traps, so
        // it is not one whose trip count we should be counting.
        if !matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor)
            && width < 128
            && (exact >= (1i128 << (width - 1)) || exact < -(1i128 << (width - 1)))
        {
            return None;
        }
        truncate(exact as u128, width)
    } else {
        let exact: u128 = match op {
            BinOp::Add | BinOp::AddUnchecked => ab.checked_add(bb)?,
            BinOp::Sub | BinOp::SubUnchecked => ab.checked_sub(bb)?,
            BinOp::Mul | BinOp::MulUnchecked => ab.checked_mul(bb)?,
            BinOp::Div => ab.checked_div(bb)?,
            BinOp::Rem => ab.checked_rem(bb)?,
            BinOp::BitAnd => ab & bb,
            BinOp::BitOr => ab | bb,
            BinOp::BitXor => ab ^ bb,
            _ => return None,
        };
        if width < 128 && exact > mask(width) {
            return None;
        }
        truncate(exact, width)
    };
    Some(Val::Int { bits, width, signed })
}

struct Simulator {
    poisoned: Vec<bool>,
    store: Store,
}

impl Simulator {
    fn operand(&self, op: &Operand) -> Option<Val> {
        match op {
            Operand::Constant(c) => const_val(c),
            Operand::Copy(place) | Operand::Move(place) => self.store.get(place, &self.poisoned),
        }
    }

    fn rvalue(&self, rvalue: &Rvalue) -> Option<Val> {
        match rvalue {
            Rvalue::Use(op) => self.operand(op),
            Rvalue::BinaryOp(op, a, b) => eval_binop(*op, self.operand(a)?, self.operand(b)?),
            Rvalue::UnaryOp(UnOp::Not, a) => match self.operand(a)? {
                Val::Bool(b) => Some(Val::Bool(!b)),
                Val::Int { bits, width, signed } => {
                    Some(Val::Int { bits: truncate(!bits, width), width, signed })
                }
            },
            Rvalue::UnaryOp(UnOp::Neg, a) => match self.operand(a)? {
                Val::Int { bits, width, signed: true } => {
                    let x = to_signed(bits, width);
                    let neg = x.checked_neg()?;
                    if width < 128
                        && (neg >= (1i128 << (width - 1)) || neg < -(1i128 << (width - 1)))
                    {
                        return None;
                    }
                    Some(Val::Int { bits: truncate(neg as u128, width), width, signed: true })
                }
                _ => None,
            },
            Rvalue::Cast(CastKind::IntToInt, op, ty) => {
                let (width, signed) = int_shape(*ty)?;
                match self.operand(op)? {
                    Val::Bool(b) => Some(Val::Int { bits: u128::from(b), width, signed }),
                    Val::Int { bits, width: from_w, signed: from_signed } => {
                        // Sign- or zero-extend from the source width, then truncate.
                        let extended =
                            if from_signed { to_signed(bits, from_w) as u128 } else { bits };
                        Some(Val::Int { bits: truncate(extended, width), width, signed })
                    }
                }
            }
            _ => None,
        }
    }

    /// Apply an assignment, including the `(T, bool)` tuple that
    /// `CheckedBinaryOp` writes and MIR immediately reads back field-wise.
    fn assign(&mut self, place: &Place, rvalue: &Rvalue) {
        // `_6 = CheckedSub(_2, 1_i32)` followed by `_2 = move (_6.0: i32)` is
        // how EVERY ordinary `-=` appears in MIR, so the tuple has to be
        // modelled field-wise or the induction variable goes unknown after one
        // iteration and no bound is ever derived.
        if let Rvalue::CheckedBinaryOp(op, a, b) = rvalue
            && let Some((local, None)) = place_slot(place)
        {
            // `eval_binop` returns `None` on overflow, which is exactly the case
            // where the `.1` flag is set and the check fails; leaving the whole
            // tuple unknown there is safe and stops the simulation shortly after.
            let value =
                self.operand(a).zip(self.operand(b)).and_then(|(x, y)| eval_binop(*op, x, y));
            self.store.kill_local(local);
            if let Some(v) = value {
                self.store.vals.insert((local, Some(0)), v);
                self.store.vals.insert((local, Some(1)), Val::Bool(false));
            }
            return;
        }
        // `_2 = Range::<i32> { start: 1, end: 4 }` is an `Aggregate`, and every
        // `a..b` loop bound is built exactly that way. Without this the whole
        // local goes to TOP, the later `(_2.0: i32)` read is unknown, and the
        // loop condition is undecidable — so the header switch bails and the
        // trip count is never derived. A struct/tuple aggregate is precisely a
        // field-wise write, so recording it is exact, not an approximation.
        if let Rvalue::Aggregate(kind, ops) = rvalue
            && let Some((local, None)) = place_slot(place)
            && aggregate_is_field_addressable(kind)
        {
            self.store.kill_local(local);
            for (idx, op) in ops.iter().enumerate() {
                if let Some(v) = self.operand(op) {
                    self.store.vals.insert((local, Some(idx as u32)), v);
                }
            }
            return;
        }
        let val = self.rvalue(rvalue);
        self.store.write(place, val);
    }

    /// Apply one statement to the store.
    fn statement(&mut self, stmt: &Statement) {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.assign(place, rvalue);
            }
            StatementKind::SetDiscriminant { place, .. } => {
                self.store.kill_local(place.local);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                self.store.kill_local(*local);
            }
            // No effect on the values this store models: FakeRead, PlaceMention,
            // AscribeUserType, Coverage, ConstEvalCounter, Nop.
            // `Intrinsic` writes only through pointers, whose targets are poisoned.
            _ => {}
        }
    }
}

/// How the simulation ended. `Completed` means every branch was decided; the
/// counts describe the whole reachable control flow of the body.
#[derive(Debug, PartialEq, Eq)]
enum SimOutcome {
    /// Reached `Return`/`Unreachable`/`Abort`/a diverging call.
    Completed,
    /// Hit an undecidable branch, inline asm, or the step cap. Counts for loops
    /// the simulation was NOT inside at that moment are still real observations,
    /// but the body may have more control flow we never saw.
    Bailed { inside: Vec<usize> },
}

struct TripCounts {
    /// Longest run of back-edges observed in a single entry of each loop.
    max_run: HashMap<usize, u32>,
    outcome: SimOutcome,
}

/// Concretely simulate the body's control flow and count loop back-edges.
fn simulate(body: &Body, loops: &HashMap<usize, Vec<bool>>) -> TripCounts {
    let mut sim = Simulator { poisoned: poisoned_locals(body), store: Store::default() };
    let mut max_run: HashMap<usize, u32> = HashMap::new();
    let mut cur_run: HashMap<usize, u32> = HashMap::new();

    let mut bb = 0usize;
    let mut prev: Option<usize> = None;
    let mut steps = 0usize;

    let inside_now = |bb: usize, loops: &HashMap<usize, Vec<bool>>| -> Vec<usize> {
        let mut v: Vec<usize> =
            loops.iter().filter(|(_, in_loop)| in_loop[bb]).map(|(h, _)| *h).collect();
        v.sort_unstable();
        v
    };

    loop {
        if steps >= MAX_SIM_STEPS {
            tracing::debug!(bb, steps, "const-trip: bail — step cap reached");
            return TripCounts {
                max_run,
                outcome: SimOutcome::Bailed { inside: inside_now(bb, loops) },
            };
        }
        steps += 1;

        // Record loop-header arrivals: a back-edge continues the current run,
        // an entry from outside the loop starts a fresh one at zero.
        if let Some(in_loop) = loops.get(&bb) {
            let from_inside = prev.is_some_and(|p| in_loop[p]);
            let run = if from_inside { cur_run.get(&bb).copied().unwrap_or(0) + 1 } else { 0 };
            cur_run.insert(bb, run);
            let entry = max_run.entry(bb).or_insert(0);
            *entry = (*entry).max(run);
        }

        let block = &body.blocks[bb];
        for stmt in &block.statements {
            sim.statement(stmt);
        }

        let next = match &block.terminator.kind {
            TerminatorKind::Goto { target } => *target,
            TerminatorKind::SwitchInt { discr, targets } => {
                let Some(val) = sim.operand(discr) else {
                    tracing::debug!(
                        bb,
                        ?discr,
                        "const-trip: bail — SwitchInt discriminant is not modelled"
                    );
                    return TripCounts {
                        max_run,
                        outcome: SimOutcome::Bailed { inside: inside_now(bb, loops) },
                    };
                };
                let (bits, width) = val.switch_bits();
                targets
                    .branches()
                    .find(|(case, _)| truncate(*case, width) == bits)
                    .map(|(_, t)| t)
                    .unwrap_or_else(|| targets.otherwise())
            }
            // Follow the success edge: we are counting the iterations of an
            // execution that does not trap. A failing assert only means the
            // real trip count is SHORTER than what we count, which is safe.
            TerminatorKind::Assert { target, .. } => *target,
            TerminatorKind::Drop { place, target, .. } => {
                sim.store.kill_local(place.local);
                *target
            }
            TerminatorKind::Call { destination, target, .. } => {
                sim.store.write(destination, None);
                match target {
                    Some(t) => *t,
                    // Diverging call: this path ends here.
                    None => return TripCounts { max_run, outcome: SimOutcome::Completed },
                }
            }
            TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::Resume
            | TerminatorKind::Abort => {
                return TripCounts { max_run, outcome: SimOutcome::Completed };
            }
            // Inline asm can mutate anything the simulator models.
            TerminatorKind::InlineAsm { .. } => {
                tracing::debug!(bb, "const-trip: bail — inline asm");
                return TripCounts {
                    max_run,
                    outcome: SimOutcome::Bailed { inside: inside_now(bb, loops) },
                };
            }
        };

        if next >= body.blocks.len() {
            tracing::debug!(bb, next, "const-trip: bail — successor out of range");
            return TripCounts {
                max_run,
                outcome: SimOutcome::Bailed { inside: inside_now(bb, loops) },
            };
        }
        // The LAST visit to a header has to be able to leave the loop through the
        // header's OWN terminator: `remap_target` sends every in-loop target of
        // the header to the unwinding-assertion failure once `iter == depth`.
        // A header that branches itself (`while c { .. }`) therefore needs
        // exactly its back-edge count — its final visit takes the out-of-loop
        // edge. A header that only computes the condition and `goto`s the block
        // that branches — exactly how an indexed `for` loop lowers — reaches an
        // in-loop successor on EVERY visit, its final one included, and so needs
        // one copy more. Recording `run + 1` for an in-loop successor covers
        // both without ever lowering the bound below the back-edge count.
        if let Some(in_loop) = loops.get(&bb)
            && in_loop[next]
        {
            let need = cur_run.get(&bb).copied().unwrap_or(0) + 1;
            let entry = max_run.entry(bb).or_insert(0);
            *entry = (*entry).max(need);
        }

        prev = Some(bb);
        bb = next;
    }
}

/// Derive an unwind bound from loops whose trip count is statically computable.
///
/// Returns `None` when nothing could be derived — the caller then keeps today's
/// behaviour exactly.
///
/// SOUNDNESS: the result is only ever combined with `.max()` against the
/// configured depth, and unwinding assertions stay ON, so a bound derived too
/// small still fails loudly rather than truncating silently.
pub(in crate::codegen_ay) fn derive_const_trip_unroll_depth(body: &Body) -> Option<u32> {
    let cfg = Cfg::from_body(body);
    if cfg.is_acyclic() {
        return None;
    }
    let headers = find_loop_headers(&cfg).ok()?;
    if headers.is_empty() {
        return None;
    }

    // Membership test per loop, so an arrival at a header can be classified as a
    // back-edge (continue the run) or an entry from outside (start a new run).
    let mut loops: HashMap<usize, Vec<bool>> = HashMap::new();
    for (header, mut latches) in headers {
        latches.sort_unstable();
        latches.dedup();
        let lp = natural_loop(&cfg, header, &latches);
        loops.insert(header, lp.in_loop);
    }

    let counts = simulate(body, &loops);
    tracing::debug!(?counts.outcome, ?counts.max_run, "const-trip: simulation finished");

    // A loop the simulation was still inside when it bailed has an INCOMPLETE
    // count, so it derives nothing.
    let incomplete: &[usize] = match &counts.outcome {
        SimOutcome::Completed => &[],
        SimOutcome::Bailed { inside } => inside,
    };

    let mut derived: Option<u32> = None;
    for (header, run) in counts.max_run {
        if incomplete.contains(&header) || run == 0 {
            continue;
        }
        if run > CONST_TRIP_DEPTH_CAP {
            tracing::debug!(
                header,
                run,
                cap = CONST_TRIP_DEPTH_CAP,
                "const-trip: derived depth over cap, deriving nothing for this loop"
            );
            continue;
        }
        derived = Some(derived.unwrap_or(0).max(run));
    }
    tracing::debug!(?derived, "const-trip: derived unwind bound");
    derived
}

#[cfg(test)]
mod tests;
