// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! A sound, local interval analysis over one MIR body, for the region scan.
//!
//! The region scan (`uncertified_check::region_may_carry_obligation`) decides
//! whether a SwitchInt arm the walker abandons can carry an obligation. It
//! used to count every `Assert` and every statement site, including a bounds
//! check that always holds: `arr[(i % 4) as usize]` on a four-element array
//! made the abandoned arm an uncertified reach check, and a safe program
//! FAILED (the walker fail-closed review's `c2_free_region_safe`,
//! fix/chc-walker-fail-closed package round 2 item a). This module proves
//! such sites discharged, and nothing else.
//!
//! # The analysis
//!
//! FLOW-INSENSITIVE over the whole body: every tracked local's interval is the
//! join of the values of ALL its assignments, so a read anywhere, on any
//! path, in any loop iteration, sees one of them. A local is tracked only when
//! every write to it is a whole-local `Assign` the evaluator reads; anything
//! else makes it `Top` (its type's range, or "unknown" for a bool):
//!
//! * an argument (the caller chose it), a call's destination, an inline-asm
//!   operand;
//! * a local whose address is taken anywhere (`&`, `&mut`, `&raw`, of the
//!   local or any projection of it: a write through the pointer is invisible
//!   here), or written through a projection (`x.0 = ..`, `x[i] = ..`);
//! * a local of a type this module does not model (a generic parameter, a
//!   128-bit integer, anything but the fixed-width integers, `bool` and the
//!   `(integer, bool)` pair of a checked operation).
//!
//! An interval that keeps growing past a few rounds is widened to `Top`.
//! Unknown means "may fail": a site is discharged only when the interval
//! proves its condition for every value.
//!
//! What it evaluates: integer constants, copies, `IntToInt` casts (the value
//! is kept when it fits the target, else the target's range), `Rem`, `Div`,
//! `BitAnd`, `Shr` and wrapping or checked `Add`/`Sub`/`Mul` by the exact
//! interval rules, an array's `Len`, and the comparisons that produce a bool.
//!
//! What it discharges: an `Assert` whose condition is provably its expected
//! value (a bounds check `idx < N`, a checked operation's overflow flag, a
//! divisor-zero or `MIN / -1` test), and the statement sites the obligation
//! walk sights when their condition is proved: an `Index` into a fixed-size
//! array, `Div`/`Rem` by a divisor that cannot be zero (nor `-1` against
//! `MIN`), an unchecked `Add`/`Sub`/`Mul` that cannot overflow, an unchecked
//! shift by an in-range distance, a signed negation that cannot see `MIN`,
//! and `assume` of a condition that holds.

use rustc_public::mir::{
    BinOp, Body, CastKind, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue,
    Statement, StatementKind, TerminatorKind, UnOp,
};
use rustc_public::ty::{IntTy, RigidTy, Ty, TyKind, UintTy};
use std::collections::{HashMap, HashSet};

/// An inclusive integer interval.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Interval {
    pub(super) lo: i128,
    pub(super) hi: i128,
}

impl Interval {
    fn point(v: i128) -> Self {
        Interval { lo: v, hi: v }
    }
    fn join(self, other: Interval) -> Interval {
        Interval { lo: self.lo.min(other.lo), hi: self.hi.max(other.hi) }
    }
    fn within(self, range: Interval) -> bool {
        range.lo <= self.lo && self.hi <= range.hi
    }
    fn contains(self, v: i128) -> bool {
        self.lo <= v && v <= self.hi
    }
}

/// What is known of a bool local.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BoolFact {
    True,
    False,
    Unknown,
}

impl BoolFact {
    fn join(self, other: BoolFact) -> BoolFact {
        if self == other { self } else { BoolFact::Unknown }
    }
    fn not(self) -> BoolFact {
        match self {
            BoolFact::True => BoolFact::False,
            BoolFact::False => BoolFact::True,
            BoolFact::Unknown => BoolFact::Unknown,
        }
    }
    fn of(v: bool) -> BoolFact {
        if v { BoolFact::True } else { BoolFact::False }
    }
}

/// The abstract value of one tracked local.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    Int(Interval),
    Bool(BoolFact),
    /// The `(result, overflowed)` pair of a checked operation.
    Checked(Interval, BoolFact),
}

impl Value {
    fn join(self, other: Value) -> Option<Value> {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => Some(Value::Int(a.join(b))),
            (Value::Bool(a), Value::Bool(b)) => Some(Value::Bool(a.join(b))),
            (Value::Checked(a, fa), Value::Checked(b, fb)) => {
                Some(Value::Checked(a.join(b), fa.join(fb)))
            }
            _ => None,
        }
    }
}

/// The integer range of `ty`, for the fixed-width integers up to 64 bits.
fn int_range(ty: Ty) -> Option<Interval> {
    let (signed, bits) = match ty.kind() {
        TyKind::RigidTy(RigidTy::Uint(u)) => (
            false,
            match u {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 | UintTy::Usize => 64,
                UintTy::U128 => return None,
            },
        ),
        TyKind::RigidTy(RigidTy::Int(i)) => (
            true,
            match i {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 | IntTy::Isize => 64,
                IntTy::I128 => return None,
            },
        ),
        _ => return None,
    };
    Some(if signed {
        Interval { lo: -(1i128 << (bits - 1)), hi: (1i128 << (bits - 1)) - 1 }
    } else {
        Interval { lo: 0, hi: (1i128 << bits) - 1 }
    })
}

fn ty_is_signed(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Int(_)))
}

fn int_bits(ty: Ty) -> Option<i128> {
    let range = int_range(ty)?;
    Some(if range.lo < 0 {
        (range.hi + 1).trailing_zeros() as i128 + 1
    } else {
        (range.hi + 1).trailing_zeros() as i128
    })
}

fn is_bool(ty: Ty) -> bool {
    matches!(ty.kind(), TyKind::RigidTy(RigidTy::Bool))
}

/// `(integer, bool)`: the destination type of a checked operation.
fn checked_pair_int(ty: Ty) -> Option<Ty> {
    let TyKind::RigidTy(RigidTy::Tuple(tys)) = ty.kind() else {
        return None;
    };
    match tys.as_slice() {
        [int, flag] if is_bool(*flag) && int_range(*int).is_some() => Some(*int),
        _ => None,
    }
}

/// An integer constant operand of type `ty`, read through the
/// constant-pointer rule (`shared/const_pointer.rs`: relocated bytes are
/// never data).
fn const_int(op: &Operand, ty: Ty) -> Option<i128> {
    use crate::codegen_ay::shared::const_pointer;
    let Operand::Constant(constant) = op else {
        return None;
    };
    let range = int_range(ty)?;
    let value = if ty_is_signed(ty) {
        const_pointer::const_int(&constant.const_)?
    } else {
        i128::try_from(const_pointer::const_uint(&constant.const_)?).ok()?
    };
    range.contains(value).then_some(value)
}

fn const_bool(op: &Operand) -> Option<bool> {
    let Operand::Constant(constant) = op else {
        return None;
    };
    crate::codegen_ay::shared::const_pointer::const_bool(&constant.const_)
}

/// The fixed length of an array type.
fn array_len(ty: Ty) -> Option<i128> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(_, len)) => len.eval_target_usize().ok().map(i128::from),
        _ => None,
    }
}

/// The analysis result for one body.
pub(super) struct BodyIntervals {
    values: HashMap<usize, Value>,
    /// Tracked locals the fixpoint never saw assigned (dead or unreachable
    /// definitions): no read of them can happen on a feasible path, but the
    /// scan does not rely on that and treats them as `Top`.
    top: HashSet<usize>,
    locals_ty: Vec<Ty>,
}

/// How many joins may grow a local's interval before it is widened to `Top`.
const WIDEN_AFTER: usize = 4;
/// Rounds of the fixpoint before every still-changing local is `Top`.
const MAX_ROUNDS: usize = 16;

impl BodyIntervals {
    /// Analyse `body` (its locals' types already resolved by the caller
    /// through `resolve_ty`, which normalises a walked generic body).
    pub(super) fn analyse(body: &Body, resolve_ty: impl Fn(Ty) -> Ty) -> Self {
        let locals_ty: Vec<Ty> = body.locals().iter().map(|decl| resolve_ty(decl.ty)).collect();
        let mut top: HashSet<usize> = (1..=body.arg_locals().len()).collect();
        // Every local written other than by a whole-local Assign, or whose
        // address escapes, is Top.
        for block in &body.blocks {
            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign(place, rvalue) => {
                        if !place.projection.is_empty() {
                            top.insert(place.local);
                        }
                        if let Rvalue::Ref(_, _, borrowed) | Rvalue::AddressOf(_, borrowed) = rvalue
                        {
                            top.insert(borrowed.local);
                        }
                    }
                    StatementKind::SetDiscriminant { place, .. } => {
                        top.insert(place.local);
                    }
                    StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_)) => {}
                    _ => {}
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { destination, .. } => {
                    top.insert(destination.local);
                }
                TerminatorKind::InlineAsm { operands, .. } => {
                    for operand in operands {
                        if let Some(Operand::Copy(place) | Operand::Move(place)) = &operand.in_value
                        {
                            top.insert(place.local);
                        }
                        if let Some(place) = &operand.out_place {
                            top.insert(place.local);
                        }
                    }
                }
                _ => {}
            }
        }
        let mut values: HashMap<usize, Value> = HashMap::new();
        let mut growth: HashMap<usize, usize> = HashMap::new();
        let mut this = BodyIntervals { values: HashMap::new(), top, locals_ty };
        for _round in 0..MAX_ROUNDS {
            let mut changed = false;
            for block in &body.blocks {
                for stmt in &block.statements {
                    let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                        continue;
                    };
                    let local = place.local;
                    if !place.projection.is_empty() || this.top.contains(&local) {
                        continue;
                    }
                    this.values.clone_from(&values);
                    let Some(new) = this.eval_rvalue(rvalue, this.locals_ty[local]) else {
                        // Not a value this module models: Top from here on.
                        this.top.insert(local);
                        values.remove(&local);
                        changed = true;
                        continue;
                    };
                    let joined = match values.get(&local) {
                        None => Some(new),
                        Some(old) => old.join(new),
                    };
                    let Some(joined) = joined else {
                        this.top.insert(local);
                        values.remove(&local);
                        changed = true;
                        continue;
                    };
                    if values.get(&local) != Some(&joined) {
                        let grown = growth.entry(local).or_insert(0);
                        *grown += 1;
                        if *grown > WIDEN_AFTER {
                            this.top.insert(local);
                            values.remove(&local);
                        } else {
                            values.insert(local, joined);
                        }
                        changed = true;
                    }
                }
            }
            if !changed {
                this.values = values;
                return this;
            }
        }
        // No fixpoint in the round budget: every tracked local is Top.
        this.values = HashMap::new();
        this.top = (0..this.locals_ty.len()).collect();
        this
    }

    /// The interval of an integer operand of type `ty` (its type's range
    /// when unknown); `None` for a type this module does not model.
    pub(super) fn operand_interval(&self, op: &Operand, ty: Ty) -> Option<Interval> {
        let range = int_range(ty)?;
        if let Some(v) = const_int(op, ty) {
            return Some(Interval::point(v));
        }
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return Some(range);
        };
        Some(self.place_interval(place).filter(|iv| iv.within(range)).unwrap_or(range))
    }

    fn place_interval(&self, place: &Place) -> Option<Interval> {
        if self.top.contains(&place.local) {
            return None;
        }
        match (self.values.get(&place.local)?, place.projection.as_slice()) {
            (Value::Int(iv), []) => Some(*iv),
            (Value::Checked(iv, _), [ProjectionElem::Field(0, _)]) => Some(*iv),
            _ => None,
        }
    }

    /// What is known of a bool operand.
    pub(super) fn operand_bool(&self, op: &Operand) -> BoolFact {
        if let Some(b) = const_bool(op) {
            return BoolFact::of(b);
        }
        let (Operand::Copy(place) | Operand::Move(place)) = op else {
            return BoolFact::Unknown;
        };
        if self.top.contains(&place.local) {
            return BoolFact::Unknown;
        }
        match (self.values.get(&place.local), place.projection.as_slice()) {
            (Some(Value::Bool(fact)), []) => *fact,
            (Some(Value::Checked(_, fact)), [ProjectionElem::Field(1, _)]) => *fact,
            _ => BoolFact::Unknown,
        }
    }

    fn operand_ty(&self, op: &Operand) -> Option<Ty> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let mut ty = *self.locals_ty.get(place.local)?;
                for elem in &place.projection {
                    ty = match (elem, ty.kind()) {
                        (ProjectionElem::Field(_, field_ty), _) => *field_ty,
                        (
                            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. },
                            TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)),
                        ) => elem,
                        (
                            ProjectionElem::Deref,
                            TyKind::RigidTy(
                                RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _),
                            ),
                        ) => pointee,
                        _ => return None,
                    };
                }
                Some(ty)
            }
            Operand::Constant(constant) => Some(constant.const_.ty()),
            #[allow(unreachable_patterns)]
            _ => None,
        }
    }

    /// The exact interval of `a op b` in unbounded integers, for the ops the
    /// module models, over operands of type `ty`.
    fn binop_exact(&self, op: BinOp, a: &Operand, b: &Operand, ty: Ty) -> Option<Interval> {
        let x = self.operand_interval(a, ty)?;
        let signed = ty_is_signed(ty);
        let b_ty = self.operand_ty(b).unwrap_or(ty);
        let y = self.operand_interval(b, b_ty)?;
        let corners = |f: fn(i128, i128) -> Option<i128>| -> Option<Interval> {
            let c = [f(x.lo, y.lo)?, f(x.lo, y.hi)?, f(x.hi, y.lo)?, f(x.hi, y.hi)?];
            Some(Interval {
                lo: *c.iter().min().expect("four corners"),
                hi: *c.iter().max().expect("four corners"),
            })
        };
        match op {
            BinOp::Add | BinOp::AddUnchecked => corners(i128::checked_add),
            BinOp::Sub | BinOp::SubUnchecked => corners(i128::checked_sub),
            BinOp::Mul | BinOp::MulUnchecked => corners(i128::checked_mul),
            BinOp::Rem if !y.contains(0) => {
                // |a % b| < |b|, and the result takes the dividend's sign.
                let bound = y.lo.unsigned_abs().max(y.hi.unsigned_abs()) as i128 - 1;
                let lo = if x.lo >= 0 { 0 } else { -bound.min(x.lo.unsigned_abs() as i128) };
                let hi = if x.hi <= 0 { 0 } else { bound.min(x.hi) };
                Some(Interval { lo, hi })
            }
            BinOp::Div if !y.contains(0) && (y.lo > 0 || y.hi < 0) => {
                corners(|p, q| p.checked_div(q))
            }
            BinOp::BitAnd if !signed || (x.lo >= 0 || y.lo >= 0) => {
                // Unsigned (or one side non-negative): the result is at most
                // the smaller non-negative side and never negative.
                let hi = match (x.lo >= 0, y.lo >= 0) {
                    (true, true) => x.hi.min(y.hi),
                    (true, false) => x.hi,
                    (false, true) => y.hi,
                    (false, false) => return None,
                };
                Some(Interval { lo: 0, hi })
            }
            BinOp::Shr | BinOp::ShrUnchecked
                if x.lo >= 0 && y.lo >= 0 && int_bits(ty).is_some_and(|bits| y.hi < bits) =>
            {
                Some(Interval { lo: x.lo >> y.hi, hi: x.hi >> y.lo })
            }
            _ => None,
        }
    }

    /// Evaluate `rvalue` assigned to a local of type `dest_ty`; `None` when
    /// it is not a value this module models.
    fn eval_rvalue(&self, rvalue: &Rvalue, dest_ty: Ty) -> Option<Value> {
        if is_bool(dest_ty) {
            return Some(Value::Bool(self.eval_bool(rvalue)));
        }
        if let Some(int_ty) = checked_pair_int(dest_ty) {
            let Rvalue::CheckedBinaryOp(op, a, b) = rvalue else {
                return None;
            };
            let range = int_range(int_ty)?;
            return Some(match self.binop_exact(*op, a, b, int_ty) {
                Some(exact) if exact.within(range) => Value::Checked(exact, BoolFact::False),
                Some(exact) if exact.hi < range.lo || exact.lo > range.hi => {
                    Value::Checked(range, BoolFact::True)
                }
                _ => Value::Checked(range, BoolFact::Unknown),
            });
        }
        let range = int_range(dest_ty)?;
        let value = match rvalue {
            Rvalue::Use(op, ..) => self.operand_interval(op, dest_ty)?,
            Rvalue::Cast(CastKind::IntToInt, op, _) => {
                let src_ty = self.operand_ty(op)?;
                let src = self.operand_interval(op, src_ty)?;
                if src.within(range) { src } else { range }
            }
            Rvalue::BinaryOp(op, a, b) => match self.binop_exact(*op, a, b, dest_ty) {
                Some(exact) if exact.within(range) => exact,
                _ => range,
            },
            Rvalue::Len(place) => {
                let place_ty = self.operand_ty(&Operand::Copy(place.clone()))?;
                Interval::point(array_len(place_ty)?)
            }
            _ => range,
        };
        Some(Value::Int(value))
    }

    fn eval_bool(&self, rvalue: &Rvalue) -> BoolFact {
        match rvalue {
            Rvalue::Use(op, ..) => self.operand_bool(op),
            Rvalue::UnaryOp(UnOp::Not, op) => self.operand_bool(op).not(),
            Rvalue::BinaryOp(
                op @ (BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne),
                a,
                b,
            ) => {
                let Some(ty) = self.operand_ty(a) else {
                    return BoolFact::Unknown;
                };
                let (Some(x), Some(y)) = (
                    self.operand_interval(a, ty),
                    self.operand_interval(b, self.operand_ty(b).unwrap_or(ty)),
                ) else {
                    return BoolFact::Unknown;
                };
                compare(*op, x, y)
            }
            _ => BoolFact::Unknown,
        }
    }

    /// Is the `Assert` on `cond` with `expected` provably holding?
    pub(super) fn assert_holds(&self, cond: &Operand, expected: bool) -> bool {
        self.operand_bool(cond) == BoolFact::of(expected)
    }

    /// Is every obligation site the obligation walk sights in `stmt` provably
    /// discharged? `false` for any site this module does not prove.
    pub(super) fn statement_obligations_discharged(&self, stmt: &Statement) -> bool {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.place_discharged(place) && self.rvalue_discharged(rvalue)
            }
            StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op)) => {
                self.operand_bool(op) == BoolFact::True
            }
            _ => false,
        }
    }

    fn place_discharged(&self, place: &Place) -> bool {
        let Some(mut ty) = self.locals_ty.get(place.local).copied() else {
            return false;
        };
        for elem in &place.projection {
            match elem {
                ProjectionElem::Deref => match ty.kind() {
                    // A reference is safe by construction; a raw pointer's
                    // access is the memory-safety site, never proved here.
                    TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => ty = pointee,
                    _ => return false,
                },
                ProjectionElem::Index(idx) => {
                    let (Some(len), TyKind::RigidTy(RigidTy::Array(elem, _))) =
                        (array_len(ty), ty.kind())
                    else {
                        return false;
                    };
                    let Some(idx_ty) = self.locals_ty.get(*idx).copied() else {
                        return false;
                    };
                    let Some(iv) = self.operand_interval(&Operand::Copy(Place::from(*idx)), idx_ty)
                    else {
                        return false;
                    };
                    if !(iv.lo >= 0 && iv.hi < len) {
                        return false;
                    }
                    ty = elem;
                }
                ProjectionElem::Field(_, field_ty) => ty = *field_ty,
                ProjectionElem::ConstantIndex { .. } | ProjectionElem::Subslice { .. } => {
                    match ty.kind() {
                        TyKind::RigidTy(RigidTy::Array(elem, _) | RigidTy::Slice(elem)) => {
                            ty = elem;
                        }
                        _ => return false,
                    }
                }
                ProjectionElem::Downcast(_) | ProjectionElem::OpaqueCast(_) => {}
                #[allow(unreachable_patterns)]
                _ => return false,
            }
        }
        true
    }

    fn operand_discharged(&self, op: &Operand) -> bool {
        match op {
            Operand::Copy(place) | Operand::Move(place) => self.place_discharged(place),
            _ => true,
        }
    }

    fn rvalue_discharged(&self, rvalue: &Rvalue) -> bool {
        match rvalue {
            Rvalue::Use(op, ..) | Rvalue::Repeat(op, _) | Rvalue::Cast(_, op, _) => {
                self.operand_discharged(op)
            }
            Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) => self.place_discharged(place),
            Rvalue::Len(place) | Rvalue::Discriminant(place) | Rvalue::CopyForDeref(place) => {
                self.place_discharged(place)
            }
            Rvalue::CheckedBinaryOp(_, a, b) => {
                self.operand_discharged(a) && self.operand_discharged(b)
            }
            Rvalue::BinaryOp(op, a, b) => {
                self.operand_discharged(a)
                    && self.operand_discharged(b)
                    && self.binop_discharged(*op, a, b)
            }
            Rvalue::UnaryOp(op, a) => {
                self.operand_discharged(a)
                    && match op {
                        UnOp::Neg => match self.operand_ty(a) {
                            Some(ty) if ty_is_signed(ty) => self
                                .operand_interval(a, ty)
                                .zip(int_range(ty))
                                .is_some_and(|(iv, range)| iv.lo > range.lo),
                            _ => true,
                        },
                        _ => true,
                    }
            }
            Rvalue::Aggregate(_, operands) => operands.iter().all(|op| self.operand_discharged(op)),
            // Every other rvalue is Free or Unknown to the obligation walk,
            // never a sighting; nothing to discharge.
            _ => true,
        }
    }

    fn binop_discharged(&self, op: BinOp, a: &Operand, b: &Operand) -> bool {
        let Some(ty) = self.operand_ty(a) else {
            return false;
        };
        match op {
            BinOp::AddUnchecked | BinOp::SubUnchecked | BinOp::MulUnchecked => int_range(ty)
                .is_some_and(|range| {
                    self.binop_exact(op, a, b, ty).is_some_and(|exact| exact.within(range))
                }),
            BinOp::ShlUnchecked | BinOp::ShrUnchecked => {
                let (Some(bits), Some(b_ty)) = (int_bits(ty), self.operand_ty(b)) else {
                    return false;
                };
                self.operand_interval(b, b_ty).is_some_and(|d| d.lo >= 0 && d.hi < bits)
            }
            BinOp::Div | BinOp::Rem => {
                let (Some(range), Some(b_ty)) = (int_range(ty), self.operand_ty(b)) else {
                    return false;
                };
                let (Some(x), Some(y)) =
                    (self.operand_interval(a, ty), self.operand_interval(b, b_ty))
                else {
                    return false;
                };
                !y.contains(0) && !(ty_is_signed(ty) && y.contains(-1) && x.contains(range.lo))
            }
            // Free to the obligation walk.
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitOr
            | BinOp::BitXor => true,
            // Comparisons are sightings only between `dyn` pointers; an
            // integer comparison is free.
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Cmp => {
                int_range(ty).is_some() || is_bool(ty)
            }
            _ => false,
        }
    }
}

fn compare(op: BinOp, x: Interval, y: Interval) -> BoolFact {
    let (always, never) = match op {
        BinOp::Lt => (x.hi < y.lo, x.lo >= y.hi),
        BinOp::Le => (x.hi <= y.lo, x.lo > y.hi),
        BinOp::Gt => (x.lo > y.hi, x.hi <= y.lo),
        BinOp::Ge => (x.lo >= y.hi, x.hi < y.lo),
        BinOp::Eq => (x.lo == x.hi && y.lo == y.hi && x.lo == y.lo, x.hi < y.lo || y.hi < x.lo),
        BinOp::Ne => (x.hi < y.lo || y.hi < x.lo, x.lo == x.hi && y.lo == y.hi && x.lo == y.lo),
        _ => (false, false),
    };
    if always {
        BoolFact::True
    } else if never {
        BoolFact::False
    } else {
        BoolFact::Unknown
    }
}
