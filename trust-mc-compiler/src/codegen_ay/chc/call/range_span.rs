// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The exact element count of a `Range<T>` / `RangeInclusive<T>`, for the
//! models that read it whole (`Vec::extend` from a range, and the trip bound
//! of its loop under a declared unwind).
//!
//! The count is `Step::steps_between(start, end)` in `T`'s own order (frozen
//! nightly `core/src/iter/range.rs`): `end - start` when `start <= end`, with
//! the 0x800 surrogate code points `0xD800..=0xDFFF` skipped for `char`, and
//! one more element for a `RangeInclusive` that is not exhausted. The models
//! used to compare zero-extended bounds unsigned, so `-2i8..3` yielded no
//! element, `2i8..-1` yielded 253, and `'\u{D7FF}'..'\u{E001}'` 2050 instead
//! of 2 (walker fail-closed repair round 5, `range_extend_kinds_dual.rs`).
//!
//! Signed bounds are sign-extended and compared signed, unsigned and `char`
//! bounds are zero-extended and compared unsigned, and every count is taken
//! at the pointer width, or at 128 bits for a 128-bit `T`, where it is exact:
//! a count past `usize::MAX` is reported (`too_long`), never wrapped.

use ay_bindings::{Expr, ExprValue};
use num_bigint::BigInt;
use rustc_public::CrateDef;
use rustc_public::ty::{GenericArgKind, IntTy, RigidTy, Ty, TyKind, UintTy};

use crate::codegen_ay::types::POINTER_WIDTH;

/// The first surrogate code point.
const SURROGATE_START: u64 = 0xD800;
/// The first scalar value past the surrogates.
const SURROGATE_END: u64 = 0xE000;
/// The surrogate code points `Step for char` steps over.
const SURROGATE_COUNT: u64 = SURROGATE_END - SURROGATE_START;

/// What a range steps over: a signed or unsigned integer of the given
/// width, or `char`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum RangeStep {
    Signed(u32),
    Unsigned(u32),
    Char,
}

impl RangeStep {
    /// The step type of a `core::ops::Range<T>` or `RangeInclusive<T>`, and
    /// whether it is the inclusive one. `None` for any other type, or a `T`
    /// that is not an integer or `char`.
    pub(in crate::codegen_ay::chc) fn of_range_ty(ty: Ty) -> Option<(Self, bool)> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else {
            return None;
        };
        let name = def.name();
        let last = name.rsplit("::").next().unwrap_or(&name);
        let inclusive = match last {
            "Range" if name.contains("ops") => false,
            "RangeInclusive" if name.contains("ops") => true,
            _ => return None,
        };
        let elem = args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(ty) => Some(*ty),
            _ => None,
        })?;
        Some((Self::of_elem_ty(elem)?, inclusive))
    }

    /// The step kind of an integer or `char` type.
    pub(in crate::codegen_ay::chc) fn of_elem_ty(ty: Ty) -> Option<Self> {
        Some(match ty.kind() {
            TyKind::RigidTy(RigidTy::Int(int)) => Self::Signed(match int {
                IntTy::I8 => 8,
                IntTy::I16 => 16,
                IntTy::I32 => 32,
                IntTy::I64 => 64,
                IntTy::I128 => 128,
                IntTy::Isize => POINTER_WIDTH,
            }),
            TyKind::RigidTy(RigidTy::Uint(uint)) => Self::Unsigned(match uint {
                UintTy::U8 => 8,
                UintTy::U16 => 16,
                UintTy::U32 => 32,
                UintTy::U64 => 64,
                UintTy::U128 => 128,
                UintTy::Usize => POINTER_WIDTH,
            }),
            TyKind::RigidTy(RigidTy::Char) => Self::Char,
            _ => return None,
        })
    }

    /// The bit width of one element.
    pub(in crate::codegen_ay::chc) fn width(self) -> u32 {
        match self {
            Self::Signed(width) | Self::Unsigned(width) => width,
            Self::Char => 32,
        }
    }

    fn signed(self) -> bool {
        matches!(self, Self::Signed(_))
    }

    /// The width the span is computed at: the pointer width, or 128 for a
    /// 128-bit element, wide enough for every step count to be exact.
    fn wide(self) -> u32 {
        self.width().max(POINTER_WIDTH)
    }

    /// `value` (an element's bit pattern) as a number in the element's order.
    fn number(self, value: &BigInt) -> BigInt {
        let width = self.width();
        if self.signed() && *value >= (BigInt::from(1u8) << (width - 1)) {
            value - (BigInt::from(1u8) << width)
        } else {
            value.clone()
        }
    }
}

/// `start` against `end` in the step type's order, at [`RangeStep::wide`] bits.
pub(in crate::codegen_ay::chc) struct RangeSpan {
    /// `start <= end`.
    pub le: Expr,
    /// `start < end`.
    pub lt: Expr,
    /// `Step::steps_between(start, end)`, meaningful when `start <= end`.
    pub steps: Expr,
    wide: u32,
}

/// What `Vec::extend` adds for a range.
pub(in crate::codegen_ay::chc) struct RangeLen {
    /// The element count, at the pointer width (wrapped when `too_long`).
    pub len: Expr,
    /// The count exceeds `usize::MAX`: `size_hint` has no upper bound and
    /// `extend` panics with "capacity overflow".
    pub too_long: Expr,
}

/// The span of `start..end` over `step`, or `None` when a bound is not a
/// bitvector of the element's width.
pub(in crate::codegen_ay::chc) fn range_span(
    step: RangeStep,
    start: &Expr,
    end: &Expr,
) -> Option<RangeSpan> {
    let wide = step.wide();
    let s = widen(start, step, wide)?;
    let e = widen(end, step, wide)?;
    let (le, lt) = if step.signed() {
        (s.clone().bvsle(e.clone()), s.clone().bvslt(e.clone()))
    } else {
        (s.clone().bvule(e.clone()), s.clone().bvult(e.clone()))
    };
    let diff = e.clone().bvsub(s.clone());
    let steps = if step == RangeStep::Char {
        let gap = s
            .bvult(Expr::bitvec_const(SURROGATE_START, wide))
            .and(e.bvuge(Expr::bitvec_const(SURROGATE_END, wide)));
        Expr::ite(gap, diff.clone().bvsub(Expr::bitvec_const(SURROGATE_COUNT, wide)), diff)
    } else {
        diff
    };
    Some(RangeSpan { le, lt, steps, wide })
}

impl RangeSpan {
    /// The elements the range yields: `steps` when `start < end` for a
    /// `Range`, `steps + 1` when `start <= end` and not `exhausted` for a
    /// `RangeInclusive`, else none.
    pub(in crate::codegen_ay::chc) fn len(&self, inclusive: bool, exhausted: Expr) -> RangeLen {
        let w = self.wide;
        let zero = Expr::bitvec_const(0u64, w);
        let usize_max = Expr::bitvec_const(u64::MAX, w);
        let (nonempty, count, too_long) = if inclusive {
            let nonempty = exhausted.not().and(self.le.clone());
            let count = self.steps.clone().bvadd(Expr::bitvec_const(1u64, w));
            // `steps + 1 > usize::MAX` exactly when `steps >= usize::MAX`.
            let too_long = nonempty.clone().and(self.steps.clone().bvuge(usize_max));
            (nonempty, count, too_long)
        } else {
            let nonempty = self.lt.clone();
            let too_long = if w > POINTER_WIDTH {
                nonempty.clone().and(self.steps.clone().bvugt(usize_max))
            } else {
                Expr::bool_const(false)
            };
            (nonempty, self.steps.clone(), too_long)
        };
        let len = Expr::ite(nonempty, count, zero);
        let len = if w > POINTER_WIDTH { len.extract(POINTER_WIDTH - 1, 0) } else { len };
        RangeLen { len, too_long }
    }

    /// The back edges `Vec::extend`'s `for_each` takes over the range: one
    /// per step, for both kinds (a `RangeInclusive`'s fold yields its last
    /// element after its loop; measured on Kani in `probes/g3_extend_grid.rs`),
    /// none when the range is empty, saturated at `usize::MAX`. An upper
    /// bound: a `RangeInclusive`'s exhaustion is not read.
    pub(in crate::codegen_ay::chc) fn loop_trips(&self, inclusive: bool) -> Expr {
        let w = self.wide;
        let nonempty = if inclusive { self.le.clone() } else { self.lt.clone() };
        let trips = Expr::ite(nonempty, self.steps.clone(), Expr::bitvec_const(0u64, w));
        if w > POINTER_WIDTH {
            let usize_max = Expr::bitvec_const(u64::MAX, w);
            Expr::ite(
                trips.clone().bvugt(usize_max),
                Expr::bitvec_const(u64::MAX, POINTER_WIDTH),
                trips.extract(POINTER_WIDTH - 1, 0),
            )
        } else {
            trips
        }
    }
}

/// `value` extended to `wide` bits in the step type's signedness, or `None`
/// when it is not a bitvector of the element's width.
fn widen(value: &Expr, step: RangeStep, wide: u32) -> Option<Expr> {
    let width = value.sort().bitvec_width()?;
    if width != step.width() || width > wide {
        return None;
    }
    Some(if width == wide {
        value.clone()
    } else if step.signed() {
        value.clone().sign_extend(wide - width)
    } else {
        value.clone().zero_extend(wide - width)
    })
}

/// The exact element count of a range with constant bounds (`exhausted` for
/// a `RangeInclusive` known to be exhausted), unbounded: the folded form of
/// [`RangeSpan::len`]. `None` when a bound is not a constant.
pub(in crate::codegen_ay::chc) fn fold_range_count(
    step: RangeStep,
    start: &Expr,
    end: &Expr,
    inclusive: bool,
    exhausted: bool,
) -> Option<BigInt> {
    let (ExprValue::BitVecConst { value: sv, .. }, ExprValue::BitVecConst { value: ev, .. }) =
        (start.value(), end.value())
    else {
        return None;
    };
    Some(range_count(step, &step.number(sv), &step.number(ev), inclusive, exhausted))
}

/// The element count of `start..end` (`start..=end` when `inclusive`) over
/// `step`, for bounds given as numbers in the element's order.
pub(in crate::codegen_ay::chc) fn range_count(
    step: RangeStep,
    start: &BigInt,
    end: &BigInt,
    inclusive: bool,
    exhausted: bool,
) -> BigInt {
    let zero = BigInt::from(0u8);
    if start > end || (inclusive && exhausted) || (!inclusive && start == end) {
        return zero;
    }
    let mut steps = end - start;
    if step == RangeStep::Char
        && *start < BigInt::from(SURROGATE_START)
        && *end >= BigInt::from(SURROGATE_END)
    {
        steps -= BigInt::from(SURROGATE_COUNT);
    }
    if inclusive { steps + 1 } else { steps }
}

#[cfg(test)]
#[path = "range_span_tests.rs"]
mod tests;
