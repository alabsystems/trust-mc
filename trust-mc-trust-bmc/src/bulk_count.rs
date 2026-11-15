// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The byte count of a trust-ir WS3.20 bulk instruction (`MemCopy`, `MemSet`)
//! and the Booleans both lanes build over it.
//!
//! Every condition a bulk instruction needs is ONE comparison of its byte count
//! with a constant that comes from a type's size (an object's, a cell's, the
//! distance between two offsets), so the encoding never depends on the count's
//! value. When the count is itself a constant every comparison folds here, so a
//! constant count emits no condition at all.

use ay_bindings::{Expr, ExprValue};

/// A Boolean over one bulk instruction's byte count, folded when that count is
/// a constant.
#[derive(Debug, Clone)]
pub(crate) enum Truth {
    Known(bool),
    When(Expr),
}

impl Truth {
    pub(crate) fn expr(&self) -> Expr {
        match self {
            Self::Known(true) => Expr::true_(),
            Self::Known(false) => Expr::false_(),
            Self::When(expr) => expr.clone(),
        }
    }

    pub(crate) fn is_false(&self) -> bool {
        matches!(self, Self::Known(false))
    }

    pub(crate) fn is_true(&self) -> bool {
        matches!(self, Self::Known(true))
    }

    pub(crate) fn negate(self) -> Self {
        match self {
            Self::Known(value) => Self::Known(!value),
            Self::When(expr) => Self::When(expr.not()),
        }
    }

    pub(crate) fn and(self, other: Self) -> Self {
        match (self, other) {
            (Self::Known(false), _) | (_, Self::Known(false)) => Self::Known(false),
            (Self::Known(true), other) | (other, Self::Known(true)) => other,
            (Self::When(left), Self::When(right)) => Self::When(left.and(right)),
        }
    }

    pub(crate) fn or(self, other: Self) -> Self {
        match (self, other) {
            (Self::Known(true), _) | (_, Self::Known(true)) => Self::Known(true),
            (Self::Known(false), other) | (other, Self::Known(false)) => other,
            (Self::When(left), Self::When(right)) => Self::When(left.or(right)),
        }
    }

    /// `ite(self, then, otherwise)` over terms of one sort, folded when known.
    pub(crate) fn select(&self, then: Expr, otherwise: Expr) -> Option<Expr> {
        match self {
            Self::Known(true) => Some(then),
            Self::Known(false) => Some(otherwise),
            Self::When(cond) => Expr::try_ite(cond.clone(), then, otherwise).ok(),
        }
    }
}

/// A bulk instruction's byte count: a 64-bit term, and its value when constant.
#[derive(Debug, Clone)]
pub(crate) struct ByteCount {
    expr: Expr,
    constant: Option<u64>,
}

impl ByteCount {
    /// `None` unless `expr` is a 64-bit vector (`usize`, or `u64` in a module
    /// with no target), the only sort trust-ir gives a byte count.
    pub(crate) fn new(expr: Expr) -> Option<Self> {
        if expr.sort().bitvec_width() != Some(64) {
            return None;
        }
        let constant = match expr.value() {
            ExprValue::BitVecConst { value, .. } => value.to_string().parse::<u64>().ok(),
            _ => None,
        };
        Some(Self { expr, constant })
    }

    /// `bytes == size`.
    pub(crate) fn equals(&self, size: u64) -> Truth {
        match self.constant {
            Some(count) => Truth::Known(count == size),
            None => Truth::When(self.expr.clone().eq(Expr::bitvec_const(size, 64))),
        }
    }

    /// `bytes >u bound`.
    pub(crate) fn exceeds(&self, bound: u64) -> Truth {
        match self.constant {
            Some(count) => Truth::Known(count > bound),
            None => Truth::When(self.expr.clone().bvugt(Expr::bitvec_const(bound, 64))),
        }
    }
}
