// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SliceOp — semantic classification for slice operations.
//!
//! Maps StubKind slice variants to a unified operation descriptor used by
//! both CHC and statement backends to enforce parity.
//! Part of #408: dispatch-layer slice parity.

use crate::codegen_ay::stubs::StubKind;

/// Semantic slice operation kind, abstracted from StubKind.
///
/// Currently used by tests; will be consumed by both backends for parity enforcement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(any(not(test), not(feature = "compiler-corpus-tests")), allow(dead_code))]
pub(in crate::codegen_ay::chc) enum SliceOp {
    /// Equality comparison: `SlicePartialEq::equal(&[T], &[T]) -> bool`
    Eq,
    /// Indexed access: `SliceIndex::index(&[T], usize) -> &T` or `Index::index`
    Index,
}

#[cfg_attr(any(not(test), not(feature = "compiler-corpus-tests")), allow(dead_code))]
impl SliceOp {
    /// Map a StubKind to its SliceOp, if it is a slice operation.
    pub(in crate::codegen_ay::chc) fn from_stub(stub: StubKind) -> Option<Self> {
        match stub {
            StubKind::SlicePartialEqEqual => Some(Self::Eq),
            StubKind::SliceIndexIndex | StubKind::IndexIndex => Some(Self::Index),
            _ => None, // internal enum: StubKind (partial dispatch)
        }
    }

    /// Whether this operation returns a bool result.
    pub(in crate::codegen_ay::chc) const fn returns_bool(self) -> bool {
        matches!(self, Self::Eq)
    }

    /// Whether this operation returns a reference to an element.
    pub(in crate::codegen_ay::chc) const fn returns_ref(self) -> bool {
        matches!(self, Self::Index)
    }

    /// Whether this operation may cause an out-of-bounds violation.
    pub(in crate::codegen_ay::chc) const fn may_oob(self) -> bool {
        matches!(self, Self::Index)
    }
}
