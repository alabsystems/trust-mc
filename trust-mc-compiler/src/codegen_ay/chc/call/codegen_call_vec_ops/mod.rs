// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec lifecycle, capacity, and query operation helpers.
//!
//! Split from a single flat file into a facade directory per #4192.
//! Previous flat file contained all Vec operation families (constructors,
//! capacity updates, resize semantics) plus shared helper API.
//!
//! Layout:
//! - `shared.rs`: cross-module helper structs/functions used by other Vec/iterator modules
//! - `constructors.rs`: VecNew, VecWithCapacity, VecFromElem
//! - `from_slice.rs`: VecFromSlice (slice::to_vec)
//! - `capacity.rs`: VecReserve, VecReserveExact, VecShrinkToFit
//! - `resize.rs`: VecResize and the resize-array quantifier helper

mod capacity;
mod constructors;
mod from_slice;
mod resize;
mod shared;

// Re-export the external surface so callers keep using
// `super::codegen_call_vec_ops::{ProjectedVecState, VecOpNewContext, ...}`.
pub(in crate::codegen_ay::chc) use constructors::VecOpNewContext;
pub(in crate::codegen_ay::chc) use resize::quantified_resize_growth_array;
pub(in crate::codegen_ay::chc) use shared::ProjectedVecState;
pub(crate) use shared::coerce_array_element;
