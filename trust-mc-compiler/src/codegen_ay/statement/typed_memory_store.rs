// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A whole-value store whose Rust type is known replaces only its object's
//! bytes.
//!
//! A datatype / array / Int value has no single bitvector image, so
//! `store_memory_bytes` keeps it for whole-value readers and, since it cannot
//! tell which bytes the object covers, replaces ALL of byte memory with a fresh
//! array: a later byte read must not see a stale image of the object (a
//! static's pinned initializer, a stack local's materialized bytes). That is
//! sound but coarse — every byte read after the store becomes free, and
//! kani/SizeAndAlignOfDst/main_assert.rs went from a solver timeout to a forced
//! FAILED.

use ay_bindings::Expr;
use rustc_public::ty::Ty;

use super::StatementCodegen;
use crate::kani_middle::abi::LayoutOf;

/// Largest object whose bytes are havocked one by one; a larger object keeps the
/// whole-memory lane.
const MAX_OBJECT_HAVOC_BYTES: usize = 256;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Store a program value of Rust type `ty` at `addr` in byte memory, on
    /// every path.
    ///
    /// A bitvector value goes through `store_memory_bytes`. A whole-value
    /// (datatype / array / Int) value is kept for whole-value readers, and its
    /// OBJECT's bytes — only those — are replaced by fresh bytes and then
    /// overwritten with every field the layout determines
    /// (`store_payload_bytes`, the `Box::new` payload layout walk). Bytes the
    /// layout does not determine (an enum's variants, a field whose encoding
    /// differs) stay fresh, recorded as a sound approximation. A zero-sized
    /// object touches no bytes; an unsized type or an oversized object keeps
    /// the whole-memory lane.
    ///
    /// Callers use this only where the store executes on every path; a store on
    /// one path goes through `store_memory_bytes_on_path`.
    pub(super) fn store_typed_value_to_memory(&mut self, addr: Expr, value: Expr, ty: Ty) {
        if self.ctx.has_native_box_allocations() && Self::ty_carries_a_pointer_value(ty) {
            self.ctx.unsupported_with_fallback(
                "BoxPointerStore",
                "typed pointer storage has no physical byte/provenance shadow",
            );
        }
        let sort = value.sort();
        if !(sort.is_int() || sort.is_array() || sort.is_datatype()) {
            self.ctx.store_memory_bytes(addr, value);
            return;
        }
        let Some(size) = LayoutOf::new(ty).size_of() else {
            self.ctx.store_memory_bytes(addr, value);
            return;
        };
        if size == 0 {
            // A zero-sized object has no bytes a later read could see stale,
            // so byte memory keeps its value: the whole-memory lane taints every
            // counterexample (`&()` taken twice left
            // offset_from_unsigned_ub_precondition_dual.rs::sp_unit_distinct_locals
            // with an uncertified expected panic).
            self.ctx.track_symbolic_store(addr, value);
            return;
        }
        if size > MAX_OBJECT_HAVOC_BYTES {
            self.ctx.store_memory_bytes(addr, value);
            return;
        }
        self.ctx.track_symbolic_store(addr.clone(), value.clone());
        self.ctx.havoc_memory_range(addr.clone(), size as u64);
        if self.store_payload_bytes(ty, &value, &addr, 0) {
            self.ctx.mark_symbolic_store_byte_image(addr);
        } else {
            self.ctx.bmc_sound_havoc("typed_store_bytes_undetermined");
        }
    }
}
