// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Formal proofs for HEAP_STRIDE isolation property (#1440).
//!
//! NOTE: This module requires trust_mc's Kani-compatible proof mode. Run with:
//! ```bash
//! cargo trust_mc --manifest-path proofs/Cargo.toml
//! ```
//!
//! This module contains trust_mc compatibility proof harnesses that formally verify:
//! 1. Non-overlapping: Distinct allocation IDs produce non-overlapping address ranges
//! 2. Null safety: ID 0 is reserved, first allocation starts at HEAP_STRIDE
//! 3. Alignment: All allocation bases are aligned to HEAP_STRIDE
//!
//! # Running Proofs
//!
//! ```bash
//! # Run all heap stride proofs
//! cargo trust_mc --manifest-path proofs/Cargo.toml
//!
//! # Run specific proof
//! cargo trust_mc --harness proof_allocation_non_overlapping --manifest-path proofs/Cargo.toml
//! ```
//!
//! # Property Specification
//!
//! The heap model uses a simple addressing scheme:
//! - `HEAP_STRIDE = 0x100000` (1MB)
//! - Allocation ID `n` gets base address `n * HEAP_STRIDE`
//! - ID 0 is reserved for null pointer representation
//! - First real allocation uses ID 1, address 0x100000
//!
//! ## Key Invariants
//!
//! 1. **Disjointness**: For any two distinct allocation IDs `i` and `j`:
//!    `[i * HEAP_STRIDE, i * HEAP_STRIDE + size_i) ∩
//!     [j * HEAP_STRIDE, j * HEAP_STRIDE + size_j) = ∅`
//!    when both sizes are less than HEAP_STRIDE.
//!
//! 2. **Non-null**: For any allocation ID `n > 0`:
//!    `n * HEAP_STRIDE > 0`
//!
//! 3. **Stride alignment**: For any allocation ID `n`:
//!    `(n * HEAP_STRIDE) % HEAP_STRIDE == 0`

/// Heap stride constant (1MB = 0x100000 bytes).
/// Matches `HEAP_STRIDE` in `trust_mc-compiler/src/codegen_ay/context/heap.rs`.
const HEAP_STRIDE: u64 = 0x100000;

/// Maximum allocation ID we can safely support without overflow.
/// Ensures `id * HEAP_STRIDE + size` never overflows for `size < HEAP_STRIDE`.
const MAX_ALLOC_ID: u64 = (u64::MAX / HEAP_STRIDE) - 1;

/// Proves that distinct allocation IDs produce non-overlapping address ranges.
///
/// For any two distinct allocation IDs i and j, and any allocation sizes
/// less than HEAP_STRIDE, the resulting memory ranges do not overlap.
#[kani::proof]
#[kani::unwind(2)]
fn proof_allocation_non_overlapping() {
    let id_i: u64 = kani::any();
    let id_j: u64 = kani::any();
    let size_i: u64 = kani::any();
    let size_j: u64 = kani::any();

    // Constrain to valid allocation IDs (non-zero, within bounds)
    kani::assume(id_i > 0 && id_i < MAX_ALLOC_ID);
    kani::assume(id_j > 0 && id_j < MAX_ALLOC_ID);
    kani::assume(id_i != id_j); // distinct allocations

    // Constrain sizes to be within HEAP_STRIDE (practical allocation sizes)
    kani::assume(size_i > 0 && size_i < HEAP_STRIDE);
    kani::assume(size_j > 0 && size_j < HEAP_STRIDE);

    // Compute base addresses
    let base_i = id_i * HEAP_STRIDE;
    let base_j = id_j * HEAP_STRIDE;

    // Compute end addresses (exclusive)
    let end_i = base_i + size_i;
    let end_j = base_j + size_j;

    // Prove non-overlapping: either range i ends before j starts, or j ends before i starts
    // [base_i, end_i) and [base_j, end_j) don't intersect
    kani::assert(
        end_i <= base_j || end_j <= base_i,
        "Allocations with distinct IDs must not overlap",
    );
}

/// Proves that base + size never overflows under the heap stride bounds.
#[kani::proof]
#[kani::unwind(2)]
fn proof_allocation_end_no_overflow() {
    let id: u64 = kani::any();
    let size: u64 = kani::any();

    kani::assume(id > 0 && id < MAX_ALLOC_ID);
    kani::assume(size < HEAP_STRIDE);

    let base = id * HEAP_STRIDE;

    // base + size stays within u64 bounds under MAX_ALLOC_ID/HEAP_STRIDE constraints.
    kani::assert(base.checked_add(size).is_some(), "heap allocation end address must not overflow");
}

/// Proves that allocation base addresses are never zero (null safety).
///
/// ID 0 is reserved for null pointer, so first allocation (ID 1) starts at HEAP_STRIDE.
#[kani::proof]
#[kani::unwind(2)]
fn proof_allocation_non_null() {
    let id: u64 = kani::any();

    // Valid allocation IDs are non-zero
    kani::assume(id > 0 && id < MAX_ALLOC_ID);

    let base_addr = id * HEAP_STRIDE;

    // Base address must be non-zero
    kani::assert(base_addr > 0, "Allocation base address must be non-null");
}

/// Proves that allocation base addresses are aligned to HEAP_STRIDE.
#[kani::proof]
#[kani::unwind(2)]
fn proof_allocation_stride_aligned() {
    let id: u64 = kani::any();

    // Any allocation ID in valid range
    kani::assume(id < MAX_ALLOC_ID);

    let base_addr = id * HEAP_STRIDE;

    // Base address must be aligned to stride
    kani::assert(base_addr % HEAP_STRIDE == 0, "Allocation base must be stride-aligned");
}

/// Proves that the object ID can be recovered from a pointer within an allocation.
///
/// Given a pointer `ptr = id * HEAP_STRIDE + offset` where `offset < HEAP_STRIDE`,
/// we can recover `id` via `ptr / HEAP_STRIDE`.
#[kani::proof]
#[kani::unwind(2)]
fn proof_object_id_recovery() {
    let id: u64 = kani::any();
    let offset: u64 = kani::any();

    // Valid allocation ID
    kani::assume(id > 0 && id < MAX_ALLOC_ID);
    // Offset within stride bounds
    kani::assume(offset < HEAP_STRIDE);

    // Construct pointer
    let ptr = id * HEAP_STRIDE + offset;

    // Recover object ID
    let recovered_id = ptr / HEAP_STRIDE;

    kani::assert(recovered_id == id, "Object ID must be recoverable from pointer");
}

/// Proves that the offset within an allocation can be recovered from a pointer.
///
/// Given a pointer `ptr = id * HEAP_STRIDE + offset` where `offset < HEAP_STRIDE`,
/// we can recover `offset` via `ptr % HEAP_STRIDE`.
#[kani::proof]
#[kani::unwind(2)]
fn proof_offset_recovery() {
    let id: u64 = kani::any();
    let offset: u64 = kani::any();

    // Valid allocation ID
    kani::assume(id > 0 && id < MAX_ALLOC_ID);
    // Offset within stride bounds
    kani::assume(offset < HEAP_STRIDE);

    // Construct pointer
    let ptr = id * HEAP_STRIDE + offset;

    // Recover offset
    let recovered_offset = ptr % HEAP_STRIDE;

    kani::assert(recovered_offset == offset, "Offset must be recoverable from pointer");
}

/// Proves that sequential allocation IDs produce increasing base addresses.
#[kani::proof]
#[kani::unwind(2)]
fn proof_monotonic_allocation_addresses() {
    let id_a: u64 = kani::any();
    let id_b: u64 = kani::any();

    // Valid allocation IDs with id_a < id_b
    kani::assume(id_a > 0 && id_a < MAX_ALLOC_ID);
    kani::assume(id_b > 0 && id_b < MAX_ALLOC_ID);
    kani::assume(id_a < id_b);

    let base_a = id_a * HEAP_STRIDE;
    let base_b = id_b * HEAP_STRIDE;

    // Earlier allocations have lower addresses
    kani::assert(base_a < base_b, "Monotonic ID implies monotonic base address");
}

/// Proves that two pointers are in the same allocation iff they share object ID.
#[kani::proof]
#[kani::unwind(2)]
fn proof_same_allocation_predicate() {
    let id_a: u64 = kani::any();
    let id_b: u64 = kani::any();
    let offset_a: u64 = kani::any();
    let offset_b: u64 = kani::any();

    // Valid allocation IDs
    kani::assume(id_a > 0 && id_a < MAX_ALLOC_ID);
    kani::assume(id_b > 0 && id_b < MAX_ALLOC_ID);
    // Valid offsets
    kani::assume(offset_a < HEAP_STRIDE);
    kani::assume(offset_b < HEAP_STRIDE);

    let ptr_a = id_a * HEAP_STRIDE + offset_a;
    let ptr_b = id_b * HEAP_STRIDE + offset_b;

    // Compute object IDs
    let obj_id_a = ptr_a / HEAP_STRIDE;
    let obj_id_b = ptr_b / HEAP_STRIDE;

    // same_allocation(ptr_a, ptr_b) iff obj_id_a == obj_id_b iff id_a == id_b
    kani::assert(
        (obj_id_a == obj_id_b) == (id_a == id_b),
        "same_allocation must correspond to ID equality",
    );
}
