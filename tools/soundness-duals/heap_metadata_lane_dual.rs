// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- a site that writes ONE heap metadata lane must not havoc
//! the other, and a call's metadata update must reach the call's own rule.
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, Kani 0.67.0, measured
//! 2026-09-25; see the manifest entry):
//!   safe_box_then_null_deref          -> SUCCESSFUL
//!   safe_box_then_dangling_deref      -> SUCCESSFUL
//!   safe_box_then_int2ptr_deref       -> SUCCESSFUL
//!   safe_null_then_box_deref          -> SUCCESSFUL
//!   safe_boxed_str_then_box_deref     -> SUCCESSFUL
//!   bug_box_then_null_value           -> FAILED ('assertion failed: *b == 6')
//!   bug_null_deref_after_box          -> FAILED ('null pointer dereference occurred')
//!   bug_use_after_free_then_null      -> FAILED (dereference of a deallocated object)
//!   bug_two_int2ptr_casts_then_box    -> FAILED ('assertion failed: *b == 6')
//!   safe_two_int2ptr_casts_then_box   -> SUCCESSFUL
//!
//! MECHANISM. The heap model threads two metadata arrays, `obj_valid` and
//! `obj_size`. A site that writes one marked BOTH modified
//! (`mark_heap_metadata_modified`), so the rule head carried an `__out` for
//! the lane it never wrote. A head `__out` no constraint binds is a HAVOC of
//! that lane (a universally quantified clause variable), and none of these
//! sites recorded an approximation for it. The one-lane writers: `ptr::null()`
//! and `without_provenance` (obj_valid), `NonNull::dangling`, the
//! integer-to-pointer cast, the RawVec / Layout dangling pointers and the empty
//! Vec's dangling pointer (obj_valid), and `String::into_boxed_str`
//! (obj_size). `ptr::null()` was worse: it is a call terminator, and its
//! `obj_valid` invalidation went to the pending-update list that the block's
//! statements had already drained, so its rule bound NEITHER lane. After
//! `Box::new`, every counterexample through that havoc was certified Genuine:
//! the Box's drop-time size or validity check was refuted on the main bundle
//! and on the fix/chc-constprop-havoc branch before this repair. Emit-time
//! constant propagation had re-bound some of those lanes to their inputs,
//! which is why removing it (the branch's first commit) moved which check
//! failed.
//!
//! Each site now marks only the lane it writes, the pointer-utility call
//! delivers its update to its own rule, and a transition rule that still
//! carries an unbound metadata output records `heap_metadata_output_unbound`
//! (a sound havoc: a proof stays clean, a counterexample is never certified).
//!
//! Two invalidations in one block chained on `current_obj_valid_array()`,
//! which is `obj_valid__out` once the lane is written, so the second one
//! pushed `obj_valid__out = store(obj_valid__out, k, false)` beside the first
//! definition: that forces the INPUT `obj_valid[k]` to false, and with two
//! integer-to-pointer casts into different objects the rule was infeasible
//! and `bug_two_int2ptr_casts_then_box` VACUOUS. A pending invalidation now
//! extends the rule's earlier pending definition instead.
//!
//! The safe rows now prove; `safe_boxed_str_then_box_deref` is NOT_GENUINE
//! because a signedness fallback in the String path demotes its proof, and
//! the row guards against its havoc being certified again. The bug rows
//! guard the other direction: the lane each site does write still carries
//! the invalidation, so real null, freed and value bugs keep failing.
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s heap_metadata_lane_dual.rs

#[kani::proof]
fn safe_box_then_null_deref() {
    let b = Box::new(5u32);
    let p: *const u8 = std::ptr::null();
    assert!(p.is_null());
    assert!(*b == 5);
}

#[kani::proof]
fn safe_box_then_dangling_deref() {
    let b = Box::new(7u64);
    let d: std::ptr::NonNull<u8> = std::ptr::NonNull::dangling();
    let _ = d;
    assert!(*b == 7);
}

#[kani::proof]
fn safe_box_then_int2ptr_deref() {
    let b = Box::new(9u16);
    let p = 0x1000usize as *const u8;
    let _ = p;
    assert!(*b == 9);
}

// Control: the null pointer before the allocation never havocked a live lane.
#[kani::proof]
fn safe_null_then_box_deref() {
    let p: *const u8 = std::ptr::null();
    let b = Box::new(5u32);
    assert!(p.is_null());
    assert!(*b == 5);
}

// `into_boxed_str` resizes obj_size only; it marked obj_valid modified too,
// which havocked the validity of the Box allocated before it.
#[kani::proof]
fn safe_boxed_str_then_box_deref() {
    let x = Box::new(7u32);
    let s = String::from("hi");
    let _b = s.into_boxed_str();
    assert!(*x == 7);
}

#[kani::proof]
fn bug_box_then_null_value() {
    let b = Box::new(5u32);
    let p: *const u8 = std::ptr::null();
    assert!(p.is_null());
    assert!(*b == 6);
}

#[kani::proof]
fn bug_null_deref_after_box() {
    let b = Box::new(5u32);
    let p: *const u32 = std::ptr::null();
    let x = unsafe { *p };
    assert!(*b == 5 && x == x);
}

#[kani::proof]
fn bug_use_after_free_then_null() {
    let b = Box::new(5u32);
    let raw = Box::into_raw(b);
    unsafe { drop(Box::from_raw(raw)); }
    let p: *const u8 = std::ptr::null();
    let _ = p;
    let x = unsafe { *raw };
    assert!(x == 5);
}

// Two integer-to-pointer casts into different objects, in one block, while the
// Box keeps obj_valid live.
#[kani::proof]
fn bug_two_int2ptr_casts_then_box() {
    let b = Box::new(5u32);
    let q = 0x1_0000_1000usize as *const u8;
    let r = 0x5_0000_1000usize as *const u8;
    let _ = (q, r);
    assert!(*b == 6);
}

#[kani::proof]
fn safe_two_int2ptr_casts_then_box() {
    let b = Box::new(5u32);
    let q = 0x1_0000_1000usize as *const u8;
    let r = 0x5_0000_1000usize as *const u8;
    let _ = (q, r);
    assert!(*b == 5);
}
