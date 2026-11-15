// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Review of fix/chc-lost-writes, lostwrite round 1 (2026-10-01).
//!
//! - Finding 1: an element store through a pointer that may name a static or
//!   an object the encoder cannot identify records
//!   `deref_store_referent_unresolved`, as the generic deref store does.
//! - Finding 2: an element store through a pointer stepped out of its object
//!   is bounds-checked and fails.
//! - Finding 3: the heap view ledger (`heap/heap_view_ledger.rs`): a read of a
//!   heap object under a key another store of its bytes did not write fails
//!   closed (`heap_view_read_stale`); a read under a key nothing wrote records
//!   `heap_view_read_unwritten`; coherent element views record neither.
//! - Finding 4: an access through a pointer whose object lane is not a
//!   constant is bounded by the object's size (`heap_access_checks`).
//! - Finding 5: a volatile store into a pointer local fails closed
//!   (`pointer_bytes_rewritten_untyped`).
//! - Finding 6: `ptr::null()` beside an exposed stack address keeps its
//!   constant null lane and records nothing.
//! - Measurement: a dispatch arm's accesses are checked under its dispatch
//!   condition, so a candidate that is not the runtime type does not fail a
//!   safe program.
//! - Merge with main dbfe268fc (Kani's address layout, dfebf493c): an integer
//!   is an address, not an identity term. A transmute of one into a raw
//!   pointer or a `NonNull` takes the integer-to-pointer lane with its
//!   invalidation, and an integer local carries no allocation id.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const PROBE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    use core::mem::MaybeUninit;
    use core::ptr::{addr_of, addr_of_mut, null};

    static mut B1: [u16; 2] = [1, 2];
    static mut P1: *mut [u16; 2] = unsafe { addr_of_mut!(B1) };
    static mut B2: [u16; 2] = [1, 2];
    static mut M3: MaybeUninit<[u16; 2]> = MaybeUninit::uninit();
    static G4: [u16; 2] = [1, 2];

    fn launder<T>(p: *mut T) -> *mut T {
        let b = Box::new(p);
        *b
    }

    pub fn probe_static_via_static_ptr_bug() {
        unsafe {
            (*P1)[1] = 5;
            kani::assert(B1[1] == 2, "the static was written through its pointer");
        }
    }

    pub fn probe_static_laundered_elem_store_bug() {
        unsafe {
            let q = launder(addr_of_mut!(B2));
            (*q)[1] = 5;
            kani::assert(B2[1] == 2, "the static was written through a laundered pointer");
        }
    }

    pub fn probe_maybeuninit_lazy_init_safe() {
        unsafe {
            let p = (*addr_of_mut!(M3)).as_mut_ptr();
            (*p)[0] = 3;
            (*p)[1] = 4;
            let v = (*addr_of!(M3)).assume_init();
            kani::assert(v[1] == 4, "the lazily initialized element");
        }
    }

    pub fn probe_box_elem_store_safe() {
        let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
        bx[1] = 5;
        let p = addr_of!(*bx) as *const u16;
        kani::assert(bx[1] == 5, "the written element");
        kani::assert(unsafe { *p.add(1) } == 5, "the written element through its address");
    }

    pub fn probe_elem_store_wrapping_oob() {
        let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
        let p = (addr_of_mut!(*bx) as *mut u16).wrapping_add(2) as *mut [u16; 2];
        unsafe { (*p)[1] = 9 };
    }

    pub fn probe_box_wide_store_index_read_bug() {
        let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
        unsafe { *(addr_of_mut!(*bx) as *mut u32) = 0x0005_0003 };
        kani::assert(bx[1] == 2, "the wide store rewrote element 1");
    }

    pub fn probe_box_elem_store_then_wide_store_bug() {
        let mut bx: Box<[u16; 2]> = Box::new([1, 2]);
        bx[1] = 9;
        unsafe { *(addr_of_mut!(*bx) as *mut u32) = 0x0005_0003 };
        kani::assert(bx[1] == 9, "the wide store rewrote element 1");
    }

    pub fn probe_box_nostore_wide_read_safe() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let p = addr_of!(*bx) as *const u32;
        kani::assert(unsafe { *p } == 0x0002_0001, "the two elements as one u32");
    }

    pub fn probe_wrapping_add_oob_read() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let p = (addr_of!(*bx) as *const u16).wrapping_add(2);
        let v = unsafe { *p };
        kani::assert(v == v, "the read is past the box");
    }

    pub fn probe_wrapping_add_inbounds_read() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let p = (addr_of!(*bx) as *const u16).wrapping_add(1);
        let v = unsafe { *p };
        kani::assert(v == v, "the read is in bounds");
    }

    pub fn probe_static_wrapping_add_oob_read() {
        let p = (addr_of!(G4) as *const u16).wrapping_add(2);
        let v = unsafe { *p };
        kani::assert(v == v, "the read is past the static");
    }

    pub fn probe_local_rebind_write_volatile_bug() {
        let mut x: u32 = 1;
        let mut y: u32 = 2;
        let mut q: *mut u32 = addr_of_mut!(x);
        unsafe { core::ptr::write_volatile(&mut q, addr_of_mut!(y)) };
        unsafe { *q = 7 };
        kani::assert(x == 7, "the store went to y");
    }

    pub fn probe_transmute_option_ref_inbounds_safe() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let a = addr_of!(*bx) as *const u16 as usize;
        let r: Option<&u16> = unsafe { core::mem::transmute::<usize, Option<&u16>>(a + 2) };
        kani::assert(*r.unwrap() == 2, "element 1 through the option");
    }

    pub fn probe_ptr_read_usize_slot_safe() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let a = addr_of!(*bx) as *const u16 as usize + 2;
        let p: *const u16 = unsafe { *(&a as *const usize as *const *const u16) };
        kani::assert(unsafe { *p } == 2, "element 1 through the slot's bits");
    }

    pub fn probe_transmute_names_no_object_read() {
        let x: u32 = 5;
        let a = &x as *const u32 as usize;
        let k: usize = 6;
        let p: *const u32 = unsafe { core::mem::transmute::<usize, *const u32>(k << 32) };
        let v = unsafe { *p };
        kani::assert(v == v || a == 0, "the pointer names no object");
    }

    pub fn probe_integer_local_names_no_allocation_read() {
        let x: u32 = 5;
        let hi: usize = 5;
        let n = hi << 32;
        let p: *const u32 = core::ptr::without_provenance(n);
        let v = unsafe { *p };
        kani::assert(v == v || x == 0, "the pointer names no object");
    }

    pub fn probe_transmute_round_trip_safe() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let a = addr_of!(*bx) as *const u16 as usize;
        let q: *const u16 = unsafe { core::mem::transmute::<usize, *const u16>(a + 2) };
        kani::assert(unsafe { *q } == 2, "element 1 through the round trip");
    }

    pub fn probe_transmute_nonnull_round_trip_safe() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let a = addr_of!(*bx) as *const u16 as usize;
        let p = unsafe { core::mem::transmute::<usize, core::ptr::NonNull<u16>>(a + 2) };
        kani::assert(unsafe { *p.as_ptr() } == 2, "element 1 through the round trip");
    }

    pub fn probe_transmute_nonnull_names_no_object_read() {
        let x: u32 = 5;
        let a = &x as *const u32 as usize;
        let k: usize = 6;
        let p = unsafe { core::mem::transmute::<usize, core::ptr::NonNull<u32>>(k << 32) };
        let q: *const u32 = unsafe { core::mem::transmute(p) };
        let v = unsafe { *q };
        kani::assert(v == v || a == 0, "the pointer names no object");
    }

    pub fn probe_pointer_from_a_number_through_a_box_cell() {
        let cell: Box<*const u32> = Box::new((1usize << 32) as *const u32);
        let b = Box::new(5u32);
        let p = *cell;
        let v = unsafe { *p };
        kani::assert(v == v || *b == 0, "the pointer names no object");
    }

    pub fn probe_array_transmute_names_no_object_read() {
        let x: u32 = 5;
        let a = &x as *const u32 as usize;
        let k: usize = 6;
        let p: *const u32 = unsafe { core::mem::transmute::<[usize; 1], *const u32>([k << 32]) };
        let v = unsafe { *p };
        kani::assert(v == v || a == 0, "the pointer names no object");
    }

    pub fn probe_null_with_stack_addr(x: u32) {
        let px = &x as *const u32;
        let n: *const u8 = null();
        let v = unsafe { *px };
        kani::assert(n.is_null() && v != 7, "x may be 7");
    }
"#;

/// Dispatch arms (review of lostwrite round 1, measurement): every `Tv` impl
/// is a candidate of `o.get()`, and the walker walks each one at the runtime
/// object's address.
const DISPATCH_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    pub trait Tv { fn get(&self) -> u8; }
    pub struct DV { pub a: u8, pub b: u8 }
    impl Tv for DV { fn get(&self) -> u8 { self.a } }
    pub struct DP { pub p: *const u8 }
    impl Tv for DP { fn get(&self) -> u8 { unsafe { *self.p } } }

    pub fn keep_impls_alive(byte: &u8) -> u8 {
        let o: Box<dyn Tv> = Box::new(DP { p: byte });
        o.get()
    }

    pub fn probe_dv_runtime_safe(a: u8) {
        let o: Box<dyn Tv> = Box::new(DV { a, b: 1 });
        kani::assert(o.get() == a, "the DV arm reads a");
    }

    pub fn probe_dv_runtime_bug(a: u8) {
        let o: Box<dyn Tv> = Box::new(DV { a, b: 1 });
        kani::assert(o.get() != a, "the DV arm reads a");
    }

    pub fn probe_dp_runtime_past_the_array() {
        let bytes = [1u8, 2];
        let o: Box<dyn Tv> = Box::new(DP { p: bytes.as_ptr().wrapping_add(2) });
        let _ = o.get();
    }
"#;

fn solve_with_reasons(fn_name: &str) -> (String, std::collections::BTreeMap<String, usize>) {
    solve_source_with_reasons(PROBE, fn_name)
}

fn solve_source_with_reasons(
    source: &str,
    fn_name: &str,
) -> (String, std::collections::BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        verdict = Some(
            run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .unwrap_or_else(|e| panic!("AY failed on {fn_name}: {e}")),
        );
    });
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (verdict.expect("the probe was encoded"), reasons)
}

const UNRESOLVED: &str = "deref_store_referent_unresolved";
const STALE: &str = "heap_view_read_stale";
const UNWRITTEN: &str = "heap_view_read_unwritten";
const PUN: &str = "pointer_bytes_rewritten_untyped";
const INT_TO_PTR: &str = "int_to_ptr_obj_invalidated";

/// Finding 1: the element lane wrote memory only and returned before the
/// unresolved-referent guard, so this bug probe proved clean.
#[test]
fn test_elem_store_through_a_static_pointer_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_static_via_static_ptr_bug");
    assert!(reasons.contains_key(UNRESOLVED), "got {reasons:?}");
}

#[test]
fn test_elem_store_through_a_laundered_static_pointer_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_static_laundered_elem_store_bug");
    assert!(reasons.contains_key(UNRESOLVED), "got {reasons:?}");
}

/// Finding 1: the lazy init of a `MaybeUninit` static was certified a Genuine
/// failure. The static lane indexed the static's state variable through a
/// pointer to its content; it now refuses a pointee that is not the static's
/// type, so whatever the verdict, it rests on a recorded reason.
#[test]
fn test_maybeuninit_static_lazy_init_is_not_placed() {
    let (_verdict, reasons) = solve_with_reasons("probe_maybeuninit_lazy_init_safe");
    assert!(
        reasons.contains_key("static_elem_store_unplaced") || reasons.contains_key(UNRESOLVED),
        "got {reasons:?}"
    );
}

/// The niche of an `Option<&T>` made by a transmute is not decoded: the value
/// is fresh and the reason keeps the unwrap's failure from being certified
/// (Genuine on main and on the branch).
#[test]
fn test_transmute_into_option_ref_is_fresh() {
    let (_verdict, reasons) = solve_with_reasons("probe_transmute_option_ref_inbounds_safe");
    assert!(reasons.contains_key("transmute_layout_fallback"), "got {reasons:?}");
}

/// A stack slot read under a key nothing wrote there selects a free cell.
#[test]
fn test_pointer_read_of_an_integer_slot_records_unwritten_view() {
    let (_verdict, reasons) = solve_with_reasons("probe_ptr_read_usize_slot_safe");
    assert!(reasons.contains_key(UNWRITTEN), "got {reasons:?}");
}

/// A Box element store names its heap object: it records nothing and its
/// views stay coherent (the lane's precision is kept).
#[test]
fn test_box_elem_store_stays_exact_and_coherent() {
    let (verdict, reasons) = solve_with_reasons("probe_box_elem_store_safe");
    assert_eq!(verdict, "unsat", "the element is read back; reasons {reasons:?}");
    for reason in [UNRESOLVED, STALE, UNWRITTEN] {
        assert!(!reasons.contains_key(reason), "got {reasons:?}");
    }
}

/// Finding 2: the out-of-bounds element store verified clean.
#[test]
fn test_elem_store_past_the_box_fails() {
    let (verdict, reasons) = solve_with_reasons("probe_elem_store_wrapping_oob");
    assert!(reasons.contains_key(UNRESOLVED), "got {reasons:?}");
    assert_eq!(verdict, "sat", "the store past the box must fail; reasons {reasons:?}");
}

/// Finding 3, pre-existing root: the index read selected the initializer's
/// element after a wide store, a clean missed bug on main.
#[test]
fn test_wide_store_then_index_read_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_box_wide_store_index_read_bug");
    assert!(reasons.contains_key(STALE), "got {reasons:?}");
}

#[test]
fn test_elem_store_then_wide_store_then_index_read_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_box_elem_store_then_wide_store_bug");
    assert!(reasons.contains_key(STALE), "got {reasons:?}");
}

/// Finding 3: a wide read of a box only ever written as `u16` selects a free
/// cell; its failure was certified Genuine on main and on the branch.
#[test]
fn test_wide_read_of_narrow_box_records_unwritten_view() {
    let (_verdict, reasons) = solve_with_reasons("probe_box_nostore_wide_read_safe");
    assert!(reasons.contains_key(UNWRITTEN), "got {reasons:?}");
}

/// Finding 4: a read through a wrapping step past a Box verified clean on main
/// and on the branch; its object lane does not fold, and the bound is now
/// taken from the object's size.
#[test]
fn test_symbolic_lane_read_past_the_box_fails() {
    let (verdict, reasons) = solve_with_reasons("probe_wrapping_add_oob_read");
    assert_eq!(verdict, "sat", "the read past the box must fail; reasons {reasons:?}");
}

#[test]
fn test_symbolic_lane_read_in_bounds_proves() {
    let (verdict, reasons) = solve_with_reasons("probe_wrapping_add_inbounds_read");
    assert_eq!(verdict, "unsat", "the in-bounds read must prove; reasons {reasons:?}");
}

#[test]
fn test_symbolic_lane_read_past_a_static_fails() {
    let (verdict, reasons) = solve_with_reasons("probe_static_wrapping_add_oob_read");
    assert_eq!(verdict, "sat", "the read past the static must fail; reasons {reasons:?}");
}

/// Finding 5: the volatile store rebinds `q` with no MIR assignment.
#[test]
fn test_volatile_store_into_a_pointer_local_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_local_rebind_write_volatile_bug");
    assert!(reasons.contains_key(PUN), "got {reasons:?}");
}

/// Finding 6: the null literal keeps its constant lane beside an exposed
/// stack address.
#[test]
fn test_null_beside_a_stack_address_records_nothing() {
    let (verdict, reasons) = solve_with_reasons("probe_null_with_stack_addr");
    assert!(!reasons.contains_key(INT_TO_PTR), "got {reasons:?}");
    assert_eq!(verdict, "sat", "x may be 7");
}

/// A dispatch arm's memory accesses are checked under the arm's condition
/// (`guard_dispatch_arm_pending_checks`). The `DP` arm, walked at the `DV`
/// object's address, dereferences whatever its pointer field reads there;
/// once an access through a symbolic object lane took a bound, that check,
/// drained by the host with no guard, failed this safe probe.
#[test]
fn test_dispatch_arm_access_is_checked_under_its_arm() {
    let (verdict, reasons) = solve_source_with_reasons(DISPATCH_PROBE, "probe_dv_runtime_safe");
    assert_eq!(verdict, "unsat", "the DP arm is not the runtime type; reasons {reasons:?}");
}

#[test]
fn test_dispatch_arm_guard_keeps_the_runtime_arm_failure() {
    let (verdict, reasons) = solve_source_with_reasons(DISPATCH_PROBE, "probe_dv_runtime_bug");
    assert_eq!(verdict, "sat", "the DV arm's read is a; reasons {reasons:?}");
}

/// The runtime arm's own out-of-bounds read still fails under its condition.
#[test]
fn test_dispatch_arm_guard_keeps_the_runtime_arm_bound() {
    let (verdict, reasons) =
        solve_source_with_reasons(DISPATCH_PROBE, "probe_dp_runtime_past_the_array");
    assert_eq!(verdict, "sat", "the DP arm reads past the array; reasons {reasons:?}");
}

/// Merge with main dbfe268fc: dfebf493c's earlier arm for an integer
/// transmuted into a raw pointer took `int_to_ptr_value` and skipped the
/// invalidation, so a pointer naming no object read clean once its object lane
/// was symbolic at the access (`int_to_ptr_const_lane_dual.rs::
/// bug_exposed_transmute_hi6_read`).
#[test]
fn test_transmute_into_a_pointer_invalidates_its_object() {
    let (verdict, reasons) = solve_with_reasons("probe_transmute_names_no_object_read");
    assert!(reasons.contains_key(INT_TO_PTR), "got {reasons:?}");
    assert_eq!(verdict, "sat", "the pointer names no object; reasons {reasons:?}");
}

/// Merge with main dbfe268fc: an integer was taken as an identity term, so
/// `without_provenance(5 << 32)` named stack slot 5 (through the stub's result
/// and through `known_alloc_ids` of the integer local), where in Kani's layout
/// it is object 0 at offset `5 << 32` (`bug_plain_without_provenance_hi5`).
/// The pointer names no object, so its read fails exactly: no reason is
/// recorded.
#[test]
fn test_integer_local_carries_no_allocation() {
    let (verdict, reasons) = solve_with_reasons("probe_integer_local_names_no_allocation_read");
    assert_eq!(verdict, "sat", "the pointer names no object; reasons {reasons:?}");
    for reason in [INT_TO_PTR, "int_to_ptr_names_always_valid_object"] {
        assert!(!reasons.contains_key(reason), "got {reasons:?}");
    }
}

/// Merge with main dbfe268fc: an integer transmuted into a `NonNull` was taken
/// as the identity term, which in Kani's layout names no object (or, as here,
/// read as the identity, a model object by the model's numbering), so a read
/// through it was unchecked (`symbolic_lane_oob_dual.rs::
/// bug_transmute_nonnull_oob`). It now takes the integer-to-pointer lane.
#[test]
fn test_transmute_into_nonnull_takes_the_integer_to_pointer_lane() {
    let (verdict, reasons) = solve_with_reasons("probe_transmute_nonnull_names_no_object_read");
    assert_eq!(verdict, "sat", "the pointer names no object; reasons {reasons:?}");
}

/// A pointer's exposed address moved by a constant names its object again
/// (`int_operand_is_exposed_address`), so the round trip through a transmute
/// proves without the lane's invalidation, as dfebf493c's arm proved it for a
/// raw pointer, and now for a `NonNull` too
/// (`int_to_ptr_exposed_dual.rs::safe_transmute_roundtrip_box`,
/// `symbolic_lane_oob_dual.rs::safe_transmute_nonnull_inbounds`).
#[test]
fn test_transmute_round_trip_of_an_exposed_address_is_exact() {
    for probe in ["probe_transmute_round_trip_safe", "probe_transmute_nonnull_round_trip_safe"] {
        let (verdict, reasons) = solve_with_reasons(probe);
        assert!(!reasons.contains_key(INT_TO_PTR), "{probe}: got {reasons:?}");
        assert_eq!(verdict, "unsat", "{probe}: the round trip reads element 1; {reasons:?}");
    }
}

/// Landing on main f61920d1a: `Box::new` rebuilt its payload from the source
/// operand of the cast that made it, so `(1 << 32) as *const u32` was stored as
/// the integer taken as the identity term, which names object 1, and the read
/// through the stored pointer proved clean (`t5_int_ptr_carried.rs::
/// bug_via_box_then_alloc_k1`, round 3 review probes, on main as well).
#[test]
fn test_box_payload_of_an_integer_to_pointer_cast_names_no_object() {
    let (verdict, reasons) = solve_with_reasons("probe_pointer_from_a_number_through_a_box_cell");
    assert_eq!(verdict, "sat", "the pointer names no object; reasons {reasons:?}");
}

/// Landing on main f61920d1a: a pointer made from a number naming no object by
/// an aggregate transmute (no invalidation on that route) read clean once its
/// object lane was symbolic; a symbolic lane at or past OBJECT_ID_LIMIT is
/// now outside every object, as a constant one is
/// (`int_to_ptr_const_lane_dual.rs::bug_exposed_array1_transmute_hi6_read`).
#[test]
fn test_symbolic_lane_past_the_object_id_limit_fails() {
    let (verdict, reasons) = solve_with_reasons("probe_array_transmute_names_no_object_read");
    assert_eq!(verdict, "sat", "the pointer names no object; reasons {reasons:?}");
}
