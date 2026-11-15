// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The untyped-view nets (`stmt/codegen_stmt_store/untyped_view_scan.rs`) and
//! the copy-chain / operand check of `pointer_field_value_source`
//! (review of fix/chc-lost-writes round 6, 2026-09-27).
//!
//! - Pointer-carrying bytes rewritten without a typed pointer store (a store
//!   through a pointer cast to another pointee, `copy_nonoverlapping`,
//!   `write_bytes`, `mem::swap`, a union field) record the FailClose reason
//!   `pointer_bytes_rewritten_untyped`; the same operations over bytes that
//!   cannot hold a pointer do not.
//! - A raw read of a static's memory under a view the entry rule does not seed
//!   records the SoundHavoc reason `static_memory_read_unseeded_view`; a read
//!   under a seeded view (the element type) does not.
//! - A copy of an owner whose pointer field was rewritten untyped, and an
//!   operand local rewritten before the aggregate, leave the store through the
//!   field unresolved (`deref_store_referent_unresolved`).

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

    use core::ptr::{addr_of, addr_of_mut};

    #[derive(Clone, Copy)]
    pub struct HR { pub p: *mut u32, pub n: u32 }

    pub fn probe_direct_local_rewritten_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        unsafe { *(addr_of_mut!(a) as *mut usize) = yp as usize; }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    pub fn probe_source_memcpy_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        unsafe { core::ptr::copy_nonoverlapping(&yp as *const *mut u32, &mut a as *mut *mut u32, 1); }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the copied pointer");
    }

    pub fn probe_source_zeroed() {
        let mut bx: Box<u32> = Box::new(0);
        let mut a: *mut u32 = &mut *bx;
        unsafe { core::ptr::write_bytes(&mut a as *mut *mut u32, 0, 1); }
        kani::assert(a.is_null(), "the pointer was zeroed");
    }

    pub fn probe_source_swapped_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let mut yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        core::mem::swap(&mut a, &mut yp);
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the swapped pointer");
    }

    #[repr(C)]
    #[derive(Clone, Copy)]
    pub union U { pub p: *mut u32, pub n: usize }

    pub fn probe_union_rewrite_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut u = U { p: &mut *bx };
        u.n = yp as usize;
        let a = unsafe { u.p };
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the union's new pointer");
    }

    pub fn probe_cast_method_rewrite_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        unsafe { addr_of_mut!(a).cast::<usize>().write(yp as usize); }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    fn punned_slot(p: &mut *mut u32) -> *mut usize {
        p as *mut *mut u32 as *mut usize
    }

    pub fn probe_returned_pun_rewrite_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        unsafe { *punned_slot(&mut a) = yp as usize; }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    pub fn probe_erased_then_recast_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        let erased = addr_of_mut!(a) as *mut ();
        unsafe { *(erased as *mut usize) = yp as usize; }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    pub trait Tr { fn get(&self) -> u32; }
    pub struct Holder { pub p: *mut u32 }
    impl Tr for Holder { fn get(&self) -> u32 { unsafe { *self.p } } }

    pub fn probe_dyn_data_store_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(5);
        let yp: *mut u32 = &mut *y;
        let mut h = Holder { p: &mut *bx };
        let d: &mut dyn Tr = &mut h;
        unsafe { *(d as *mut dyn Tr as *mut usize) = yp as usize; }
        kani::assert(h.get() == 5, "the holder now points at y");
    }

    pub fn probe_dyn_data_pointer_read() {
        let mut bx: Box<u32> = Box::new(3);
        let h = Holder { p: &mut *bx };
        let d: &dyn Tr = &h;
        let thin = d as *const dyn Tr as *const u8;
        kani::assert(!thin.is_null() && d.get() == 3, "reads only");
    }

    // Controls: the same operations over bytes that cannot hold a pointer.
    pub fn probe_scalar_punned_store() {
        let mut x: u32 = 0;
        unsafe { *(addr_of_mut!(x) as *mut u8) = 1; }
        kani::assert(x == 1, "the low byte was written");
    }

    pub fn probe_swap_stack_refs() {
        let mut a = 0u8;
        let mut b = 0u8;
        {
            let mut p = &mut a;
            let mut q = &mut b;
            core::mem::swap(&mut p, &mut q);
            *p = 7;
            *q = 3;
        }
        kani::assert(b == 7 && a == 3, "the swap exchanged the borrows");
    }

    pub fn probe_scalar_swap() {
        let mut x: u32 = 1;
        let mut z: u32 = 2;
        core::mem::swap(&mut x, &mut z);
        kani::assert(x == 2 && z == 1, "swapped");
    }

    pub fn probe_pointer_typed_store() {
        let mut bx: Box<u32> = Box::new(0);
        let a: *mut u32 = &mut *bx;
        unsafe { *a = 7; }
        kani::assert(*bx == 7, "the store went through the pointer");
    }

    // A copy of an owner whose pointer field was rewritten untyped.
    pub fn probe_copy_owner_after_untyped_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut h = HR { p: &mut *bx, n: 0 };
        unsafe { *(addr_of_mut!(h.p) as *mut usize) = yp as usize; }
        let mut h2 = h;
        let r = &mut h2;
        unsafe { *r.p = 7; }
        kani::assert(*bx == 0, "the store went through the copied owner's new pointer");
    }

    // The aggregate's operand local rewritten before the aggregate.
    pub fn probe_source_local_rewritten_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        unsafe { *(addr_of_mut!(a) as *mut usize) = yp as usize; }
        let mut h = HR { p: a, n: 0 };
        let r = &mut h;
        unsafe { *r.p = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten operand");
    }

    static mut GA: [u16; 2] = [1, 0x0102];
    static mut GB: [u16; 2] = [1, 2];
    static mut GC: [u8; 4] = [1, 2, 3, 4];

    static mut FOO: &mut i32 = &mut 12;
    pub fn probe_static_ref_typed_read() {
        unsafe { kani::assert(*FOO == 12, "the referent of a reference-typed static"); }
    }

    pub struct Wrap { pub c: core::cell::UnsafeCell<u32> }
    static mut CELLED: Wrap = Wrap { c: core::cell::UnsafeCell::new(5) };
    pub fn probe_static_unsafe_cell_read() {
        unsafe {
            let p = (*addr_of!(CELLED)).c.get();
            kani::assert(*p == 5, "the cell's value through UnsafeCell::get");
        }
    }

    pub fn probe_static_u16_bytes_nostore() {
        unsafe {
            let p = addr_of!(GA) as *const u8;
            kani::assert(*p.add(2) == 2, "the low byte of element 1");
        }
    }

    pub fn probe_static_u16_elem_store_bytes() {
        unsafe {
            GB[1] = 0x0102;
            let p = addr_of!(GB) as *const u8;
            kani::assert(*p.add(2) == 2, "the low byte of element 1");
        }
    }

    pub fn probe_static_u16_elem_view() {
        unsafe {
            GB[1] = 0x0102;
            let p = addr_of!(GB) as *const u16;
            kani::assert(*p.add(1) == 0x0102, "element 1 through its own view");
        }
    }

    // Round 8 (review of fix/chc-lost-writes round 7): carriers the nets must
    // follow, and the decoder and image seeding of reordered structs.
    pub fn probe_pun_through_ref_to_ptr_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        let q: *mut usize = addr_of_mut!(a) as *mut usize;
        let rq = &q;
        unsafe { **rq = yp as usize; }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    pub fn probe_pun_option_payload_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        let o = Some(addr_of_mut!(a) as *mut usize);
        if let Some(q) = o {
            unsafe { *q = yp as usize; }
        }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    pub fn probe_pun_checked_add_launder_safe(k: usize) {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        let addr = addr_of_mut!(a) as usize + k;
        unsafe { *(addr as *mut usize) = yp as usize; }
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    #[inline(never)]
    fn store_through_ref(p: &*mut usize, v: usize) {
        unsafe { **p = v; }
    }

    pub fn probe_pun_ref_to_helper_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut a: *mut u32 = &mut *bx;
        let q: *mut usize = addr_of_mut!(a) as *mut usize;
        store_through_ref(&q, yp as usize);
        unsafe { *a = 7; }
        kani::assert(*bx == 0, "the store went through the rewritten pointer");
    }

    pub fn probe_int_addr_rebound_safe() {
        let mut bx: Box<u32> = Box::new(0);
        let mut y: Box<u32> = Box::new(0);
        let yp: *mut u32 = &mut *y;
        let mut addr: usize = (&mut *bx as *mut u32) as usize;
        {
            let pa = &mut addr;
            *pa = yp as usize;
        }
        unsafe { *(addr as *mut u32) = 7; }
        kani::assert(*bx == 0, "the store went through the rebound address");
    }

    pub fn probe_typed_copy_into_ref_array() {
        let x = 1u32;
        let yv = 2u32;
        let src = [&yv, &x];
        let mut dst = [&x, &x];
        unsafe { core::ptr::copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 2) };
        kani::assert(*dst[0] == 2, "the typed copy moved the references");
    }

    static mut SR: [u16; 2] = [1, 0x0102];
    pub fn probe_static_byte_read_through_ref() {
        unsafe { SR[1] = 0x0304; }
        let q: *const u8 = unsafe { addr_of!(SR) } as *const u8;
        let rq = &q;
        kani::assert(unsafe { *(*rq).add(2) } == 4, "the low byte of element 1");
    }

    pub struct SHolder { pub p: *const [u16; 2], pub n: u8 }
    static mut SS: [u16; 2] = [1, 0x0102];
    pub fn probe_static_byte_read_through_field() {
        unsafe { SS[1] = 0x0304; }
        let h = SHolder { p: unsafe { addr_of!(SS) }, n: 1 };
        let q = h.p as *const u8;
        kani::assert(unsafe { *q.add(2) } == 4, "the low byte of element 1");
    }

    static mut ST: [u16; 2] = [1, 0x0102];
    pub fn probe_static_byte_read_through_tuple() {
        unsafe { ST[1] = 0x0304; }
        let t = (unsafe { addr_of!(ST) }, 7u8);
        let q = t.0 as *const u8;
        kani::assert(unsafe { *q.add(2) } == 4, "the low byte of element 1");
    }

    pub struct P { pub x: u8, pub y: u32 }
    static SP: P = P { x: 1, y: 10 };
    pub fn probe_reordered_struct_static() {
        kani::assert(SP.x == 1 && SP.y == 10, "the initializer as written");
    }

    #[derive(Clone, Copy)]
    pub struct T3 { pub a: u8, pub b: u32, pub c: u8 }
    static AT: [T3; 2] = [T3 { a: 1, b: 10, c: 2 }, T3 { a: 3, b: 30, c: 4 }];
    pub fn probe_reordered_struct_array_static() {
        kani::assert(AT[1].a == 3 && AT[1].b == 30 && AT[1].c == 4 && AT[0].c == 2, "as written");
    }

    pub fn probe_static_element_field_through_pointer() {
        let q = addr_of!(AT) as *const T3;
        kani::assert(unsafe { (*q.add(1)).b } == 30, "a field of element 1");
    }

    static EO: Option<u32> = Some(5);
    pub fn probe_static_enum_payload_direct() {
        let p = addr_of!(EO);
        if let Some(v) = unsafe { &*p } {
            kani::assert(*v == 5, "the payload");
        }
    }

    pub struct EHolder { pub p: *const Option<u32>, pub n: u8 }
    pub fn probe_static_enum_payload_through_field() {
        let h = EHolder { p: addr_of!(EO), n: 1 };
        if let Some(v) = unsafe { &*h.p } {
            kani::assert(*v == 5, "the payload");
        }
    }

    pub fn probe_static_u8_array_bytes() {
        unsafe {
            GC[3] = 9;
            let p = addr_of!(GC) as *const u8;
            kani::assert(*p.add(3) == 9, "element 3 through its own view");
        }
    }
"#;

fn solve_with_reasons(fn_name: &str) -> (String, std::collections::BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(PROBE, |ctx| {
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

const REWRITE: &str = "pointer_bytes_rewritten_untyped";
const UNSEEDED: &str = "static_memory_read_unseeded_view";

fn assert_reason(fn_name: &str, reason: &str) {
    let (_verdict, reasons) = solve_with_reasons(fn_name);
    assert!(reasons.contains_key(reason), "{fn_name} must record {reason}; got {reasons:?}");
}

fn assert_no_reason(fn_name: &str, reason: &str) {
    let (_verdict, reasons) = solve_with_reasons(fn_name);
    assert!(!reasons.contains_key(reason), "{fn_name} must not record {reason}; got {reasons:?}");
}

#[test]
fn test_punned_store_into_pointer_local_fails_closed() {
    assert_reason("probe_direct_local_rewritten_safe", REWRITE);
}

#[test]
fn test_byte_copy_into_pointer_local_fails_closed() {
    assert_reason("probe_source_memcpy_safe", REWRITE);
}

#[test]
fn test_write_bytes_over_pointer_local_fails_closed() {
    assert_reason("probe_source_zeroed", REWRITE);
}

#[test]
fn test_swap_of_pointer_locals_fails_closed() {
    assert_reason("probe_source_swapped_safe", REWRITE);
}

#[test]
fn test_union_field_store_over_pointer_fails_closed() {
    assert_reason("probe_union_rewrite_safe", REWRITE);
}

#[test]
fn test_cast_method_rewrite_fails_closed() {
    assert_reason("probe_cast_method_rewrite_safe", REWRITE);
}

/// The helper returns the punned pointer and the caller stores through it:
/// the helper's body records the escape when the walker inlines it.
#[test]
fn test_returned_pun_rewrite_fails_closed() {
    assert_reason("probe_returned_pun_rewrite_safe", REWRITE);
}

/// `*mut ()` names no bytes, so the cast to it is harmless; the cast back to
/// `*mut usize` and the store through it are the rewrite.
#[test]
fn test_erased_then_recast_rewrite_fails_closed() {
    assert_reason("probe_erased_then_recast_safe", REWRITE);
}

/// A trait object's data pointer taken thin is erased, not punned (the
/// standard library does that in `is_null`, `addr_eq` and `Box`'s drop), but a
/// store of bytes through it is still a rewrite.
#[test]
fn test_store_through_dyn_data_pointer_fails_closed() {
    assert_reason("probe_dyn_data_store_safe", REWRITE);
}

#[test]
fn test_dyn_data_pointer_read_is_not_a_rewrite() {
    assert_no_reason("probe_dyn_data_pointer_read", REWRITE);
}

#[test]
fn test_scalar_punned_store_is_not_a_pointer_rewrite() {
    assert_no_reason("probe_scalar_punned_store", REWRITE);
}

/// Two pointers that only ever hold borrows of locals: the typed-swap model
/// exchanges their points-at edges exactly, so the net stays out of the way
/// (negative/merged_pointer_shapes.rs::swap_refs_store_safe).
#[test]
fn test_swap_of_stack_borrows_is_left_to_the_swap_model() {
    let (verdict, reasons) = solve_with_reasons("probe_swap_stack_refs");
    assert!(!reasons.contains_key(REWRITE), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "the swap stays exact");
}

#[test]
fn test_scalar_swap_is_not_a_pointer_rewrite() {
    assert_no_reason("probe_scalar_swap", REWRITE);
}

#[test]
fn test_typed_store_through_pointer_is_not_a_pointer_rewrite() {
    let (verdict, reasons) = solve_with_reasons("probe_pointer_typed_store");
    assert!(!reasons.contains_key(REWRITE), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "the typed store stays exact");
}

/// Without the copy-chain check the store through `h2.p` resolved to `bx`'s
/// allocation (no unresolved-referent reason) and the safe twin was certified
/// Genuine.
#[test]
fn test_copy_of_rewritten_owner_leaves_the_store_unresolved() {
    let (_verdict, reasons) = solve_with_reasons("probe_copy_owner_after_untyped_safe");
    assert!(
        reasons.contains_key("deref_store_referent_unresolved")
            || reasons.contains_key("deref_store_stack_target_unresolved"),
        "the store through the copied owner's field must stay unresolved; got {reasons:?}"
    );
}

/// Without the operand check the store through `h.p` resolved to `bx`'s
/// allocation, the value the operand's single definition gave it.
#[test]
fn test_rewritten_operand_local_leaves_the_store_unresolved() {
    let (_verdict, reasons) = solve_with_reasons("probe_source_local_rewritten_safe");
    assert!(
        reasons.contains_key("deref_store_referent_unresolved")
            || reasons.contains_key("deref_store_stack_target_unresolved"),
        "the store through the rewritten operand must stay unresolved; got {reasons:?}"
    );
}

#[test]
fn test_static_byte_read_of_wider_elements_is_not_evidence() {
    assert_reason("probe_static_u16_bytes_nostore", UNSEEDED);
}

#[test]
fn test_static_byte_read_after_element_store_is_not_evidence() {
    assert_reason("probe_static_u16_elem_store_bytes", UNSEEDED);
}

/// The static's declared type carries `'static`, the body's types erased
/// regions; the comparison must not read that difference as another view.
#[test]
fn test_reference_typed_static_read_is_a_seeded_view() {
    assert_no_reason("probe_static_ref_typed_read", UNSEEDED);
}

/// `UnsafeCell::get` casts `*const UnsafeCell<u32>` to `*const u32`: the same
/// bytes under the leaf type the entry rule seeds.
#[test]
fn test_unsafe_cell_view_of_static_is_seeded() {
    assert_no_reason("probe_static_unsafe_cell_read", UNSEEDED);
}

#[test]
fn test_static_element_view_read_stays_exact() {
    let (verdict, reasons) = solve_with_reasons("probe_static_u16_elem_view");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "the element view is seeded and written");
}

#[test]
fn test_static_byte_array_read_stays_exact() {
    let (verdict, reasons) = solve_with_reasons("probe_static_u8_array_bytes");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "a byte array's own view is seeded and written");
}

// Round 8 (review of fix/chc-lost-writes round 7).

/// Finding 2: the pun travels through a reference to the pointer local and is
/// read back with `copy (*rq)`.
#[test]
fn test_pun_through_reference_fails_closed() {
    assert_reason("probe_pun_through_ref_to_ptr_safe", REWRITE);
}

/// Finding 2: the pun travels through an `Option` payload.
#[test]
fn test_pun_through_option_payload_fails_closed() {
    assert_reason("probe_pun_option_payload_safe", REWRITE);
}

/// Finding 2: the address is laundered through an addition.
#[test]
fn test_pun_through_integer_launder_fails_closed() {
    assert_reason("probe_pun_checked_add_launder_safe", REWRITE);
}

/// Finding 2: a reference to the punned pointer reaches a helper that writes
/// through it.
#[test]
fn test_reference_to_pun_passed_to_helper_fails_closed() {
    assert_reason("probe_pun_ref_to_helper_safe", REWRITE);
}

/// Finding 4: an integer holding an exposed address is rewritten through
/// `&mut`; the int-to-pointer lane read the address off its definition.
#[test]
fn test_address_integer_rewritten_through_reference_fails_closed() {
    assert_reason("probe_int_addr_rebound_safe", REWRITE);
}

/// Finding 5: a typed copy into a local array of references is read through
/// memory and stays exact.
#[test]
fn test_typed_copy_into_reference_array_stays_exact() {
    let (verdict, reasons) = solve_with_reasons("probe_typed_copy_into_ref_array");
    assert!(!reasons.contains_key(REWRITE), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "the typed copy stays exact");
}

/// Finding 1: a byte view of a static read through a reference to the
/// pointer local.
#[test]
fn test_static_byte_read_through_reference_is_not_evidence() {
    assert_reason("probe_static_byte_read_through_ref", UNSEEDED);
}

/// Finding 1: the static's typed pointer travels through a struct field and
/// is cast to bytes after it is loaded.
#[test]
fn test_static_byte_read_through_struct_field_is_not_evidence() {
    assert_reason("probe_static_byte_read_through_field", UNSEEDED);
}

/// Finding 1: the same through a tuple field.
#[test]
fn test_static_byte_read_through_tuple_field_is_not_evidence() {
    assert_reason("probe_static_byte_read_through_tuple", UNSEEDED);
}

/// Finding 3 (root cause): a struct static whose fields rustc reorders
/// decodes by its layout.
#[test]
fn test_reordered_struct_static_decodes_by_layout() {
    let (verdict, _) = solve_with_reasons("probe_reordered_struct_static");
    assert_eq!(verdict, "unsat", "the initializer decodes as written");
}

#[test]
fn test_reordered_struct_array_static_decodes_by_layout() {
    let (verdict, _) = solve_with_reasons("probe_reordered_struct_array_static");
    assert_eq!(verdict, "unsat", "every element decodes as written");
}

/// Finding 3: a field of an array element read through the element pointer
/// is a seeded view (the image seeds element fields) and stays exact.
#[test]
fn test_static_element_field_through_pointer_stays_exact() {
    let (verdict, reasons) = solve_with_reasons("probe_static_element_field_through_pointer");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "the element's field is seeded");
}

/// A payload read through a borrow chain of the static's own place resolves to
/// the static's state variable, not its image, so it is not an unseeded read.
/// (An enum static with a payload has no decoded initializer at all: the state
/// variable starts unconstrained and the harness is demoted as
/// `static_init_incomplete`; after a store it holds the stored value.)
#[test]
fn test_static_enum_payload_direct_is_a_place_read() {
    let (_verdict, reasons) = solve_with_reasons("probe_static_enum_payload_direct");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
}

/// An enum's variants are not decomposed in the image: a payload read
/// through a pointer loaded out of a struct field is not evidence.
#[test]
fn test_static_enum_payload_through_field_is_not_evidence() {
    assert_reason("probe_static_enum_payload_through_field", UNSEEDED);
}
