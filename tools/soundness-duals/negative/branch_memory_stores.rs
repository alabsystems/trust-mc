// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a store through a pointer made on one path stays on that path.
//
// Found while fixing negative/stack_heap_disjoint.rs (2026-09-12). The BMC
// byte memory is one store chain for every path, and stores through a pointer
// were not guarded by the path condition, so a store made in a branch was seen
// on the other path too. `atomic_store_in_branch_safe` FAILED with
// CTREX_CAT:Genuine on the re-land bundle 11ba3129, and so did
// `read_after_box_store_in_branch_safe`; the raw-read guard added on this
// branch turned the latter into an OverApproximation failure. In BMC the
// box-backed swap, copy, write_bytes and `&mut`-then-raw-read shapes stay
// INCONCLUSIVE (ay memout or an undecided model; `&mut *p` through a raw
// pointer gets an address not tied to `p`), so their safe twins are known red
// for class `unknown` there; the stack-backed `swap_stack`, `ref_store_stack`
// and `wide_stack` pairs decide.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

use std::sync::atomic::{AtomicU8, Ordering};

#[derive(Clone, Copy, PartialEq)]
struct Pair {
    a: u8,
    b: u16,
}

#[kani::proof]
fn box_store_in_branch_safe() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    unsafe { assert!(*p == if c { 1 } else { 0 }) }
}

#[kani::proof]
fn box_store_in_branch_must_fail() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    unsafe { assert!(*p == 1) }
}

#[kani::proof]
fn read_after_box_store_in_branch_safe() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    let y = unsafe { p.read() };
    assert!(y == if c { 1 } else { 0 });
}

#[kani::proof]
fn read_after_box_store_in_branch_must_fail() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    let y = unsafe { p.read() };
    assert!(y == 1);
}

#[kani::proof]
fn field_store_in_branch_safe() {
    let p = Box::into_raw(Box::new((0u8, 0u16)));
    let c: bool = kani::any();
    if c {
        unsafe { (*p).1 = 7 }
    }
    unsafe { assert!((*p).1 == if c { 7 } else { 0 }) }
}

#[kani::proof]
fn field_store_in_branch_must_fail() {
    let p = Box::into_raw(Box::new((0u8, 0u16)));
    let c: bool = kani::any();
    if c {
        unsafe { (*p).1 = 7 }
    }
    unsafe { assert!((*p).1 == 7) }
}

#[kani::proof]
fn wide_store_in_branch_safe() {
    let p = Box::into_raw(Box::new(0u128));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 << 100 }
    }
    unsafe { assert!(*p == if c { 1 << 100 } else { 0 }) }
}

#[kani::proof]
fn wide_store_in_branch_must_fail() {
    let p = Box::into_raw(Box::new(0u128));
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 << 100 }
    }
    unsafe { assert!(*p == 1 << 100) }
}

#[kani::proof]
fn struct_store_in_branch_safe() {
    let p = Box::into_raw(Box::new(Pair { a: 0, b: 0 }));
    let c: bool = kani::any();
    if c {
        unsafe { *p = Pair { a: 1, b: 2 } }
    }
    unsafe { assert!((*p).a == if c { 1 } else { 0 }) }
}

#[kani::proof]
fn struct_store_in_branch_must_fail() {
    let p = Box::into_raw(Box::new(Pair { a: 0, b: 0 }));
    let c: bool = kani::any();
    if c {
        unsafe { *p = Pair { a: 1, b: 2 } }
    }
    unsafe { assert!((*p).a == 1) }
}

#[kani::proof]
fn atomic_store_in_branch_safe() {
    let a = AtomicU8::new(0);
    let c: bool = kani::any();
    if c {
        a.store(1, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == if c { 1 } else { 0 });
}

#[kani::proof]
fn atomic_store_in_branch_must_fail() {
    let a = AtomicU8::new(0);
    let c: bool = kani::any();
    if c {
        a.store(1, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == 1);
}

#[kani::proof]
fn atomic_fetch_add_in_branch_safe() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        a.fetch_add(2, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == if c { 7 } else { 5 });
}

#[kani::proof]
fn atomic_fetch_add_in_branch_must_fail() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        a.fetch_add(2, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == 7);
}

#[kani::proof]
fn swap_in_branch_safe() {
    let p = Box::into_raw(Box::new(1u8));
    let q = Box::into_raw(Box::new(2u8));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::swap(p, q) }
    }
    unsafe { assert!(*p == if c { 2 } else { 1 }) }
}

#[kani::proof]
fn swap_in_branch_must_fail() {
    let p = Box::into_raw(Box::new(1u8));
    let q = Box::into_raw(Box::new(2u8));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::swap(p, q) }
    }
    unsafe { assert!(*p == 2) }
}

#[kani::proof]
fn copy_in_branch_safe() {
    let src = Box::into_raw(Box::new(3u8));
    let dst = Box::into_raw(Box::new(5u8));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::copy_nonoverlapping(src, dst, 1) }
    }
    unsafe { assert!(*dst == if c { 3 } else { 5 }) }
}

#[kani::proof]
fn copy_in_branch_must_fail() {
    let src = Box::into_raw(Box::new(3u8));
    let dst = Box::into_raw(Box::new(5u8));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::copy_nonoverlapping(src, dst, 1) }
    }
    unsafe { assert!(*dst == 3) }
}

#[kani::proof]
fn write_bytes_in_branch_safe() {
    let p = Box::into_raw(Box::new(5u8));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::write_bytes(p, 7, 1) }
    }
    unsafe { assert!(*p == if c { 7 } else { 5 }) }
}

#[kani::proof]
fn write_bytes_in_branch_must_fail() {
    let p = Box::into_raw(Box::new(5u8));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::write_bytes(p, 7, 1) }
    }
    unsafe { assert!(*p == 7) }
}

#[kani::proof]
fn stack_read_after_store_in_branch_safe() {
    let mut x = 0u8;
    let p = &mut x as *mut u8;
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    let y = unsafe { p.read() };
    assert!(y == if c { 1 } else { 0 });
}

#[kani::proof]
fn stack_read_after_store_in_branch_must_fail() {
    let mut x = 0u8;
    let p = &mut x as *mut u8;
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 }
    }
    let y = unsafe { p.read() };
    assert!(y == 1);
}

#[kani::proof]
fn ref_store_in_branch_then_raw_read_safe() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        let r = unsafe { &mut *p };
        *r = 4;
    }
    unsafe { assert!(*p == if c { 4 } else { 0 }) }
}

#[kani::proof]
fn ref_store_in_branch_then_raw_read_must_fail() {
    let p = Box::into_raw(Box::new(0u8));
    let c: bool = kani::any();
    if c {
        let r = unsafe { &mut *p };
        *r = 4;
    }
    unsafe { assert!(*p == 4) }
}

#[kani::proof]
fn atomic_swap_in_branch_safe() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        a.swap(9, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == if c { 9 } else { 5 });
}

#[kani::proof]
fn atomic_swap_in_branch_must_fail() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        a.swap(9, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == 9);
}

#[kani::proof]
fn atomic_compare_exchange_in_branch_safe() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        let _ = a.compare_exchange(5, 6, Ordering::SeqCst, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == if c { 6 } else { 5 });
}

#[kani::proof]
fn atomic_compare_exchange_in_branch_must_fail() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        let _ = a.compare_exchange(5, 6, Ordering::SeqCst, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == 6);
}

#[kani::proof]
fn atomic_fetch_max_in_branch_safe() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        a.fetch_max(8, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == if c { 8 } else { 5 });
}

#[kani::proof]
fn atomic_fetch_max_in_branch_must_fail() {
    let a = AtomicU8::new(5);
    let c: bool = kani::any();
    if c {
        a.fetch_max(8, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == 8);
}

#[kani::proof]
fn atomic_fetch_nand_in_branch_safe() {
    let a = AtomicU8::new(0b1100);
    let c: bool = kani::any();
    if c {
        a.fetch_nand(0b1010, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == if c { !(0b1100u8 & 0b1010) } else { 0b1100 });
}

#[kani::proof]
fn atomic_fetch_nand_in_branch_must_fail() {
    let a = AtomicU8::new(0b1100);
    let c: bool = kani::any();
    if c {
        a.fetch_nand(0b1010, Ordering::SeqCst);
    }
    assert!(a.load(Ordering::SeqCst) == !(0b1100u8 & 0b1010));
}

#[kani::proof]
fn overlapping_copy_in_branch_safe() {
    let p = Box::into_raw(Box::new([1u8, 2, 3]));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::copy(p as *const u8, (p as *mut u8).add(1), 2) }
    }
    unsafe { assert!((*p)[2] == if c { 2 } else { 3 }) }
}

#[kani::proof]
fn overlapping_copy_in_branch_must_fail() {
    let p = Box::into_raw(Box::new([1u8, 2, 3]));
    let c: bool = kani::any();
    if c {
        unsafe { std::ptr::copy(p as *const u8, (p as *mut u8).add(1), 2) }
    }
    unsafe { assert!((*p)[2] == 2) }
}

#[kani::proof]
fn swap_stack_in_branch_safe() {
    let mut a = 1u8;
    let mut b = 2u8;
    let c: bool = kani::any();
    if c {
        std::mem::swap(&mut a, &mut b);
    }
    assert!(a == if c { 2 } else { 1 });
}

#[kani::proof]
fn swap_stack_in_branch_must_fail() {
    let mut a = 1u8;
    let mut b = 2u8;
    let c: bool = kani::any();
    if c {
        std::mem::swap(&mut a, &mut b);
    }
    assert!(a == 2);
}

#[kani::proof]
fn ref_store_stack_in_branch_then_raw_read_safe() {
    let mut x = 0u8;
    let p = &mut x as *mut u8;
    let c: bool = kani::any();
    if c {
        let r = unsafe { &mut *p };
        *r = 4;
    }
    unsafe { assert!(*p == if c { 4 } else { 0 }) }
}

#[kani::proof]
fn ref_store_stack_in_branch_then_raw_read_must_fail() {
    let mut x = 0u8;
    let p = &mut x as *mut u8;
    let c: bool = kani::any();
    if c {
        let r = unsafe { &mut *p };
        *r = 4;
    }
    unsafe { assert!(*p == 4) }
}

#[kani::proof]
fn wide_stack_store_in_branch_safe() {
    let mut x = 0u128;
    let p = &mut x as *mut u128;
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 << 100 }
    }
    unsafe { assert!(*p == if c { 1 << 100 } else { 0 }) }
}

#[kani::proof]
fn wide_stack_store_in_branch_must_fail() {
    let mut x = 0u128;
    let p = &mut x as *mut u128;
    let c: bool = kani::any();
    if c {
        unsafe { *p = 1 << 100 }
    }
    unsafe { assert!(*p == 1 << 100) }
}
