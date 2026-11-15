// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: a store through a pointer chosen on a path — a three-arm
// `match`, a loop reassignment, an array of `&mut`, `mem::swap` of two `&mut`,
// an `Option<&mut T>`, a struct holding the chosen `&mut`, a callee returning
// one of two `&mut`, a compound assignment, pointers to array elements, a nested
// join and a raw pointer.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-12) around
// b0ec37052 (the BMC reference-pointee table follows the control flow; merged
// pointers fail closed) and cf6685810 (CHC resolves a path-chosen pointer from
// its state variable).
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

struct H<'x> {
    p: &'x mut u8,
}

fn pick<'x>(a: &'x mut u8, b: &'x mut u8, c: bool) -> &'x mut u8 {
    if c { a } else { b }
}

#[kani::proof]
fn match_three_arms_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let mut c = 0u8;
    let k: u8 = kani::any();
    {
        let p = match k {
            0 => &mut a,
            1 => &mut b,
            _ => &mut c,
        };
        *p = 7;
    }
    assert!(match k {
        0 => a == 7 && b == 0 && c == 0,
        1 => b == 7 && a == 0 && c == 0,
        _ => c == 7 && a == 0 && b == 0,
    });
}

#[kani::proof]
fn match_three_arms_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let mut c = 0u8;
    let k: u8 = kani::any();
    {
        let p = match k {
            0 => &mut a,
            1 => &mut b,
            _ => &mut c,
        };
        *p = 7;
    }
    assert!(a == 7);
}

#[kani::proof]
#[kani::unwind(4)]
fn loop_reassign_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let n: u8 = kani::any();
    kani::assume(n < 3);
    {
        let mut p = &mut a;
        let mut i = 0u8;
        while i < n {
            p = &mut b;
            i += 1;
        }
        *p = 7;
    }
    assert!(if n == 0 { a == 7 && b == 0 } else { b == 7 && a == 0 });
}

#[kani::proof]
#[kani::unwind(4)]
fn loop_reassign_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let n: u8 = kani::any();
    kani::assume(n < 3);
    {
        let mut p = &mut a;
        let mut i = 0u8;
        while i < n {
            p = &mut b;
            i += 1;
        }
        *p = 7;
    }
    assert!(a == 7);
}

#[kani::proof]
fn array_of_refs_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let mut ptrs: [&mut u8; 2] = [&mut a, &mut b];
        *ptrs[i] = 7;
    }
    assert!(if i == 0 { a == 7 && b == 0 } else { b == 7 && a == 0 });
}

#[kani::proof]
fn array_of_refs_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let mut ptrs: [&mut u8; 2] = [&mut a, &mut b];
        *ptrs[i] = 7;
    }
    assert!(a == 7);
}

#[kani::proof]
fn swap_refs_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    {
        let mut p = &mut a;
        let mut q = &mut b;
        std::mem::swap(&mut p, &mut q);
        *p = 7;
        *q = 3;
    }
    assert!(b == 7 && a == 3);
}

#[kani::proof]
fn swap_refs_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    {
        let mut p = &mut a;
        let mut q = &mut b;
        std::mem::swap(&mut p, &mut q);
        *p = 7;
        *q = 3;
    }
    assert!(a == 7);
}

#[kani::proof]
fn option_ref_store_safe() {
    let mut a = 0u8;
    let c: bool = kani::any();
    {
        let o: Option<&mut u8> = if c { Some(&mut a) } else { None };
        if let Some(r) = o {
            *r = 7;
        }
    }
    assert!(a == if c { 7 } else { 0 });
}

#[kani::proof]
fn option_ref_store_must_fail() {
    let mut a = 0u8;
    let c: bool = kani::any();
    {
        let o: Option<&mut u8> = if c { Some(&mut a) } else { None };
        if let Some(r) = o {
            *r = 7;
        }
    }
    assert!(a == 7);
}

#[kani::proof]
fn struct_holder_chosen_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    {
        let mut h = if c { H { p: &mut a } } else { H { p: &mut b } };
        *h.p = 7;
    }
    assert!(if c { a == 7 && b == 0 } else { b == 7 && a == 0 });
}

#[kani::proof]
fn struct_holder_chosen_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    {
        let mut h = if c { H { p: &mut a } } else { H { p: &mut b } };
        *h.p = 7;
    }
    assert!(a == 7);
}

#[kani::proof]
fn pick_fn_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    *pick(&mut a, &mut b, c) = 7;
    assert!(if c { a == 7 && b == 0 } else { b == 7 && a == 0 });
}

#[kani::proof]
fn pick_fn_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    *pick(&mut a, &mut b, c) = 7;
    assert!(a == 7);
}

#[kani::proof]
fn compound_assign_merged_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    {
        let p = if c { &mut a } else { &mut b };
        *p += 5;
    }
    assert!(if c { a == 5 && b == 0 } else { b == 5 && a == 0 });
}

#[kani::proof]
fn compound_assign_merged_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    {
        let p = if c { &mut a } else { &mut b };
        *p += 5;
    }
    assert!(a == 5);
}

#[kani::proof]
fn array_elem_ptr_merged_safe() {
    let mut arr = [0u8; 2];
    let c: bool = kani::any();
    {
        let p = if c { &mut arr[0] } else { &mut arr[1] };
        *p = 7;
    }
    assert!(if c { arr[0] == 7 && arr[1] == 0 } else { arr[1] == 7 && arr[0] == 0 });
}

#[kani::proof]
fn array_elem_ptr_merged_must_fail() {
    let mut arr = [0u8; 2];
    let c: bool = kani::any();
    {
        let p = if c { &mut arr[0] } else { &mut arr[1] };
        *p = 7;
    }
    assert!(arr[0] == 7);
}

#[kani::proof]
fn merged_read_through_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    let p = if c { &mut a } else { &mut b };
    *p = 7;
    assert!(*p == 7);
}

#[kani::proof]
fn merged_read_through_other_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    {
        let p = if c { &mut a } else { &mut b };
        *p = 7;
    }
    let q = &a;
    assert!(*q == 7);
}

#[kani::proof]
fn nested_merge_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let mut d = 0u8;
    let c1: bool = kani::any();
    let c2: bool = kani::any();
    {
        let inner = if c1 { &mut a } else { &mut b };
        let outer = if c2 { inner } else { &mut d };
        *outer = 7;
    }
    assert!(if c2 {
        if c1 { a == 7 && b == 0 && d == 0 } else { b == 7 && a == 0 && d == 0 }
    } else {
        d == 7 && a == 0 && b == 0
    });
}

#[kani::proof]
fn nested_merge_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let mut d = 0u8;
    let c1: bool = kani::any();
    let c2: bool = kani::any();
    {
        let inner = if c1 { &mut a } else { &mut b };
        let outer = if c2 { inner } else { &mut d };
        *outer = 7;
    }
    assert!(a == 7);
}

#[kani::proof]
fn raw_ptr_merged_store_safe() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    let p: *mut u8 = if c { &mut a } else { &mut b };
    unsafe { *p = 7 };
    assert!(if c { a == 7 && b == 0 } else { b == 7 && a == 0 });
}

#[kani::proof]
fn raw_ptr_merged_store_must_fail() {
    let mut a = 0u8;
    let mut b = 0u8;
    let c: bool = kani::any();
    let p: *mut u8 = if c { &mut a } else { &mut b };
    unsafe { *p = 7 };
    assert!(a == 7);
}
