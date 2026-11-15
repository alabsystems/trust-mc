// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: element stores through `&mut [T; N]` / `&mut [T]` made by every
// shape that is NOT the plain `(*r)[i] = v` edec8fd8a handles: a field after the
// index, a compound assignment, `swap`, `mem::swap` of two elements, `fill`,
// `reverse`, `iter_mut`, `first_mut`, `split_at_mut`, `get_mut`, a raw `add().write`,
// `copy_within`, a symbolic 2-D index, a `&mut &mut [T; N]`, an `Option<&mut [T; N]>`,
// a loop with a symbolic bound, and a store through the reference followed by a
// read through the SAME reference.
//
// Written by the adversarial review of m3/soundness-fixes-2 (2026-09-13) around
// edec8fd8a (try_codegen_assign_ref_deref_index) and 212720222 (reborrow
// metadata): every store must reach the referent, or the harness must fail closed.
//
// Oracle (per harness):
//   *_must_fail   -> VERIFICATION:- FAILED (assertion); never SUCCESSFUL
//   *_safe        -> never a Genuine counterexample

#[derive(Clone, Copy)]
struct P {
    x: u8,
    y: u8,
}

#[kani::proof]
fn field_after_index_store_safe() {
    let mut a = [P { x: 1, y: 2 }, P { x: 3, y: 4 }];
    {
        let r: &mut [P; 2] = &mut a;
        r[1].x = 9;
    }
    assert!(a[1].x == 9 && a[1].y == 4 && a[0].x == 1);
}

#[kani::proof]
fn field_after_index_store_must_fail() {
    let mut a = [P { x: 1, y: 2 }, P { x: 3, y: 4 }];
    {
        let r: &mut [P; 2] = &mut a;
        r[1].x = 9;
    }
    assert!(a[1].x == 3);
}

#[kani::proof]
fn compound_index_store_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        r[0] += 5;
    }
    assert!(a[0] == 6 && a[1] == 2);
}

#[kani::proof]
fn compound_index_store_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        r[0] += 5;
    }
    assert!(a[0] == 1);
}

#[kani::proof]
fn swap_through_ref_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        r.swap(0, 1);
    }
    assert!(a[0] == 2 && a[1] == 1);
}

#[kani::proof]
fn swap_through_ref_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        r.swap(0, 1);
    }
    assert!(a[0] == 1);
}

#[kani::proof]
fn mem_swap_elems_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        let (lo, hi) = r.split_at_mut(1);
        std::mem::swap(&mut lo[0], &mut hi[0]);
    }
    assert!(a[0] == 2 && a[1] == 1);
}

#[kani::proof]
fn mem_swap_elems_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        let (lo, hi) = r.split_at_mut(1);
        std::mem::swap(&mut lo[0], &mut hi[0]);
    }
    assert!(a[1] == 2);
}

#[kani::proof]
fn fill_through_ref_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        r.fill(0);
    }
    assert!(a[0] == 0 && a[1] == 0);
}

#[kani::proof]
fn fill_through_ref_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        r.fill(0);
    }
    assert!(a[1] == 2);
}

#[kani::proof]
fn reverse_through_ref_safe() {
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8; 3] = &mut a;
        r.reverse();
    }
    assert!(a == [3, 2, 1]);
}

#[kani::proof]
fn reverse_through_ref_must_fail() {
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8; 3] = &mut a;
        r.reverse();
    }
    assert!(a[0] == 1);
}

#[kani::proof]
fn iter_mut_through_ref_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        for x in r.iter_mut() {
            *x = 0;
        }
    }
    assert!(a[0] == 0 && a[1] == 0);
}

#[kani::proof]
fn iter_mut_through_ref_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        for x in r.iter_mut() {
            *x = 0;
        }
    }
    assert!(a[1] == 2);
}

#[kani::proof]
fn first_mut_through_ref_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8] = &mut a;
        if let Some(x) = r.first_mut() {
            *x = 9;
        }
    }
    assert!(a[0] == 9 && a[1] == 2);
}

#[kani::proof]
fn first_mut_through_ref_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8] = &mut a;
        if let Some(x) = r.first_mut() {
            *x = 9;
        }
    }
    assert!(a[0] == 1);
}

#[kani::proof]
fn split_at_mut_store_safe() {
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8] = &mut a;
        let (lo, hi) = r.split_at_mut(1);
        lo[0] = 7;
        hi[1] = 9;
    }
    assert!(a == [7, 2, 9]);
}

#[kani::proof]
fn split_at_mut_store_must_fail() {
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8] = &mut a;
        let (lo, hi) = r.split_at_mut(1);
        lo[0] = 7;
        hi[1] = 9;
    }
    assert!(a[2] == 3);
}

#[kani::proof]
fn get_mut_store_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        if let Some(x) = r.get_mut(1) {
            *x = 9;
        }
    }
    assert!(a[1] == 9 && a[0] == 1);
}

#[kani::proof]
fn get_mut_store_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        if let Some(x) = r.get_mut(1) {
            *x = 9;
        }
    }
    assert!(a[1] == 2);
}

#[kani::proof]
fn raw_add_write_through_ref_safe() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        unsafe { r.as_mut_ptr().add(1).write(9) };
    }
    assert!(a[1] == 9 && a[0] == 1);
}

#[kani::proof]
fn raw_add_write_through_ref_must_fail() {
    let mut a = [1u8, 2];
    {
        let r: &mut [u8; 2] = &mut a;
        unsafe { r.as_mut_ptr().add(1).write(9) };
    }
    assert!(a[1] == 2);
}

#[kani::proof]
fn copy_within_through_ref_safe() {
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8] = &mut a;
        r.copy_within(0..2, 1);
    }
    assert!(a == [1, 1, 2]);
}

#[kani::proof]
fn copy_within_through_ref_must_fail() {
    let mut a = [1u8, 2, 3];
    {
        let r: &mut [u8] = &mut a;
        r.copy_within(0..2, 1);
    }
    assert!(a[2] == 3);
}

#[kani::proof]
fn grid_symbolic_store_safe() {
    let mut g = [[0u8; 2]; 2];
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let r: &mut [[u8; 2]; 2] = &mut g;
        r[i][1] = 9;
    }
    assert!(g[i][1] == 9 && g[i][0] == 0 && g[1 - i][1] == 0);
}

#[kani::proof]
fn grid_symbolic_store_must_fail() {
    let mut g = [[0u8; 2]; 2];
    let i: usize = kani::any();
    kani::assume(i < 2);
    {
        let r: &mut [[u8; 2]; 2] = &mut g;
        r[i][1] = 9;
    }
    assert!(g[i][1] == 0);
}

#[kani::proof]
fn double_ref_index_store_safe() {
    let mut a = [1u8, 2];
    {
        let mut r: &mut [u8; 2] = &mut a;
        let rr: &mut &mut [u8; 2] = &mut r;
        rr[0] = 9;
    }
    assert!(a[0] == 9 && a[1] == 2);
}

#[kani::proof]
fn double_ref_index_store_must_fail() {
    let mut a = [1u8, 2];
    {
        let mut r: &mut [u8; 2] = &mut a;
        let rr: &mut &mut [u8; 2] = &mut r;
        rr[0] = 9;
    }
    assert!(a[0] == 1);
}

#[kani::proof]
fn option_ref_index_store_safe() {
    let mut a = [1u8, 2];
    let c: bool = kani::any();
    {
        let o: Option<&mut [u8; 2]> = if c { Some(&mut a) } else { None };
        if let Some(r) = o {
            r[1] = 9;
        }
    }
    assert!(a[1] == if c { 9 } else { 2 });
}

#[kani::proof]
fn option_ref_index_store_must_fail() {
    let mut a = [1u8, 2];
    let c: bool = kani::any();
    {
        let o: Option<&mut [u8; 2]> = if c { Some(&mut a) } else { None };
        if let Some(r) = o {
            r[1] = 9;
        }
    }
    assert!(a[1] == 2);
}

#[kani::proof]
#[kani::unwind(5)]
fn loop_index_store_safe() {
    let mut a = [0u8; 3];
    let n: usize = kani::any();
    kani::assume(n <= 3);
    {
        let r: &mut [u8; 3] = &mut a;
        let mut i = 0;
        while i < n {
            r[i] = 7;
            i += 1;
        }
    }
    assert!((n == 0 || a[0] == 7) && (n == 3 || a[2] == 0));
}

#[kani::proof]
#[kani::unwind(5)]
fn loop_index_store_must_fail() {
    let mut a = [0u8; 3];
    let n: usize = kani::any();
    kani::assume(n >= 1 && n <= 3);
    {
        let r: &mut [u8; 3] = &mut a;
        let mut i = 0;
        while i < n {
            r[i] = 7;
            i += 1;
        }
    }
    assert!(a[0] == 0);
}

#[kani::proof]
fn store_then_read_same_ref_safe() {
    let mut a = [1u8, 2];
    let r: &mut [u8; 2] = &mut a;
    r[1] = 9;
    let v = r[1];
    assert!(v == 9 && r[0] == 1);
}

#[kani::proof]
fn store_then_read_same_ref_must_fail() {
    let mut a = [1u8, 2];
    let r: &mut [u8; 2] = &mut a;
    r[1] = 9;
    assert!(r[1] == 2);
}

#[kani::proof]
fn unsized_param_symbolic_store_safe() {
    fn set(s: &mut [u8], i: usize, v: u8) {
        s[i] = v;
    }
    let mut a = [1u8, 2, 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    set(&mut a, i, 9);
    assert!(a[i] == 9 && (i == 0 || a[0] == 1));
}

#[kani::proof]
fn unsized_param_symbolic_store_must_fail() {
    fn set(s: &mut [u8], i: usize, v: u8) {
        s[i] = v;
    }
    let mut a = [1u8, 2, 3];
    let i: usize = kani::any();
    kani::assume(i < 3);
    set(&mut a, i, 9);
    assert!(a[1] == 2);
}
