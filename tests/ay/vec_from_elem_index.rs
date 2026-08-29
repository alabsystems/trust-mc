// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-expect: UNKNOWN
// kani-expect: one_vec_struct_first_read_only=PROOF
// kani-expect: two_vec_struct_first_read_only=PROOF
// kani-expect: vec_from_elem_read=PROOF
// kani-expect: vec_push_then_len=PROOF
// kani-expect: two_vec_struct_push_len_only=PROOF
// kani-expect: vec_push_then_read=PROOF
// NOTE: 9 harness(es) demoted PROOF→UNKNOWN by false proof defense (ay#8578).
//
//! Diagnostic: isolate vec![val; n] + index read/write patterns.
//! Part of #3348: These harnesses test the VecFromElem → Index → IndexMut
//! pipeline in isolation, without struct projection overhead.

/// Minimal: from_elem then read — checks const_array model
#[kani::proof]
fn vec_from_elem_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let idx: usize = kani::any();
    kani::assume(idx < n);

    let v: Vec<bool> = vec![false; n];
    assert!(!v[idx], "vec![false; n] must have false at every index");
}

/// push then len — checks VecPush metadata
#[kani::proof]
fn vec_push_then_len() {
    let mut v: Vec<u32> = Vec::new();
    let val: u32 = kani::any();
    v.push(val);
    assert_eq!(v.len(), 1);
}

/// push then index read — checks VecPush + data model
#[kani::proof]
fn vec_push_then_read() {
    let mut v: Vec<u32> = Vec::new();
    let val: u32 = kani::any();
    v.push(val);
    assert_eq!(v[0], val);
}

/// From_elem then write then read — checks store/select roundtrip
#[kani::proof]
fn vec_from_elem_write_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let idx: usize = kani::any();
    kani::assume(idx < n);

    let mut v: Vec<bool> = vec![false; n];
    v[idx] = true;
    assert!(v[idx], "v[idx] must be true after assignment");
}

/// From_elem u32 then write then read — check with non-bool type
#[kani::proof]
fn vec_from_elem_u32_write_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let idx: usize = kani::any();
    kani::assume(idx < n);

    let mut v: Vec<u32> = vec![0u32; n];
    v[idx] = 42;
    assert_eq!(v[idx], 42);
}

/// From_elem with read-over-write-miss — checks isolation
#[kani::proof]
fn vec_from_elem_isolation() {
    let n: usize = kani::any();
    kani::assume(n >= 2 && n <= 10);
    let i: usize = kani::any();
    let j: usize = kani::any();
    kani::assume(i < n && j < n);
    kani::assume(i != j);

    let mut v: Vec<bool> = vec![false; n];
    v[i] = true;

    assert!(v[i], "written index must be true");
    assert!(!v[j], "other index must still be false");
}

/// Struct-embedded Vec store + read (no push/len).
/// Tests C2 flattened struct-projected IndexMut store propagation.
/// Part of #3439.
#[kani::proof]
fn struct_vec_store_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    struct S {
        data: Vec<bool>,
    }

    let mut s = S { data: vec![false; n] };
    s.data[var] = true;
    assert!(s.data[var]);
}

/// Two-Vec struct — tests struct field projection with Vec members
#[kani::proof]
fn two_vec_struct_mark() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    struct Marks {
        data: Vec<bool>,
        indices: Vec<usize>,
    }

    let mut m = Marks { data: vec![false; n], indices: Vec::new() };

    assert!(!m.data[var]);
    m.data[var] = true;
    m.indices.push(var);
    assert!(m.data[var]);
    assert_eq!(m.indices.len(), 1);
}

/// DIAG: Isolate write+read without push (test IndexMut carry-forward)
/// Expected: PROOF if IndexMut + subsequent read work for 2-Vec struct
#[kani::proof]
fn two_vec_struct_write_read_only() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    struct Marks {
        data: Vec<bool>,
        indices: Vec<usize>,
    }

    let mut m = Marks { data: vec![false; n], indices: Vec::new() };

    assert!(!m.data[var]);
    m.data[var] = true;
    assert!(m.data[var]);
}

/// DIAG: Isolate push+len without IndexMut write
/// Expected: PROOF if VecPush + VecLen work for 2-Vec struct
#[kani::proof]
fn two_vec_struct_push_len_only() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    struct Marks {
        data: Vec<bool>,
        indices: Vec<usize>,
    }

    let mut m = Marks { data: vec![false; n], indices: Vec::new() };

    m.indices.push(var);
    assert_eq!(m.indices.len(), 1);
}

/// DIAG: Single-Vec struct first read only.
/// Expected: PROOF if vec_from_elem + struct + read works for 1-Vec struct
#[kani::proof]
fn one_vec_struct_first_read_only() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    struct S {
        data: Vec<bool>,
    }

    let s = S { data: vec![false; n] };

    assert!(!s.data[var]);
}

/// DIAG: first read only (no write, no push)
/// Expected: PROOF if vec_from_elem + read works
#[kani::proof]
fn two_vec_struct_first_read_only() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    struct Marks {
        data: Vec<bool>,
        indices: Vec<usize>,
    }

    let mut m = Marks { data: vec![false; n], indices: Vec::new() };

    assert!(!m.data[var]);
}

/// DIAG: write + push + read (no len check)
/// Expected: PROOF if VecPush doesn't corrupt data Vec state
#[kani::proof]
fn two_vec_struct_write_push_read() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n <= 10);
    let var: usize = kani::any();
    kani::assume(var < n);

    struct Marks {
        data: Vec<bool>,
        indices: Vec<usize>,
    }

    let mut m = Marks { data: vec![false; n], indices: Vec::new() };

    assert!(!m.data[var]);
    m.data[var] = true;
    m.indices.push(var);
    assert!(m.data[var]);
}
