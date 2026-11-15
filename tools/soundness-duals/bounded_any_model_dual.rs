// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// T4a review dual (fix/chc-row72-small, 2026-09-24): the native model of
// `<Vec<T> | String as kani::BoundedArbitrary>::bounded_any` left out library
// behaviour and proved each `*_bug` harness below clean (or certified a `*_safe`
// harness Genuine) where the library path had not:
// - a zero-sized element: std reports `capacity() == usize::MAX`, the model N;
// - an element with `Drop`: the library's `truncate` drops elements len..N;
// - a hand-written `Arbitrary` that panics inside `any()` or restricts values
//   by arithmetic, which the derive check (calls only) read as unconstrained;
// - a model-built `String`: the lane's `String` drop is a no-op, so a use after
//   free through `as_ptr()` was proved clean.
// Oracle: upstream Kani 0.67 corpus-rev build (~/tmc-measure/kani-src):
// every `*_bug` VERIFICATION:- FAILED, every `*_safe` VERIFICATION:- SUCCESSFUL.
// `derived_len_bound_safe` is a false Genuine certificate on the library path
// too (known red, pre-existing).

#[kani::proof]
fn zst_unit_cap_bug() {
    let v: Vec<()> = kani::bounded_any::<_, 3>();
    assert!(v.capacity() <= 3);
}

#[kani::proof]
fn zst_arr0_cap_bug() {
    let v: Vec<[u8; 0]> = kani::bounded_any::<_, 3>();
    assert!(v.capacity() == 3);
}

#[kani::proof]
fn u8_cap_safe() {
    let v: Vec<u8> = kani::bounded_any::<_, 3>();
    assert!(v.capacity() == 3);
}

#[derive(kani::BoundedArbitrary)]
struct ZstField {
    #[bounded]
    v: Vec<()>,
}

#[kani::proof]
fn derived_zst_cap_bug() {
    let z: ZstField = kani::bounded_any::<_, 3>();
    assert!(z.v.capacity() <= 3);
}

#[derive(kani::Arbitrary)]
struct AssertOnDrop(u8);
impl Drop for AssertOnDrop {
    fn drop(&mut self) {
        assert!(self.0 != 7, "dropped a seven");
    }
}

#[kani::proof]
#[kani::unwind(4)]
fn truncate_drop_assert_bug() {
    let v: Vec<AssertOnDrop> = kani::bounded_any::<_, 2>();
    core::mem::forget(v);
}

#[kani::proof]
#[kani::unwind(4)]
fn option_truncate_drop_bug() {
    let o: Option<Vec<AssertOnDrop>> = kani::bounded_any::<_, 2>();
    core::mem::forget(o);
}

static mut DROPS: u32 = 0;
#[derive(kani::Arbitrary)]
struct CountOnDrop(u8);
impl Drop for CountOnDrop {
    fn drop(&mut self) {
        unsafe {
            DROPS += 1;
        }
    }
}

#[kani::proof]
#[kani::unwind(4)]
fn truncate_drop_count_bug() {
    let v: Vec<CountOnDrop> = kani::bounded_any::<_, 2>();
    core::mem::forget(v);
    assert!(unsafe { DROPS } == 0);
}

#[derive(Clone, Copy)]
struct Inc(u8);
impl kani::Arbitrary for Inc {
    fn any() -> Self {
        let x: u8 = kani::any();
        Inc(x + 1)
    }
}

#[kani::proof]
fn manual_any_overflow_bug() {
    let v: Vec<Inc> = kani::bounded_any::<_, 2>();
    assert!(v.len() <= 2);
}

#[derive(Clone, Copy)]
struct Idx(u8);
impl kani::Arbitrary for Idx {
    fn any() -> Self {
        let x: u8 = kani::any();
        let t = [1u8, 2, 3, 4];
        Idx(t[x as usize])
    }
}

#[kani::proof]
fn manual_any_index_oob_bug() {
    let v: Vec<Idx> = kani::bounded_any::<_, 2>();
    assert!(v.len() <= 2);
}

#[derive(Clone, Copy)]
struct Small(u8);
impl kani::Arbitrary for Small {
    fn any() -> Self {
        let x: u8 = kani::any();
        Small(x & 3)
    }
}

#[kani::proof]
fn masked_pop_safe() {
    let mut v: Vec<Small> = kani::bounded_any::<_, 2>();
    if let Some(s) = v.pop() {
        assert!(s.0 < 4);
    }
}

#[kani::proof]
fn masked_copy_index_safe() {
    let v: Vec<Small> = kani::bounded_any::<_, 2>();
    if v.len() > 0 {
        let s = v[0];
        assert!(s.0 < 4);
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn string_uaf_bug() {
    let s: String = kani::bounded_any::<_, 3>();
    if !s.is_empty() {
        let p = s.as_ptr();
        drop(s);
        let _x = unsafe { *p };
    }
}

#[derive(kani::BoundedArbitrary)]
struct BoundedBytes {
    #[bounded]
    v: Vec<u8>,
}

#[kani::proof]
fn derived_len_bound_safe() {
    let w: BoundedBytes = kani::bounded_any::<_, 2>();
    assert!(w.v.len() <= 2);
}

#[kani::proof]
fn derived_len_reach_bug() {
    let w: BoundedBytes = kani::bounded_any::<_, 2>();
    assert!(w.v.len() != 2);
}
