// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

// User ADTs with library wrapper names must retain both ordinary fields.
mod user {
    #[repr(C)]
    pub struct Mutex<T> {
        pub tag: u32,
        pub value: T,
    }

    #[repr(C)]
    pub struct RefCell<T> {
        pub tag: u32,
        pub value: T,
    }

    #[repr(C)]
    pub struct NonNull<T> {
        pub tag: u32,
        pub value: T,
    }

    pub const NON_NULL_VALUE: NonNull<u32> = NonNull { tag: 7, value: 11 };

    #[inline(never)]
    pub fn constant_fields(value: NonNull<u32>) -> bool {
        value.tag == 7 && value.value == 11
    }

    #[inline(never)]
    pub fn move_mutex(value: Mutex<u32>) -> Mutex<u32> {
        value
    }

    #[inline(never)]
    pub fn move_refcell(value: RefCell<u32>) -> RefCell<u32> {
        value
    }

    #[inline(never)]
    pub fn view_mutex(value: &Mutex<u32>, expected: u32) -> bool {
        value.tag == 7 && value.value == expected
    }

    #[inline(never)]
    pub fn view_refcell(value: &RefCell<u32>, expected: u32) -> bool {
        value.tag == 7 && value.value == expected
    }
}

// A reexport preserves the real compiler-library wrapper's identity.
mod exports {
    pub use std::cell::Cell as CellAlias;
    pub use std::mem::ManuallyDrop as ManuallyDropAlias;
}

#[kani::proof]
fn mutex_move_safe() {
    let value: u32 = kani::any();
    let original = user::Mutex { tag: 7u32, value };
    let moved = user::move_mutex(original);
    assert!(moved.tag == 7 && moved.value == value);
}

#[kani::proof]
fn mutex_move_bug() {
    let value: u32 = kani::any();
    let original = user::Mutex { tag: 7u32, value };
    let moved = user::move_mutex(original);
    assert!(moved.tag == 8 && moved.value == value);
}

#[kani::proof]
fn mutex_ref_safe() {
    let value: u32 = kani::any();
    let original = user::Mutex { tag: 7u32, value };
    let view = &original;
    assert!(user::view_mutex(view, value));
}

#[kani::proof]
fn mutex_ref_bug() {
    let value: u32 = kani::any();
    let original = user::Mutex { tag: 7u32, value };
    let view = &original;
    assert!(!user::view_mutex(view, value));
}

#[kani::proof]
fn refcell_move_safe() {
    let value: u32 = kani::any();
    let original = user::RefCell { tag: 7u32, value };
    let moved = user::move_refcell(original);
    assert!(moved.tag == 7 && moved.value == value);
}

#[kani::proof]
fn refcell_move_bug() {
    let value: u32 = kani::any();
    let original = user::RefCell { tag: 7u32, value };
    let moved = user::move_refcell(original);
    assert!(moved.tag == 8 && moved.value == value);
}

#[kani::proof]
fn refcell_ref_safe() {
    let value: u32 = kani::any();
    let original = user::RefCell { tag: 7u32, value };
    let view = &original;
    assert!(user::view_refcell(view, value));
}

#[kani::proof]
fn refcell_ref_bug() {
    let value: u32 = kani::any();
    let original = user::RefCell { tag: 7u32, value };
    let view = &original;
    assert!(!user::view_refcell(view, value));
}

#[kani::proof]
fn nonnull_constant_safe() {
    assert!(user::constant_fields(user::NON_NULL_VALUE));
}

#[kani::proof]
fn nonnull_constant_bug() {
    assert!(!user::constant_fields(user::NON_NULL_VALUE));
}

#[kani::proof]
fn native_md_safe() {
    let value: u32 = kani::any();
    let wrapped = exports::ManuallyDropAlias::new(value);
    assert!(*wrapped == value);
}

#[kani::proof]
fn native_md_bug() {
    let value: u32 = kani::any();
    let wrapped = exports::ManuallyDropAlias::new(value);
    assert!(*wrapped != value);
}

#[kani::proof]
fn native_cell_safe() {
    let value: u32 = kani::any();
    let wrapped = exports::CellAlias::new(value);
    assert!(wrapped.get() == value);
}

#[kani::proof]
fn native_cell_bug() {
    let value: u32 = kani::any();
    let wrapped = exports::CellAlias::new(value);
    assert!(wrapped.get() != value);
}
