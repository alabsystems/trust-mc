// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z mem-predicates

// Primitive physical writes preserve buffer bytes and owner metadata. Logical
// model reads after such a write retain a target-bound refusal until coherent.

#[kani::proof]
pub fn primitive_u8_store_fresh_getter_safe() {
    let mut values = vec![1u8];
    unsafe {
        *values.as_mut_ptr() = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[kani::proof]
pub fn primitive_u8_store_fresh_getter_bug() {
    let mut values = vec![1u8];
    unsafe {
        *values.as_mut_ptr() = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 1);
}

use std::vec::Vec as ReexportedVec;

#[kani::proof]
pub fn primitive_copied_pointer_fresh_getter_safe() {
    let mut values: ReexportedVec<u64> = vec![1u64];
    let pointer = values.as_mut_ptr();
    let copied = pointer;
    unsafe {
        *copied = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[kani::proof]
pub fn primitive_buffer_store_preserves_owner_header_safe() {
    let mut values = vec![1u64];
    let original = values.as_ptr();
    let capacity = values.capacity();
    unsafe {
        *values.as_mut_ptr() = 9;
    }
    assert!(values.len() == 1);
    assert!(values.capacity() == capacity);
    assert!(original == values.as_ptr());
    assert!(unsafe { *values.as_ptr() } == 9);
}

mod fake {
    #[repr(C)]
    pub struct Vec {
        pub value: u64,
        pub other: u64,
    }
    impl Vec {
        pub fn as_mut_ptr(&mut self) -> *mut u64 {
            &raw mut self.value
        }
        pub fn as_ptr(&self) -> *const u64 {
            &raw const self.value
        }
    }
}

#[kani::proof]
pub fn user_vec_fields_store_safe() {
    let mut values = fake::Vec { value: 1, other: 2 };
    unsafe {
        *values.as_mut_ptr() = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 9 && values.other == 2);
}

#[kani::proof]
pub fn user_vec_fields_store_bug() {
    let mut values = fake::Vec { value: 1, other: 2 };
    unsafe {
        *values.as_mut_ptr() = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 1);
}

// The next twin is semantically old-value Bug/new-value Safe. Both contracts
// require own reverse-alias refusal and incomplete VC, with no semantic credit.
#[kani::proof]
pub fn shared_old3_bug_reverse_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    unsafe {
        *pointer = 9;
    }
    assert!(r[0] == 3);
}

#[kani::proof]
pub fn shared_new9_safe_reverse_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    unsafe {
        *pointer = 9;
    }
    assert!(r[0] == 9);
}

#[kani::proof]
pub fn shared_header_queries_then_fresh_raw_read_safe() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    let r = &values;
    unsafe {
        *pointer = 9;
    }
    assert!(r.len() == 1);
    assert!(r.capacity() >= 1);
    assert!(unsafe { *r.as_ptr() } == 9);
}

// Custody does not excuse a possible reallocation between getter and store.
#[kani::proof]
pub fn growth_before_primitive_store_refusal() {
    let mut values = vec![3u8];
    let pointer = values.as_mut_ptr();
    values.push(4);
    unsafe {
        *pointer = 9;
    }
    assert!(unsafe { *values.as_ptr() } == 9);
}

// Similar helper names grant no trusted byte-effect permissions.
mod shadow_name_authority {
    pub mod mem_init {
        #[inline(never)]
        pub fn grow(v: &mut Vec<u64>) {
            v.push(4);
        }
        #[inline(never)]
        pub unsafe fn read(p: *const u64) -> u64 {
            unsafe { *p }
        }
        #[inline(never)]
        pub unsafe fn write(p: *mut u64, value: u64) {
            unsafe {
                *p = value;
            }
        }
    }
    pub mod ub_checks {
        #[inline(never)]
        pub unsafe fn inspect(p: *const u64) -> u64 {
            unsafe { *p }
        }
    }
    #[inline(never)]
    pub unsafe fn add(p: *const u64) -> u64 {
        unsafe { *p }
    }
    #[inline(never)]
    pub unsafe fn write_bytes(p: *mut u64, value: u64) {
        unsafe {
            *p = value;
        }
    }
}

#[kani::proof]
pub fn shadow_name_read_after_growth_refusal() {
    let mut v = vec![3u64];
    v.push(4);
    let p = v.as_ptr();
    assert!(unsafe { shadow_name_authority::mem_init::read(p) } == 3);
}
#[kani::proof]
pub fn shadow_name_write_after_growth_refusal() {
    let mut v = vec![3u64];
    v.push(4);
    let p = v.as_mut_ptr();
    unsafe {
        shadow_name_authority::mem_init::write(p, 9);
    }
    assert!(v[0] == 9);
}
#[kani::proof]
pub fn shadow_name_write_then_model_refusal() {
    let mut v = vec![3u64];
    let p = v.as_mut_ptr();
    unsafe {
        shadow_name_authority::mem_init::write(p, 9);
    }
    assert!(v[0] == 9);
}
#[kani::proof]
pub fn shadow_name_write_bytes_then_model_refusal() {
    let mut v = vec![3u64];
    let p = v.as_mut_ptr();
    unsafe {
        shadow_name_authority::write_bytes(p, 9);
    }
    assert!(v[0] == 9);
}

// Native-prescan-only extra controls. Do not register these as semantic proofs.
pub fn shadow_name_add_after_growth_refusal() {
    let mut v = vec![3u64];
    v.push(4);
    let p = v.as_ptr();
    assert!(unsafe { shadow_name_authority::add(p) } == 3);
}
pub fn shadow_name_ub_after_growth_refusal() {
    let mut v = vec![3u64];
    v.push(4);
    let p = v.as_ptr();
    assert!(unsafe { shadow_name_authority::ub_checks::inspect(p) } == 3);
}
pub fn shadow_name_preborrowed_grow_refusal() {
    let mut v = vec![3u64];
    let receiver = &mut v;
    let p = receiver.as_ptr();
    shadow_name_authority::mem_init::grow(receiver);
    assert!(unsafe { *p } == 3);
}
