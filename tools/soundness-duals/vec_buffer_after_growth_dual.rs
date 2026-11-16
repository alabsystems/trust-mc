// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z mem-predicates

// Taking a fresh pointer cannot synchronize a logical Vec mutation with
// physical buffer bytes/extent. These cases retain an explicit refusal.
#[kani::proof]
pub fn append_then_getter_read_refusal() {
    let mut dst = vec![0u64];
    let mut src = vec![3u64];
    dst.append(&mut src);
    let pointer = dst.as_ptr();
    assert!(unsafe { *pointer.add(1) } == 3);
}

#[kani::proof]
pub fn append_then_getter_extent_refusal() {
    let mut dst = vec![0u64];
    let mut src = vec![3u64];
    dst.append(&mut src);
    let pointer = unsafe { dst.as_ptr().add(1) };
    assert!(kani::mem::can_dereference(pointer));
}

#[kani::proof]
pub fn push_then_getter_read_refusal() {
    let mut values = vec![1u64];
    values.push(2);
    assert!(unsafe { *values.as_ptr().add(1) } == 2);
}

#[kani::proof]
pub fn index_then_getter_read_refusal() {
    let mut values = vec![1u64];
    values[0] = 9;
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[kani::proof]
pub fn mutation_then_move_then_getter_refusal() {
    let mut values = vec![1u64];
    values[0] = 9;
    let moved = values;
    assert!(unsafe { *moved.as_ptr() } == 9);
}

#[kani::proof]
pub fn mutation_then_owner_reference_getter_refusal() {
    let mut values = vec![1u64];
    values.push(2);
    let owner = &mut values;
    assert!(unsafe { *owner.as_ptr().add(1) } == 2);
}

#[kani::proof]
pub fn mutation_then_raw_owner_getter_refusal() {
    let mut values = vec![1u64];
    values.push(2);
    let owner = &raw mut values;
    assert!(unsafe { *(&*owner).as_ptr().add(1) } == 2);
}

mod mem_init {
    #[inline(never)]
    pub fn mutate(values: &mut Vec<u64>) { values[0] = 9; }
    #[inline(never)]
    pub unsafe fn mutate_raw(values: *mut Vec<u64>) { unsafe { (&mut *values)[0] = 9; } }
}

#[kani::proof]
pub fn local_shadow_name_then_getter_refusal() {
    let mut values = vec![1u64];
    mem_init::mutate(&mut values);
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[kani::proof]
pub fn local_shadow_raw_name_then_getter_refusal() {
    let mut values = vec![1u64];
    unsafe { mem_init::mutate_raw(&raw mut values); }
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[kani::proof]
pub fn unchanged_getter_safe() {
    let values = vec![1u64];
    assert!(unsafe { *values.as_ptr() } == 1);
}

#[kani::proof]
pub fn unchanged_getter_bug() {
    let values = vec![1u64];
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[kani::proof]
pub fn physical_store_then_fresh_getter_safe() {
    let mut values = vec![1u64];
    unsafe { *values.as_mut_ptr() = 9; }
    assert!(unsafe { *values.as_ptr() } == 9);
}

#[kani::proof]
pub fn physical_store_then_fresh_getter_bug() {
    let mut values = vec![1u64];
    unsafe { *values.as_mut_ptr() = 9; }
    assert!(unsafe { *values.as_ptr() } == 1);
}

#[kani::proof]
pub fn clear_then_fresh_getter_keeps_bytes_safe() {
    let mut values = vec![1u64];
    values.clear();
    assert!(unsafe { *values.as_ptr() } == 1);
}


struct Holder { values: Vec<u64> }

#[kani::proof]
pub fn mutation_then_aggregate_getter_refusal() {
    let mut values = vec![1u64];
    values.push(2);
    let holder = Holder { values };
    assert!(unsafe { *holder.values.as_ptr().add(1) } == 2);
}

#[kani::proof]
pub fn mutation_then_projected_move_getter_refusal() {
    let mut values = vec![1u64];
    values.push(2);
    let holder = Holder { values };
    let moved = holder.values;
    assert!(unsafe { *moved.as_ptr().add(1) } == 2);
}


#[kani::proof]
pub fn unchanged_aggregate_getter_safe() {
    let holder = Holder { values: vec![1u64] };
    assert!(unsafe { *holder.values.as_ptr() } == 1);
}

#[kani::proof]
pub fn unchanged_aggregate_getter_bug() {
    let holder = Holder { values: vec![1u64] };
    assert!(unsafe { *holder.values.as_ptr() } == 9);
}

#[kani::proof]
pub fn unchanged_projected_move_getter_safe() {
    let holder = Holder { values: vec![1u64] };
    let moved = holder.values;
    assert!(unsafe { *moved.as_ptr() } == 1);
}

#[kani::proof]
pub fn unchanged_projected_move_getter_bug() {
    let holder = Holder { values: vec![1u64] };
    let moved = holder.values;
    assert!(unsafe { *moved.as_ptr() } == 9);
}
