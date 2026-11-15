// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

static mut OBSERVED: u32 = 0;
trait Tag {}
struct Quiet(u32);
struct Loud(u32);
struct PanicDrop(u32);
struct ValueDrop(u32);
struct Owner {
    inner: Box<u32>,
}
impl Tag for Quiet {}
impl Tag for Loud {}
impl Tag for PanicDrop {}
impl Tag for ValueDrop {}
impl Tag for Owner {}
impl Drop for Loud {
    fn drop(&mut self) {
        unsafe {
            OBSERVED = 7;
        }
    }
}
impl Drop for PanicDrop {
    fn drop(&mut self) {
        assert!(false, "intended payload destructor panic");
    }
}
impl Drop for ValueDrop {
    fn drop(&mut self) {
        unsafe {
            OBSERVED = self.0;
        }
    }
}

#[kani::proof]
fn quiet_with_loud_decoy_safe() {
    unsafe {
        OBSERVED = 0;
    }
    let decoy: Box<dyn Tag> = Box::new(Loud(1));
    core::mem::forget(decoy);
    {
        let _actual: Box<dyn Tag> = Box::new(Quiet(2));
    }
    assert!(unsafe { OBSERVED } == 0);
}
#[kani::proof]
fn quiet_with_loud_decoy_bug() {
    unsafe {
        OBSERVED = 0;
    }
    let decoy: Box<dyn Tag> = Box::new(Loud(1));
    core::mem::forget(decoy);
    {
        let _actual: Box<dyn Tag> = Box::new(Quiet(2));
    }
    assert!(unsafe { OBSERVED } == 7);
}
#[kani::proof]
fn empty_drop_successor_bug() {
    {
        let _actual: Box<dyn Tag> = Box::new(Quiet(2));
    }
    assert!(false, "successor of empty drop must stay reachable");
}
#[kani::proof]
fn loud_effect_safe() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _actual: Box<dyn Tag> = Box::new(Loud(2));
    }
    assert!(unsafe { OBSERVED } == 7);
}
#[kani::proof]
fn loud_effect_bug() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _actual: Box<dyn Tag> = Box::new(Loud(2));
    }
    assert!(unsafe { OBSERVED } == 0);
}
#[kani::proof]
fn user_destructor_panic_bug() {
    let _actual: Box<dyn Tag> = Box::new(PanicDrop(2));
}
#[kani::proof]
fn payload_destructor_value_safe() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _actual: Box<dyn Tag> = Box::new(ValueDrop(19));
    }
    assert!(unsafe { OBSERVED } == 19);
}
#[kani::proof]
fn payload_destructor_value_bug() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _actual: Box<dyn Tag> = Box::new(ValueDrop(19));
    }
    assert!(unsafe { OBSERVED } == 0);
}
#[kani::proof]
fn inner_outer_drop_safe() {
    {
        let _actual: Box<dyn Tag> = Box::new(Owner { inner: Box::new(3) });
    }
    assert!(true);
}
#[kani::proof]
fn inner_outer_drop_successor_bug() {
    {
        let _actual: Box<dyn Tag> = Box::new(Owner { inner: Box::new(3) });
    }
    assert!(false, "inner and outer frees must not prune this successor");
}
#[kani::proof]
fn inner_outer_drop_uaf_bug() {
    let value = Owner { inner: Box::new(3) };
    let pointer = &raw const *value.inner;
    {
        let _actual: Box<dyn Tag> = Box::new(value);
    }
    assert!(unsafe { *pointer } == 3);
}
#[kani::proof]
fn empty_and_loud_join_safe() {
    unsafe {
        OBSERVED = 0;
    }
    let branch: bool = kani::any();
    {
        let _actual: Box<dyn Tag> = if branch { Box::new(Loud(2)) } else { Box::new(Quiet(2)) };
    }
    assert!(unsafe { OBSERVED } == if branch { 7 } else { 0 });
}
#[kani::proof]
fn empty_and_loud_join_bug() {
    unsafe {
        OBSERVED = 0;
    }
    let branch: bool = kani::any();
    {
        let _actual: Box<dyn Tag> = if branch { Box::new(Loud(2)) } else { Box::new(Quiet(2)) };
    }
    assert!(unsafe { OBSERVED } == 7);
}
#[kani::proof]
fn repeated_drop_safe() {
    for _ in 0..2 {
        let _actual: Box<dyn Tag> = Box::new(Quiet(2));
    }
}

#[inline(never)]
fn consume(_value: Box<dyn Tag>) {}
#[kani::proof]
fn walked_loud_effect_safe() {
    unsafe {
        OBSERVED = 0;
    }
    consume(Box::new(Loud(2)));
    assert!(unsafe { OBSERVED } == 7);
}
#[kani::proof]
fn walked_loud_effect_bug() {
    unsafe {
        OBSERVED = 0;
    }
    consume(Box::new(Loud(2)));
    assert!(unsafe { OBSERVED } == 0);
}
#[kani::proof]
fn walked_quiet_successor_safe() {
    consume(Box::new(Quiet(2)));
    assert!(true);
}
#[kani::proof]
fn walked_quiet_successor_bug() {
    consume(Box::new(Quiet(2)));
    assert!(false, "walked empty drop successor");
}
#[kani::proof]
fn walked_panic_bug() {
    consume(Box::new(PanicDrop(2)));
}

#[kani::proof]
fn explicit_mem_drop_effect_safe() {
    unsafe {
        OBSERVED = 0;
    }
    let actual: Box<dyn Tag> = Box::new(Loud(2));
    core::mem::drop(actual);
    assert!(unsafe { OBSERVED } == 7);
}
#[kani::proof]
fn explicit_mem_drop_effect_bug() {
    unsafe {
        OBSERVED = 0;
    }
    let actual: Box<dyn Tag> = Box::new(Loud(2));
    core::mem::drop(actual);
    assert!(unsafe { OBSERVED } == 0);
}
mod lookalike {
    pub fn drop(value: Box<dyn super::Tag>) {
        core::mem::forget(value);
        unsafe {
            super::OBSERVED = 23;
        }
    }
}
#[kani::proof]
fn user_named_drop_keeps_its_body_safe() {
    unsafe {
        OBSERVED = 0;
    }
    let actual: Box<dyn Tag> = Box::new(Loud(2));
    lookalike::drop(actual);
    assert!(unsafe { OBSERVED } == 23);
}
#[kani::proof]
fn user_named_drop_keeps_its_body_bug() {
    unsafe {
        OBSERVED = 0;
    }
    let actual: Box<dyn Tag> = Box::new(Loud(2));
    lookalike::drop(actual);
    assert!(unsafe { OBSERVED } == 7);
}
