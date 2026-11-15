// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

static mut OBSERVED: u32 = 0;
trait Tag {}
struct Temporal {
    first: u32,
    second: u32,
}
impl Tag for Temporal {}
#[inline(never)]
fn write_and_observe(value: &mut u32) -> u32 {
    *value = 31;
    let observed = *value;
    *value = 37;
    observed
}
impl Drop for Temporal {
    fn drop(&mut self) {
        let before = self.first;
        let middle = write_and_observe(&mut self.first);
        self.second = middle;
        assert!(self.first == 37);
        assert!(before == 11);
        assert!(middle == 31);
        assert!(self.second == 31);
        unsafe {
            OBSERVED = before + middle;
        }
    }
}
#[kani::proof]
fn native_payload_alias_and_later_store_safe() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _value: Box<dyn Tag> = Box::new(Temporal { first: 11, second: 13 });
    }
    assert!(unsafe { OBSERVED } == 42);
}
#[kani::proof]
fn native_payload_alias_and_later_store_bug() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _value: Box<dyn Tag> = Box::new(Temporal { first: 11, second: 13 });
    }
    assert!(unsafe { OBSERVED } == 0);
}
struct Past<const WRONG: bool>(u32);
impl<const WRONG: bool> Tag for Past<WRONG> {}
impl<const WRONG: bool> Drop for Past<WRONG> {
    fn drop(&mut self) {
        self.0 = 1;
        let observed = self.0;
        self.0 = 2;
        assert!(observed == if WRONG { 2 } else { 1 });
    }
}
#[kani::proof]
fn native_earlier_payload_observation_safe() {
    {
        let _value: Box<dyn Tag> = Box::new(Past::<false>(9));
    }
    assert!(true);
}
#[kani::proof]
fn native_later_payload_store_cannot_repair_earlier_check_bug() {
    let _value: Box<dyn Tag> = Box::new(Past::<true>(9));
}
struct StaticTwice(u32);
impl Tag for StaticTwice {}
impl Drop for StaticTwice {
    fn drop(&mut self) {
        unsafe {
            OBSERVED = self.0;
            let earlier = OBSERVED;
            OBSERVED = 29;
            assert!(earlier == self.0);
        }
    }
}
#[kani::proof]
fn native_two_static_stores_preserve_successor_safe() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _value: Box<dyn Tag> = Box::new(StaticTwice(19));
    }
    assert!(unsafe { OBSERVED } == 29);
}
#[kani::proof]
fn native_two_static_stores_do_not_prune_successor_bug() {
    unsafe {
        OBSERVED = 0;
    }
    {
        let _value: Box<dyn Tag> = Box::new(StaticTwice(19));
    }
    assert!(unsafe { OBSERVED } == 19);
}
