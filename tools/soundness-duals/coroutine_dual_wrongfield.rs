// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Adversarial guard for coroutine Fix B (by-name field select/update).
//
// Coroutine view datatypes order fields by increasing byte OFFSET while MIR
// indexes fields by declaration order. With THREE saved locals declared as
// (u32, u64, u64), align-descending layout stores them as
// [u64 first, u64 second, u32 small] — so the two SAME-SORT u64 fields sit at
// swapped positions relative to their MIR indices. A positional field select
// on the coroutine state silently reads `second` where `first` was meant.
//
// first=11, second=500 hold DIFFERENT values and the assert depends on
// reading the right one: 2*first + second = 522, but a swapped read gives
// 2*second + first = 1011.
//
// - dual_wrongfield_safe MUST be SUCCESSFUL (correct by-name reads).
// - dual_wrongfield_buggy asserts the SWAPPED result 1011 and MUST FAIL:
//   under a wrong-field encoding it would pass — the exact missed-bug this
//   test guards against.
//
// The upvar pair exercises the same shape through the AGGREGATE path
// (captured (u32, u64, u64) reordered in direct_fields).

#![feature(coroutines, coroutine_trait)]
#![feature(stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[kani::proof]
fn dual_wrongfield_safe() {
    let mut coro = #[coroutine]
    || {
        let small: u32 = 3;
        let first: u64 = 11;
        let second: u64 = 500;
        yield;
        2 * first + second + u64::from(small) - 3
    };

    match Pin::new(&mut coro).resume(()) {
        CoroutineState::Yielded(()) => {}
        s => panic!("bad state: {:?}", s),
    }
    match Pin::new(&mut coro).resume(()) {
        CoroutineState::Complete(v) => assert_eq!(v, 522),
        s => panic!("bad state: {:?}", s),
    }
}

#[kani::proof]
fn dual_wrongfield_buggy() {
    let mut coro = #[coroutine]
    || {
        let small: u32 = 3;
        let first: u64 = 11;
        let second: u64 = 500;
        yield;
        2 * first + second + u64::from(small) - 3
    };

    match Pin::new(&mut coro).resume(()) {
        CoroutineState::Yielded(()) => {}
        s => panic!("bad state: {:?}", s),
    }
    match Pin::new(&mut coro).resume(()) {
        // 1011 is exactly what a first<->second swapped read computes:
        // this harness MUST FAIL; if it ever passes, the wrong-field
        // select is back.
        CoroutineState::Complete(v) => assert_eq!(v, 1011),
        s => panic!("bad state: {:?}", s),
    }
}

#[kani::proof]
fn dual_wrongfield_upvar_safe() {
    let small: u32 = 7;
    let x: u64 = 21;
    let y: u64 = 900;
    let mut coro = #[coroutine]
    move || {
        yield;
        2 * x + y + u64::from(small) - 7
    };

    match Pin::new(&mut coro).resume(()) {
        CoroutineState::Yielded(()) => {}
        s => panic!("bad state: {:?}", s),
    }
    match Pin::new(&mut coro).resume(()) {
        CoroutineState::Complete(v) => assert_eq!(v, 942),
        s => panic!("bad state: {:?}", s),
    }
}

#[kani::proof]
fn dual_wrongfield_upvar_buggy() {
    let small: u32 = 7;
    let x: u64 = 21;
    let y: u64 = 900;
    let mut coro = #[coroutine]
    move || {
        yield;
        2 * x + y + u64::from(small) - 7
    };

    match Pin::new(&mut coro).resume(()) {
        CoroutineState::Yielded(()) => {}
        s => panic!("bad state: {:?}", s),
    }
    match Pin::new(&mut coro).resume(()) {
        // 2*y + x = 1821: the swapped-upvar result — MUST FAIL.
        CoroutineState::Complete(v) => assert_eq!(v, 1821),
        s => panic!("bad state: {:?}", s),
    }
}
