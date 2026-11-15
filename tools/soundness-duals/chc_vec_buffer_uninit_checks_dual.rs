// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL. Run with
// `-Z uninit-checks`.
//
// WHY THIS FILE EXISTS: Kani's uninitialized-memory instrumentation passes a
// `Vec`'s buffer pointer, and the `Vec` itself, to `kani::mem_init`'s
// `is_ptr_initialized` / `set_ptr_initialized`, which read and write the
// shadow memory only. The `Vec`-buffer rule of the third review of round 10
// of fix/chc-false-certificates took those calls for writes through the
// buffer and the drop glue's instrumented borrow for a read of the `Vec`'s
// model, and failed the harness closed: the parity unit
// `expected/uninit/vec-read-uninit/vec-read-uninit.rs` lost its certificate
// (`bug_read_uninit_through_buffer` is that unit) and a read of an initialized
// element failed closed. The instrumentation is no access and no model read.

#[kani::proof]
fn bug_read_uninit_through_buffer() {
    let v: Vec<u8> = Vec::with_capacity(10);
    let _uninit = unsafe { *v.as_ptr().add(5) };
}

#[kani::proof]
fn safe_read_init_through_buffer() {
    let v: Vec<u8> = vec![1, 2, 3];
    let x = unsafe { *v.as_ptr().add(1) };
    assert!(x == 2);
}

#[kani::proof]
fn bug_read_init_through_buffer_wrong_value() {
    let v: Vec<u8> = vec![1, 2, 3];
    let x = unsafe { *v.as_ptr().add(1) };
    assert!(x == 3);
}

#[kani::proof]
fn safe_write_then_read_through_buffer() {
    let mut v: Vec<u8> = Vec::with_capacity(4);
    let p = v.as_mut_ptr();
    unsafe { *p.add(2) = 9 };
    let x = unsafe { *p.add(2) };
    assert!(x == 9);
}
