// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// kani-flags: -Z stubbing
//
//! Tests signature validation for stubs when bodies are unavailable (#956).
//!
//! When stubbing extern functions (which have no body), the check_compatibility
//! function should still validate that parameter and return types match via
//! function signatures.

extern "C" {
    fn extern_returns_i32() -> i32;
    fn extern_takes_i32(x: i32);
    fn extern_takes_two_i32(a: i32, b: i32);
}

// Stub with wrong return type
fn stub_returns_u64() -> u64 {
    42
}

// Stub with wrong parameter type
fn stub_takes_u64(x: u64) {
    let _ = x;
}

// Stub with wrong arity
fn stub_takes_one_i32(a: i32) {
    let _ = a;
}

// Return type mismatch: extern returns i32, stub returns u64
#[kani::proof]
#[kani::stub(extern_returns_i32, stub_returns_u64)]
fn test_return_type_mismatch() {
    unsafe {
        let _ = extern_returns_i32();
    }
}

// Parameter type mismatch: extern takes i32, stub takes u64
#[kani::proof]
#[kani::stub(extern_takes_i32, stub_takes_u64)]
fn test_param_type_mismatch() {
    unsafe {
        extern_takes_i32(42);
    }
}

// Arity mismatch: extern takes 2 params, stub takes 1
#[kani::proof]
#[kani::stub(extern_takes_two_i32, stub_takes_one_i32)]
fn test_arity_mismatch() {
    unsafe {
        extern_takes_two_i32(1, 2);
    }
}
