// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// kani-expect: UNKNOWN
// kani-expect: proof_minimal_array_lookup=PROOF
// kani-expect: proof_minimal_array_search=PROOF
// kani-expect: proof_struct_array_lookup=PROOF
// NOTE: proof_minimal_array_lookup was ERROR at ay 417854b7, now UNKNOWN at ay 8a4a9bcc2.

/// Minimal: flat array + while loop search (no nested struct)
#[kani::proof]
fn proof_minimal_array_search() {
    let vals: [u32; 4] = [10, 20, 30, 40];
    let len: usize = 2; // Only 2 elements used

    let target: u32 = 99;

    let mut i = 0;
    let mut found = false;
    while i < len {
        if vals[i] == target {
            found = true;
        }
        i += 1;
    }
    assert!(!found, "99 not in [10,20]");
}

/// Minimal: flat array search returns u32 value
#[kani::proof]
fn proof_minimal_array_lookup() {
    let keys: [u32; 4] = [1, 0, 0, 0];
    let values: [u32; 4] = [42, 0, 0, 0];
    let len: usize = 1;

    let target: u32 = 2;
    let mut result: u32 = 0;
    let mut i = 0;
    while i < len {
        if keys[i] == target {
            result = values[i];
        }
        i += 1;
    }
    assert!(result == 0, "Missing key returns 0");
}

/// Like coeff method: struct in array
#[derive(Clone, Copy)]
struct Pair {
    a: i64,
    b: i64,
}

#[kani::proof]
fn proof_struct_array_lookup() {
    let keys: [u32; 4] = [1, 0, 0, 0];
    let vals: [Pair; 4] =
        [Pair { a: 3, b: 1 }, Pair { a: 0, b: 1 }, Pair { a: 0, b: 1 }, Pair { a: 0, b: 1 }];
    let len: usize = 1;

    let target: u32 = 2;
    let mut result_a: i64 = 0;
    let mut i = 0;
    while i < len {
        if keys[i] == target {
            result_a = vals[i].a;
        }
        i += 1;
    }
    assert!(result_a == 0, "Missing key returns 0");
}
