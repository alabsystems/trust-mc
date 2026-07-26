// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
// kani-flags: -Z ghost-state -Z uninit-checks

//! Checks that delayed UB through a slice is rejected.
//! This remains separate from `delayed-ub.rs` to preserve the regression
//! coverage from <https://github.com/model-checking/kani/issues/3881>.

/// Delayed UB via mutable pointer write into a slice element.
#[kani::proof]
fn delayed_ub_slices() {
    unsafe {
        // Create an array.
        let mut arr = [0u128; 4];
        // Materialize the full slice so this exercises slice shadow state,
        // while avoiding the nested subslices that introduced unrelated
        // bounds failures in the legacy test.
        let slice = &mut arr[..];
        let ptr = &mut slice[0] as *mut _ as *mut (u8, u32);
        *ptr = (4, 4);
        let _arr_copy = arr; // UB: This reads a padding value inside the array!
    }
}
