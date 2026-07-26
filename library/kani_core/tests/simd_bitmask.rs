// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests for the simd_bitmask model algorithm.
//!
//! These tests verify the bitmask computation from `models.rs::simd_models`
//! by inlining the core algorithm. The algorithm cannot be imported directly
//! because it lives inside the `generate_models!` macro and kani_core is
//! a `no_core` crate.
//!
//! Restored from #1653 / #1658 — the original in-macro tests were dead code
//! (`#[cfg(any())]`) and a prior extraction attempt (#1652) failed due to
//! macro expansion context issues.

#![feature(repr_simd)]
#![feature(portable_simd)]
#![feature(generic_const_exprs)]
#![feature(core_intrinsics)]
// Clippy ptr casts suppressed: fixes trigger nightly-2025-12-03 ICE in
// #[repr(simd)] derived Clone/Debug MIR validation.
#![allow(
    incomplete_features,
    internal_features,
    clippy::ptr_as_ptr,
    clippy::borrow_as_ptr,
    clippy::ref_as_ptr
)]

use core::fmt::Debug;
use core::mem::size_of;
use core::simd::*;

// ---------------------------------------------------------------------------
// Inlined algorithm from models.rs::simd_models
// ---------------------------------------------------------------------------

/// Trait mirroring the `MaskElement` from the generate_models macro.
trait MaskElement: PartialEq + Debug {
    const TRUE: Self;
    const FALSE: Self;
}

macro_rules! impl_element {
    ($ty:ty) => {
        impl MaskElement for $ty {
            const TRUE: Self = -1;
            const FALSE: Self = 0;
        }
    };
}

macro_rules! impl_unsigned_element {
    ($ty:ty) => {
        impl MaskElement for $ty {
            const TRUE: Self = <$ty>::MAX;
            const FALSE: Self = 0;
        }
    };
}

impl_element! { i8 }
impl_element! { i16 }
impl_element! { i32 }
impl_element! { i64 }
impl_element! { i128 }
impl_element! { isize }

impl_unsigned_element! { u8 }
impl_unsigned_element! { u16 }
impl_unsigned_element! { u32 }
impl_unsigned_element! { u64 }
impl_unsigned_element! { u128 }
impl_unsigned_element! { usize }

const fn mask_len(len: usize) -> usize {
    len.div_ceil(8)
}

#[cfg(target_endian = "little")]
unsafe fn simd_bitmask_impl<T, const LANES: usize>(input: &[T; LANES]) -> [u8; mask_len(LANES)]
where
    T: MaskElement,
{
    let mut mask_array = [0; mask_len(LANES)];

    for (byte_idx, byte) in mask_array.iter_mut().enumerate() {
        let start_lane = byte_idx << 3;
        let bits_to_process = (LANES - start_lane).min(8);

        *byte = if bits_to_process > 0 && input[start_lane] == T::TRUE { 1 << 0 } else { 0 }
            | if bits_to_process > 1 && input[start_lane + 1] == T::TRUE { 1 << 1 } else { 0 }
            | if bits_to_process > 2 && input[start_lane + 2] == T::TRUE { 1 << 2 } else { 0 }
            | if bits_to_process > 3 && input[start_lane + 3] == T::TRUE { 1 << 3 } else { 0 }
            | if bits_to_process > 4 && input[start_lane + 4] == T::TRUE { 1 << 4 } else { 0 }
            | if bits_to_process > 5 && input[start_lane + 5] == T::TRUE { 1 << 5 } else { 0 }
            | if bits_to_process > 6 && input[start_lane + 6] == T::TRUE { 1 << 6 } else { 0 }
            | if bits_to_process > 7 && input[start_lane + 7] == T::TRUE { 1 << 7 } else { 0 };

        assert!(
            bits_to_process < 1 || input[start_lane] == T::TRUE || input[start_lane] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
        assert!(
            bits_to_process < 2
                || input[start_lane + 1] == T::TRUE
                || input[start_lane + 1] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
        assert!(
            bits_to_process < 3
                || input[start_lane + 2] == T::TRUE
                || input[start_lane + 2] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
        assert!(
            bits_to_process < 4
                || input[start_lane + 3] == T::TRUE
                || input[start_lane + 3] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
        assert!(
            bits_to_process < 5
                || input[start_lane + 4] == T::TRUE
                || input[start_lane + 4] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
        assert!(
            bits_to_process < 6
                || input[start_lane + 5] == T::TRUE
                || input[start_lane + 5] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
        assert!(
            bits_to_process < 7
                || input[start_lane + 6] == T::TRUE
                || input[start_lane + 6] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
        assert!(
            bits_to_process < 8
                || input[start_lane + 7] == T::TRUE
                || input[start_lane + 7] == T::FALSE,
            "Masks values should either be 0 or -1"
        );
    }

    mask_array
}

/// Structure used for sanity check our parameters.
#[repr(simd)]
struct SimdRepr<T, const LANES: usize>([T; LANES]);

unsafe fn simd_bitmask<T, U, E, const LANES: usize>(input: T) -> U
where
    [u8; mask_len(LANES)]: Sized,
    E: MaskElement,
{
    assert_eq!(
        size_of::<U>(),
        size_of::<[u8; mask_len(LANES)]>(),
        "Expected size of return type and mask lanes to match",
    );
    assert_eq!(
        size_of::<T>(),
        size_of::<SimdRepr::<E, LANES>>(),
        "Expected size of input and lanes to match",
    );

    unsafe {
        let data = &*(&input as *const T as *const [E; LANES]);
        let mask = simd_bitmask_impl(data);
        (&mask as *const [u8; mask_len(LANES)] as *const U).read()
    }
}

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

/// Compare the model's output against portable SIMD's `to_bitmask()`.
fn check_portable_bitmask<T, E, const LANES: usize, M>(mask: Mask<T, LANES>)
where
    T: core::simd::MaskElement,
    LaneCount<LANES>: SupportedLaneCount,
    E: MaskElement,
    [u8; mask_len(LANES)]: Sized,
    u64: From<M>,
{
    assert_eq!(unsafe { u64::from(simd_bitmask::<_, M, E, LANES>(mask)) }, mask.to_bitmask());
}

// derive(Clone, Debug) on #[repr(simd)] structs with const-generic arrays
// triggers nightly-2025-12-03 ICE (broken MIR in Clone::clone / Debug::fmt).
// Manual Clone + no Debug; check_bitmask only requires T: Clone + Copy.
#[repr(simd)]
#[derive(Copy)]
struct CustomMask<T, const LANES: usize>([T; LANES]);

#[allow(clippy::expl_impl_clone_on_copy)]
impl<T: Copy, const LANES: usize> Clone for CustomMask<T, LANES> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Compare the model's output against the compiler's `simd_bitmask` intrinsic.
fn check_bitmask<T, U, E, const LANES: usize>(mask: T)
where
    T: Clone + Copy,
    U: PartialEq + Debug,
    E: MaskElement,
    [u8; mask_len(LANES)]: Sized,
{
    assert_eq!(unsafe { simd_bitmask::<_, U, E, LANES>(mask) }, unsafe {
        core::intrinsics::simd::simd_bitmask::<T, U>(mask)
    },);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// All-true and all-false masks with i16 lanes (16 lanes → u16 result).
#[test]
fn test_bitmask_i16() {
    check_portable_bitmask::<_, i16, 16, u16>(mask16x16::splat(false));
    check_portable_bitmask::<_, i16, 16, u16>(mask16x16::splat(true));
}

/// All-true and all-false masks with i32 lanes (8 lanes → u8 result).
#[test]
fn test_bitmask_i32_all() {
    check_portable_bitmask::<_, i32, 8, u8>(mask32x8::splat(false));
    check_portable_bitmask::<_, i32, 8, u8>(mask32x8::splat(true));
}

/// All-true and all-false masks with i64 lanes (4 lanes → u8 result).
#[test]
fn test_bitmask_i64_all() {
    check_portable_bitmask::<_, i64, 4, u8>(mask64x4::splat(false));
    check_portable_bitmask::<_, i64, 4, u8>(mask64x4::splat(true));
}

/// All-true and all-false masks with i128 lanes using custom SIMD type.
/// (Portable SIMD does not support i128 as a MaskElement.)
#[test]
fn test_bitmask_i128_all() {
    check_bitmask::<_, u8, i128, 2>(CustomMask([0i128; 2]));
    check_bitmask::<_, u8, i128, 2>(CustomMask([-1i128; 2]));
}

/// Model correctly rejects invalid mask values (not 0 or -1).
///
/// Uses `from_int_unchecked` with value 10 — undefined behavior. In release
/// mode LLVM can optimize the UB away before the assertion runs, so we only
/// test this in debug mode.
#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "Masks values should either be 0 or -1")]
fn test_invalid_bitmask() {
    let invalid_mask = unsafe { mask32x16::from_int_unchecked(i32x16::splat(10)) };
    assert_eq!(unsafe { simd_bitmask::<_, u16, i32, 16>(invalid_mask) }, u16::MAX);
}

/// Model rejects mismatched generic size parameters.
#[test]
#[should_panic(expected = "Expected size of return type and mask lanes to match")]
fn test_invalid_generics() {
    let mask = mask32x16::splat(false);
    assert_eq!(unsafe { simd_bitmask::<_, u16, i32, 2>(mask) }, u16::MAX);
}

/// Non-symmetric patterns to verify correct bit ordering and endianness.
#[test]
fn test_bitmask_i32() {
    check_portable_bitmask::<_, i32, 8, u8>(mask32x8::from([
        true, true, false, true, false, false, false, true,
    ]));

    check_portable_bitmask::<_, i32, 4, u8>(mask32x4::from([true, false, false, true]));
}

/// Odd-sized SIMD arrays using custom types (not restricted by portable SIMD
/// lane count requirements).
#[test]
fn test_bitmask_odd_lanes() {
    check_bitmask::<_, [u8; 3], i128, 23>(CustomMask([0i128; 23]));
    check_bitmask::<_, [u8; 9], i128, 70>(CustomMask([-1i128; 70]));
}

/// Manually constructed mask pattern — verifies specific bit positions.
#[test]
fn check_mask_harness() {
    let mut mask = mask32x4::splat(false);
    mask.set(1, true);
    mask.set(3, true);
    let bitmask = mask.to_bitmask();
    assert_eq!(bitmask, 0b1010);

    let model_mask = unsafe { u64::from(simd_bitmask::<_, u8, u32, 4>(mask)) };
    assert_eq!(model_mask, bitmask);
}
