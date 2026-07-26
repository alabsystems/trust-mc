// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Functions for generating arbitrary vectors in verification proofs.
//!
//! This module provides helpers for creating symbolic `Vec<T>` instances with
//! controlled sizes, which is essential for bounded verification of code that
//! operates on vectors.
//!
//! # Overview
//!
//! trust_mc's verification is bounded, meaning vectors must have a known maximum
//! length. This module provides two functions for generating arbitrary vectors:
//!
//! | Function | Length | Use Case |
//! |----------|--------|----------|
//! | [`any_vec`] | 0 to `MAX_LENGTH` | General verification with size variance |
//! | [`exact_vec`] | Exactly `EXACT_LENGTH` | When exact length is required |
//!
//! # Example
//!
//! ```rust
//! use kani::vec::{any_vec, exact_vec};
//!
//! #[kani::proof]
//! fn verify_vec_length() {
//!     // Generate a vector of 0-5 arbitrary u32 values
//!     let v: Vec<u32> = any_vec::<u32, 5>();
//!
//!     // Verify the length is within bounds
//!     kani::assert(v.len() <= 5, "Length is at most MAX_LENGTH");
//! }
//!
//! #[kani::proof]
//! fn verify_with_exact_length() {
//!     // Generate a vector of exactly 3 elements
//!     let v: Vec<i32> = exact_vec::<i32, 3>();
//!     kani::assert(v.len() == 3, "Vector has exactly 3 elements");
//! }
//! ```
//!
//! # Choosing Between `any_vec` and `exact_vec`
//!
//! - Use [`any_vec`] when your code should handle vectors of varying lengths.
//!   This is the most common choice for general verification.
//!
//! - Use [`exact_vec`] when testing code that requires a specific length, or
//!   when you want faster verification by eliminating length variance.
//!
//! # Performance Considerations
//!
//! The `MAX_LENGTH` parameter directly affects verification time:
//! - Larger bounds = more paths to explore = longer verification
//! - Start with small bounds (3-5) and increase if needed
//! - [`exact_vec`] is faster than [`any_vec`] with the same length bound

use crate::{Arbitrary, any, any_where};

/// Generates an arbitrary vector whose length is at most MAX_LENGTH.
#[must_use]
pub fn any_vec<T, const MAX_LENGTH: usize>() -> Vec<T>
where
    T: Arbitrary,
{
    let real_length: usize = any_where(|sz| *sz <= MAX_LENGTH);
    match real_length {
        0 => vec![],
        exact if exact == MAX_LENGTH => exact_vec::<T, MAX_LENGTH>(),
        _ => {
            let mut any_vec = exact_vec::<T, MAX_LENGTH>();
            any_vec.truncate(real_length);
            any_vec.shrink_to_fit();
            assert!(any_vec.capacity() == any_vec.len());
            any_vec
        }
    }
}

/// Generates an arbitrary vector that is exactly EXACT_LENGTH long.
#[must_use]
pub fn exact_vec<T, const EXACT_LENGTH: usize>() -> Vec<T>
where
    T: Arbitrary,
{
    let boxed_array: Box<[T; EXACT_LENGTH]> = Box::new(any());
    <[T]>::into_vec(boxed_array)
}
