// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Simplified iterator implementations for verification.
//!
//! This module provides [`KaniIntoIter`] trait implementations for common
//! collection types. These implementations replace Rust's standard `IntoIterator`
//! with simpler alternatives that are more verification-friendly.
//!
//! # Why KaniIntoIter?
//!
//! Rust's standard iterator infrastructure involves deep call stacks and complex
//! types that make verification challenging. The [`KaniIntoIter`] trait provides
//! equivalent semantics with a flattened implementation:
//!
//! - Reduces call stack depth during verification
//! - Simplifies loop invariant specifications
//! - Maintains correct iterator semantics for `for` loops
//!
//! # Supported Types
//!
//! Currently, [`KaniIntoIter`] is implemented for:
//!
//! - `Vec<T>` - Converts to pointer-based iteration over elements
//!
//! # Internal Use
//!
//! This trait is primarily used internally by trust_mc's loop handling. Users
//! typically don't interact with it directly - regular `for` loops work
//! transparently:
//!
//! ```rust
//! #[kani::proof]
//! fn verify_iteration() {
//!     let v = vec![1, 2, 3];
//!     let mut sum = 0;
//!     for x in v {  // Uses KaniIntoIter automatically
//!         sum += x;
//!     }
//!     kani::assert(sum == 6, "Sum should be 6");
//! }
//! ```
//!
//! # Implementation Details
//!
//! The implementations use [`KaniPtrIter`], a pointer-based iterator that
//! avoids the complexity of Rust's `std::vec::IntoIter`. This is an internal
//! optimization that doesn't affect user-facing semantics.

use crate::{KaniIntoIter, KaniPtrIter};

impl<T: Clone> KaniIntoIter for Vec<T> {
    type Iter = KaniPtrIter<T>;
    fn kani_into_iter(self) -> Self::Iter {
        let s = self.iter();
        KaniPtrIter::new(s.as_slice().as_ptr(), s.len())
    }
}
