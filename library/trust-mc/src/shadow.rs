// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Experimental ghost-state support for shadow memory.
//!
//! Shadow memory lets harnesses track metadata for memory locations, for
//! example whether a location is initialized.
//!
//! The main data structure provided by this module is [`ShadowMem`], which
//! requires `-Z ghost-state`.
//!
//! ```text
//! cargo trust_mc -Z ghost-state
//! ```
//!
//! # Limits
//!
//! The current shadow memory model is fixed-size:
//!
//! - At most [`MAX_TRACKED_OBJECTS`] (1024) distinct objects can be tracked.
//! - At most [`MAX_TRACKED_BYTES_PER_OBJECT`] (64) bytes per object are tracked.
//!
//! Exceeding either limit triggers a fail-closed assertion in [`ShadowMem::get`]
//! or [`ShadowMem::set`].
//!
//! # Example
//!
//! ```no_run
//! use kani::shadow::ShadowMem;
//! use std::alloc::{alloc, Layout};
//!
//! let mut sm = ShadowMem::new(false);
//!
//! unsafe {
//!     let ptr = alloc(Layout::new::<u8>());
//!     // assert the memory location is not initialized
//!     assert!(!sm.get(ptr));
//!     // write to the memory location
//!     *ptr = 42;
//!     // update the shadow memory to indicate that this location is now initialized
//!     sm.set(ptr, true);
//! }
//! ```

/// Maximum number of distinct objects tracked by [`ShadowMem`].
#[crate::unstable(
    feature = "ghost-state",
    issue = 3184,
    reason = "experimental ghost state/shadow memory API"
)]
pub const MAX_TRACKED_OBJECTS: usize = 1024;

/// Maximum number of bytes tracked per object in [`ShadowMem`].
#[crate::unstable(
    feature = "ghost-state",
    issue = 3184,
    reason = "experimental ghost state/shadow memory API"
)]
pub const MAX_TRACKED_BYTES_PER_OBJECT: usize = 64;

const MAX_NUM_OBJECTS_ASSERT_MSG: &str = "The number of objects exceeds the maximum number supported by trust_mc's shadow memory model (1024)";
const MAX_OBJECT_SIZE_ASSERT_MSG: &str =
    "The object size exceeds the maximum size supported by trust_mc's shadow memory model (64)";

/// A shadow memory data structure that contains a two-dimensional array of a
/// generic type `T`.
/// Each element of the outer array represents an object, and each element of
/// the inner array represents a byte in the object.
///
/// The model tracks at most [`MAX_TRACKED_OBJECTS`] objects with at most
/// [`MAX_TRACKED_BYTES_PER_OBJECT`] bytes each. Exceeding either limit
/// triggers a fail-closed assertion.
#[kanitool::unstable(
    feature = "ghost-state",
    issue = 3184,
    reason = "experimental ghost state/shadow memory API"
)]
pub struct ShadowMem<T: Copy> {
    mem: [[T; MAX_TRACKED_BYTES_PER_OBJECT]; MAX_TRACKED_OBJECTS],
}

impl<T: Copy> ShadowMem<T> {
    /// Create a new shadow memory instance initialized with the given value
    #[crate::unstable(
        feature = "ghost-state",
        issue = 3184,
        reason = "experimental ghost state/shadow memory API"
    )]
    #[must_use]
    pub const fn new(val: T) -> Self {
        Self { mem: [[val; MAX_TRACKED_BYTES_PER_OBJECT]; MAX_TRACKED_OBJECTS] }
    }

    /// Get the shadow memory value of the given pointer
    #[crate::unstable(
        feature = "ghost-state",
        issue = 3184,
        reason = "experimental ghost state/shadow memory API"
    )]
    #[must_use]
    pub fn get<U>(&self, ptr: *const U) -> T {
        let obj = crate::mem::pointer_object(ptr);
        let offset = crate::mem::pointer_offset(ptr);
        crate::assert(obj < MAX_TRACKED_OBJECTS, MAX_NUM_OBJECTS_ASSERT_MSG);
        crate::assert(offset < MAX_TRACKED_BYTES_PER_OBJECT, MAX_OBJECT_SIZE_ASSERT_MSG);
        self.mem[obj][offset]
    }

    /// Set the shadow memory value of the given pointer
    #[crate::unstable(
        feature = "ghost-state",
        issue = 3184,
        reason = "experimental ghost state/shadow memory API"
    )]
    pub fn set<U>(&mut self, ptr: *const U, val: T) {
        let obj = crate::mem::pointer_object(ptr);
        let offset = crate::mem::pointer_offset(ptr);
        crate::assert(obj < MAX_TRACKED_OBJECTS, MAX_NUM_OBJECTS_ASSERT_MSG);
        crate::assert(offset < MAX_TRACKED_BYTES_PER_OBJECT, MAX_OBJECT_SIZE_ASSERT_MSG);
        self.mem[obj][offset] = val;
    }
}
