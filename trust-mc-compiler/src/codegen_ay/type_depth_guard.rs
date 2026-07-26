// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Thread-local depth guard for recursive type-to-sort translation.
//!
//! Both the CHC path (`translate_ty`) and BMC path (`infer_sort_from_ty`)
//! recurse through Rust type structures (structs, enums, tuples, closures)
//! without any depth limit. A deeply nested or self-referential type can
//! overflow the call stack.
//!
//! This module provides an RAII depth guard that tracks recursion depth
//! via a thread-local counter. When the maximum depth is exceeded, the
//! guard returns `None`, causing the type translation to gracefully fall
//! back to `None` (unsupported type) instead of crashing.

use std::cell::Cell;

/// Maximum recursion depth for type-to-sort translation.
///
/// 64 levels handles any realistic Rust type nesting (typical programs
/// rarely exceed 10-15 levels). Deep enough to avoid false negatives,
/// shallow enough to prevent stack overflow (each frame is ~200-500 bytes,
/// so 64 levels uses ~32KB of the default 8MB stack).
const MAX_TYPE_TRANSLATION_DEPTH: usize = 64;

thread_local! {
    static TYPE_TRANSLATION_DEPTH: Cell<usize> = const { Cell::new(0) };
}

/// RAII guard that increments the thread-local depth counter on creation
/// and decrements it on drop.
///
/// Use `TypeDepthGuard::acquire()` at the entry of each recursive type
/// translation function. Returns `None` if the maximum depth has been
/// reached, which should propagate as a `None` sort (unsupported type).
pub(in crate::codegen_ay) struct TypeDepthGuard {
    _private: (), // prevent external construction
}

impl TypeDepthGuard {
    /// Attempt to acquire the depth guard. Returns `None` if max depth exceeded.
    #[inline]
    pub(in crate::codegen_ay) fn acquire() -> Option<Self> {
        TYPE_TRANSLATION_DEPTH.with(|d| {
            let current = d.get();
            if current >= MAX_TYPE_TRANSLATION_DEPTH {
                tracing::warn!(
                    depth = current,
                    max = MAX_TYPE_TRANSLATION_DEPTH,
                    "type translation depth limit reached — returning None"
                );
                None
            } else {
                d.set(current + 1);
                Some(TypeDepthGuard { _private: () })
            }
        })
    }
}

impl Drop for TypeDepthGuard {
    #[inline]
    fn drop(&mut self) {
        TYPE_TRANSLATION_DEPTH.with(|d| {
            d.set(d.get().saturating_sub(1));
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_depth_guard_basic() {
        // Acquire and drop should work
        let guard = TypeDepthGuard::acquire();
        assert!(guard.is_some());
        drop(guard);
    }

    #[test]
    fn test_depth_guard_nesting() {
        let g1 = TypeDepthGuard::acquire();
        assert!(g1.is_some());
        let g2 = TypeDepthGuard::acquire();
        assert!(g2.is_some());
        drop(g2);
        drop(g1);
    }

    #[test]
    fn test_depth_guard_limit() {
        let mut guards = Vec::new();
        for _ in 0..MAX_TYPE_TRANSLATION_DEPTH {
            let g = TypeDepthGuard::acquire();
            assert!(g.is_some(), "should succeed within limit");
            guards.push(g);
        }
        // Next acquisition should fail
        let overflow = TypeDepthGuard::acquire();
        assert!(overflow.is_none(), "should fail at limit");
        drop(guards);
    }

    #[test]
    fn test_depth_guard_reset_after_drop() {
        {
            let mut guards = Vec::new();
            for _ in 0..MAX_TYPE_TRANSLATION_DEPTH {
                guards.push(TypeDepthGuard::acquire());
            }
            // At max depth
            assert!(TypeDepthGuard::acquire().is_none());
        }
        // After dropping all guards, should succeed again
        let g = TypeDepthGuard::acquire();
        assert!(g.is_some());
        drop(g);
    }
}
