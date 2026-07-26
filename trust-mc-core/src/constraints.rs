// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Constraint storage for Horn rule bodies.
//!
//! Supports two modes: owned `Vec<Expr>` and `Arc<[Expr]>` shared base +
//! per-rule extras. The shared mode avoids copying the constraint vector
//! when multiple rules from the same block share the same base constraints.
//! Part of #2507.

use std::sync::Arc;

use ay_bindings::Expr;

/// Constraint storage for Horn rule bodies.
///
/// Supports two modes:
/// - `Owned`: a plain `Vec<Expr>` (for init rules, tests, and small constraint sets)
/// - `Shared`: an `Arc<[Expr]>` base shared across all rules from the same block,
///   plus an optional `extra` Vec for per-rule additions (guards, violations).
///
/// For a SwitchInt with K branches, `Shared` avoids K-1 copies of the base
/// constraint slice. Part of #2507.
#[derive(Debug, Clone, Eq)]
pub enum Constraints {
    /// Fully owned constraint vector.
    Owned(Vec<Expr>),
    /// Shared base constraints (from block-level stmt encoding) plus per-rule extras.
    Shared {
        /// Base constraints shared across all rules from the same block.
        base: Arc<[Expr]>,
        /// Additional per-rule constraints (guards, violation conditions).
        extra: Vec<Expr>,
    },
}

impl Constraints {
    /// Returns the total number of constraints.
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            Constraints::Owned(v) => v.len(),
            Constraints::Shared { base, extra } => base.len() + extra.len(),
        }
    }

    /// Returns `true` if there are no constraints.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns `true` if the constraints use `Arc`-shared base storage.
    #[must_use]
    pub fn is_shared(&self) -> bool {
        matches!(self, Constraints::Shared { .. })
    }

    /// Returns the first constraint, if any.
    #[must_use]
    pub fn first(&self) -> Option<&Expr> {
        match self {
            Constraints::Owned(v) => v.first(),
            Constraints::Shared { base, extra } => base.first().or_else(|| extra.first()),
        }
    }

    /// Returns the last constraint, if any.
    #[must_use]
    pub fn last(&self) -> Option<&Expr> {
        match self {
            Constraints::Owned(v) => v.last(),
            Constraints::Shared { base, extra } => extra.last().or_else(|| base.last()),
        }
    }

    /// Returns an iterator over all constraints.
    pub fn iter(&self) -> ConstraintsIter<'_> {
        match self {
            Constraints::Owned(v) => ConstraintsIter::Owned(v.iter()),
            Constraints::Shared { base, extra } => {
                ConstraintsIter::Shared(base.iter().chain(extra.iter()))
            }
        }
    }
}

impl PartialEq for Constraints {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

impl std::hash::Hash for Constraints {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for expr in self {
            expr.hash(state);
        }
    }
}

/// Iterator over [`Constraints`].
pub enum ConstraintsIter<'a> {
    /// Iterating over an owned Vec.
    Owned(std::slice::Iter<'a, Expr>),
    /// Iterating over shared base + extra.
    Shared(std::iter::Chain<std::slice::Iter<'a, Expr>, std::slice::Iter<'a, Expr>>),
}

impl<'a> Iterator for ConstraintsIter<'a> {
    type Item = &'a Expr;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ConstraintsIter::Owned(iter) => iter.next(),
            ConstraintsIter::Shared(iter) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            ConstraintsIter::Owned(iter) => iter.size_hint(),
            ConstraintsIter::Shared(iter) => iter.size_hint(),
        }
    }
}

impl ExactSizeIterator for ConstraintsIter<'_> {}

impl<'a> IntoIterator for &'a Constraints {
    type Item = &'a Expr;
    type IntoIter = ConstraintsIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Owning iterator over [`Constraints`], consuming the container.
pub enum ConstraintsIntoIter {
    /// Iterating over an owned Vec.
    Owned(std::vec::IntoIter<Expr>),
    /// Iterating over shared base + extra (clones Arc elements, moves extra).
    Shared(std::iter::Chain<std::vec::IntoIter<Expr>, std::vec::IntoIter<Expr>>),
}

impl Iterator for ConstraintsIntoIter {
    type Item = Expr;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ConstraintsIntoIter::Owned(iter) => iter.next(),
            ConstraintsIntoIter::Shared(iter) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            ConstraintsIntoIter::Owned(iter) => iter.size_hint(),
            ConstraintsIntoIter::Shared(iter) => iter.size_hint(),
        }
    }
}

impl ExactSizeIterator for ConstraintsIntoIter {}

impl IntoIterator for Constraints {
    type Item = Expr;
    type IntoIter = ConstraintsIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Constraints::Owned(v) => ConstraintsIntoIter::Owned(v.into_iter()),
            Constraints::Shared { base, extra } => {
                // Arc<[Expr]> is unsized so Arc::try_unwrap isn't available.
                // Expr is Arc-backed (O(1) clone per element), so to_vec() is cheap.
                let base_vec = base.to_vec();
                ConstraintsIntoIter::Shared(base_vec.into_iter().chain(extra))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chc::RuleBody;

    #[test]
    fn test_constraints_owned_basic() {
        let c = Constraints::Owned(vec![Expr::int_const(1), Expr::int_const(2)]);
        assert_eq!(c.len(), 2);
        assert!(!c.is_empty());
        assert_eq!(*c.last().expect("non-empty constraints"), Expr::int_const(2));

        let items: Vec<&Expr> = c.iter().collect();
        assert_eq!(items.len(), 2);
    }

    #[test]
    fn test_constraints_shared_no_extra() {
        let base: Arc<[Expr]> = vec![Expr::int_const(1), Expr::int_const(2)].into();
        let c = Constraints::Shared { base, extra: Vec::new() };
        assert_eq!(c.len(), 2);
        assert!(!c.is_empty());
        assert_eq!(*c.last().expect("non-empty constraints"), Expr::int_const(2));
    }

    #[test]
    fn test_constraints_shared_with_extra() {
        let base: Arc<[Expr]> = vec![Expr::int_const(1)].into();
        let c = Constraints::Shared { base, extra: vec![Expr::int_const(99)] };
        assert_eq!(c.len(), 2);
        // last() returns the last extra element.
        assert_eq!(*c.last().expect("non-empty constraints"), Expr::int_const(99));

        let items: Vec<&Expr> = c.iter().collect();
        assert_eq!(items.len(), 2);
        assert_eq!(*items[0], Expr::int_const(1));
        assert_eq!(*items[1], Expr::int_const(99));
    }

    #[test]
    fn test_constraints_shared_clone_shares_arc() {
        let base: Arc<[Expr]> = vec![Expr::int_const(1), Expr::int_const(2)].into();
        let c1 = Constraints::Shared { base: Arc::clone(&base), extra: vec![Expr::int_const(3)] };
        let c2 = Constraints::Shared { base: Arc::clone(&base), extra: vec![Expr::int_const(4)] };

        // Both share the same base allocation — this is the O(N²) → O(N) optimization.
        match (&c1, &c2) {
            (Constraints::Shared { base: b1, .. }, Constraints::Shared { base: b2, .. }) => {
                assert!(Arc::ptr_eq(b1, b2));
            }
            _ => panic!("expected Shared variants"),
        }
    }

    #[test]
    fn test_constraints_equality_across_variants() {
        let owned = Constraints::Owned(vec![Expr::int_const(1), Expr::int_const(2)]);
        let shared = Constraints::Shared {
            base: vec![Expr::int_const(1), Expr::int_const(2)].into(),
            extra: Vec::new(),
        };
        // Same logical content, different representations — should be equal.
        assert_eq!(owned, shared);
    }

    #[test]
    fn test_from_shared_base_produces_shared_constraints() {
        let base: Arc<[Expr]> = vec![Expr::int_const(10)].into();
        let body = RuleBody::from_shared_base(None, Arc::clone(&base), [Expr::int_const(20)]);
        assert_eq!(body.constraints.len(), 2);
        match &body.constraints {
            Constraints::Shared { base: b, extra } => {
                assert!(Arc::ptr_eq(b, &base));
                assert_eq!(extra.len(), 1);
            }
            Constraints::Owned(_) => panic!("expected Shared"),
        }
    }
}
