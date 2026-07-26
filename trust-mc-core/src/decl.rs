// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Declarations for solver-level constructs.
//!
//! These types mirror the declaration capabilities of `ay_bindings::Constraint`
//! but are backend-agnostic containers.

use std::sync::Arc;

use ay_bindings::Sort;

/// A declaration in the verification condition.
///
/// This mirrors SMT-LIB declarations but is solver-independent.
/// Emitters convert these to concrete solver commands.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Decl {
    /// A symbolic constant: `(declare-const name sort)`
    Const {
        /// The name of the constant.
        name: String,
        /// The sort (type) of the constant.
        sort: Sort,
    },

    /// A function declaration: `(declare-fun name (arg_sorts) ret_sort)`
    Fun {
        /// The name of the function.
        name: String,
        /// The sorts of the function arguments.
        arg_sorts: Vec<Sort>,
        /// The return sort of the function.
        ret_sort: Sort,
    },

    /// A datatype declaration.
    ///
    /// Stores the `DatatypeSort` behind an `Arc` so that cloning `Decl` is
    /// O(1) (refcount bump) instead of a deep copy of the name + constructors.
    Datatype {
        /// The Arc-wrapped datatype definition.
        datatype: Arc<ay_bindings::DatatypeSort>,
    },
}

impl Decl {
    /// Creates a new constant declaration.
    pub fn constant(name: impl Into<String>, sort: Sort) -> Self {
        Self::Const { name: name.into(), sort }
    }

    /// Creates a new function declaration.
    pub fn function(name: impl Into<String>, arg_sorts: Vec<Sort>, ret_sort: Sort) -> Self {
        Self::Fun { name: name.into(), arg_sorts, ret_sort }
    }

    /// Creates a new datatype declaration from an owned `DatatypeSort`.
    ///
    /// Wraps in `Arc` so subsequent clones of this `Decl` are O(1).
    pub fn datatype(datatype: ay_bindings::DatatypeSort) -> Self {
        Self::Datatype { datatype: Arc::new(datatype) }
    }

    /// Creates a new datatype declaration from an already-Arc-wrapped `DatatypeSort`.
    ///
    /// O(1) — preferred when the `DatatypeSort` is already behind an `Arc`.
    pub fn datatype_arc(datatype: Arc<ay_bindings::DatatypeSort>) -> Self {
        Self::Datatype { datatype }
    }

    /// Returns the name of this declaration.
    pub fn name(&self) -> &str {
        match self {
            Decl::Const { name, .. } => name,
            Decl::Fun { name, .. } => name,
            Decl::Datatype { datatype } => &datatype.name,
        }
    }

    /// Returns the `DatatypeSort` for Datatype declarations.
    pub fn datatype_sort(&self) -> Option<&ay_bindings::DatatypeSort> {
        match self {
            Decl::Datatype { datatype } => Some(datatype),
            _ => None,
        }
    }
}
