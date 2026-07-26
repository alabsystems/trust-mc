// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Identifiers and source locations for property reporting.
//!
//! These types enable the driver to map verification failures back to
//! meaningful source locations and harness names.

use serde::{Deserialize, Serialize};

/// A unique identifier for a harness function.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct HarnessId {
    /// The mangled name of the harness function.
    pub mangled_name: String,
    /// The pretty-printed name for display.
    pub pretty_name: String,
}

impl HarnessId {
    /// Creates a new harness identifier.
    pub fn new(mangled_name: impl Into<String>, pretty_name: impl Into<String>) -> Self {
        Self { mangled_name: mangled_name.into(), pretty_name: pretty_name.into() }
    }
}

impl std::fmt::Display for HarnessId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.pretty_name)
    }
}

/// A unique identifier for a property check.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PropertyId {
    /// Unique identifier for this property within the harness.
    pub id: u32,
    /// Optional human-readable description.
    pub description: Option<String>,
}

impl PropertyId {
    /// Creates a new property identifier.
    pub fn new(id: u32) -> Self {
        Self { id, description: None }
    }

    /// Creates a new property identifier with a description.
    #[must_use]
    pub fn with_description(id: u32, description: impl Into<String>) -> Self {
        Self { id, description: Some(description.into()) }
    }
}

impl std::fmt::Display for PropertyId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.description {
            Some(desc) => write!(f, "{}: {}", self.id, desc),
            None => write!(f, "{}", self.id),
        }
    }
}

/// Source code location for diagnostic messages.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceLocation {
    /// Source file path.
    pub file: String,
    /// Line number (1-indexed).
    pub line: u32,
    /// Column number (1-indexed, optional).
    pub column: Option<u32>,
    /// Function name containing this location.
    pub function: Option<String>,
}

impl SourceLocation {
    /// Creates a new source location.
    pub fn new(file: impl Into<String>, line: u32) -> Self {
        Self { file: file.into(), line, column: None, function: None }
    }

    /// Sets the column number.
    #[must_use]
    pub fn with_column(mut self, column: u32) -> Self {
        self.column = Some(column);
        self
    }

    /// Sets the containing function name.
    #[must_use]
    pub fn with_function(mut self, function: impl Into<String>) -> Self {
        self.function = Some(function.into());
        self
    }
}

impl std::fmt::Display for SourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.file, self.line)?;
        if let Some(col) = self.column {
            write!(f, ":{}", col)?;
        }
        Ok(())
    }
}
