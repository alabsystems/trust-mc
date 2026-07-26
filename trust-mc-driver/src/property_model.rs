// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Property model types for verification results.
//!
//! Defines the core property types (`Property`, `CheckStatus`, `RawSourceLocation`,
//! `TraceItem`, etc.) used by the AY backend, concrete playback, and result formatting.

use std::borrow::Cow;
use std::env;
use std::path::PathBuf;

use console::style;
use pathdiff::diff_paths;
use rustc_demangle::demangle;
use serde::{Deserialize, Deserializer, Serialize};

/// Struct that represents a single property in a set of verification results.
///
/// Note: `reach` is not part of the parsed data, but it's useful to annotate
/// its reachability status.
#[derive(Clone, Debug, Deserialize)]
pub(crate) struct Property {
    pub description: Cow<'static, str>,
    #[serde(rename = "property")]
    pub property_id: PropertyId,
    #[serde(rename = "sourceLocation")]
    pub source_location: RawSourceLocation,
    pub status: CheckStatus,
    pub trace: Option<Vec<TraceItem>>,
}

/// Somewhat-ish consistent format for naming properties.
#[derive(Clone, Debug)]
pub(crate) struct PropertyId {
    pub fn_name: Option<String>,
    pub class: Cow<'static, str>,
    pub id: u32,
}

impl Property {
    const COVER_PROPERTY_CLASS: &'static str = "cover";

    pub(crate) fn property_class(&self) -> &str {
        &self.property_id.class
    }

    /// Returns true if this is a cover property
    pub(crate) fn is_cover_property(&self) -> bool {
        self.property_id.class == Self::COVER_PROPERTY_CLASS
    }

    pub(crate) fn property_name(&self) -> String {
        let class = &self.property_id.class;
        let id = self.property_id.id;
        match &self.property_id.fn_name {
            Some(fn_name) => format!("{fn_name}.{class}.{id}"),
            None => format!("{class}.{id}"),
        }
    }

    pub(crate) fn has_property_class_format(string: &str) -> bool {
        string == "NaN" || string.chars().all(|c| c.is_ascii_lowercase() || c == '_' || c == '-')
    }
}

impl<'de> serde::Deserialize<'de> for PropertyId {
    /// Gets all property attributes from the property ID.
    ///
    /// In general, property IDs have the format `<function>.<class>.<counter>`.
    ///
    /// However, there are cases where we only get two attributes:
    ///  * `<class>.<counter>` (the function is a builtin)
    ///  * `<function>.<counter>` (missing function definition)
    ///
    /// In these cases, we try to determine if the attribute is a function or not
    /// based on its characters (we assume property classes are a combination
    /// of lowercase letters and the characters `_` and `-`). This heuristic is
    /// not completely reliable.
    fn deserialize<D>(d: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let id_str = String::deserialize(d)?;

        // Handle a special case that doesn't respect the format: recursion
        // unwinding assertions use `<function>.recursion` or just `.recursion`.
        if id_str.ends_with(".recursion") {
            let attributes: Vec<&str> = id_str.splitn(2, '.').collect();
            let fn_name = if attributes[0].is_empty() {
                None
            } else {
                Some(format!("{:#}", demangle(attributes[0])))
            };
            return Ok(PropertyId { fn_name, class: Cow::Borrowed("recursion"), id: 1 });
        }

        // Split the property name into three from the end, using `.` as the separator
        let property_attributes: Vec<&str> = id_str.rsplitn(3, '.').collect();
        let attributes_tuple = match property_attributes.len() {
            // The general case, where we get all the attributes
            3 => {
                // Since mangled function names may contain `.`, we check if
                // `property_attributes[1]` has the class format. If it doesn't,
                // it means we've split a function name, so we rebuild it and
                // demangle it.
                if Property::has_property_class_format(property_attributes[1]) {
                    let name = format!("{:#}", demangle(property_attributes[2]));
                    (
                        Some(name),
                        Cow::Owned(property_attributes[1].to_string()),
                        property_attributes[0],
                    )
                } else {
                    let full_name =
                        format!("{}.{}", property_attributes[2], property_attributes[1]);
                    let name = format!("{:#}", demangle(&full_name));
                    (Some(name), Cow::Borrowed("missing_definition"), property_attributes[0])
                }
            }
            2 => {
                // The case where `property_attributes[1]` could be a function
                // or a class. If it has the class format, then it's likely a
                // class (functions are usually mangled names which contain many
                // other symbols).
                if Property::has_property_class_format(property_attributes[1]) {
                    (None, Cow::Owned(property_attributes[1].to_string()), property_attributes[0])
                } else {
                    let name = format!("{:#}", demangle(property_attributes[1]));
                    (Some(name), Cow::Borrowed("missing_definition"), property_attributes[0])
                }
            }
            // The case we don't expect. It's best to fail with an informative message.
            _ => unreachable!("Found property which doesn't have 2 or 3 attributes"),
        };
        // Do more sanity checks, just in case.
        assert!(
            attributes_tuple.2.chars().all(|c| c.is_ascii_digit()),
            "Found property counter that doesn't match number format"
        );
        // Return tuple after converting counter from string into number.
        // Safe to do because we've checked the format earlier.
        Ok(PropertyId {
            fn_name: attributes_tuple.0,
            class: attributes_tuple.1,
            id: attributes_tuple.2.parse().map_err(|_| {
                serde::de::Error::custom("property ID should be a valid integer after format check")
            })?,
        })
    }
}

/// Raw source location from parsing/deserialization.
///
/// This is a **parsing-only** type where all fields are optional strings,
/// matching the CBMC XML / AY JSON format where fields may be absent.
/// For domain logic, prefer `trust-mc_core::ident::SourceLocation` which has
/// typed required fields (file: String, line: u32).
#[derive(Clone, Debug, Deserialize)]
pub(crate) struct RawSourceLocation {
    pub column: Option<String>,
    pub file: Option<String>,
    pub function: Option<String>,
    pub line: Option<String>,
}

impl RawSourceLocation {
    /// Determines if fundamental parts of a source location are missing.
    pub(crate) fn is_missing(&self) -> bool {
        self.file.is_none() && self.function.is_none()
    }
}

/// `Display` implement for `RawSourceLocation`.
///
/// This is used to format source locations for individual checks. But source
/// locations may be printed in a different way in other places (e.g., in the
/// "Failed Checks" summary at the end).
///
/// Source locations formatted this way will look like:
/// `<file>:<line>:<column> in function <function>`
/// if all attributes were specified. Otherwise, we:
///  * Omit `in function <function>` if the function isn't specified.
///  * Use `Unknown file` instead of `<file>:<line>:<column>` if the file isn't
///    specified.
///  * Lines and columns are only formatted if they were specified and preceding
///    attribute was formatted.
impl std::fmt::Display for RawSourceLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(file) = &self.file {
            let file_path = filepath(file);
            write!(f, "{file_path}")?;
            if let Some(line) = &self.line {
                write!(f, ":{line}")?;
                if let Some(column) = &self.column {
                    write!(f, ":{column}")?;
                }
            }
        } else {
            write!(f, "Unknown file")?;
        }
        if let Some(function) = &self.function {
            let demangled_function = demangle(function);
            write!(f, " in function {demangled_function:#}")?;
        }
        Ok(())
    }
}

/// Returns a path relative to the current working directory.
fn filepath(file: &str) -> String {
    let file_path = PathBuf::from(file);
    let Ok(cur_dir) = env::current_dir() else {
        return file.to_owned();
    };

    match diff_paths(file_path, cur_dir) {
        Some(diff_path) => {
            diff_path.into_os_string().into_string().unwrap_or_else(|_| file.to_owned())
        }
        None => file.to_owned(),
    }
}

/// Struct that represents traces.
///
/// In general, traces may include more information than this, but this is not
/// documented anywhere. So we ignore the rest for now.
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct TraceItem {
    pub step_type: Cow<'static, str>,
    pub lhs: Option<String>,
    pub source_location: Option<RawSourceLocation>,
    pub value: Option<TraceValue>,
}

/// Struct that represents a trace value.
///
/// Note: this struct can have a lot of different fields depending on the value type.
/// The fields included right now are relevant to primitive types and arrays.
#[derive(Clone, Debug, Deserialize)]
pub(crate) struct TraceValue {
    pub binary: Option<String>,
    pub data: Option<TraceData>,
    pub width: Option<u32>,
    // Invariant: elements is Some iff binary, data, and width are None.
    pub elements: Option<Vec<TraceArrayValue>>,
}

/// Struct that represents an element of an array in a trace.
#[derive(Clone, Debug, Deserialize)]
pub(crate) struct TraceArrayValue {
    pub value: TraceValue,
}

/// Enum that represents a trace data item.
#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub(crate) enum TraceData {
    NonBool(String),
    Bool(bool),
}

impl std::fmt::Display for TraceData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonBool(trace_data) => write!(f, "{trace_data}"),
            Self::Bool(trace_data) => write!(f, "{trace_data}"),
        }
    }
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "UPPERCASE")]
pub(crate) enum CheckStatus {
    Failure,
    Covered,   // for `code_coverage` properties only
    Satisfied, // for `cover` properties only
    Success,
    Undetermined,
    Unknown,
    Unreachable,
    Uncovered,     // for `code_coverage` properties only
    Unsatisfiable, // for `cover` properties only
}

impl std::fmt::Display for CheckStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let check_str = match self {
            CheckStatus::Satisfied => style("SATISFIED").green(),
            CheckStatus::Success => style("SUCCESS").green(),
            CheckStatus::Covered => style("COVERED").green(),
            CheckStatus::Uncovered => style("UNCOVERED").red(),
            CheckStatus::Failure => style("FAILURE").red(),
            CheckStatus::Unreachable => style("UNREACHABLE").yellow(),
            CheckStatus::Undetermined => style("UNDETERMINED").yellow(),
            // UNKNOWN: another UB property failed, so this property's result is inconclusive.
            CheckStatus::Unknown => style("UNDETERMINED").yellow(),
            CheckStatus::Unsatisfiable => style("UNSATISFIABLE").yellow(),
        };
        write!(f, "{check_str}")
    }
}
