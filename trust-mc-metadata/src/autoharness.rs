// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use strum_macros::{Display, EnumString};

/// For the autoharness subcommand, all of the user-defined functions we found,
/// which are "chosen" if we generated an automatic harness for them, and "skipped" otherwise.
/// We use ordered data structures so that the metadata is in alphabetical order.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AutoHarnessMetadata {
    /// Functions we generated automatic harnesses for.
    pub chosen: BTreeSet<String>,
    /// Map function names to the reason why we did not generate an automatic harness for that function.
    pub skipped: BTreeMap<String, AutoHarnessSkipReason>,
}

/// Reasons that trust_mc does not generate an automatic harness for a function.
#[derive(Debug, Clone, Serialize, Deserialize, Display, EnumString)]
// `trust_mcImpl` mirrors the `trust_mc` namespace; strum serialize is explicit.
#[allow(non_camel_case_types)]
pub enum AutoHarnessSkipReason {
    /// The function is generic.
    #[strum(serialize = "Generic Function")]
    GenericFn,
    /// A trust_mc-internal function: already a harness, implementation of a trust_mc associated item or trust_mc contract instrumentation functions).
    #[strum(serialize = "trust_mc implementation")]
    trust_mcImpl,
    /// At least one of the function's arguments does not implement kani::Arbitrary
    /// (The Vec<(String, String)> contains the list of (name, type) tuples for each argument that does not implement it
    #[strum(serialize = "Missing Arbitrary implementation for argument(s)")]
    MissingArbitraryImpl(Vec<(String, String)>),
    /// The function does not have a body.
    #[strum(serialize = "The function does not have a body")]
    NoBody,
    /// The function doesn't match the user's provided filters.
    #[strum(serialize = "Did not match provided filters")]
    UserFilter,
}
