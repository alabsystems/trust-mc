// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::property_model::CheckStatus;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fmt, fmt::Display};

/// The coverage data maps a function name to a set of coverage checks.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct CoverageResults {
    pub data: BTreeMap<String, Vec<CoverageCheck>>,
}

impl CoverageResults {
    pub(crate) fn empty() -> Self {
        Self { data: BTreeMap::new() }
    }
}

impl fmt::Display for CoverageResults {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (file, checks) in &self.data {
            let mut checks_by_function: BTreeMap<String, Vec<CoverageCheck>> = BTreeMap::new();

            // Group checks by function
            for check in checks {
                // Insert the check into the vector corresponding to its function
                checks_by_function.entry(check.function.clone()).or_default().push(check.clone());
            }

            for (function, checks) in checks_by_function {
                writeln!(f, "{file} ({function})")?;
                let mut sorted_checks: Vec<CoverageCheck> = checks.clone();
                sorted_checks.sort_by(|a, b| a.region.start.cmp(&b.region.start));
                for check in &sorted_checks {
                    writeln!(f, " * {} {}", check.region, check.status)?;
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) struct CoverageCheck {
    pub function: String,
    term: CoverageTerm,
    pub region: CoverageRegion,
    status: CheckStatus,
}

impl CoverageCheck {
    pub(crate) fn counter(
        function: String,
        counter: u32,
        region: CoverageRegion,
        status: CheckStatus,
    ) -> Self {
        Self { function, term: CoverageTerm::Counter(counter), region, status }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub(crate) enum CoverageTerm {
    Counter(u32),
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct CoverageRegion {
    pub file: String,
    pub start: (u32, u32),
    pub end: (u32, u32),
}

impl Display for CoverageRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{} - {}:{}", self.start.0, self.start.1, self.end.0, self.end.1)
    }
}
