// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

/// Driver-side classification for why CHC solving ended in UNKNOWN.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SolverUnknownReason {
    Timeout,
    SolverError,
}

impl SolverUnknownReason {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Timeout => "Timeout",
            Self::SolverError => "SolverError",
        }
    }
}
