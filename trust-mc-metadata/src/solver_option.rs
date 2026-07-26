// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use serde::{Deserialize, Serialize};
use strum_macros::{AsRefStr, EnumString, VariantNames};

/// Solver options parsed from `#[kani::solver]` attributes.
///
/// When using the AY backend, the `--ay-solver` flag controls solver selection.
/// The `Binary` variant specifies a custom solver binary that must exist in PATH.
#[derive(Debug, Clone, AsRefStr, EnumString, VariantNames, PartialEq, Eq, Serialize, Deserialize)]
#[strum(serialize_all = "snake_case")]
pub enum SolverOption {
    /// Bitwuzla SMT solver
    Bitwuzla,

    /// CaDiCaL SAT solver
    Cadical,

    /// cvc5 SMT solver
    Cvc5,

    /// The kissat solver that is included in the trust_mc bundle
    Kissat,

    /// MiniSAT SAT solver
    Minisat,

    /// Z3 SMT solver
    Z3,

    /// A custom solver binary. The specified binary must exist in PATH.
    #[strum(disabled, serialize = "bin=<SAT_SOLVER_BINARY>")]
    Binary(String),
}
