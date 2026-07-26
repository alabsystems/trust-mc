// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! This module contains points-to analysis primitives, such as the graph and types representing its
//! nodes, and the analysis itself.

mod points_to_analysis;
mod points_to_graph;

pub(crate) use points_to_analysis::run_points_to_analysis;
pub(crate) use points_to_graph::{MemLoc, PointsToGraph};
