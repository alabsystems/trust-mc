// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Unit tests for StubRegistry.
// Split from monolithic tests.rs by lookup layer and family (Part of #3649).

use super::{StubKind, StubRegistry};

fn lookup(path: &str) -> Option<StubKind> {
    StubRegistry::new().lookup(path)
}

mod registry_collections;
mod registry_core;
mod registry_iter_routes;
mod registry_maps_numeric;
mod stubkind_predicates;
mod suffix_common;
mod suffix_intrinsics;
mod suffix_maps_numeric;
mod suffix_sets_btree;
mod suffix_vec_iter_string;
