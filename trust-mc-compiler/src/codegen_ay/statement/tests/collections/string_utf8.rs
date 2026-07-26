// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! BMC StrFromUtf8 stub tests.
//!
//! The BMC `codegen_str_from_utf8_stub` resolves concrete byte slices via
//! `resolve_collection_base`, which requires proper map-base-ref registration.
//! Seeding this in unit tests requires MIR-level ref tracking that isn't
//! available through `seed_collections_local` alone.
//!
//! Integration coverage is provided by the compiletest harnesses
//! (boxslice1, boxslice2). Unit-level BMC tests are deferred to D3 (#3708).
