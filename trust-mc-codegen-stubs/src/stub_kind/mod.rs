// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! StubKind module — enum variants, group bitmask, and predicates.
//!
//! Split from monolith stub_kind.rs — Part of #2408.
//! - `variants.rs`: StubKind enum definition (267 variants)
//! - `groups.rs`: StubGroup bitmask model + `group_mask()` for table-driven dispatch
//! - `predicates.rs`: `is_*` group membership queries (33 methods)

pub(crate) mod groups;
mod predicates;
mod variants;

pub use variants::StubKind;
