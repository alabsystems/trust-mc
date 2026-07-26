// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! StubKind facade.
//!
//! The enum definition lives in `stub_kind/variants/definition.rs`.

#[path = "variants/definition.rs"]
mod definition;

pub use definition::StubKind;
