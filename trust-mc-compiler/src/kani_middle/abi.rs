// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Type ABI layout information — re-export shim.
//!
//! `LayoutOf` is defined in `trust_mc-kani-types` crate (Part of #2997: subcrate split).
//! This module re-exports it so existing `use crate::kani_middle::abi::LayoutOf`
//! imports continue to work.

pub(crate) use trust_mc_kani_types::abi::LayoutOf;
