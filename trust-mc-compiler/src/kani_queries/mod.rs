// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Define the communication between KaniCompiler and the codegen implementation.

use crate::args::Arguments;
use crate::kani_middle::kani_functions::{
    KaniFunction, find_kani_functions, validate_kani_functions,
};
use rustc_public::ty::FnDef;
use std::cell::{OnceCell, RefCell};
use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, Ordering};

thread_local! {
    pub(crate) static QUERY_DB: RefCell<QueryDb> = RefCell::new(QueryDb::default());
}

/// Whether `check_crate_items` has already run in this process.
static CRATE_ITEMS_CHECKED: AtomicBool = AtomicBool::new(false);

/// Claim this process's single `check_crate_items` run: `true` for the first
/// caller only.
///
/// The check runs from the top of `codegen_crate`, which the embedded binary
/// and the trustc-hosted dylib share. The binary's `after_analysis` claims it
/// only when the session will not reach `codegen_crate` (`-Z no-codegen`, or no
/// output that needs codegen), so neither path runs it twice. `codegen_crate`
/// makes a lost claim fatal rather than generating VCs unchecked.
pub(crate) fn claim_crate_items_check() -> bool {
    !CRATE_ITEMS_CHECKED.swap(true, Ordering::SeqCst)
}

/// This structure is only accessed via thread_local storage to ensure thread safety.
///
/// Design note: QueryDb intentionally wraps Arguments rather than merging with it because:
/// - Arguments is a clap-derived struct for CLI parsing (pure data, no runtime state)
/// - QueryDb adds runtime state: the kani_functions cache computed after parsing
/// - Merging would conflate parsing concerns with runtime state, breaking clap derive
#[derive(Debug, Default, Clone)]
pub(crate) struct QueryDb {
    args: Option<Arguments>,
    kani_functions: OnceCell<HashMap<KaniFunction, FnDef>>,
}

impl QueryDb {
    pub(crate) fn set_args(&mut self, args: Arguments) {
        self.args = Some(args);
    }

    /// Whether this database already carries the engine arguments.
    pub(crate) fn has_args(&self) -> bool {
        self.args.is_some()
    }

    pub(crate) fn args(&self) -> &Arguments {
        self.args.as_ref().expect("Arguments have not been initialized")
    }

    /// Return a map with model and intrinsic functions defined in Kani's library.
    ///
    /// For `kani_core`, those definitions live in the `core` library.
    ///
    /// We cache these definitions to avoid doing the lookup every time it is needed.
    /// The cache should not be used after the `rustc_public` context ends.
    /// For example, in the AY backend, we run the entire crate codegen under the same
    /// rustc_public context, which is defined by the scope of the rustc_public `run` callback.
    /// See the `codegen_crate` function in `crate::codegen_ay::compiler_interface`.
    /// It is OK to set the cache and use it inside the callback scope, however, the cache should
    /// not be accessible after that.
    ///
    /// For that, users should create a new QueryDb that does not outlive the callback scope.
    ///
    /// To ensure we don't accidentally use the cache outside of the callback context, we run a
    /// sanity check if we are reusing the cache.
    pub(crate) fn kani_functions(&self) -> &HashMap<KaniFunction, FnDef> {
        if let Some(kani_functions) = self.kani_functions.get() {
            // Sanity check the values stored to ensure the cache is being within the rustc_public
            // context used to populate the cache.
            validate_kani_functions(kani_functions);
            kani_functions
        } else {
            self.kani_functions.get_or_init(|| {
                // Find all kani functions
                find_kani_functions()
            })
        }
    }
}
