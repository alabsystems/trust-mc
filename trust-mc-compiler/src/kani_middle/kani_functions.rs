// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Kani function classification and lookup.
//!
//! Enum definitions and `try_get_kani_function` are in `trust_mc-kani-types` crate
//! (Part of #2997: subcrate split). This module re-exports them and adds
//! rustc-dependent lookup functions that cannot live in the foundation crate
//! (they depend on `attributes::fn_marker` and rustc types).

// Re-export all public items from trust_mc-kani-types so existing
// `use crate::kani_middle::kani_functions::*` imports continue to work.
pub(crate) use trust_mc_kani_types::kani_functions::{
    KaniFunction, KaniHook, KaniIntrinsic, KaniModel, try_get_kani_function,
};

use crate::kani_middle::attributes;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::FnDef;
use std::collections::HashMap;
use strum::IntoEnumIterator;
use tracing::debug;

/// Try to classify a `FnDef` as a `KaniFunction` by inspecting its `fn_marker` attribute.
///
/// This is the rustc-dependent counterpart of `try_get_kani_function` (string-based).
/// Standalone function instead of `TryFrom` impl because `KaniFunction` is in
/// `trust_mc-kani-types` (orphan rule). Part of #2997 subcrate split.
pub(crate) fn try_kani_function_from_fn_def(def: FnDef) -> Option<KaniFunction> {
    let value = attributes::fn_marker(def)?;
    try_get_kani_function(&value)
}

/// Try to classify an `Instance` as a `KaniFunction`.
///
/// Convenience wrapper around `try_kani_function_from_fn_def`.
pub(crate) fn try_kani_function_from_instance(instance: Instance) -> Option<KaniFunction> {
    let fn_attr = attributes::fn_marker(instance.def)?;
    try_get_kani_function(&fn_attr)
}

/// Find all Kani functions.
///
/// First try to find `kani` crate. If that exists, look for the items there.
/// If there's no Kani crate, look for the items in `core` since we could be using `kani_core`.
/// Note that users could have other `kani` crates, so we look in all the ones we find.
pub(crate) fn find_kani_functions() -> HashMap<KaniFunction, FnDef> {
    let mut kani = rustc_public::find_crates("kani");
    if kani.is_empty() {
        // In case we are using `kani_core`.
        kani.extend(rustc_public::find_crates("core"));
    }
    debug!(?kani, "find_kani_functions");
    let fns = kani
        .into_iter()
        .find_map(|krate| {
            let kani_funcs: HashMap<_, _> = krate
                .fn_defs()
                .into_iter()
                .filter_map(|fn_def| {
                    try_kani_function_from_fn_def(fn_def).map(|kani_function| {
                        debug!(?kani_function, ?fn_def, "Found kani function");
                        (kani_function, fn_def)
                    })
                })
                .collect();
            (!kani_funcs.is_empty()).then_some(kani_funcs)
        })
        .unwrap_or_default();
    if cfg!(debug_assertions) {
        validate_kani_functions(&fns);
    }
    fns
}

/// Ensure we have the valid definitions.
pub(crate) fn validate_kani_functions(kani_funcs: &HashMap<KaniFunction, FnDef>) {
    let mut missing = 0u8;
    for func in KaniIntrinsic::iter()
        .map(std::convert::Into::into)
        .chain(KaniModel::iter().map(std::convert::Into::into))
        .chain(KaniHook::iter().map(std::convert::Into::into))
    {
        if let Some(fn_def) = kani_funcs.get(&func) {
            assert_eq!(
                try_kani_function_from_fn_def(*fn_def),
                Some(func),
                "Unexpected function marker"
            );
        } else {
            tracing::error!(?func, "Missing kani function");
            missing += 1;
        }
    }
    if missing != 0 {
        tracing::error!("Failed to find `{missing}` trust_mc functions");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reexport_try_get_kani_function_works() {
        assert_eq!(try_get_kani_function("AssertHook"), Some(KaniFunction::Hook(KaniHook::Assert)));
    }
}
