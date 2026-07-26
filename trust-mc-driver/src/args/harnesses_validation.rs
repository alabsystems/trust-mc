// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Validation for the Kani-compatible `--harnesses` listing shortcut.

use clap::error::{Error, ErrorKind};

#[allow(clippy::fn_params_excessive_bools)]
pub(crate) fn validate_harnesses_shortcut(
    list_harnesses: bool,
    has_subcommand: bool,
    quiet: bool,
    has_trust_vc_bundle: bool,
) -> Result<(), Error> {
    if !list_harnesses {
        return Ok(());
    }

    if has_subcommand {
        return Err(Error::raw(
            ErrorKind::ArgumentConflict,
            "argument `--harnesses` cannot be used with a subcommand.",
        ));
    }

    if quiet {
        return Err(Error::raw(
            ErrorKind::ArgumentConflict,
            "The `--quiet` flag is not compatible with `--harnesses`, since the default `pretty` format prints to the terminal. Use `list --format json --quiet` or `list --format markdown --quiet` instead.",
        ));
    }

    if has_trust_vc_bundle {
        return Err(Error::raw(
            ErrorKind::ArgumentConflict,
            "argument `--harnesses` cannot be used with `--trust-vc-bundle`.",
        ));
    }

    Ok(())
}
