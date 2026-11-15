// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! The canonical release owns an exact compiler-bound private AY component.

use crate::keyed::run_capture;
use crate::release::ReleaseSeal;
use anyhow::{Result, bail};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn helper_command(root: &Path, seal: &ReleaseSeal) -> Command {
    let mut command = Command::new(root.join("scripts/build-pinned-ay-cli.sh"));
    command
        .env("TRUST_MC_TRUST_TOOLCHAIN", &seal.compiler.sysroot)
        .env("TRUST_MC_TARGO", seal.compiler.sysroot.join("bin/targo"))
        .stderr(Stdio::inherit());
    command
}

pub(crate) fn prepare(root: &Path, seal: &ReleaseSeal) -> Result<PathBuf> {
    // The existing helper owns source/compiler/binary cache admission and builds
    // only on a missing complete matching receipt. It never accepts PATH AY.
    let output = run_capture(&mut helper_command(root, seal), "prepare compiler-bound private AY")?;
    let binary = PathBuf::from(output.trim());
    if !binary.is_absolute() || output.trim().lines().count() != 1 {
        bail!("private AY builder returned no single absolute helper path");
    }
    let checked = run_capture(
        helper_command(root, seal).arg("--check-path"),
        "recheck compiler-bound private AY",
    )?;
    if checked.trim() != binary.to_string_lossy() {
        bail!("private AY changed between build and receipt recheck");
    }
    Ok(binary)
}

pub(crate) fn stage(
    root: &Path,
    seal: &ReleaseSeal,
    binary: &Path,
    destination: &Path,
) -> Result<()> {
    // The script's existing interpreter selection is shared with its builder;
    // no ambient Python or second provenance implementation is introduced.
    let mut command = Command::new(root.join("scripts/stage-bundled-ay.sh"));
    command.arg(binary).arg(destination).arg(&seal.compiler.sysroot).arg(&seal.commit);
    run_capture(&mut command, "stage private AY closure")?;
    Ok(())
}
