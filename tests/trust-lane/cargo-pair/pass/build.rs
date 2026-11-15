// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 cargo pair: the build script. Cargo compiles it for the host, so on the
//! Trustc route it must reach trustc with the host posture and no engine backend
//! (a build script the backend compiled would link nothing that runs). It hands
//! the library its operand bound and a cfg the library requires.

use std::env;
use std::fs;
use std::path::Path;

#[cfg(not(kani_host))]
compile_error!("build.rs is a host unit: it must be compiled with --cfg=kani_host");

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(pair_build_script_ran)");
    println!("cargo:rustc-cfg=pair_build_script_ran");
    let out = Path::new(&env::var("OUT_DIR").expect("cargo sets OUT_DIR")).join("bound.rs");
    fs::write(out, "pub const OPERAND_BOUND: u8 = 100;\n").expect("write bound.rs");
}
