// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::env;
use std::path::PathBuf;
use std::process::Command;

macro_rules! path_str {
    ($input:expr) => {
        String::from(
            $input
                .iter()
                .collect::<PathBuf>()
                .to_str()
                .unwrap_or_else(|| panic!("Invalid path {}", stringify!($input))),
        )
    };
}

fn rustup_toolchain_lib() -> Option<String> {
    let rustup_home = env::var("RUSTUP_HOME").ok()?;
    let rustup_tc = env::var("RUSTUP_TOOLCHAIN").ok()?;
    Some(path_str!([&rustup_home, "toolchains", &rustup_tc, "lib"]))
}

fn active_rustc_sysroot_lib() -> Option<String> {
    let rustc = env::var_os("RUSTC")?;
    let output = Command::new(rustc).args(["--print", "sysroot"]).output().ok()?;
    if !output.status.success() {
        return None;
    }
    let sysroot = String::from_utf8(output.stdout).ok()?;
    let sysroot = sysroot.trim();
    if sysroot.is_empty() {
        return None;
    }
    Some(path_str!([sysroot, "lib"]))
}

fn rustc_driver_rpath() -> String {
    rustup_toolchain_lib()
        .or_else(active_rustc_sysroot_lib)
        .expect("RUSTUP_HOME/RUSTUP_TOOLCHAIN must be set, or RUSTC must print a sysroot")
}

/// Configure the compiler to properly link the scanner binary with rustc's library.
pub fn main() {
    println!("cargo:rerun-if-env-changed=RUSTUP_HOME");
    println!("cargo:rerun-if-env-changed=RUSTUP_TOOLCHAIN");
    println!("cargo:rerun-if-env-changed=RUSTC");
    let rustc_lib = rustc_driver_rpath();
    println!("cargo:rustc-link-arg-bin=scan=-Wl,-rpath,{rustc_lib}");
}
