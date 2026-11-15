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

/// `<sysroot>/lib` of the compiler cargo builds this crate with, which holds the
/// `librustc_driver` it links: the Trust seal under `targo`. Not a rustup
/// toolchain directory: that follows a moving channel link (and a targo build
/// sets no `RUSTUP_TOOLCHAIN`), while the sysroot names the exact build.
fn rustc_driver_rpath() -> String {
    active_rustc_sysroot_lib().expect("RUSTC must print a sysroot (`$RUSTC --print sysroot`)")
}

/// Configure the compiler to properly link the scanner binary with rustc's library.
pub fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");
    let rustc_lib = rustc_driver_rpath();
    println!("cargo:rustc-link-arg-bin=scan=-Wl,-rpath,{rustc_lib}");
}
