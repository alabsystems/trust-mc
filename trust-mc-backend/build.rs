// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bake the identity of the compiler this dylib is built against (plan S3).
//!
//! * `MC_BACKEND_RUSTC_COMMIT`: `commit-hash:` from `$RUSTC -vV`.
//! * `MC_BACKEND_DRIVER`: basename of the `librustc_driver-*` that
//!   `<sysroot>/bin/rustc` links (`otool -L` / `ldd`), or the only one in
//!   `<sysroot>/lib` when that cannot be read.
//! * `MC_BACKEND_DRIVER_SHA256`: `artifact_driver_sha256` from
//!   `<sysroot>/PROVENANCE`, empty when the toolchain has none. An unreadable
//!   PROVENANCE fails the build rather than baking an empty label.
//!
//! These private compile-time labels use `MC_*` because authenticated Targo
//! reserves `TRUST_*` for verification authority and rejects unrecognized
//! build-script writes to that namespace.
//!
//! No hashing of the (438 MB) driver happens here or at load time; see
//! `src/identity.rs` for why the PROVENANCE label is not a content hash.
//!
//! On macOS it also sets the install name to `@rpath/...`, so no build-host
//! path ships inside the dylib.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[path = "src/identity.rs"]
#[allow(dead_code)]
mod identity;

fn rustc_output(args: &[&str]) -> String {
    let rustc = env::var_os("RUSTC").expect("cargo sets RUSTC for build scripts");
    let out = Command::new(&rustc).args(args).output().unwrap_or_else(|e| {
        panic!("could not run {} {}: {e}", rustc.to_string_lossy(), args.join(" "))
    });
    assert!(out.status.success(), "{} {} failed", rustc.to_string_lossy(), args.join(" "));
    String::from_utf8(out.stdout).expect("rustc output is UTF-8")
}

fn is_driver_name(name: &str) -> bool {
    name.strip_prefix("librustc_driver-").is_some_and(|rest| {
        [".dylib", ".so", ".dll"].iter().any(|ext| {
            rest.strip_suffix(ext)
                .is_some_and(|hash| !hash.is_empty() && hash.bytes().all(|b| b.is_ascii_hexdigit()))
        })
    })
}

/// The `librustc_driver-*` basename `binary` links, as `otool -L` (macOS) or
/// `ldd` (Linux) reports it. A sysroot can keep an old driver beside the active
/// one during an atomic promotion; the executable names the active one.
fn linked_driver(binary: &Path) -> Option<String> {
    let tools: &[(&str, &[&str])] = &[("otool", &["-L"]), ("ldd", &[])];
    tools.iter().find_map(|(tool, args)| {
        let out = Command::new(tool).args(*args).arg(binary).output().ok()?;
        if !out.status.success() {
            return None;
        }
        String::from_utf8_lossy(&out.stdout)
            .split(|c: char| c.is_whitespace() || c == '(' || c == ')')
            .filter_map(|token| token.rsplit('/').next())
            .find(|name| is_driver_name(name))
            .map(str::to_owned)
    })
}

fn main() {
    println!("cargo:rerun-if-env-changed=RUSTC");
    println!("cargo:rerun-if-changed=src/identity.rs");

    let vv = rustc_output(&["-vV"]);
    let commit = vv
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .map(str::trim)
        .expect("rustc -vV reports a commit-hash");

    let sysroot = PathBuf::from(rustc_output(&["--print", "sysroot"]).trim());
    let lib = sysroot.join("lib");
    let exe = if cfg!(windows) { "rustc.exe" } else { "rustc" };
    let driver = linked_driver(&sysroot.join("bin").join(exe))
        .filter(|name| lib.join(name).is_file())
        .unwrap_or_else(|| {
            let mut drivers: Vec<String> = fs::read_dir(&lib)
                .unwrap_or_else(|e| panic!("cannot read {}: {e}", lib.display()))
                .filter_map(|entry| entry.ok()?.file_name().into_string().ok())
                .filter(|name| is_driver_name(name))
                .collect();
            drivers.sort();
            assert_eq!(
                drivers.len(),
                1,
                "{}/bin/{exe} names no librustc_driver, and {} does not hold exactly one: \
                 {drivers:?}",
                sysroot.display(),
                lib.display()
            );
            drivers.remove(0)
        });
    println!("cargo:rerun-if-changed={}", lib.join(&driver).display());

    let provenance_path = sysroot.join("PROVENANCE");
    let driver_sha256 = match identity::read_provenance(&provenance_path) {
        Ok(Some(text)) => {
            println!("cargo:rerun-if-changed={}", provenance_path.display());
            identity::provenance_value(&text, "artifact_driver_sha256").unwrap_or("").to_owned()
        }
        Ok(None) => String::new(),
        Err(e) => panic!("{e}"),
    };

    println!("cargo:rustc-env=MC_BACKEND_RUSTC_COMMIT={commit}");
    println!("cargo:rustc-env=MC_BACKEND_DRIVER={driver}");
    println!("cargo:rustc-env=MC_BACKEND_DRIVER_SHA256={driver_sha256}");

    // rustc gives a cdylib no install name of its own, so ld records the
    // absolute output path. trustc dlopens the file by path, so the name only
    // has to be relocatable.
    if env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("macos") {
        println!(
            "cargo:rustc-cdylib-link-arg=-Wl,-install_name,@rpath/librustc_codegen_trust_mc.dylib"
        );
    }
}
