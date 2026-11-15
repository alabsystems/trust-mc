// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `librustc_codegen_trust_mc.dylib`: the shim rustc's
//! `-Zcodegen-backend=<path>` loader calls.
//!
//! `rustc_interface::util::load_backend_from_dylib` looks up exactly one
//! symbol, `__rustc_codegen_backend`, of type `fn() -> Box<dyn CodegenBackend>`.
//! The engine lives in the `trust_mc_engine` rlib. What lives here is the
//! compiler identity handshake (plan S3): `build.rs` bakes the identity of the
//! compiler this dylib was built against, and the backend's `init` refuses to
//! run inside any other build.

#![feature(rustc_private)]
#![feature(cfg_version)]

#[cfg(not(test))]
extern crate rustc_codegen_ssa;
#[cfg(not(test))]
extern crate rustc_driver;
#[cfg(not(test))]
extern crate rustc_interface;
#[cfg(not(test))]
extern crate rustc_session;

mod identity;

#[cfg(not(test))]
use identity::{BakedIdentity, check_identity, read_provenance};

/// The compiler this dylib was built against, as `build.rs` measured it.
#[cfg(not(test))]
const BAKED: BakedIdentity<'static> = BakedIdentity {
    rustc_commit: env!("MC_BACKEND_RUSTC_COMMIT"),
    driver: env!("MC_BACKEND_DRIVER"),
    driver_sha256: env!("MC_BACKEND_DRIVER_SHA256"),
};

/// Compare [`BAKED`] with the compiler that loaded this dylib.
///
/// The PROVENANCE read is the loading compiler's own install
/// (`Sysroot::default`, derived from where its `librustc_driver` lives), not an
/// explicit `--sysroot`: on the driver's Trustc route that names the keyed Kani
/// library, which carries no compiler identity. A PROVENANCE that exists but
/// cannot be read is an error, never "absent". Only a dylib built without
/// PROVENANCE compares the commit in `rustc_interface`'s version string.
#[cfg(not(test))]
#[cfg(not(version("1.101")))]
type IdentitySession = rustc_session::Session;
#[cfg(all(not(test), version("1.101")))]
type IdentitySession = rustc_session::EarlySession;

#[cfg(not(test))]
fn verify_compiler_identity(sess: &IdentitySession) -> Result<(), String> {
    let sysroot = &sess.opts.sysroot.default;
    let provenance = read_provenance(&sysroot.join("PROVENANCE"))?;
    check_identity(
        &BAKED,
        &sysroot.display().to_string(),
        provenance.as_deref(),
        rustc_interface::util::rustc_version_str(),
    )
}

/// The codegen-backend entry point rustc resolves by name after `dlopen`.
#[cfg(not(test))]
#[unsafe(no_mangle)]
pub fn __rustc_codegen_backend() -> Box<dyn rustc_codegen_ssa::traits::CodegenBackend> {
    trust_mc_engine::make_backend_with_identity(trust_mc_engine::BackendIdentity {
        rustc_commit: BAKED.rustc_commit,
        driver: BAKED.driver,
        driver_sha256: BAKED.driver_sha256,
        verify: verify_compiler_identity,
    })
}
