// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! trust-ir wire v60's typed signature ABI (`FuncTy::abi`), which no trust-mc
//! lowering models.
//!
//! A recorded descriptor states how a call and a function entry move their
//! values on the producer's target: a by-value argument the caller passes
//! indirectly through a fresh copy (`caller_copy`), the extension of a narrow
//! argument, a hidden result buffer, an ignored source argument, and which
//! lowered parameters carry each source argument. trust-mc's BMC and CHC
//! lowerings model an entry and a call by the lowered parameter list alone.
//! Read as if the record were absent, a module whose transport differs could
//! be proved or refuted. The trust-ir reference interpreter
//! (`Interpreter::execute_function`) and trust-ir-build's ByteV1 reflector
//! refuse such a module for the same reason, and trust-mc does too, at every
//! entry:
//!
//! - the native-bundle boundary refuses the whole bundle by name, before
//!   validation hashes the module
//!   ([`crate::NativeTrustMcBundleError::TypedSignatureAbiNotModeled`]);
//! - the CHC translator adds an unconditional `error` rule with the
//!   [`crate::TrustIrChcUnsupportedReason::TypedSignatureAbiTransport`]
//!   diagnostic, so no proof exists and a refutation is demoted;
//! - the BMC translator adds an always-failing violation that names it.
//!
//! Every row of the table is read, whether a function uses it or not: a row
//! only a function pointer names still types a `CallIndirect`, and skipping a
//! row would erase its record silently. A signature with `abi: None` is the
//! legacy, unrecorded state of every module before wire v60; trust-mc keeps
//! reading it as before.

use trust_ir::Module;

/// The index in `module.func_types` of the first signature that records a
/// typed ABI, or `None` when no signature records one.
#[must_use]
pub fn first_typed_signature_abi(module: &Module) -> Option<usize> {
    module.func_types.iter().position(|signature| signature.abi.is_some())
}
