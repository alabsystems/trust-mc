// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Public library facade for native trust_mc compiler integration.
//!
//! The current compiler binary still owns the full rustc/MIR lowering path.
//! This library target exposes the first fail-closed native API shape for
//! callers that need an in-process encode boundary while those internals are
//! lifted behind stable public types.

pub mod native;

pub use native::{
    EncodedNativeVc, NativeEncodeError, NativeEncodeRequest, NativeEncodeResult,
    NativeEncodeUnsupported, NativeInput, NativeOperation, NativeProofMode, NativeProofProvenance,
    NativeVcKind, encode_native,
};

#[cfg(feature = "ay")]
pub use native::{
    NativeContractRef, NativeLocal, NativeObligationRef, NativeResourceLimits, NativeRustMirInput,
    NativeSnapshotIdentity, NativeSourceSpan, NativeToolIdentity, NativeTrustIrFunctionInput,
    NativeTrustIrModuleInput, NativeTypeLayout, NativeTypeRef, NativeVerifierEnvironment,
    NativeVerifierOptions, NativeVerifyRequest, PreparedNativeVerification,
    prepare_native_verification,
};
