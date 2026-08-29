// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared panic helper classification for BMC statement/terminator lowering.

use rustc_public::mir::Operand;

use super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// The panic message carried by a panic shim's arguments, if it is a literal.
    ///
    /// Every user panic funnels through a shim that takes the message as a
    /// `&'static str` FIRST argument: `kani::panic(msg)` (the `panic!` /
    /// `unreachable!` overrides in `library/std/src/lib.rs` pass
    /// `concat!($msg)` / `stringify!(..)` through deliberately),
    /// `panic_stub(t: &str)`, and `core::panicking::panic(msg)` /
    /// `Result::unwrap_failed(msg, _)`. Without this the operand was dropped and
    /// every one of them rendered as the label-derived "panic reached", so a
    /// report could not say WHICH panic fired.
    ///
    /// Returns None — the caller then records the violation with no message and
    /// keeps the old generic wording — when there is no argument, when the first
    /// argument is not a `&str` literal (e.g. a runtime-formatted
    /// `core::panicking::panic_fmt` `Arguments`), or when the literal is empty.
    pub(in crate::codegen_ay::statement) fn panic_message_from_args(
        &self,
        args: &[Operand],
    ) -> Option<String> {
        let message = self.try_extract_str_constant(args.first()?)?;
        (!message.is_empty()).then_some(message)
    }
}

pub(in crate::codegen_ay::statement) fn bmc_is_no_return_panic_helper(path: &str) -> bool {
    path.contains("core::panicking::")
        || path.contains("std::panicking::")
        || path.contains("core::result::unwrap_failed")
        || path.contains("std::result::unwrap_failed")
        || path.contains("core::option::unwrap_failed")
        || path.contains("std::option::unwrap_failed")
}

#[cfg(test)]
mod tests {
    use super::bmc_is_no_return_panic_helper;

    #[test]
    fn bmc_no_return_panic_helper_includes_unwrap_failed_shims() {
        assert!(bmc_is_no_return_panic_helper("core::result::unwrap_failed"));
        assert!(bmc_is_no_return_panic_helper("std::result::unwrap_failed"));
        assert!(bmc_is_no_return_panic_helper("core::option::unwrap_failed"));
        assert!(!bmc_is_no_return_panic_helper("core::result::Result::<u8, u8>::unwrap"));
    }
}
