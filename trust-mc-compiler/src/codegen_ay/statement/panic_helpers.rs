// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared panic helper classification for BMC statement/terminator lowering.

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
