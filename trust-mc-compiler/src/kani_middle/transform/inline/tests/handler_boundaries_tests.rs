// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::FunctionInlinePass;

#[test]
fn test_has_special_codegen_handler_slice_contains() {
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::slice::<impl [char]>::contains"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler("<[char]>::contains"));
    assert!(!FunctionInlinePass::has_special_codegen_handler("core::str::<impl str>::contains"));
}

#[test]
fn test_has_special_codegen_handler_range_contains() {
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "std::ops::RangeInclusive::<u8>::contains::<u8>"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "<std::ops::RangeInclusive<u8> as std::ops::RangeBounds<u8>>::contains"
    ));
    assert!(FunctionInlinePass::has_special_codegen_handler(
        "core::ops::range::Range::<usize>::contains"
    ));
    assert!(!FunctionInlinePass::has_special_codegen_handler("my_crate::RangeBag::contains"));
}
