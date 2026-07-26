// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Static method-to-stub mapping tables for numeric type-based detection.
//! Converted from include!() to proper module per #2595.

use super::stubs::StubKind;

#[derive(Clone, Copy)]
pub(in crate::codegen_ay::chc) struct MethodStubSpec {
    pub(in crate::codegen_ay::chc) method: &'static str,
    pub(in crate::codegen_ay::chc) stub: StubKind,
}

pub(in crate::codegen_ay::chc) const BIGINT_METHOD_STUBS: &[MethodStubSpec] = &[
    MethodStubSpec { method: "abs", stub: StubKind::BigIntAbs },
    MethodStubSpec { method: "add", stub: StubKind::BigIntAdd },
    MethodStubSpec { method: "add_assign", stub: StubKind::BigIntAddAssign },
    MethodStubSpec { method: "bitand", stub: StubKind::BigIntBitAnd },
    MethodStubSpec { method: "bitor", stub: StubKind::BigIntBitOr },
    MethodStubSpec { method: "bitxor", stub: StubKind::BigIntBitXor },
    MethodStubSpec { method: "clone", stub: StubKind::BigIntClone },
    MethodStubSpec { method: "cmp", stub: StubKind::BigIntCmp },
    MethodStubSpec { method: "div", stub: StubKind::BigIntDiv },
    MethodStubSpec { method: "eq", stub: StubKind::BigIntEq },
    MethodStubSpec { method: "from", stub: StubKind::BigIntFrom },
    MethodStubSpec { method: "ge", stub: StubKind::BigIntGe },
    MethodStubSpec { method: "gt", stub: StubKind::BigIntGt },
    MethodStubSpec { method: "is_negative", stub: StubKind::BigIntIsNegative },
    MethodStubSpec { method: "is_zero", stub: StubKind::BigIntIsZero },
    MethodStubSpec { method: "le", stub: StubKind::BigIntLe },
    MethodStubSpec { method: "lt", stub: StubKind::BigIntLt },
    MethodStubSpec { method: "mul", stub: StubKind::BigIntMul },
    MethodStubSpec { method: "mul_assign", stub: StubKind::BigIntMulAssign },
    MethodStubSpec { method: "neg", stub: StubKind::BigIntNeg },
    // Part of #3687: normalize/normalized are BigUint internal housekeeping
    // (strip leading zeros in Vec<u64>). In the SMT Int model this is identity.
    MethodStubSpec { method: "normalize", stub: StubKind::BigIntClone },
    MethodStubSpec { method: "normalized", stub: StubKind::BigIntClone },
    MethodStubSpec { method: "one", stub: StubKind::BigIntOne },
    MethodStubSpec { method: "partial_cmp", stub: StubKind::BigIntPartialCmp },
    MethodStubSpec { method: "rem", stub: StubKind::BigIntRem },
    MethodStubSpec { method: "shl", stub: StubKind::BigIntShl },
    MethodStubSpec { method: "shl_assign", stub: StubKind::BigIntShlAssign },
    MethodStubSpec { method: "shr", stub: StubKind::BigIntShr },
    MethodStubSpec { method: "shr_assign", stub: StubKind::BigIntShrAssign },
    MethodStubSpec { method: "sub", stub: StubKind::BigIntSub },
    MethodStubSpec { method: "sub_assign", stub: StubKind::BigIntSubAssign },
    MethodStubSpec { method: "zero", stub: StubKind::BigIntZero },
];

pub(in crate::codegen_ay::chc) const BIGRATIONAL_METHOD_STUBS: &[MethodStubSpec] = &[
    MethodStubSpec { method: "add", stub: StubKind::BigRationalAdd },
    MethodStubSpec { method: "add_assign", stub: StubKind::BigRationalAddAssign },
    MethodStubSpec { method: "clone", stub: StubKind::BigRationalClone },
    MethodStubSpec { method: "div", stub: StubKind::BigRationalDiv },
    MethodStubSpec { method: "div_assign", stub: StubKind::BigRationalDivAssign },
    MethodStubSpec { method: "eq", stub: StubKind::BigRationalEq },
    MethodStubSpec { method: "from", stub: StubKind::BigRationalFrom },
    MethodStubSpec { method: "ge", stub: StubKind::BigRationalGe },
    MethodStubSpec { method: "gt", stub: StubKind::BigRationalGt },
    MethodStubSpec { method: "le", stub: StubKind::BigRationalLe },
    MethodStubSpec { method: "lt", stub: StubKind::BigRationalLt },
    MethodStubSpec { method: "mul", stub: StubKind::BigRationalMul },
    MethodStubSpec { method: "mul_assign", stub: StubKind::BigRationalMulAssign },
    MethodStubSpec { method: "neg", stub: StubKind::BigRationalNeg },
    MethodStubSpec { method: "new", stub: StubKind::BigRationalNew },
    MethodStubSpec { method: "sub", stub: StubKind::BigRationalSub },
    MethodStubSpec { method: "sub_assign", stub: StubKind::BigRationalSubAssign },
];

pub(in crate::codegen_ay::chc) fn lookup_method_stub(
    table: &'static [MethodStubSpec],
    method: &str,
) -> Option<StubKind> {
    table.binary_search_by_key(&method, |spec| spec.method).ok().map(|idx| table[idx].stub)
}
