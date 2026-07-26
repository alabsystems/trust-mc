// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::StubKind;

impl StubKind {
    pub const fn is_primitive_cmp(self) -> bool {
        matches!(
            self,
            Self::PrimitivePartialEqEq
                | Self::PrimitivePartialEqNe
                | Self::PrimitivePartialOrdLt
                | Self::PrimitivePartialOrdLe
                | Self::PrimitivePartialOrdGt
                | Self::PrimitivePartialOrdGe
                | Self::OrdCmp
                | Self::OrdMin
                | Self::OrdMax
                | Self::OrdClamp
        )
    }

    /// BigRational stubs (unsupported in BMC, over-approximated in CHC).
    pub const fn is_big_rational(self) -> bool {
        matches!(
            self,
            Self::BigRationalNew
                | Self::BigRationalFrom
                | Self::BigRationalAdd
                | Self::BigRationalSub
                | Self::BigRationalMul
                | Self::BigRationalDiv
                | Self::BigRationalNeg
                | Self::BigRationalEq
                | Self::BigRationalLt
                | Self::BigRationalLe
                | Self::BigRationalGt
                | Self::BigRationalGe
                | Self::BigRationalClone
                | Self::BigRationalAddAssign
                | Self::BigRationalSubAssign
                | Self::BigRationalMulAssign
                | Self::BigRationalDivAssign
        )
    }
}
