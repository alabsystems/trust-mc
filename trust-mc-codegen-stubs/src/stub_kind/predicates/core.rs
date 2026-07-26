// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::StubKind;

impl StubKind {
    pub const fn is_slice_stub(self) -> bool {
        matches!(
            self,
            Self::SlicePartialEqEqual
                | Self::SliceIndexIndex
                | Self::IndexIndex
                | Self::IndexMut
                | Self::SliceGetUnchecked
                | Self::SliceIsEmpty
                | Self::SliceFirst
                | Self::SliceGet
                | Self::SlicePartitionPoint
                | Self::SliceLast
                | Self::SliceBinarySearchByKey
                | Self::SliceChunks
                | Self::SliceWindows
                | Self::MemchrMemchr
        )
    }

    pub const fn is_option_predicate(self) -> bool {
        matches!(self, Self::OptionIsSome | Self::OptionIsSomeAnd | Self::OptionIsNone)
    }

    pub const fn is_result_predicate(self) -> bool {
        matches!(self, Self::ResultIsOk | Self::ResultIsErr)
    }

    pub const fn is_primitive_clone(self) -> bool {
        matches!(self, Self::PrimitiveClone)
    }

    pub const fn is_unwrap_or(self) -> bool {
        matches!(self, Self::OptionUnwrapOr | Self::ResultUnwrapOr)
    }

    pub const fn is_unwrap_expect(self) -> bool {
        matches!(
            self,
            Self::OptionUnwrap
                | Self::OptionExpect
                | Self::OptionUnwrapUnchecked
                | Self::ResultUnwrap
                | Self::ResultExpect
                | Self::ResultUnwrapErr
        )
    }

    pub const fn is_unwrap_or_else(self) -> bool {
        matches!(self, Self::OptionUnwrapOrElse | Self::ResultUnwrapOrElse)
    }

    pub const fn is_combinator(self) -> bool {
        matches!(
            self,
            Self::OptionAndThen
                | Self::OptionOkOrElse
                | Self::OptionOkOr
                | Self::OptionMap
                | Self::OptionTake
                | Self::OptionMapOr
                | Self::ResultMap
                | Self::ResultAndThen
                | Self::ResultMapErr
                | Self::ResultOk
                | Self::ResultErr
        )
    }

    /// Option::copied/cloned — identity pass-through in CHC encoding (#3348).
    pub const fn is_option_copied(self) -> bool {
        matches!(self, Self::OptionCopied)
    }

    pub const fn is_ub_panic(self) -> bool {
        matches!(
            self,
            Self::UbCheckLanguageUb
                | Self::UbCheckMaybeIsAligned
                | Self::UbCheckMaybeIsNonoverlapping
                | Self::PreconditionCheck
                | Self::AssertInhabited
                | Self::PanicUnreachable
                | Self::PanicError
        )
    }

    pub const fn is_fmt(self) -> bool {
        matches!(
            self,
            Self::FmtArgumentNewDisplay
                | Self::FmtArgumentsNew
                | Self::FmtArgumentsFromStr
                | Self::FmtFormat
        )
    }
}
