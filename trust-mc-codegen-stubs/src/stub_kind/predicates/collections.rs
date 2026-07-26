// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::StubKind;

impl StubKind {
    pub const fn is_collection_predicate(self) -> bool {
        matches!(
            self,
            Self::VecIsEmpty
                | Self::StringIsEmpty
                | Self::VecContains
                | Self::VecEq
                | Self::StringContains
                | Self::StringStartsWith
                | Self::StringEndsWith
                | Self::StringIsAscii
        )
    }

    pub const fn is_vec_core(self) -> bool {
        matches!(
            self,
            Self::VecNew
                | Self::VecWithCapacity
                | Self::VecWithCapacityIn
                | Self::VecFromElem
                | Self::VecPush
                | Self::VecReserve
                | Self::VecReserveExact
                | Self::VecShrinkToFit
                | Self::VecPop
                | Self::VecLen
                | Self::VecCapacity
                | Self::VecResize
                | Self::VecSetLen
                | Self::VecClear
                | Self::VecClone
                | Self::VecDrop
                | Self::VecAsSlice
                | Self::VecAsPtr
                | Self::VecAsMutPtr
                | Self::VecExtendFromSlice
                | Self::VecExtendRange
                | Self::VecIsEmpty
                | Self::VecFromSlice
                | Self::VecAppendElements
                | Self::VecFromIter
                | Self::VecExtendWith
                | Self::VecSpareCapacityMut
                | Self::VecExtendTrusted
                | Self::VecIntoBoxedSlice
                | Self::VecSwap
                | Self::VecRetain
                | Self::VecAppend
                | Self::VecLast
                | Self::VecReverse
                | Self::VecDedup
                | Self::VecSplitOff
                | Self::VecSort
                | Self::VecDrain
                | Self::VecSplice
        )
    }

    pub const fn is_string_core(self) -> bool {
        matches!(
            self,
            Self::StringNew
                | Self::StringFrom
                | Self::StringFromRawParts
                | Self::StringLen
                | Self::StringPush
                | Self::StringPushStr
                | Self::StringClear
                | Self::StringClone
                | Self::StringTruncate
                | Self::StringFromUtf8Lossy
                | Self::StrFromUtf8
                | Self::IntParse
                | Self::SplitWhitespace
                | Self::SplitWhitespaceNext
                | Self::StringEq
                | Self::StringAsStr
                | Self::StringIntoBoxedStr
                | Self::StrBytesNth
                | Self::StrCharsNth
        )
    }

    /// Vec stubs that model capacity changes. Used by V1 RawVec dedup
    /// to record which Vec locals already have authoritative capacity
    /// constraints, so RawVec stubs skip redundant updates.
    /// Part of #1037 V1.
    pub const fn is_vec_capacity_modifier(self) -> bool {
        matches!(
            self,
            Self::VecPush
                | Self::VecReserve
                | Self::VecReserveExact
                | Self::VecShrinkToFit
                | Self::VecNew
                | Self::VecWithCapacity
                | Self::VecWithCapacityIn
                | Self::VecFromElem
                | Self::VecResize
                | Self::VecPop
                | Self::VecClear
                | Self::VecExtendFromSlice
                | Self::VecAppendElements
                | Self::VecExtendWith
                | Self::VecExtendTrusted
                | Self::VecAppend
                | Self::VecRetain
                | Self::VecDedup
                | Self::VecDrain
                | Self::VecSplice
                | Self::VecSplitOff
                | Self::VecFromIter
        )
    }

    pub const fn is_rawvec(self) -> bool {
        matches!(
            self,
            Self::RawVecNewIn
                | Self::RawVecCapacity
                | Self::RawVecGrowOne
                | Self::RawVecPtr
                | Self::RawVecFromNonNullIn
                | Self::RawVecDrop
                | Self::RawVecShrinkToFit
        )
    }

    pub const fn is_display_cow(self) -> bool {
        matches!(self, Self::CowToString | Self::DisplayToString)
    }

    pub const fn is_btreeset(self) -> bool {
        matches!(
            self,
            Self::BTreeSetNew
                | Self::BTreeSetInsert
                | Self::BTreeSetContains
                | Self::BTreeSetRemove
                | Self::BTreeSetLen
                | Self::BTreeSetIsEmpty
                | Self::BTreeSetClear
                | Self::BTreeSetClone
                | Self::BTreeSetIntoIter
                | Self::BTreeSetIter
                | Self::BTreeSetIterNext
        )
    }

    pub const fn is_hashset(self) -> bool {
        matches!(
            self,
            Self::HashSetNew
                | Self::HashSetInsert
                | Self::HashSetContains
                | Self::HashSetRemove
                | Self::HashSetLen
                | Self::HashSetIsEmpty
                | Self::HashSetClear
                | Self::HashSetClone
                | Self::HashSetIntoIter
                | Self::HashSetIter
                | Self::HashSetIterNext
        )
    }

    pub const fn is_btreemap_internal(self) -> bool {
        matches!(
            self,
            Self::BTreeMapEntry
                | Self::BTreeMapVacantInsert
                | Self::BTreeMapVacantInsertEntry
                | Self::BTreeMapOccupiedInsert
                | Self::BTreeMapOccupiedGetMut
                | Self::BTreeMapOccupiedIntoMut
                | Self::BTreeMapEntryOrInsert
                | Self::BTreeMapEntryOrInsertWith
                | Self::BTreeMapEntryOrInsertWithKey
                | Self::BTreeSearchTree
                | Self::BTreeNodeReborrow
                | Self::BTreeHandleIntoKv
                | Self::SetValZstDefault
        )
    }

    pub const fn is_iterator_adapter(self) -> bool {
        matches!(
            self,
            Self::IterMap
                | Self::IterFilter
                | Self::IterFilterMap
                | Self::IterZip
                | Self::IterFold
                | Self::IterSum
                | Self::MapNext
                | Self::FilterNext
                | Self::FilterMapNext
                | Self::ZipNext
                | Self::RangeIntoIter
                | Self::RangeSpecNext
                | Self::IterFlatten
                | Self::IterCollect
                | Self::FlattenNext
                | Self::ChainNext
                | Self::IterSizeHint
        )
    }

    /// Maps TrustMcMap/BTreeMap stubs to their HashMap equivalents.
    ///
    /// HashMap stubs pass through unchanged. TrustMcMap and BTreeMap stubs are
    /// remapped because all three map types share the same SMT Array model.
    /// Returns `None` for non-map stubs.
    ///
    /// Part of #2304: extracted from detect_hashmap_stub 21-arm match.
    pub const fn to_hashmap_equivalent(self) -> Option<StubKind> {
        match self {
            // HashMap stubs pass through
            Self::HashMapNew
            | Self::HashMapInsert
            | Self::HashMapGet
            | Self::HashMapGetMut
            | Self::HashMapContainsKey
            | Self::HashMapRemove
            | Self::HashMapLen
            | Self::HashMapIsEmpty
            | Self::HashMapClear
            | Self::HashMapClone
            | Self::HashMapDrop
            | Self::HashMapIntoIter
            | Self::HashMapIter
            | Self::HashMapIterNext => Some(self),
            // TrustMcMap -> HashMap (same SMT Array model, Part of #788)
            Self::TrustMcMapNew => Some(Self::HashMapNew),
            Self::TrustMcMapInsert => Some(Self::HashMapInsert),
            Self::TrustMcMapGet => Some(Self::HashMapGet),
            Self::TrustMcMapContainsKey => Some(Self::HashMapContainsKey),
            Self::TrustMcMapRemove => Some(Self::HashMapRemove),
            Self::TrustMcMapLen => Some(Self::HashMapLen),
            Self::TrustMcMapIsEmpty => Some(Self::HashMapIsEmpty),
            Self::TrustMcMapClear => Some(Self::HashMapClear),
            Self::TrustMcMapClone => Some(Self::HashMapClone),
            // BTreeMap -> HashMap (same SMT Array model, Part of #2125)
            Self::BTreeMapNew => Some(Self::HashMapNew),
            Self::BTreeMapInsert => Some(Self::HashMapInsert),
            Self::BTreeMapGet => Some(Self::HashMapGet),
            Self::BTreeMapGetMut => Some(Self::HashMapGetMut),
            Self::BTreeMapContainsKey => Some(Self::HashMapContainsKey),
            Self::BTreeMapRemove => Some(Self::HashMapRemove),
            Self::BTreeMapLen => Some(Self::HashMapLen),
            Self::BTreeMapIsEmpty => Some(Self::HashMapIsEmpty),
            Self::BTreeMapClear => Some(Self::HashMapClear),
            Self::BTreeMapClone => Some(Self::HashMapClone),
            _ => None, // partial dispatch: StubKind — non-map stubs
        }
    }
}
