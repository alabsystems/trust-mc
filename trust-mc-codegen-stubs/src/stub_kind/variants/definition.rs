// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! StubKind enum — semantic categories for stdlib function stubs.
//!
//! Extracted from stubs/stub_kind.rs — Part of #2154, #2408.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum StubKind {
    SlicePartialEqEqual,
    SliceIndexIndex,
    IndexIndex,
    /// IndexMut::index_mut — returns `&mut T` for deferred Vec store (#3348)
    IndexMut,
    /// Option::unwrap - extracts payload and propagates ref_pointees (#703)
    OptionUnwrap,
    /// Option::is_some(&self) -> bool - discriminant check (#1739)
    OptionIsSome,
    /// Option::is_some_and(self, f) -> bool - is_some && symbolic predicate result (#3687)
    OptionIsSomeAnd,
    /// Option::is_none(&self) -> bool - check if variant is None (discriminant check)
    OptionIsNone,
    /// Result::is_ok(&self) -> bool - discriminant check (#2125)
    ResultIsOk,
    /// Result::is_err(&self) -> bool - check if variant is Err (discriminant check)
    ResultIsErr,
    /// Option::unwrap_or(self, default) -> T - return inner value or default (#1836)
    OptionUnwrapOr,
    /// Result::unwrap_or(self, default) -> T - return Ok value or default (#1836)
    ResultUnwrapOr,
    /// Option::expect(self, msg) -> T - same as unwrap, message ignored (#1836)
    OptionExpect,
    /// Result::unwrap(self) -> T - extract Ok value (#1836)
    ResultUnwrap,
    /// Result::expect(self, msg) -> T - same as Result::unwrap, message ignored (#1836)
    ResultExpect,
    /// Result::unwrap_err(self) -> E - extract Err value (#3587)
    ResultUnwrapErr,
    /// Option::unwrap_or_else(self, f) -> T - over-approximate closure result (#1836)
    OptionUnwrapOrElse,
    /// Result::unwrap_or_else(self, f) -> T - over-approximate closure result (#1836)
    ResultUnwrapOrElse,
    /// Option::and_then(self, f) -> Option<U> - over-approximate closure result (#1836)
    OptionAndThen,
    /// Option::ok_or_else(self, f) -> Result<T, E> - over-approximate closure err (#1836)
    OptionOkOrElse,
    /// Result::map(self, f) -> Result<U, E> - over-approximate closure result (#1836)
    ResultMap,
    /// Result::and_then(self, f) -> Result<U, E> - over-approximate closure result (#1836)
    ResultAndThen,
    /// Result::map_err(self, f) -> Result<T, F> - over-approximate closure result (#1836)
    ResultMapErr,
    /// Option::map(self, f) -> Option<U> - over-approximate closure result (#1836)
    OptionMap,
    /// Option::take(&mut self) -> Option<T> - take value, leaving None (Part of #4208)
    OptionTake,
    /// Option::map_or(self, default, f) -> U - map with default (Part of #4208)
    OptionMapOr,
    /// Option::copied(self) -> Option<T> - dereference inner &T to T (#3348)
    /// In CHC encoding, this is identity (HashMap stubs already return raw V, not &V).
    OptionCopied,
    /// Result::ok(self) -> Option<T> - convert Result to Option (#1836)
    ResultOk,
    /// Result::err(self) -> Option<E> - convert Result to Option (#1836)
    ResultErr,
    // Primitive trait stubs (Part of #1240, #502) - for assert_eq!, Copy, comparison
    // These handle core/std trait impls on primitive types (u8, i32, etc.)
    /// PartialEq::eq for primitives - SMT equality (blocks assert_eq! macro)
    PrimitivePartialEqEq,
    /// PartialEq::ne for primitives - SMT not-equality
    PrimitivePartialEqNe,
    /// Clone::clone for primitives - identity (Copy semantics)
    PrimitiveClone,
    /// Ord::cmp for primitives - SMT comparison returning Ordering
    OrdCmp,
    /// Ord::min for primitives - ITE(self <= other, self, other)
    OrdMin,
    /// Ord::max for primitives - ITE(self >= other, self, other)
    OrdMax,
    /// Ord::clamp for primitives - ITE(self < min, min, ITE(self > max, max, self))
    OrdClamp,
    // Heap allocation intrinsics (#1100)
    /// alloc::alloc::alloc(layout) -> *mut u8 (and __rust_alloc)
    RustAlloc,
    /// alloc::alloc::alloc_zeroed(layout) -> *mut u8 (and __rust_alloc_zeroed)
    RustAllocZeroed,
    /// alloc::alloc::dealloc(ptr, layout) (and __rust_dealloc)
    RustDealloc,
    /// alloc::alloc::realloc(ptr, layout, new_size) -> *mut u8 (and __rust_realloc)
    RustRealloc,
    // Layout helper methods (#1112) - used by inlined allocation sequences
    /// Layout::size(&self) -> usize - return size field
    LayoutSize,
    /// Layout::align(&self) -> usize - return alignment field
    LayoutAlign,
    /// Layout::dangling(&self) -> NonNull<u8> - return dangling pointer
    LayoutDangling,
    /// Layout::is_size_align_valid(size, align) -> bool - return true (assume valid)
    LayoutIsSizeAlignValid,
    /// Layout::padding_needed_for(&self, align) -> usize - compute round-up padding
    LayoutPaddingNeededFor,
    /// Layout::array<T>(n) -> Result<Layout, LayoutError> - compute array layout (#1037)
    LayoutArray,
    /// Layout::array::inner(element_size, align, n) -> Result<Layout, LayoutError> (#3273)
    LayoutArrayInner,
    /// Layout::new<T>() -> Layout - create layout from type size/align (#1037)
    LayoutNew,
    /// Layout::calculate_layout_for(n) -> Result<(Layout, usize), LayoutError> (#2632)
    LayoutCalculateLayoutFor,
    /// Layout::for_value_raw(ptr) -> Layout - compute Layout from raw pointer (#2632)
    LayoutForValueRaw,
    /// Layout::from_size_align(size, align) -> Result<Layout, LayoutError> (#2632)
    LayoutFromSizeAlign,
    // Pointer operation stubs (Part of #1037) - raw pointer arithmetic/access
    /// *mut T::add(count) -> *mut T - pointer arithmetic (ptr + count * sizeof(T))
    PtrAdd,
    /// *mut T::sub(count) -> *mut T - pointer arithmetic (#2632)
    PtrSub,
    /// *mut T::write(value) - raw pointer store (no drop, just store)
    PtrWrite,
    /// std::ptr::read(ptr) -> T - raw pointer load
    PtrRead,
    /// *mut T::wrapping_add(count) -> *mut T - wrapping pointer addition (#2632)
    PtrWrappingAdd,
    /// *mut T::wrapping_sub(count) -> *mut T - wrapping pointer subtraction (#2632)
    PtrWrappingSub,
    /// *mut T::wrapping_offset(count) -> *mut T - wrapping pointer offset (#2632)
    PtrWrappingOffset,
    /// *mut T::wrapping_byte_offset(count) -> *mut T - wrapping byte offset, no sizeof(T) scaling (#3510)
    PtrWrappingByteOffset,
    /// *mut T::wrapping_byte_add(count) -> *mut T - wrapping byte add, no sizeof(T) scaling (#3514)
    PtrWrappingByteAdd,
    /// *mut T::wrapping_byte_sub(count) -> *mut T - wrapping byte sub, no sizeof(T) scaling (#3514)
    PtrWrappingByteSub,
    /// *mut T::with_metadata_of(ptr) -> *mut T - pointer metadata transfer (#2632)
    PtrWithMetadataOf,
    /// std::intrinsics::assert_inhabited — compile-time inhabitedness check, no-op at verification
    AssertInhabited,
    /// std::mem::MaybeUninit::<T>::as_ptr — identity (transparent wrapper, return inner pointer)
    MaybeUninitAsPtr,
    /// char::from_u32_unchecked(u32) -> char — identity (Part of #3470)
    /// Used by kani::Arbitrary for char. Without this stub the call becomes an
    /// uninterpreted function, breaking the assume-constraint chain.
    CharFromU32Unchecked,
    /// core::slice::<impl [T]>::get_unchecked — unchecked element access (unconstrained pass-through)
    SliceGetUnchecked,
    /// core::slice::<impl [T]>::as_ptr(&self) -> *const T — pointer identity (Part of #3104)
    SliceAsPtr,
    /// core::slice::<impl [T]>::as_mut_ptr(&mut self) -> *mut T — pointer identity (Part of #3104)
    SliceAsMutPtr,
    /// core::slice::<impl [T]>::is_empty(&self) -> bool — returns len == 0 (Part of #3713)
    SliceIsEmpty,
    /// core::slice::<impl [T]>::first(&self) -> Option<&T> — first element or None (Part of #3768)
    SliceFirst,
    /// core::slice::<impl [T]>::get(&self, index) -> Option<&T> — checked element access (Part of #4174)
    SliceGet,
    /// core::slice::<impl [T]>::partition_point — binary search returning 0..=len (Part of dterm#6841)
    SlicePartitionPoint,
    /// core::slice::<impl [T]>::last(&self) -> Option<&T> — last element or None (Part of #4208)
    SliceLast,
    /// core::slice::<impl [T]>::binary_search_by_key — returns Result<usize, usize> (Part of #4208)
    SliceBinarySearchByKey,
    /// core::slice::<impl [T]>::chunks(&self, size) -> Chunks<T> — chunked iterator (Part of #4208)
    SliceChunks,
    /// core::slice::<impl [T]>::windows(&self, size) -> Windows<T> — sliding window iterator (Part of #4208)
    SliceWindows,
    /// core::slice::memchr::{memchr,memchr_naive,memchr_aligned} (module match also covers
    /// memrchr) — Option<usize> = index of the needle byte in the haystack, else None. SIMD
    /// stdlib with no inlinable MIR; modeled as a SOUND over-approximation (nondet Option;
    /// when Some, index <= haystack.len() — the encoding's single tightening).
    MemchrMemchr,
    /// std::ptr::Alignment::new(align) -> Option<Alignment> - validate alignment value
    AlignmentNew,
    /// std::ptr::Alignment::as_usize(&self) -> usize - return alignment value
    AlignmentAsUsize,
    /// std::alloc::Layout::max_size_for_align(align) -> usize - max size for alignment
    LayoutMaxSizeForAlign,
    /// __rust_no_alloc_shim_is_unstable_v2 - no-op unstable shim signal
    RustNoAllocShimIsUnstable,
    // NonNull/Option allocation helpers (#1112) - needed for allocation path
    /// NonNull::new(ptr) -> Option<NonNull<T>>
    NonNullNew,
    /// NonNull::slice_from_raw_parts(ptr, len) -> NonNull<[T]>
    NonNullSliceFromRawParts,
    /// NonNull::<[T]>::as_non_null_ptr() -> NonNull<T> - extract data pointer from slice ptr
    NonNullAsNonNullPtr,
    /// NonNull::dangling() -> NonNull<T> - return well-aligned non-null pointer (#1039)
    NonNullDangling,
    /// NonNull::<[T]>::as_mut_ptr() -> *mut T - extract mutable data pointer from slice ptr
    NonNullAsMutPtr,
    /// NonNull::<T>::cast<U>() -> NonNull<U> - reinterpret cast (#2632)
    NonNullCast,
    /// Option::ok_or(self, err) -> Result<T, E> - for allocation result handling
    OptionOkOr,
    /// Box::<T>::new(value) -> Box<T> - allocate and initialize (#2745)
    BoxNew,
    /// Box::into_raw_with_allocator(self) -> (*mut T, A) - decompose Box into pointer and allocator
    BoxIntoRawWithAllocator,
    /// Unique::<T>::new_unchecked(ptr) -> Unique<T> - pointer identity (#1739)
    UniqueNewUnchecked,
    /// Vec::from_raw_parts_in(ptr, len, cap, alloc) -> Vec<T, A> - create Vec from raw parts
    VecFromRawPartsIn,
    /// <[T]>::into_vec / alloc::slice::hack::into_vec — Box<[T]> to Vec<T> (#2967)
    /// The vec![...] macro expansion path. Models data transfer from heap to abstract Vec.
    SliceIntoVec,
    // RawVec stubs (Part of #1037) - low-level buffer management
    // RawVec is Vec's internal allocation layer - must be stubbed when MIR bodies unavailable
    /// RawVec::new_in(alloc) -> RawVec<T, A> - create empty buffer
    RawVecNewIn,
    /// RawVec::capacity(&self) -> usize - return buffer capacity
    RawVecCapacity,
    /// RawVec::grow_one(&mut self) - grow buffer by one element
    RawVecGrowOne,
    /// RawVec::ptr(&self) -> *mut T - return buffer pointer
    RawVecPtr,
    /// RawVec::from_nonnull_in(ptr, cap, alloc) -> RawVec<T, A> (#1841)
    RawVecFromNonNullIn,
    /// <RawVec<T, A> as Drop>::drop(&mut self) - no-op for verification (#1841)
    RawVecDrop,
    /// RawVec::shrink_to_fit(&mut self) - no-op, old capacity is over-approx (#2665)
    RawVecShrinkToFit,
    // Try trait stubs (Part of #1100) - needed for ? operator in allocation paths
    // Since allocation never fails (--no-malloc-may-fail), always return success variant.
    /// std::ops::Try::branch(self) -> ControlFlow<Residual, Output>
    TryBranch,
    /// std::ops::FromResidual::from_residual - should never be called (branch returns Continue)
    FromResidualFromResidual,
    /// Panic functions unreachable in verified code (alloc error handler only).
    /// Note: panic_nounwind/panic_nounwind_fmt reclassified to PanicError (#3300)
    /// because checked arithmetic overflow paths (e.g., ptr.offset) call them.
    PanicUnreachable,
    /// Reachable panic paths that emit error() rules (panic, assert_failed) (#2252)
    PanicError,
    // Pointer operation stubs (Part of #1100) - pointer cast/check intrinsics
    /// *const T::is_null::runtime() - null check intrinsic (compare pointer with null)
    PtrIsNullRuntime,
    /// *mut T::is_null() - null check (compare pointer with null)
    PtrIsNull,
    /// *mut T::cast_const() -> *const T - return same pointer
    PtrCastConst,
    /// *mut T::cast<U>() -> *mut U - reinterpret cast (return same pointer)
    PtrCast,
    /// core::ub_checks::check_language_ub() - UB check (assume safe, skip)
    UbCheckLanguageUb,
    /// core::ub_checks::maybe_is_aligned_and_not_null() - alignment/null check (assume safe, return true)
    UbCheckMaybeIsAligned,
    /// core::ub_checks::maybe_is_nonoverlapping() - overlap check (assume safe, return true)
    UbCheckMaybeIsNonoverlapping,
    /// NonNull::new_unchecked::precondition_check() - precondition check (assume safe, skip)
    PreconditionCheck,
    /// std::mem::size_of::<T>() -> usize - return compile-time size constant
    MemSizeOf,
    /// std::mem::align_of::<T>() -> usize - return compile-time alignment constant
    MemAlignOf,
    /// PartialOrd::lt for primitives - SMT less-than comparison
    PrimitivePartialOrdLt,
    /// PartialOrd::le for primitives - SMT less-or-equal comparison
    PrimitivePartialOrdLe,
    /// PartialOrd::gt for primitives - SMT greater-than comparison
    PrimitivePartialOrdGt,
    /// PartialOrd::ge for primitives - SMT greater-or-equal comparison
    PrimitivePartialOrdGe,
    // Formatting stubs (Part of #1100) - panic formatting helpers
    /// fmt::rt::Argument::new_display() - formatting argument constructor (diverging path)
    FmtArgumentNewDisplay,
    /// fmt::Arguments::new() - formatting arguments constructor (diverging path)
    FmtArgumentsNew,
    /// fmt::Arguments::from_str() - formatting from string (diverging path)
    FmtArgumentsFromStr,
    // Additional allocation-path stubs (Part of #1100)
    /// Layout::from_size_align_unchecked(size, align) -> Layout - create Layout without validation
    LayoutFromSizeAlignUnchecked,
    /// Allocator::allocate(&self, layout) -> Result<NonNull<[u8]>, AllocError>
    AllocatorAllocate,
    /// NonNull::as_ptr(self) -> *mut T - convert NonNull to raw pointer
    NonNullAsPtr,
    /// NonZero::get(self) -> T - extract inner value from NonZero wrapper
    NonZeroGet,
    /// ptr::without_provenance_mut(addr) -> *mut T - create dangling pointer from address
    WithoutProvenanceMut,
    /// ptr::without_provenance(addr) -> *const T - create dangling const pointer from address
    WithoutProvenance,
    /// ptr::null() / ptr::null_mut() -> *const T / *mut T - return null pointer (Part of #3323)
    PtrNull,
    /// *const T::addr(self) -> usize - get address from pointer
    PtrAddr,
    /// *mut T::with_addr(self, addr: usize) -> *mut T - pointer with new address (Part of #3492)
    PtrWithAddr,
    /// kani::mem::is_ptr_aligned<T>(ptr) -> bool - over-approximate as true (Part of #1229)
    KaniMemIsPtrAligned,
    /// kani::mem::is_inbounds<T>(ptr) -> bool - over-approximate as true (Part of #1229)
    KaniMemIsInbounds,
    /// kani::mem::assert_is_initialized<T>(ptr) - no-op (Part of #1229)
    KaniMemAssertIsInitialized,
    /// kani::mem::can_read_unaligned<T>(ptr) -> bool - over-approximate as true (Part of #3470)
    KaniMemCanReadUnaligned,
    /// kani::mem::can_dereference<T>(ptr) -> bool - over-approximate as true (Part of #3470)
    KaniMemCanDereference,
    /// kani::mem::can_write<T>(ptr) -> bool - over-approximate as true (Part of #1739 D1)
    KaniMemCanWrite,
    /// kani::mem::same_allocation<T>(ptr1, ptr2) -> bool - direct obj_id comparison (Part of #4249)
    KaniMemSameAllocation,
    /// Global::alloc_impl - low-level allocation implementation
    GlobalAllocImpl,
    /// handle_alloc_error::rt_error - allocation error handler (should not be reached)
    HandleAllocError,
    // BigInt stubs (Part of #734, #470)
    // Constructors
    BigIntFrom, // BigInt::from(primitive)
    BigIntOne,  // num_traits::One::one()
    BigIntZero, // num_traits::Zero::zero()
    // Predicates
    BigIntIsZero,     // num_traits::Zero::is_zero()
    BigIntIsNegative, // num_traits::Signed::is_negative()
    // Arithmetic operations
    BigIntAdd, // core::ops::Add::add
    BigIntSub, // core::ops::Sub::sub
    BigIntMul, // core::ops::Mul::mul
    BigIntDiv, // core::ops::Div::div
    BigIntRem, // core::ops::Rem::rem
    BigIntNeg, // core::ops::Neg::neg
    BigIntAbs, // num_traits::Signed::abs
    // Compound assignment
    BigIntMulAssign, // core::ops::MulAssign::mul_assign
    BigIntAddAssign, // core::ops::AddAssign::add_assign
    BigIntSubAssign, // core::ops::SubAssign::sub_assign
    // Comparisons (Part of #734)
    BigIntEq,         // PartialEq::eq
    BigIntCmp,        // Ord::cmp
    BigIntPartialCmp, // PartialOrd::partial_cmp
    BigIntLt,         // PartialOrd::lt  (a < b)
    BigIntLe,         // PartialOrd::le  (a <= b)
    BigIntGt,         // PartialOrd::gt  (a > b)
    BigIntGe,         // PartialOrd::ge  (a >= b)
    // Utility
    BigIntClone, // Clone::clone
    // Bit shifts (Part of #742)
    BigIntShl,       // core::ops::Shl::shl (left shift = multiply by 2^n)
    BigIntShr,       // core::ops::Shr::shr (right shift = floor divide by 2^n)
    BigIntShlAssign, // core::ops::ShlAssign::shl_assign
    BigIntShrAssign, // core::ops::ShrAssign::shr_assign
    // Bitwise operations (Part of #742)
    // Note: Bitwise ops on unbounded Int are modeled as nondet (sound over-approximation)
    BigIntBitAnd, // core::ops::BitAnd::bitand
    BigIntBitOr,  // core::ops::BitOr::bitor
    BigIntBitXor, // core::ops::BitXor::bitxor
    // BigRational stubs (Part of #911)
    // Modeled using SMT Real sort (rational fragment - no sqrt/transcendentals)
    // BigRational = numerator / denominator where denom != 0
    BigRationalNew,   // BigRational::new(numer: BigInt, denom: BigInt)
    BigRationalFrom,  // BigRational::from(BigInt) -> BigRational (n/1)
    BigRationalAdd,   // core::ops::Add::add
    BigRationalSub,   // core::ops::Sub::sub
    BigRationalMul,   // core::ops::Mul::mul
    BigRationalDiv,   // core::ops::Div::div
    BigRationalNeg,   // core::ops::Neg::neg
    BigRationalEq,    // PartialEq::eq
    BigRationalLt,    // PartialOrd::lt
    BigRationalLe,    // PartialOrd::le
    BigRationalGt,    // PartialOrd::gt
    BigRationalGe,    // PartialOrd::ge
    BigRationalClone, // Clone::clone
    // Compound assignment operations (Part of #911 follow-up)
    BigRationalAddAssign, // core::ops::AddAssign::add_assign
    BigRationalSubAssign, // core::ops::SubAssign::sub_assign
    BigRationalMulAssign, // core::ops::MulAssign::mul_assign
    BigRationalDivAssign, // core::ops::DivAssign::div_assign
    // HashMap stubs (Part of #788, #772, #471)
    // Modeled as Array<KeySort, Option<ValueSort>> using SMT Array theory
    HashMapNew,         // HashMap::new() or HashMap::default()
    HashMapInsert,      // HashMap::insert(&mut self, k, v) -> Option<V>
    HashMapGet,         // HashMap::get(&self, k) -> Option<&V>
    HashMapGetMut,      // HashMap::get_mut(&mut self, k) -> Option<&mut V>
    HashMapContainsKey, // HashMap::contains_key(&self, k) -> bool
    HashMapRemove,      // HashMap::remove(&mut self, k) -> Option<V>
    HashMapLen,         // HashMap::len(&self) -> usize
    HashMapIsEmpty,     // HashMap::is_empty(&self) -> bool
    HashMapClear,       // HashMap::clear(&mut self)
    HashMapClone,       // Clone::clone(&self) -> HashMap
    HashMapDrop,        // <HashMap/BTreeMap as Drop>::drop(&mut self) - no-op in verifier
    // TrustMcMap stubs (Part of #788 - verification-friendly HashMap)
    // Same SMT Array model but uses marker functions that don't inline to hashbrown
    TrustMcMapNew,         // TrustMcMap::new()
    TrustMcMapInsert,      // TrustMcMap::insert(&mut self, k, v) -> Option<V>
    TrustMcMapGet,         // TrustMcMap::get(&self, k) -> Option<&V>
    TrustMcMapContainsKey, // TrustMcMap::contains_key(&self, k) -> bool
    TrustMcMapRemove,      // TrustMcMap::remove(&mut self, k) -> Option<V>
    TrustMcMapLen,         // TrustMcMap::len(&self) -> usize
    TrustMcMapIsEmpty,     // TrustMcMap::is_empty(&self) -> bool
    TrustMcMapClear,       // TrustMcMap::clear(&mut self)
    TrustMcMapClone,       // Clone::clone(&self) -> TrustMcMap
    // TrustMcMap iterator stubs (Part of #1812)
    TrustMcMapIntoIter, // <TrustMcMap as IntoIterator>::into_iter(self) -> TrustMcMapIntoIter
    TrustMcMapIterNext, // TrustMcMapIntoIter::next(&mut self) -> Option<(K, V)>
    // Vec stubs (Part of #1312)
    // Modeled as struct with (ptr, len, cap) fields
    VecNew,          // Vec::new()
    VecWithCapacity, // Vec::with_capacity(cap)
    VecFromElem,     // alloc::vec::from_elem(elem, n) — `vec![val; n]` macro (Part of #3348)
    /// <Vec<T> as From<&[T]>>::from — create Vec from slice (#3673)
    VecFromSlice,
    VecPush,            // Vec::push(&mut self, value)
    VecInsert,          // Vec::insert(&mut self, index, element)
    VecReserve,         // Vec::reserve(&mut self, additional)
    VecReserveExact,    // Vec::reserve_exact(&mut self, additional)
    VecShrinkToFit,     // Vec::shrink_to_fit(&mut self)
    VecPop,             // Vec::pop(&mut self) -> Option<T>
    VecRemove,          // Vec::remove(&mut self, index: usize) -> T
    VecLen,             // Vec::len(&self) -> usize
    VecCapacity,        // Vec::capacity(&self) -> usize
    VecIsEmpty,         // Vec::is_empty(&self) -> bool
    VecResize,          // Vec::resize(&mut self, new_len, value) (Part of #3348)
    VecSetLen,          // Vec::set_len(&mut self, new_len) — unsafe len-only mutation
    VecClear,           // Vec::clear(&mut self)
    VecTruncate,        // Vec::truncate(&mut self, len)
    VecClone,           // Clone::clone(&self) -> Vec
    VecDrop,            // <Vec<T, A> as Drop>::drop(&mut self) - no-op in verifier
    VecContains,        // Vec::contains(&self, &T) -> bool (Part of #2125 Phase 2)
    VecEq,              // PartialEq::eq(&Vec<T>, &Vec<T>) -> bool (Part of #3348)
    VecAsSlice,         // Vec::as_slice(&self) -> &[T] (#1037)
    VecAsPtr,           // Vec::as_ptr(&self) -> *const T (#1037)
    VecAsMutPtr,        // Vec::as_mut_ptr(&mut self) -> *mut T (#1037)
    VecIntoIter,        // Vec::into_iter(self) -> IntoIter<T> (#1611)
    VecIter,            // Vec::iter(&self) -> Iter<T> (Part of #1751)
    VecIterMut,         // Vec::iter_mut(&mut self) -> IterMut<T> (Part of #1751)
    VecExtendFromSlice, // Vec::extend_from_slice(&mut self, &[T]) (Part of #3348)
    VecExtendRange,     // Vec::extend with Range/RangeInclusive source (#3607 D3)
    // Additional Vec stubs (Part of #4208) — high-impact methods for dterm Kani proofs
    /// Vec::with_capacity_in(cap, alloc) — allocator variant of with_capacity
    VecWithCapacityIn,
    /// Vec::append_elements(&mut self, other: *const [T]) — internal extend helper
    VecAppendElements,
    /// <Vec<T> as FromIterator<T>>::from_iter — collect from iterator
    VecFromIter,
    /// Vec::extend_with(&mut self, n, value) — internal helper for resize
    VecExtendWith,
    /// Vec::spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] — internal buffer access
    VecSpareCapacityMut,
    /// Vec::extend_trusted(&mut self, iter) — internal for trusted-len iterators
    VecExtendTrusted,
    /// Vec::into_boxed_slice(self) -> Box<[T]> — convert Vec to boxed slice
    VecIntoBoxedSlice,
    /// Vec::swap(&mut self, a: usize, b: usize) — swap two elements
    VecSwap,
    /// Vec::retain(&mut self, f: F) — retain elements matching predicate
    VecRetain,
    /// Vec::append(&mut self, other: &mut Vec<T>) — move all elements from other
    VecAppend,
    /// Vec::last(&self) -> Option<&T> — last element (via Deref to slice)
    VecLast,
    /// Vec::reverse(&mut self) — reverse element order
    VecReverse,
    /// Vec::dedup(&mut self) — remove consecutive duplicates (Part of #4208)
    VecDedup,
    /// Vec::split_off(&mut self, at: usize) -> Vec<T> — split at index
    VecSplitOff,
    /// Vec::sort(&mut self) / sort_unstable — sort elements (via DerefMut to slice)
    VecSort,
    /// Vec::drain(&mut self, range) -> Drain<T> — remove and yield range of elements
    VecDrain,
    /// Vec::splice(range, replace_with) -> Splice<I> (Part of #4202)
    VecSplice,
    // Iterator stubs (Part of #1611)
    // IntoIter<T> modeled as (vec: Vec<T>, pos: usize)
    IntoIterNext, // IntoIter<T>::next(&mut self) -> Option<T>
    IterFlatten,  // Iterator::flatten(self) -> Flatten<Self> (#1694)
    IterCollect,  // Iterator::collect(self) -> B (#1694)
    FlattenNext,  // Flatten<I>::next(&mut self) -> Option<I::Item> (#1694)
    // Iterator adapters (Part of #1751)
    // These wrap an inner iterator and transform elements.
    // For verification, closures are modeled as opaque - results are over-approximated as symbolic.
    IterMap,       // Iterator::map(self, f) -> Map<Self, F> - applies closure to elements
    IterFilter,    // Iterator::filter(self, f) -> Filter<Self, F> - keeps matching elements
    IterFilterMap, // Iterator::filter_map(self, f) -> FilterMap<Self, F> - filter + map combined (#3692)
    IterZip,       // Iterator::zip(self, other) -> Zip<Self, Other> - pairs two iterators (#3381)
    IterFold,      // Iterator::fold(self, init, f) -> B - accumulates via closure
    IterSum,       // Iterator::sum(self) -> S - sum all elements (Sum trait)
    MapNext,       // Map<I, F>::next(&mut self) -> Option<B> - advance mapped iterator
    FilterNext,    // Filter<I, F>::next(&mut self) -> Option<I::Item> - advance filtered iterator
    FilterMapNext, // FilterMap<I, F>::next(&mut self) -> Option<B> - advance filter_mapped iterator (#3692)
    ZipNext, // Zip<A, B>::next(&mut self) -> Option<(A::Item, B::Item)> - advance zipped iterator (#3381)
    ChainNext, // Chain<A, B>::next(&mut self) -> Option<A::Item> - advance chained iterator (#4160)
    RangeIntoIter, // <Range<T> as IntoIterator>::into_iter — identity copy (#3002)
    RangeSpecNext, // Range<T>::spec_next - for-loop desugaring (#2323)
    /// RangeBounds::contains(&self, item) -> bool — over-approximate as true (Part of #3470)
    RangeBoundsContains,
    /// Iterator::size_hint(&self) -> (usize, Option<usize>) — symbolic over-approx (#3348)
    IterSizeHint,
    // HashMap/BTreeMap iterator stubs (Part of #1751)
    // HashMapIntoIter modeled as (map: Array<K, Option<V>>, keys: Array<usize, K>, pos: usize, len: usize)
    // We track a symbolic keys array that represents all keys in the map
    HashMapIntoIter, // HashMap::into_iter(self) -> IntoIter<K, V>
    HashMapIterNext, // IntoIter<K, V>::next(&mut self) -> Option<(K, V)>
    HashMapIter,     // HashMap::iter(&self) -> Iter<K, V>
    HashMapKeys,     // HashMap::keys(&self) -> Keys<K, V>
    HashMapValues,   // HashMap::values(&self) -> Values<K, V>
    // Numeric intrinsics for iterator support (Part of #1712)
    // Range iterators use checked arithmetic which must be stubbed in CHC mode
    /// i32::checked_add_unsigned(u32) -> Option<i32> - Range iterator increment (#1712)
    CheckedAddUnsigned,
    /// Option::unwrap_unchecked() -> T - unsafe extract, used by iterator (#1712)
    OptionUnwrapUnchecked,
    // String stubs (Part of #1312)
    // Modeled as struct with (ptr, len, cap) fields (like Vec<u8>)
    StringNew,           // String::new()
    StringFrom,          // String::from(&str) or From::from
    StringFromRawParts,  // String::from_raw_parts(ptr, len, cap) (#3607 D1)
    StringLen,           // String::len(&self) -> usize
    StringIsEmpty,       // String::is_empty(&self) -> bool
    StringPush,          // String::push(&mut self, char)
    StringPushStr,       // String::push_str(&mut self, &str)
    StringClear,         // String::clear(&mut self)
    StringClone,         // Clone::clone(&self) -> String
    StringTruncate,      // String::truncate(&mut self, new_len: usize) (#1610)
    StringFromUtf8Lossy, // String::from_utf8_lossy(&[u8]) -> Cow<str> (#1610)
    /// core::str::from_utf8(&[u8]) -> Result<&str, Utf8Error> (#3672)
    /// Sound over-approximation: destination unconstrained (symbolic Result).
    StrFromUtf8,
    /// <integer as FromStr>::from_str(&str) -> Result<T, ParseIntError> (#3676)
    /// Sound over-approximation: destination unconstrained (symbolic Result).
    /// Handles str::parse::<i32>() and similar integer parse calls.
    IntParse,
    /// core::str::<impl str>::split_whitespace(&self) -> SplitWhitespace<'_> (#4117)
    SplitWhitespace,
    /// core::str::iter::SplitWhitespace::next(&mut self) -> Option<&str> (#4117)
    SplitWhitespaceNext,
    StringEq,           // PartialEq::eq(&String, &String) -> bool (#1610)
    StringContains,     // String::contains(&self, pat) -> bool (Part of #2125 Phase 2)
    StringStartsWith,   // String::starts_with(&self, pat) -> bool (Part of #2125 Phase 2)
    StringEndsWith,     // String::ends_with(&self, pat) -> bool (Part of #2125 Phase 2)
    StringIsAscii,      // str::is_ascii(&self) -> bool (Part of #2125 Phase 2)
    StringAsStr,        // String::as_str(&self) -> &str (Part of #3582)
    StringIntoBoxedStr, // String::into_boxed_str(self) -> Box<str> (#3646)
    /// kani_str_bytes_nth(source: &str, index: usize) -> Option<u8> (#4161)
    /// Intercepts MIR-rewritten str.bytes().nth(i) before fn_inline bails.
    StrBytesNth,
    /// kani_str_chars_nth(source: &str, index: usize) -> Option<char> (#4161)
    /// Intercepts MIR-rewritten str.chars().nth(i) before fn_inline bails.
    StrCharsNth,
    // Cow<str> stubs - collapse to String (#1691)
    // from_utf8_lossy returns Cow<str>, but we model the whole chain as String
    CowToString, // <Cow<str> as ToString>::to_string() -> String
    // Display trait to_string (#1700, #1701)
    // <T as ToString>::to_string() where T: Display
    // Returns symbolic String - overapproximation for any Display impl
    DisplayToString,
    // format! macro (#1704)
    // std::fmt::format(Arguments) -> String
    // Returns symbolic String - overapproximation for formatted output
    FmtFormat,
    // BTreeSet stubs (Part of #1312)
    // Modeled as Array<Key, Bool> - element presence map
    BTreeSetNew,      // BTreeSet::new()
    BTreeSetInsert,   // BTreeSet::insert(&mut self, value) -> bool
    BTreeSetContains, // BTreeSet::contains(&self, value) -> bool
    BTreeSetRemove,   // BTreeSet::remove(&mut self, value) -> bool
    BTreeSetLen,      // BTreeSet::len(&self) -> usize
    BTreeSetIsEmpty,  // BTreeSet::is_empty(&self) -> bool
    BTreeSetClear,    // BTreeSet::clear(&mut self)
    BTreeSetClone,    // Clone::clone(&self) -> BTreeSet
    // BTreeMap basic stubs (Part of #1752)
    // Modeled as Array<Key, Option<Value>> - same as HashMap
    // BTreeMap ordering properties are NOT modeled - see hashmap.rs for limitations
    BTreeMapNew,         // BTreeMap::new()
    BTreeMapInsert,      // BTreeMap::insert(&mut self, key, value) -> Option<V>
    BTreeMapGet,         // BTreeMap::get(&self, key) -> Option<&V>
    BTreeMapGetMut,      // BTreeMap::get_mut(&mut self, key) -> Option<&mut V>
    BTreeMapContainsKey, // BTreeMap::contains_key(&self, key) -> bool
    BTreeMapRemove,      // BTreeMap::remove(&mut self, key) -> Option<V>
    BTreeMapLen,         // BTreeMap::len(&self) -> usize
    BTreeMapIsEmpty,     // BTreeMap::is_empty(&self) -> bool
    BTreeMapClear,       // BTreeMap::clear(&mut self)
    BTreeMapClone,       // Clone::clone(&self) -> BTreeMap
    // NOTE: BTreeMap iterators use shared HashMap iterator stubs (HashMapIntoIter, HashMapIter,
    // HashMapIterNext) since both use the same Array<K, Option<V>> model. See lookup_collections.rs.
    // BTreeMap internal operation stubs (Part of #1622)
    // These are triggered when MIR inlines BTreeSet operations to internal BTreeMap calls.
    // BTreeSet uses BTreeMap<K, SetValZST> internally - we model SetValZST as ()
    // Entry<K,V> is modeled as symbolic - we track array state for the underlying operations.
    //
    // Note: Actual paths in MIR may use std::collections::* or alloc::collections::btree::map::*
    // depending on how the code is compiled. We match both.
    BTreeMapEntry,                // BTreeMap::entry(&mut self, key) -> Entry<K, V>
    BTreeMapVacantInsert,         // VacantEntry::insert(self, value) -> &mut V
    BTreeMapVacantInsertEntry,    // VacantEntry::insert_entry(self, value) -> OccupiedEntry
    BTreeMapOccupiedInsert,       // OccupiedEntry::insert(&mut self, value) -> V (replaces old)
    BTreeMapOccupiedGetMut,       // OccupiedEntry::get_mut(&mut self) -> &mut V
    BTreeMapOccupiedIntoMut,      // OccupiedEntry::into_mut(self) -> &mut V
    BTreeMapEntryOrInsert,        // Entry::or_insert(self, default) -> &mut V
    BTreeMapEntryOrInsertWith,    // Entry::or_insert_with(self, default) -> &mut V
    BTreeMapEntryOrInsertWithKey, // Entry::or_insert_with_key(self, default) -> &mut V
    // Internal BTree node operations (Part of #1622, #1627)
    // These are triggered when MIR inlines BTreeSet operations past the Entry API
    BTreeSearchTree,   // search_tree(key) -> SearchResult
    BTreeNodeReborrow, // NodeRef::reborrow() -> NodeRef<Immut>
    BTreeHandleIntoKv, // Handle::into_kv() -> (&K, &V)
    // SetValZST stubs (Part of #1622)
    // SetValZST is a ZST marker type used by BTreeSet internals when using BTreeMap<K, SetValZST>.
    // We stub Default::default for SetValZST to avoid descending into BTree internals.
    SetValZstDefault, // Default::default::<SetValZST>() -> SetValZST
    // NOTE: mem::replace<SetValZST> and Option::as_ref<NodeRef> are handled by
    // try_codegen_btree_internal_precheck() in dispatch.rs, not via stub registry.
    // Reason: def_path_str doesn't include generic args. (Part of #1627)
    // HashSet stubs (Part of #1613)
    // Modeled as Array<Key, Bool> - element presence map (same as BTreeSet)
    // HashSet internally uses HashMap<T, ()>, but we model it as a simple set
    HashSetNew,      // HashSet::new()
    HashSetInsert,   // HashSet::insert(&mut self, value) -> bool
    HashSetContains, // HashSet::contains(&self, value) -> bool
    HashSetRemove,   // HashSet::remove(&mut self, value) -> bool
    HashSetLen,      // HashSet::len(&self) -> usize
    HashSetIsEmpty,  // HashSet::is_empty(&self) -> bool
    HashSetClear,    // HashSet::clear(&mut self)
    HashSetClone,    // Clone::clone(&self) -> HashSet
    // BTreeSet/HashSet iterator stubs (Part of #1751)
    // Set iterators yield keys only (unlike HashMap which yields (K, V) pairs)
    // Modeled as (set: Array<K, Bool>, keys: Array<usize, K>, pos: usize, len: usize)
    BTreeSetIntoIter, // BTreeSet::into_iter(self) -> IntoIter<K>
    BTreeSetIter,     // BTreeSet::iter(&self) -> Iter<K>
    BTreeSetIterNext, // btree_set::IntoIter<K>::next(&mut self) -> Option<K>
    HashSetIntoIter,  // HashSet::into_iter(self) -> IntoIter<K>
    HashSetIter,      // HashSet::iter(&self) -> Iter<K>
    HashSetIterNext,  // hash_set::IntoIter<K>::next(&mut self) -> Option<K>
}
