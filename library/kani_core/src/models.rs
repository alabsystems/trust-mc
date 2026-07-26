// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Contains definitions that Kani compiler may use to model functions that are not suitable for
//! verification or functions without a body, such as intrinsics.
//!
//! Note that these are models that Kani uses by default, and they should not be user visible.
//! Thus, we separate them from stubs.

#[macro_export]
#[allow(clippy::crate_in_macro_def)]
macro_rules! generate_models {
    () => {
        /// Model rustc intrinsics. These definitions are not visible to the crate user.
        /// They are used by Kani's compiler.
        #[allow(dead_code)]
        mod rustc_intrinsics {
            // Fix for #1637: When expanded in kani_lib!(kani), this is at crate root,
            // and we need to import from `crate::*` to get kani_core exports.
            // For kani_lib!(core/std), this expands inside `mod kani { }`, and
            // `crate::kani` correctly reaches the kani API module.
            // Note: We import from both crate (for kani_lib!(kani)) and try crate::kani
            // for other contexts. The macro user must ensure one works.
            #[allow(unused_imports)]
            use crate::*;
            use core::convert::TryFrom;
            use core::ptr::Pointee;

            #[kanitool::fn_marker = "SizeOfValRawModel"]
            pub fn size_of_val_raw<T: ?Sized>(ptr: *const T) -> usize {
                if let Some(size) = mem::checked_size_of_raw(ptr) {
                    size
                } else if core::mem::size_of::<<T as Pointee>::Metadata>() == 0 {
                    panic("cannot compute `size_of_val` for extern types")
                } else {
                    safety_check(false, "failed to compute `size_of_val`");
                    // Unreachable without panic.
                    kani_intrinsic()
                }
            }

            #[kanitool::fn_marker = "PanicStub"]
            pub fn panic_stub(t: &str) -> ! {
                // Using an infinite loop here to have the function return the never (`!`) type.
                // We could also use `exit()` / `abort()` but both require depending on std::process.
                loop {}
            }

            #[kanitool::fn_marker = "AlignOfValRawModel"]
            pub fn align_of_val_raw<T: ?Sized>(ptr: *const T) -> usize {
                if let Some(size) = mem::checked_align_of_raw(ptr) {
                    size
                } else if core::mem::size_of::<<T as Pointee>::Metadata>() == 0 {
                    panic("cannot compute `align_of_val` for extern types")
                } else {
                    safety_check(false, "failed to compute `align_of_val`");
                    // Unreachable without panic.
                    kani_intrinsic()
                }
            }

            /// Implements core::intrinsics::ptr_offset_from with safety checks in place.
            ///
            /// From original documentation:
            ///
            /// # Safety
            ///
            /// If any of the following conditions are violated, the result is Undefined Behavior:
            ///
            /// * `self` and `origin` must either
            ///
            ///   * point to the same address, or
            ///   * both be *derived from* a pointer to the same allocated object,
            ///     and the memory range between
            ///     the two pointers must be in bounds of that object.
            ///
            /// * The distance between the pointers, in bytes, must be an exact multiple
            ///   of the size of `T`.
            ///
            /// # Panics
            ///
            /// This function panics if `T` is a Zero-Sized Type ("ZST").
            #[kanitool::fn_marker = "PtrOffsetFromModel"]
            pub unsafe fn ptr_offset_from<T>(ptr1: *const T, ptr2: *const T) -> isize {
                // This is not a safety condition.
                assert(core::mem::size_of::<T>() > 0, "Cannot compute offset of a ZST");
                if ptr1 == ptr2 {
                    0
                } else {
                    safety_check(
                        mem::same_allocation_internal(ptr1, ptr2),
                        "Offset result and original pointer should point to the same allocation",
                    );
                    // The offset must fit in isize since this represents the same allocation.
                    let offset_bytes =
                        mem::pointer_offset(ptr1).wrapping_sub(mem::pointer_offset(ptr2)) as isize;
                    let t_size = size_of::<T>() as isize;
                    safety_check(
                        offset_bytes % t_size == 0,
                        "Expected the distance between the pointers, in bytes, to be a
                        multiple of the size of `T`",
                    );
                    offset_bytes / t_size
                }
            }

            #[kanitool::fn_marker = "PtrOffsetFromUnsignedModel"]
            pub unsafe fn ptr_offset_from_unsigned<T>(ptr1: *const T, ptr2: *const T) -> usize {
                let offset = ptr_offset_from(ptr1, ptr2);
                safety_check(offset >= 0, "Expected non-negative distance between pointers");
                offset as usize
            }

            /// An offset model that checks UB.
            #[kanitool::fn_marker = "OffsetModel"]
            pub fn offset<T, P: Ptr<T>, O: ToISize>(ptr: P, offset: O) -> P {
                let t_size = core::mem::size_of::<T>() as isize;
                if t_size == 0 {
                    // It's always safe to perform an offset on a ZST.
                    return ptr;
                }

                // Note that this check must come after the t_size check, c.f. https://github.com/model-checking/kani/issues/3896
                let offset = offset.to_isize();
                if offset == 0 {
                    // It's always safe to perform an offset of length 0.
                    return ptr;
                }

                let (byte_offset, overflow) = offset.overflowing_mul(t_size);
                safety_check(!overflow, "Offset in bytes overflows isize");
                let orig_ptr = ptr.to_const_ptr();
                // NOTE: Using usize arithmetic here caused unexpected failures that
                // require further debugging. Using wrapping_byte_offset instead.
                // See: https://github.com/model-checking/kani/issues/1150
                // let new_ptr = orig_ptr.addr().wrapping_add_signed(byte_offset) as *const T;
                let new_ptr = orig_ptr.wrapping_byte_offset(byte_offset);
                safety_check(
                    mem::same_allocation_internal(orig_ptr, new_ptr),
                    "Offset result and original pointer must point to the same allocation",
                );
                P::from_const_ptr(new_ptr)
            }

            pub trait Ptr<T> {
                fn to_const_ptr(self) -> *const T;
                fn from_const_ptr(ptr: *const T) -> Self;
            }

            impl<T> Ptr<T> for *const T {
                fn to_const_ptr(self) -> *const T {
                    self
                }
                fn from_const_ptr(ptr: *const T) -> Self {
                    ptr
                }
            }

            impl<T> Ptr<T> for *mut T {
                fn to_const_ptr(self) -> *const T {
                    self
                }
                fn from_const_ptr(ptr: *const T) -> Self {
                    ptr as _
                }
            }

            pub trait ToISize {
                fn to_isize(self) -> isize;
            }

            impl ToISize for isize {
                fn to_isize(self) -> isize {
                    self
                }
            }

            impl ToISize for usize {
                fn to_isize(self) -> isize {
                    if let Ok(val) = self.try_into() {
                        val
                    } else {
                        safety_check(false, "Offset value overflows isize");
                        unreachable!();
                    }
                }
            }
        }

        #[allow(dead_code)]
        mod simd_models {
            use core::fmt::Debug;
            use core::mem::size_of;

            /// Similar definition to portable SIMD.
            /// We cannot reuse theirs since TRUE and FALSE defs are private.
            /// We leave this private today, since this is not necessarily a final solution, so we
            /// don't want users relying on this.
            /// Our definitions are also a bit more permissive to comply with the platform intrinsics.
            pub(super) trait MaskElement: PartialEq + Debug {
                const TRUE: Self;
                const FALSE: Self;
            }

            macro_rules! impl_element {
                                                        { $ty:ty } => {
                                                            impl MaskElement for $ty {
                                                                const TRUE: Self = -1;
                                                                const FALSE: Self = 0;
                                                            }
                                                        }
                                                    }

            macro_rules! impl_unsigned_element {
                                                        { $ty:ty } => {
                                                            impl MaskElement for $ty {
                                                                // Note that in the declaration of the intrinsic it is documented that the lane
                                                                // values should be -1 or 0:
                                                                // <https://github.com/rust-lang/rust/blob/338cfd3/library/portable-simd/crates/core_simd/src/intrinsics.rs#L134-L144>
                                                                //
                                                                // However, MIRI and the Rust compiler seems to accept unsigned values and they
                                                                // use their binary representation. Thus, that's what we use for now.
                                                                /// All bits are 1 which represents TRUE.
                                                                const TRUE: Self = <$ty>::MAX;
                                                                /// All bits are 0 which represents FALSE.
                                                                const FALSE: Self = 0;
                                                            }
                                                        }
                                                    }

            impl_element! { i8 }
            impl_element! { i16 }
            impl_element! { i32 }
            impl_element! { i64 }
            impl_element! { i128 }
            impl_element! { isize }

            impl_unsigned_element! { u8 }
            impl_unsigned_element! { u16 }
            impl_unsigned_element! { u32 }
            impl_unsigned_element! { u64 }
            impl_unsigned_element! { u128 }
            impl_unsigned_element! { usize }

            /// Calculate the minimum number of lanes to represent a mask
            /// Logic similar to `bitmask_len` from `portable_simd`.
            /// <https://github.com/rust-lang/portable-simd/blob/490b5cf/crates/core_simd/src/masks/to_bitmask.rs#L75-L79>
            pub(super) const fn mask_len(len: usize) -> usize {
                len.div_ceil(8)
            }

            #[cfg(target_endian = "little")]
            unsafe fn simd_bitmask_impl<T, const LANES: usize>(
                input: &[T; LANES],
            ) -> [u8; mask_len(LANES)]
            where
                T: MaskElement,
            {
                let mut mask_array = [0; mask_len(LANES)];

                // The implementation below is the equivalent of the following:
                // ```rust
                //     for lane in (0..input.len()).rev() {
                //         let byte = lane / 8;
                //         let mask = &mut mask_array[byte];
                //         let shift_mask = *mask << 1;
                //         *mask = if input[lane] == T::TRUE {
                //             shift_mask | 0x1
                //         } else {
                //             assert_eq!(input[lane], T::FALSE, "Masks values should either be 0 or -1");
                //             shift_mask
                //         };
                //     }
                // ```
                // but is intentionally written in a way that minimizes the number of
                // loop iterations. In particular, it's implemented as a nested loop
                // where the outer loop iterates over bytes and the inner "loop" (which
                // is manually unwound) iterates over bits in a byte.  This is to avoid
                // needing a high unwind value for harnesses that invoke this code (e.g.
                // through the `HashSet` data structure).
                for (byte_idx, byte) in mask_array.iter_mut().enumerate() {
                    // Calculate the starting lane for this byte
                    let start_lane = byte_idx << 3;
                    // Calculate how many bits to process (handle the last byte which might be partial)
                    let bits_to_process = (LANES - start_lane).min(8);

                    *byte = if bits_to_process > 0 && input[start_lane] == T::TRUE {
                        1 << 0
                    } else {
                        0
                    } | if bits_to_process > 1 && input[start_lane + 1] == T::TRUE {
                        1 << 1
                    } else {
                        0
                    } | if bits_to_process > 2 && input[start_lane + 2] == T::TRUE {
                        1 << 2
                    } else {
                        0
                    } | if bits_to_process > 3 && input[start_lane + 3] == T::TRUE {
                        1 << 3
                    } else {
                        0
                    } | if bits_to_process > 4 && input[start_lane + 4] == T::TRUE {
                        1 << 4
                    } else {
                        0
                    } | if bits_to_process > 5 && input[start_lane + 5] == T::TRUE {
                        1 << 5
                    } else {
                        0
                    } | if bits_to_process > 6 && input[start_lane + 6] == T::TRUE {
                        1 << 6
                    } else {
                        0
                    } | if bits_to_process > 7 && input[start_lane + 7] == T::TRUE {
                        1 << 7
                    } else {
                        0
                    };

                    assert!(
                        bits_to_process < 1
                            || input[start_lane] == T::TRUE
                            || input[start_lane] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                    assert!(
                        bits_to_process < 2
                            || input[start_lane + 1] == T::TRUE
                            || input[start_lane + 1] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                    assert!(
                        bits_to_process < 3
                            || input[start_lane + 2] == T::TRUE
                            || input[start_lane + 2] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                    assert!(
                        bits_to_process < 4
                            || input[start_lane + 3] == T::TRUE
                            || input[start_lane + 3] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                    assert!(
                        bits_to_process < 5
                            || input[start_lane + 4] == T::TRUE
                            || input[start_lane + 4] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                    assert!(
                        bits_to_process < 6
                            || input[start_lane + 5] == T::TRUE
                            || input[start_lane + 5] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                    assert!(
                        bits_to_process < 7
                            || input[start_lane + 6] == T::TRUE
                            || input[start_lane + 6] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                    assert!(
                        bits_to_process < 8
                            || input[start_lane + 7] == T::TRUE
                            || input[start_lane + 7] == T::FALSE,
                        "Masks values should either be 0 or -1"
                    );
                }

                mask_array
            }

            /// Stub for simd_bitmask.
            ///
            /// It will reduce a simd vector (TxN), into an integer of size S (in bits), where S >= N.
            /// Each bit of the output will represent a lane from the input. A lane value of all 0's will be
            /// translated to 1b0, while all 1's will be translated to 1b1.
            ///
            /// In order to be able to do this pragmatically, we take additional parameters that are filled
            /// by the compiler.
            #[kanitool::fn_marker = "SimdBitmaskModel"]
            pub(super) unsafe fn simd_bitmask<T, U, E, const LANES: usize>(input: T) -> U
            where
                [u8; mask_len(LANES)]: Sized,
                E: MaskElement,
            {
                // These checks are compiler sanity checks to ensure we are not doing anything invalid.
                assert_eq!(
                    size_of::<U>(),
                    size_of::<[u8; mask_len(LANES)]>(),
                    "Expected size of return type and mask lanes to match",
                );
                assert_eq!(
                    size_of::<T>(),
                    size_of::<Simd::<E, LANES>>(),
                    "Expected size of input and lanes to match",
                );

                unsafe {
                    let data = &*(&input as *const T as *const [E; LANES]);
                    let mask = simd_bitmask_impl(data);
                    (&mask as *const [u8; mask_len(LANES)] as *const U).read()
                }
            }

            /// Structure used for sanity check our parameters.
            #[repr(simd)]
            struct Simd<T, const LANES: usize>([T; LANES]);
        }

        #[allow(dead_code)]
        mod mem_models {
            use core::ptr::{self, DynMetadata, Pointee};

            /// Retrieve the size of the object pointed by the given raw pointer.
            ///
            /// Where `U` is a trait, and `T` is either equal to `U` or has a tail `U`.
            ///
            /// In cases where `T` is different than `U`,
            /// `T` may have a sized portion, the head, while the unsized portion will be at its
            /// tail.
            ///
            /// Arguments `head_size` and `head_align` represent the size and alignment of the sized
            /// portion.
            /// These values are known at compilation time, and they are extracted by the compiler.
            /// If `T` doesn't have a sized portion, or if `T` is equal to `U`,
            /// `head_size` will be set to `0`, and `head_align` will be set to 1.
            ///
            /// This model is used to implement `checked_size_of_raw`.
            #[kanitool::fn_marker = "SizeOfDynObjectModel"]
            pub(crate) fn size_of_dyn_object<T, U: ?Sized>(
                ptr: *const T,
                head_size: usize,
                head_align: usize,
            ) -> Option<usize>
            where
                T: ?Sized + Pointee<Metadata = DynMetadata<U>>,
            {
                let metadata = ptr::metadata(ptr);
                let align = metadata.align_of().max(head_align);
                if align.is_power_of_two() {
                    let size_dyn = metadata.size_of();
                    let (total, sum_overflow) = size_dyn.overflowing_add(head_size);
                    // Round up size to the nearest multiple of alignment, i.e.: (size + (align - 1)) & -align
                    let (adjust, adjust_overflow) = total.overflowing_add(align.wrapping_sub(1));
                    let adjusted_size = adjust & align.wrapping_neg();
                    if sum_overflow || adjust_overflow || adjusted_size > isize::MAX as _ {
                        None
                    } else {
                        Some(adjusted_size)
                    }
                } else {
                    None
                }
            }

            /// Retrieve the alignment of the object stored in the vtable.
            ///
            /// Where `U` is a trait, and `T` is either equal to `U` or has a tail `U`.
            ///
            /// In cases where `T` is different than `U`,
            /// `T` may have a sized portion, the head, while the unsized portion will be at its
            /// tail.
            ///
            /// `head_align` represents the alignment of the sized portion,
            /// and its value is known at compilation time.
            ///
            /// If `T` doesn't have a sized portion, or if `T` is equal to `U`,
            /// `head_align` will be set to 1.
            ///
            /// This model is used to implement `checked_aligned_of_raw`.
            #[kanitool::fn_marker = "AlignOfDynObjectModel"]
            pub(crate) fn align_of_dyn_object<T, U: ?Sized>(
                ptr: *const T,
                head_align: usize,
            ) -> Option<usize>
            where
                T: ?Sized + Pointee<Metadata = DynMetadata<U>>,
            {
                let align = ptr::metadata(ptr).align_of().max(head_align);
                align.is_power_of_two().then_some(align)
            }

            /// Compute the size of a slice or object with a slice tail.
            ///
            /// The slice length may be a symbolic value which is computed at runtime.
            /// All the other inputs are extracted and validated by Kani compiler,
            /// i.e., these are well known concrete values that should be safe to use.
            /// Example, align is a power-of-two and smaller than isize::MAX.
            ///
            /// Thus, this generate the logic to ensure the size computation does not
            /// does not overflow and it is smaller than `isize::MAX`.
            #[kanitool::fn_marker = "SizeOfSliceObjectModel"]
            pub(crate) fn size_of_slice_object(
                len: usize,
                elem_size: usize,
                head_size: usize,
                align: usize,
            ) -> Option<usize> {
                let (slice_sz, mul_overflow) = elem_size.overflowing_mul(len);
                let (total, sum_overflow) = slice_sz.overflowing_add(head_size);
                // Round up size to the nearest multiple of alignment, i.e.: (size + (align - 1)) & -align
                let (adjust, adjust_overflow) = total.overflowing_add(align.wrapping_sub(1));
                let adjusted_size = adjust & align.wrapping_neg();
                if mul_overflow
                    || sum_overflow
                    || adjust_overflow
                    || adjusted_size > isize::MAX as _
                {
                    None
                } else {
                    Some(adjusted_size)
                }
            }
        }
    };
}
