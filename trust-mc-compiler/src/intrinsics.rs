// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Single source of truth about which intrinsics we support.

use rustc_public::{
    mir::{Mutability, mono::Instance},
    ty::{FloatTy, FnSig, IntTy, RigidTy, TyKind, UintTy},
};

/// Extract the intrinsic name string and function signature from an intrinsic instance.
fn intrinsic_preamble(instance: &Instance) -> (String, FnSig) {
    let name = instance.intrinsic_name().expect("intrinsic instance should have intrinsic name");
    let sig = instance
        .ty()
        .kind()
        .fn_sig()
        .expect("intrinsic instance should have function signature")
        .skip_binder();
    (name, sig)
}

// Enumeration of all intrinsics we support right now, with the last option being a catch-all. This
// way, adding an intrinsic would highlight all places where they are used.
#[allow(unused)]
#[derive(Clone, Debug)]
pub(crate) enum Intrinsic {
    AddWithOverflow,
    AlignOf,
    AlignOfVal,
    ArithOffset,
    AssertInhabited,
    AssertMemUninitializedValid,
    AssertZeroValid,
    Assume,
    AtomicAnd,
    AtomicCxchg,
    AtomicCxchgWeak,
    AtomicFence,
    AtomicLoad,
    AtomicMax,
    AtomicMin,
    AtomicNand,
    AtomicOr,
    AtomicSingleThreadFence,
    AtomicStore,
    AtomicUmax,
    AtomicUmin,
    AtomicXadd,
    AtomicXchg,
    AtomicXor,
    AtomicXsub,
    Bitreverse,
    BlackBox,
    Breakpoint,
    Bswap,
    CeilF32,
    CeilF64,
    CompareBytes,
    Copy,
    CopySignF32,
    CopySignF64,
    CosF32,
    CosF64,
    Ctlz,
    CtlzNonZero,
    Ctpop,
    Cttz,
    CttzNonZero,
    DiscriminantValue,
    ExactDiv,
    Exp2F32,
    Exp2F64,
    ExpF32,
    ExpF64,
    FabsF32,
    FabsF64,
    FaddFast,
    FdivFast,
    FloatToIntUnchecked,
    FloorF32,
    FloorF64,
    FmafF32,
    FmafF64,
    FmulFast,
    Forget,
    FsubFast,
    IsValStaticallyKnown,
    Likely,
    Log10F32,
    Log10F64,
    Log2F32,
    Log2F64,
    LogF32,
    LogF64,
    MaxNumF32,
    MaxNumF64,
    MinNumF32,
    MinNumF64,
    MulWithOverflow,
    PowF32,
    PowF64,
    PowIF32,
    PowIF64,
    PtrGuaranteedCmp,
    PtrOffsetFrom,
    PtrOffsetFromUnsigned,
    RawEq,
    RetagBoxToRaw,
    RotateLeft,
    RotateRight,
    RoundF32,
    RoundF64,
    RoundTiesEvenF32,
    RoundTiesEvenF64,
    SaturatingAdd,
    SaturatingSub,
    SinF32,
    SinF64,
    SimdAdd,
    SimdAnd,
    SimdDiv,
    SimdRem,
    SimdEq,
    SimdExtract,
    SimdGe,
    SimdGt,
    SimdInsert,
    SimdLe,
    SimdLt,
    SimdMul,
    SimdNe,
    SimdOr,
    SimdShl,
    SimdShr,
    SimdShuffle(String),
    SimdSub,
    SimdXor,
    SimdBitmask,
    SizeOf,
    SizeOfVal,
    SqrtF32,
    SqrtF64,
    SubWithOverflow,
    Transmute,
    TruncF32,
    TruncF64,
    TypedSwap,
    UnalignedVolatileLoad,
    UncheckedDiv,
    UncheckedRem,
    Unlikely,
    VolatileCopyMemory,
    VolatileCopyNonOverlappingMemory,
    VolatileLoad,
    VolatileStore,
    VtableSize,
    VtableAlign,
    WrappingAdd,
    WrappingMul,
    WrappingSub,
    WriteBytes,
    Unimplemented { name: String, issue_link: String },
}

/// Assert that top-level types of a function signature match the given patterns.
macro_rules! assert_sig_matches {
    ($sig:expr, $($input_type:pat),* => $output_type:pat) => {
        let inputs = $sig.inputs();
        let output = $sig.output();
        #[allow(unused_mut)]
        let mut index = 0;
        $(
            #[allow(unused_assignments)]
            {
                assert!(matches!(inputs[index].kind(), TyKind::RigidTy($input_type)));
                index += 1;
            }
        )*
        assert!(inputs.len() == index);
        assert!(matches!(output.kind(), TyKind::RigidTy($output_type)));
    }
}

/// Signature shape for direct intrinsic lookups.
#[derive(Clone, Copy)]
enum DirectSig {
    /// `(T) -> U`
    UnaryAny,
    /// `(T) -> bool`
    UnaryToBool,
    /// `(T) -> u32`
    UnaryToU32,
    /// `(T) -> ()`
    UnaryToTuple,
    /// `(T, U) -> V`
    BinaryAny,
    /// `(T, U) -> ()`
    BinaryToTuple,
    /// `(bool) -> bool`
    BoolToBool,
    /// `(T, u32) -> U`
    BinaryU32Any,
}

/// Intrinsics that share simple signature shapes and can be matched via table lookup.
const DIRECT_INTRINSICS: &[(&str, Intrinsic, DirectSig)] = &[
    ("add_with_overflow", Intrinsic::AddWithOverflow, DirectSig::BinaryToTuple),
    ("bitreverse", Intrinsic::Bitreverse, DirectSig::UnaryAny),
    ("black_box", Intrinsic::BlackBox, DirectSig::UnaryAny),
    ("bswap", Intrinsic::Bswap, DirectSig::UnaryAny),
    ("ctlz", Intrinsic::Ctlz, DirectSig::UnaryToU32),
    ("ctlz_nonzero", Intrinsic::CtlzNonZero, DirectSig::UnaryToU32),
    ("ctpop", Intrinsic::Ctpop, DirectSig::UnaryToU32),
    ("cttz", Intrinsic::Cttz, DirectSig::UnaryToU32),
    ("cttz_nonzero", Intrinsic::CttzNonZero, DirectSig::UnaryToU32),
    ("exact_div", Intrinsic::ExactDiv, DirectSig::BinaryAny),
    ("fadd_fast", Intrinsic::FaddFast, DirectSig::BinaryAny),
    ("fdiv_fast", Intrinsic::FdivFast, DirectSig::BinaryAny),
    ("fmul_fast", Intrinsic::FmulFast, DirectSig::BinaryAny),
    ("forget", Intrinsic::Forget, DirectSig::UnaryToTuple),
    ("fsub_fast", Intrinsic::FsubFast, DirectSig::BinaryAny),
    ("is_val_statically_known", Intrinsic::IsValStaticallyKnown, DirectSig::UnaryToBool),
    ("likely", Intrinsic::Likely, DirectSig::BoolToBool),
    ("mul_with_overflow", Intrinsic::MulWithOverflow, DirectSig::BinaryToTuple),
    ("rotate_left", Intrinsic::RotateLeft, DirectSig::BinaryU32Any),
    ("rotate_right", Intrinsic::RotateRight, DirectSig::BinaryU32Any),
    ("saturating_add", Intrinsic::SaturatingAdd, DirectSig::BinaryAny),
    ("saturating_sub", Intrinsic::SaturatingSub, DirectSig::BinaryAny),
    ("sub_with_overflow", Intrinsic::SubWithOverflow, DirectSig::BinaryToTuple),
    ("transmute", Intrinsic::Transmute, DirectSig::UnaryAny),
    ("unchecked_div", Intrinsic::UncheckedDiv, DirectSig::BinaryAny),
    ("unchecked_rem", Intrinsic::UncheckedRem, DirectSig::BinaryAny),
    ("unlikely", Intrinsic::Unlikely, DirectSig::BoolToBool),
    ("wrapping_add", Intrinsic::WrappingAdd, DirectSig::BinaryAny),
    ("wrapping_mul", Intrinsic::WrappingMul, DirectSig::BinaryAny),
    ("wrapping_sub", Intrinsic::WrappingSub, DirectSig::BinaryAny),
];

/// Table-driven lookup for direct intrinsics with shared signature shapes.
fn try_match_direct_intrinsic(name: &str, sig: &FnSig) -> Option<Intrinsic> {
    let (_, variant, direct_sig) =
        DIRECT_INTRINSICS.iter().find(|(intrinsic_name, _, _)| *intrinsic_name == name)?;

    match direct_sig {
        DirectSig::UnaryAny => {
            assert_sig_matches!(sig, _ => _); // non-enum: macro wildcard pattern
        }
        DirectSig::UnaryToBool => {
            assert_sig_matches!(sig, _ => RigidTy::Bool); // non-enum: macro wildcard pattern
        }
        DirectSig::UnaryToU32 => {
            assert_sig_matches!(sig, _ => RigidTy::Uint(UintTy::U32)); // non-enum: macro wildcard pattern
        }
        DirectSig::UnaryToTuple => {
            assert_sig_matches!(sig, _ => RigidTy::Tuple(_)); // non-enum: macro wildcard pattern
        }
        DirectSig::BinaryAny => {
            assert_sig_matches!(sig, _, _ => _); // non-enum: macro wildcard pattern
        }
        DirectSig::BinaryToTuple => {
            assert_sig_matches!(sig, _, _ => RigidTy::Tuple(_)); // non-enum: macro wildcard pattern
        }
        DirectSig::BoolToBool => {
            assert_sig_matches!(sig, RigidTy::Bool => RigidTy::Bool);
        }
        DirectSig::BinaryU32Any => {
            assert_sig_matches!(sig, _, RigidTy::Uint(UintTy::U32) => _);
        }
    }

    Some(variant.clone())
}

impl Intrinsic {
    /// Create an intrinsic enum from a given intrinsic instance, shallowly validating the argument types.
    pub(crate) fn from_instance(intrinsic_instance: &Instance) -> Self {
        let (intrinsic_str, sig) = intrinsic_preamble(intrinsic_instance);
        if let Some(intrinsic) = try_match_direct_intrinsic(intrinsic_str.as_str(), &sig) {
            return intrinsic;
        }
        match intrinsic_str.as_str() {
            "align_of" => {
                Self::AlignOf
                //"Expected `core::intrinsics::align_of` to be handled by NullOp::SizeOf"
            }
            "align_of_val" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not) => RigidTy::Uint(UintTy::Usize));
                Self::AlignOfVal
            }
            "arith_offset" => {
                assert_sig_matches!(sig,
                    RigidTy::RawPtr(_, Mutability::Not),
                    RigidTy::Int(IntTy::Isize)
                    => RigidTy::RawPtr(_, Mutability::Not));
                Self::ArithOffset
            }
            "assert_inhabited" => {
                assert_sig_matches!(sig, => RigidTy::Tuple(_));
                Self::AssertInhabited
            }
            "assert_mem_uninitialized_valid" => {
                assert_sig_matches!(sig, => RigidTy::Tuple(_));
                Self::AssertMemUninitializedValid
            }
            "assert_zero_valid" => {
                assert_sig_matches!(sig, => RigidTy::Tuple(_));
                Self::AssertZeroValid
            }
            "assume" => {
                assert_sig_matches!(sig, RigidTy::Bool => RigidTy::Tuple(_));
                Self::Assume
            }
            "breakpoint" => {
                assert_sig_matches!(sig, => RigidTy::Tuple(_));
                Self::Breakpoint
            }
            "caller_location" => {
                assert_sig_matches!(sig, => RigidTy::Ref(_, _, Mutability::Not));
                Self::Unimplemented {
                    name: intrinsic_str,
                    issue_link: "https://github.com/model-checking/kani/issues/374".into(),
                }
            }
            "catch_unwind" => {
                assert_sig_matches!(sig, RigidTy::FnPtr(_), RigidTy::RawPtr(_, Mutability::Mut), RigidTy::FnPtr(_) => RigidTy::Int(IntTy::I32));
                Self::Unimplemented {
                    name: intrinsic_str,
                    issue_link: "https://github.com/model-checking/kani/issues/267".into(),
                }
            }
            "compare_bytes" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not), RigidTy::RawPtr(_, Mutability::Not), RigidTy::Uint(UintTy::Usize) => RigidTy::Int(IntTy::I32));
                Self::CompareBytes
            }
            "copy" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not), RigidTy::RawPtr(_, Mutability::Mut), RigidTy::Uint(UintTy::Usize) => RigidTy::Tuple(_));
                Self::Copy
            }
            "copy_nonoverlapping" => unreachable!(
                "Expected `core::intrinsics::unreachable` to be handled by `StatementKind::CopyNonOverlapping`"
            ),
            "discriminant_value" => {
                assert_sig_matches!(sig, RigidTy::Ref(_, _, Mutability::Not) => _);
                Self::DiscriminantValue
            }
            "float_to_int_unchecked" => {
                assert_sig_matches!(sig, RigidTy::Float(_) => _);
                assert!(matches!(
                    sig.output().kind(),
                    TyKind::RigidTy(RigidTy::Int(_)) | TyKind::RigidTy(RigidTy::Uint(_))
                ));
                Self::FloatToIntUnchecked
            }
            // For const eval of nullary intrinsics, see https://github.com/rust-lang/rust/pull/142839
            "needs_drop" => unreachable!(
                "Expected nullary intrinsic `core::intrinsics::type_id` to be const-evaluated before codegen"
            ),
            // As of https://github.com/rust-lang/rust/pull/110822 the `offset` intrinsic is lowered to `mir::BinOp::Offset`
            "offset" => unreachable!(
                "Expected `core::intrinsics::unreachable` to be handled by `BinOp::OffSet`"
            ),
            "ptr_guaranteed_cmp" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not), RigidTy::RawPtr(_, Mutability::Not) => RigidTy::Uint(UintTy::U8));
                Self::PtrGuaranteedCmp
            }
            "ptr_offset_from" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not), RigidTy::RawPtr(_, Mutability::Not) => RigidTy::Int(IntTy::Isize));
                Self::PtrOffsetFrom
            }
            "ptr_offset_from_unsigned" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not), RigidTy::RawPtr(_, Mutability::Not) => RigidTy::Uint(UintTy::Usize));
                Self::PtrOffsetFromUnsigned
            }
            "raw_eq" => {
                assert_sig_matches!(sig, RigidTy::Ref(_, _, Mutability::Not), RigidTy::Ref(_, _, Mutability::Not) => RigidTy::Bool);
                Self::RawEq
            }
            "size_of" => Self::SizeOf,
            "size_of_val" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not) => RigidTy::Uint(UintTy::Usize));
                Self::SizeOfVal
            }
            "type_id" => unreachable!(
                "Expected nullary intrinsic `core::intrinsics::type_id` to be const-evaluated before codegen"
            ),
            "type_name" => unreachable!(
                "Expected nullary intrinsic `core::intrinsics::type_name` to be const-evaluated before codegen"
            ),
            "typed_swap_nonoverlapping" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), RigidTy::RawPtr(_, Mutability::Mut) => RigidTy::Tuple(_));
                Self::TypedSwap
            }
            "unaligned_volatile_load" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not) => _);
                Self::UnalignedVolatileLoad
            }
            "unchecked_add" | "unchecked_mul" | "unchecked_shl" | "unchecked_shr"
            | "unchecked_sub" => {
                unreachable!("Expected intrinsic `{intrinsic_str}` to be lowered before codegen")
            }
            "unreachable" => unreachable!(
                "Expected `std::intrinsics::unreachable` to be handled by `TerminatorKind::Unreachable`"
            ),
            "variant_count" => unreachable!(
                "Expected nullary intrinsic `core::intrinsics::variant_count` to be const-evaluated before codegen"
            ),
            "volatile_copy_memory" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), RigidTy::RawPtr(_, Mutability::Not), RigidTy::Uint(UintTy::Usize) => RigidTy::Tuple(_));
                Self::VolatileCopyMemory
            }
            "volatile_copy_nonoverlapping_memory" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), RigidTy::RawPtr(_, Mutability::Not), RigidTy::Uint(UintTy::Usize) => RigidTy::Tuple(_));
                Self::VolatileCopyNonOverlappingMemory
            }
            "volatile_load" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not) => _);
                Self::VolatileLoad
            }
            "volatile_store" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), _ => RigidTy::Tuple(_)); // non-enum: macro wildcard pattern
                Self::VolatileStore
            }
            "vtable_size" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not) => RigidTy::Uint(UintTy::Usize));
                Self::VtableSize
            }
            "vtable_align" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not) => RigidTy::Uint(UintTy::Usize));
                Self::VtableAlign
            }
            "write_bytes" => {
                assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), RigidTy::Uint(UintTy::U8), RigidTy::Uint(UintTy::Usize) => RigidTy::Tuple(_));
                Self::WriteBytes
            }
            _ => try_match_atomic(intrinsic_instance) // non-enum: &str (intrinsic name)
                .or_else(|| try_match_simd(intrinsic_instance))
                .or_else(|| try_match_float(intrinsic_instance))
                .unwrap_or(Self::Unimplemented {
                    name: intrinsic_str,
                    issue_link: "https://github.com/model-checking/kani/issues/new/choose".into(),
                }),
        }
    }
}

/// Signature shape for atomic intrinsics, used for arity validation.
#[derive(Clone, Copy)]
enum AtomicSig {
    /// `() -> ()` — fence operations
    Fence,
    /// `*const T -> T` — load
    Load,
    /// `*mut T, T -> ()` — store
    Store,
    /// `*mut T, T -> T` — read-modify-write (and, or, xadd, xsub, etc.)
    Rmw,
    /// `*mut T, T, T -> (T, bool)` — compare-and-swap
    Cas,
}

/// Atomic intrinsic lookup table: (name, variant, expected signature shape).
const ATOMIC_TABLE: &[(&str, Intrinsic, AtomicSig)] = &[
    ("atomic_and", Intrinsic::AtomicAnd, AtomicSig::Rmw),
    ("atomic_cxchg", Intrinsic::AtomicCxchg, AtomicSig::Cas),
    ("atomic_cxchgweak", Intrinsic::AtomicCxchgWeak, AtomicSig::Cas),
    ("atomic_fence", Intrinsic::AtomicFence, AtomicSig::Fence),
    ("atomic_load", Intrinsic::AtomicLoad, AtomicSig::Load),
    ("atomic_max", Intrinsic::AtomicMax, AtomicSig::Rmw),
    ("atomic_min", Intrinsic::AtomicMin, AtomicSig::Rmw),
    ("atomic_nand", Intrinsic::AtomicNand, AtomicSig::Rmw),
    ("atomic_or", Intrinsic::AtomicOr, AtomicSig::Rmw),
    ("atomic_singlethreadfence", Intrinsic::AtomicSingleThreadFence, AtomicSig::Fence),
    ("atomic_store", Intrinsic::AtomicStore, AtomicSig::Store),
    ("atomic_umax", Intrinsic::AtomicUmax, AtomicSig::Rmw),
    ("atomic_umin", Intrinsic::AtomicUmin, AtomicSig::Rmw),
    ("atomic_xadd", Intrinsic::AtomicXadd, AtomicSig::Rmw),
    ("atomic_xchg", Intrinsic::AtomicXchg, AtomicSig::Rmw),
    ("atomic_xor", Intrinsic::AtomicXor, AtomicSig::Rmw),
    ("atomic_xsub", Intrinsic::AtomicXsub, AtomicSig::Rmw),
];

/// Match atomic intrinsics via table lookup with signature validation.
fn try_match_atomic(intrinsic_instance: &Instance) -> Option<Intrinsic> {
    let (intrinsic_str, sig) = intrinsic_preamble(intrinsic_instance);
    let entry = ATOMIC_TABLE.iter().find(|(name, _, _)| *name == intrinsic_str.as_str())?;
    let (_, ref variant, atomic_sig) = *entry;

    // Validate signature shape matches the expected atomic pattern.
    match atomic_sig {
        AtomicSig::Fence => {
            assert_sig_matches!(sig, => RigidTy::Tuple(_));
        }
        AtomicSig::Load => {
            assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Not) => _);
        }
        AtomicSig::Store => {
            assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), _ => RigidTy::Tuple(_)); // non-enum: macro wildcard pattern
        }
        AtomicSig::Rmw => {
            assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), _ => _); // non-enum: macro wildcard pattern
        }
        AtomicSig::Cas => {
            assert_sig_matches!(sig, RigidTy::RawPtr(_, Mutability::Mut), _, _ => RigidTy::Tuple(_)); // non-enum: macro wildcard pattern
        }
    }
    Some(variant.clone())
}

/// SIMD intrinsic lookup table: (name suffix after "simd_", variant, expected arg count).
/// Most SIMD intrinsics are binary (2 args). Special cases handled inline.
const SIMD_BINARY_TABLE: &[(&str, Intrinsic)] = &[
    ("add", Intrinsic::SimdAdd),
    ("and", Intrinsic::SimdAnd),
    ("div", Intrinsic::SimdDiv),
    ("eq", Intrinsic::SimdEq),
    ("ge", Intrinsic::SimdGe),
    ("gt", Intrinsic::SimdGt),
    ("le", Intrinsic::SimdLe),
    ("lt", Intrinsic::SimdLt),
    ("mul", Intrinsic::SimdMul),
    ("ne", Intrinsic::SimdNe),
    ("or", Intrinsic::SimdOr),
    ("rem", Intrinsic::SimdRem),
    ("shl", Intrinsic::SimdShl),
    ("shr", Intrinsic::SimdShr),
    ("sub", Intrinsic::SimdSub),
    ("xor", Intrinsic::SimdXor),
];

/// Match SIMD intrinsics via table lookup with signature validation.
fn try_match_simd(intrinsic_instance: &Instance) -> Option<Intrinsic> {
    let (intrinsic_str, sig) = intrinsic_preamble(intrinsic_instance);
    let suffix = intrinsic_str.strip_prefix("simd_")?;

    // Binary SIMD ops: (vec, vec) -> vec
    if let Some((_, variant)) = SIMD_BINARY_TABLE.iter().find(|(name, _)| *name == suffix) {
        assert_sig_matches!(sig, _, _ => _); // non-enum: macro wildcard pattern
        return Some(variant.clone());
    }

    // Special-cased SIMD ops with unique signatures.
    match suffix {
        "bitmask" => {
            assert_sig_matches!(sig, _ => _); // non-enum: macro wildcard pattern
            Some(Intrinsic::SimdBitmask)
        }
        "extract" => {
            assert_sig_matches!(sig, _, RigidTy::Uint(UintTy::U32) => _); // non-enum: macro wildcard pattern
            Some(Intrinsic::SimdExtract)
        }
        "insert" => {
            assert_sig_matches!(sig, _, RigidTy::Uint(UintTy::U32), _ => _); // non-enum: macro wildcard pattern
            Some(Intrinsic::SimdInsert)
        }
        _ if suffix.starts_with("shuffle") => {
            // non-enum: &str (SIMD suffix)
            assert_sig_matches!(sig, _, _, _ => _); // non-enum: macro wildcard pattern
            Some(Intrinsic::SimdShuffle(suffix.strip_prefix("shuffle").unwrap_or("").into()))
        }
        _ => None, // non-enum: &str (SIMD suffix)
    }
}

/// Match f32 and f64 arithmetic intrinsics by instance. Unifies the previously separate
/// `try_match_f32` and `try_match_f64` functions by stripping the float suffix and dispatching
/// through a shared match on base names.
fn try_match_float(intrinsic_instance: &Instance) -> Option<Intrinsic> {
    let (intrinsic_str, sig) = intrinsic_preamble(intrinsic_instance);
    let name = intrinsic_str.as_str();

    // Determine float width from the suffix. Check `_f32`/`_f64` before bare `f32`/`f64`
    // because `"round_ties_even_f32".strip_suffix("f32")` would leave a trailing underscore
    // in the base name, preventing table lookup from matching `"round_ties_even"`.
    let (base, float_ty) = if let Some(base) = name.strip_suffix("_f32") {
        (base, FloatTy::F32)
    } else if let Some(base) = name.strip_suffix("_f64") {
        (base, FloatTy::F64)
    } else if let Some(base) = name.strip_suffix("f32") {
        (base, FloatTy::F32)
    } else if let Some(base) = name.strip_suffix("f64") {
        (base, FloatTy::F64)
    } else {
        return None;
    };

    // Validate signature: output must be the expected float type.
    assert!(
        matches!(sig.output().kind(), TyKind::RigidTy(RigidTy::Float(ft)) if ft == float_ty),
        "float intrinsic `{name}` output should be Float({float_ty:?})"
    );

    /// Maps a base intrinsic name to the pair of (F32, F64) enum variants.
    /// Signature arity is validated separately below.
    macro_rules! float_intrinsic {
        ($base:expr, $( $pat:literal => ($f32v:ident, $f64v:ident, $arity:literal) ),+ $(,)?) => {
            match $base {
                $( $pat => {
                    let expected_arity: usize = $arity;
                    assert_eq!(
                        sig.inputs().len(), expected_arity,
                        "float intrinsic `{}` expected {} args, got {}",
                        name, expected_arity, sig.inputs().len()
                    );
                    Some(match float_ty {
                        FloatTy::F32 => Intrinsic::$f32v,
                        FloatTy::F64 => Intrinsic::$f64v,
                        _ => return None, // external enum: FloatTy
                    })
                } )+
                _ => None, // non-enum: &str (float intrinsic name)
            }
        }
    }

    float_intrinsic!(base,
        // Unary: f -> f
        "ceil"     => (CeilF32,     CeilF64,     1),
        "cos"      => (CosF32,      CosF64,      1),
        "exp2"     => (Exp2F32,     Exp2F64,     1),
        "exp"      => (ExpF32,      ExpF64,      1),
        "fabs"     => (FabsF32,     FabsF64,     1),
        "floor"    => (FloorF32,    FloorF64,    1),
        "log10"    => (Log10F32,    Log10F64,    1),
        "log2"     => (Log2F32,     Log2F64,     1),
        "log"      => (LogF32,      LogF64,      1),
        "round"    => (RoundF32,    RoundF64,    1),
        "sin"      => (SinF32,      SinF64,      1),
        "sqrt"     => (SqrtF32,     SqrtF64,     1),
        "trunc"    => (TruncF32,    TruncF64,    1),
        // Binary: f, f -> f
        "copysign" => (CopySignF32, CopySignF64, 2),
        "maxnum"   => (MaxNumF32,   MaxNumF64,   2),
        "minnum"   => (MinNumF32,   MinNumF64,   2),
        "pow"      => (PowF32,      PowF64,      2),
        // Binary: f, i32 -> f (powi)
        "powi"     => (PowIF32,     PowIF64,     2),
        // Ternary: f, f, f -> f
        "fma"      => (FmafF32,     FmafF64,     3),
        // round_ties_even — base is "round_ties_even" after stripping "_f32"/"_f64"
        "round_ties_even" => (RoundTiesEvenF32, RoundTiesEvenF64, 1),
    )
}
