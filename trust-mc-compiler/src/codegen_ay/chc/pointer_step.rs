// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Split-pointer arithmetic helper for CHC encoding.
//!
//! The heap model treats 64-bit pointers as `(obj_id : bv32) ++ (offset : bv32)`.
//! Pointer-step operations must preserve the object ID by adding to only the
//! lower 32-bit offset lane. Whole-pointer `bvadd` can spill symbolic low-offset
//! arithmetic into the high object-id bits, causing spurious cross-object results.
//!
//! Part of #3921.

use ay_bindings::Expr;
use num_bigint::BigInt;

use crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Result of a split-pointer step operation.
pub(in crate::codegen_ay::chc) struct PointerStep {
    /// The resulting pointer expression (`obj_id ++ new_offset` when split, or
    /// `ptr.bvadd(byte_offset)` as fallback for non-64-bit pointers).
    pub result: Expr,
    /// When split-pointer recomposition was used, a predicate expressing that
    /// the low-lane addition did not carry into the object-id lane.
    /// `None` for the non-split fallback path.
    pub same_object_ok: Option<Expr>,
}

/// Compute a pointer step that preserves the split-pointer object ID.
///
/// For 64-bit pointers, decomposes into `(obj_id, offset)`, adds `byte_offset`
/// to the offset lane only, and recombines. Surfaces a `same_object_ok` predicate
/// for the carry/overflow case.
///
/// For non-64-bit pointers, falls back to whole-pointer `bvadd`.
pub(in crate::codegen_ay::chc) fn step_split_pointer(ptr: Expr, byte_offset: Expr) -> PointerStep {
    let ptr_width = ptr.sort().bitvec_width();
    if ptr_width != Some(POINTER_WIDTH) || POINTER_WIDTH != 64 {
        // Non-64-bit or non-bitvec: fall back to whole-pointer arithmetic.
        return PointerStep { result: ptr.bvadd(byte_offset), same_object_ok: None };
    }

    // Constant fast-path: fold the lane arithmetic to a literal address so
    // downstream constant-address machinery (memory scalarization, statically
    // discharged error-rule guards) keeps seeing a BitVecConst instead of a
    // concat/extract tree.
    if let Some(step) = const_fold_step(&ptr, &byte_offset, /* is_sub = */ false) {
        return step;
    }

    // Split: upper 32 = obj_id, lower 32 = offset.
    let obj_id = ptr.clone().extract(63, 32);
    let offset = ptr.extract(31, 0);

    // Truncate byte_offset to 32 bits for the offset-lane addition.
    let byte_offset_low = byte_offset.clone().extract(31, 0);

    let new_offset = offset.clone().bvadd(byte_offset_low);

    // Recombine: obj_id ++ new_offset.
    let result = obj_id.concat(new_offset.clone());

    // same_object_ok: the addition in the low lane must not produce a carry
    // that would logically change the object ID.
    //
    // For signed-negative byte offsets (e.g., -4 as 64-bit two's complement),
    // the positive-only checks would always fail because:
    //   - no_carry: new_offset < old_offset after wrapping subtraction
    //   - high_offset_zero: upper 32 bits are 0xFFFFFFFF (sign extension)
    // So we branch on the sign bit of byte_offset. (#4029)
    let sign_bit = byte_offset.clone().extract(63, 63);
    let is_negative = sign_bit.eq(Expr::bitvec_const(1u128, 1));

    // Positive path: no carry (new >= old), upper bits = 0.
    let no_carry = new_offset.clone().bvuge(offset.clone());
    let high_zero = byte_offset.clone().extract(63, 32).eq(Expr::bitvec_const(0u128, 32));

    // Negative path: no underflow (new <= old), upper bits = 0xFFFFFFFF (sign extension).
    let no_underflow = new_offset.bvule(offset);
    let high_ffff = byte_offset.extract(63, 32).eq(Expr::bitvec_const(0xFFFF_FFFFu128, 32));

    let same_object_ok =
        Expr::ite(is_negative, no_underflow.and(high_ffff), no_carry.and(high_zero));

    PointerStep { result, same_object_ok: Some(same_object_ok) }
}

/// Compute a pointer step for subtraction (ptr - byte_offset) preserving object ID.
///
/// Same split-pointer logic as `step_split_pointer` but uses `bvsub` in the
/// offset lane. The `same_object_ok` predicate checks for underflow instead of carry.
pub(in crate::codegen_ay::chc) fn step_split_pointer_sub(
    ptr: Expr,
    byte_offset: Expr,
) -> PointerStep {
    let ptr_width = ptr.sort().bitvec_width();
    if ptr_width != Some(POINTER_WIDTH) || POINTER_WIDTH != 64 {
        return PointerStep { result: ptr.bvsub(byte_offset), same_object_ok: None };
    }

    // Constant fast-path — see step_split_pointer.
    if let Some(step) = const_fold_step(&ptr, &byte_offset, /* is_sub = */ true) {
        return step;
    }

    let obj_id = ptr.clone().extract(63, 32);
    let offset = ptr.extract(31, 0);
    let byte_offset_low = byte_offset.clone().extract(31, 0);

    let new_offset = offset.clone().bvsub(byte_offset_low);

    let result = obj_id.concat(new_offset.clone());

    // For subtraction, underflow occurred iff new_offset > offset (unsigned wrap).
    let no_underflow = new_offset.bvule(offset);
    let high_offset_zero = byte_offset.extract(63, 32).eq(Expr::bitvec_const(0u128, 32));
    let same_object_ok = no_underflow.and(high_offset_zero);

    PointerStep { result, same_object_ok: Some(same_object_ok) }
}

/// Constant fast-path for the split-pointer step: when both the pointer and
/// the byte offset evaluate to constants, perform the obj_id-preserving lane
/// arithmetic numerically and return a literal result.
///
/// Semantics match the symbolic encoding exactly: the offset lane wraps mod
/// 2^32 while the obj_id lane is left untouched, and `same_object_ok` reports
/// whether the step stayed within the lane (no carry for positive offsets, no
/// underflow for negative/sub, upper offset bits matching the sign).
fn const_fold_step(ptr: &Expr, byte_offset: &Expr, is_sub: bool) -> Option<PointerStep> {
    // Part of #72: derived offsets (`count * size_of::<T>()` arrives as an
    // unfolded BvMul over literals) fold through the shared evaluator before
    // the literal extraction — without this the out-of-lane wrap detection
    // below never sees `wrapping_add(usize::MAX/64)`-class steps.
    let folded_off = trust_mc_core::chc_const_prop::eval::try_eval_to_const(byte_offset);
    let byte_offset = folded_off.as_ref().unwrap_or(byte_offset);
    let folded_ptr = trust_mc_core::chc_const_prop::eval::try_eval_to_const(ptr);
    let ptr = folded_ptr.as_ref().unwrap_or(ptr);
    let (off_v, off_w) = const_bv_value(byte_offset)?;
    if off_w != 64 {
        return None;
    }

    // Zero-offset identity: stepping by 0 is exact in both the whole-width and
    // the split model. Returning `ptr` unchanged preserves expression identity
    // with stores made through the un-stepped pointer (memory scalarization
    // and select-over-store matching rely on it).
    if off_v == BigInt::from(0u8) {
        return Some(PointerStep {
            result: ptr.clone(),
            same_object_ok: Some(Expr::bool_const(true)),
        });
    }

    let (ptr_v, ptr_w) = const_bv_value(ptr)?;
    if ptr_w != 64 {
        return None;
    }

    let lane: BigInt = BigInt::from(1u8) << 32;
    let lane_mask: BigInt = &lane - 1u8;
    let hi: BigInt = &ptr_v >> 32;
    let lo: BigInt = &ptr_v & &lane_mask;
    let off_hi: BigInt = &off_v >> 32;
    let off_lo: BigInt = &off_v & &lane_mask;
    let zero = BigInt::from(0u8);

    let (new_lo, same_object_ok) = if is_sub {
        let new_lo: BigInt = ((&lo - &off_lo) % &lane + &lane) % &lane;
        let ok = off_lo <= lo && off_hi == zero;
        (new_lo, ok)
    } else {
        let sum: BigInt = &lo + &off_lo;
        let carried = sum >= lane;
        let new_lo: BigInt = &sum & &lane_mask;
        let is_negative = (&off_v >> 63u32) == BigInt::from(1u8);
        let ok = if is_negative {
            new_lo <= lo && off_hi == lane_mask
        } else {
            !carried && off_hi == zero
        };
        (new_lo, ok)
    };

    // Part of #72: a step that LEAVES the 32-bit offset lane is a real
    // address-space wrap, and lane-truncating it would keep the obj_id lane
    // intact — the wrapped pointer would still "belong" to its original
    // allocation, so the offset_from same-allocation check (obj-id equality)
    // could never fire and `p.wrapping_add(usize::MAX/2+1)` false-proved
    // (offset-wraps-around original_harness). Fold out-of-lane steps with
    // FULL 64-bit wrapping arithmetic instead: the obj_id lane corrupts
    // exactly as a real wrapped address would, and downstream provenance
    // checks see the mismatch.
    if !same_object_ok {
        let modulus: BigInt = BigInt::from(1u8) << 64u32;
        let full: BigInt = if is_sub { &ptr_v - &off_v } else { &ptr_v + &off_v };
        let wrapped: BigInt = ((full % &modulus) + &modulus) % &modulus;
        return Some(PointerStep {
            result: Expr::bitvec_const(wrapped, 64),
            same_object_ok: Some(Expr::bool_const(false)),
        });
    }

    let result_v: BigInt = (hi << 32u32) | new_lo;
    Some(PointerStep {
        result: Expr::bitvec_const(result_v, 64),
        same_object_ok: Some(Expr::bool_const(same_object_ok)),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_split_pointer_step_preserves_obj_id() {
        // Create a split-pointer: obj_id=0x00000042, offset=0x00000100
        let obj_id = Expr::bitvec_const(0x42u128, 32);
        let offset = Expr::bitvec_const(0x100u128, 32);
        let ptr = obj_id.concat(offset);

        // Step by 8 bytes
        let byte_offset = Expr::bitvec_const(8u128, 64);

        let step = step_split_pointer(ptr, byte_offset);

        // Structural: result is a concat, not a raw bvadd
        assert!(
            step.same_object_ok.is_some(),
            "split-pointer step should produce same_object_ok predicate"
        );
        assert_eq!(step.result.sort().bitvec_width(), Some(64));

        // Verify extracted lanes have expected widths.
        let result_obj_id = step.result.clone().extract(63, 32);
        let result_offset = step.result.extract(31, 0);
        assert_eq!(result_obj_id.sort().bitvec_width(), Some(32));
        assert_eq!(result_offset.sort().bitvec_width(), Some(32));
    }

    #[test]
    fn test_non_64bit_falls_back() {
        let ptr = Expr::bitvec_const(0x100u128, 32);
        let byte_offset = Expr::bitvec_const(8u128, 32);

        let step = step_split_pointer(ptr, byte_offset);

        assert!(
            step.same_object_ok.is_none(),
            "non-64-bit pointer should use whole-pointer fallback"
        );
    }

    #[test]
    fn test_split_pointer_sub_preserves_obj_id() {
        let obj_id = Expr::bitvec_const(0x42u128, 32);
        let offset = Expr::bitvec_const(0x100u128, 32);
        let ptr = obj_id.concat(offset);

        let byte_offset = Expr::bitvec_const(8u128, 64);

        let step = step_split_pointer_sub(ptr, byte_offset);

        assert!(
            step.same_object_ok.is_some(),
            "split-pointer sub should produce same_object_ok predicate"
        );
        assert_eq!(step.result.sort().bitvec_width(), Some(64));
    }

    /// Regression for #4029: same_object_ok must not be always-false for
    /// signed-negative byte offsets. A -4 offset (0xFFFFFFFF_FFFFFFFC) within
    /// a same-object allocation is valid.
    #[test]
    fn test_split_pointer_step_allows_negative_same_object_offset() {
        // ptr at obj_id=0x42, offset=0x100
        let obj_id = Expr::bitvec_const(0x42u128, 32);
        let offset = Expr::bitvec_const(0x100u128, 32);
        let ptr = obj_id.concat(offset);

        // byte_offset = -4 as signed 64-bit (two's complement: 0xFFFFFFFF_FFFFFFFC)
        let byte_offset = Expr::bitvec_const(0xFFFF_FFFF_FFFF_FFFCu128, 64);

        let step = step_split_pointer(ptr, byte_offset);

        // Fully-constant inputs fold: -4 within the object stays same-object.
        let same_object_ok =
            step.same_object_ok.expect("split-pointer step must surface same_object_ok");
        assert_eq!(
            same_object_ok,
            Expr::bool_const(true),
            "-4 within the offset lane must be same-object"
        );

        // Result folds to obj_id=0x42, offset=0xFC.
        assert_eq!(step.result, Expr::bitvec_const(0x0000_0042_0000_00FCu128, 64));
    }

    /// The #4029 sign-branch must survive on the symbolic path: a symbolic
    /// byte offset (unfoldable) still gets an ite-based same_object_ok.
    #[test]
    fn test_split_pointer_step_symbolic_offset_branches_on_sign() {
        use ay_bindings::Sort;

        let obj_id = Expr::bitvec_const(0x42u128, 32);
        let offset = Expr::bitvec_const(0x100u128, 32);
        let ptr = obj_id.concat(offset);

        let byte_offset = Expr::var("sym_count", Sort::bitvec(64));

        let step = step_split_pointer(ptr, byte_offset);

        let same_object_ok =
            step.same_object_ok.expect("split-pointer step must surface same_object_ok");
        let smt = same_object_ok.to_string();
        assert!(
            smt.contains("ite"),
            "same_object_ok should branch on sign bit for symbolic offsets: {smt}"
        );

        // Result keeps the split shape with a foldable obj_id lane.
        assert_eq!(step.result.sort().bitvec_width(), Some(64));
        let result_obj_id = step.result.extract(63, 32);
        assert_eq!(
            const_bv_value(&result_obj_id).map(|(v, w)| (v, w)),
            Some((BigInt::from(0x42u32), 32)),
            "obj_id lane must const-fold for symbolic offsets"
        );
    }

    /// Constant lane-carry: same_object_ok folds to false when the offset-lane
    /// addition would spill into the obj_id lane.
    ///
    /// Part of #72: the carry now folds with FULL 64-bit wrapping arithmetic —
    /// the obj_id lane corrupts exactly as a real wrapped address would
    /// (0x42_FFFFFFF0 + 0x20 = 0x43_00000010), so downstream provenance
    /// checks (offset_from same-allocation) see the mismatch instead of a
    /// lane-truncated pointer that still "belongs" to its allocation.
    #[test]
    fn test_split_pointer_step_const_carry_is_not_same_object() {
        let obj_id = Expr::bitvec_const(0x42u128, 32);
        let offset = Expr::bitvec_const(0xFFFF_FFF0u128, 32);
        let ptr = obj_id.concat(offset);

        let byte_offset = Expr::bitvec_const(0x20u128, 64);

        let step = step_split_pointer(ptr, byte_offset);

        // Offset lane overflows (0xFFFFFFF0 + 0x20): full 64-bit wrap carries
        // into the obj_id lane (#72).
        assert_eq!(step.result, Expr::bitvec_const(0x0000_0043_0000_0010u128, 64));
        assert_eq!(
            step.same_object_ok.expect("const fold must surface same_object_ok"),
            Expr::bool_const(false),
            "lane carry must not count as same-object"
        );
    }
}
