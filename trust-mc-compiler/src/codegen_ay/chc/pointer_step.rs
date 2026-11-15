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
/// # Exactness
///
/// The lane result drops the byte offset's high 32 bits and the carry out of
/// the low lane, so it is a NARROWING of the exact address `ptr + byte_offset`
/// (mod 2^64). `same_object_ok` is exactly the condition under which the
/// narrowing is exact: the result equals `ptr.bvadd(byte_offset)` if and only
/// if `same_object_ok` holds. That is only a sound model for the in-bounds
/// family (`offset`, `add`, `sub`), where a step that leaves its allocation is
/// UB and a caller must check `same_object_ok`; the wrapping family must use
/// [`step_wrapping_pointer`].
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

    // Negative path: no underflow, upper bits = 0xFFFFFFFF (sign extension).
    // STRICT `new < old`: the only negative offset with a zero low lane is
    // exactly -2^32, whose lane step leaves the offset unchanged (`new == old`)
    // while the exact address moves down one whole lane. Every other negative
    // offset in range moves the lane strictly down when it does not underflow.
    let no_underflow = new_offset.bvult(offset);
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

/// Element-address step for an unsigned INDEX: `ptr + idx * elem_size` in the
/// split-pointer lane model, with the condition under which that lane result
/// is the exact address.
///
/// Slice element loads step the data pointer by `idx * size_of::<T>()` with
/// [`step_split_pointer`], which keeps only the low 32 bits of the byte offset
/// and drops the carry out of the lane. The index bounds check compares `idx`
/// against the slice's CLAIMED length, which is not the allocation extent
/// (`from_raw_parts(p, 1 << 33)`), so an index at or past `2^32` bytes used to
/// fold back onto a low element: the allocation bound was checked against the
/// truncated address, passed, and `s[1 << 32] == s[0]` was proven.
///
/// The returned `same_object_ok` is `idx * size` not overflowing `usize`, the
/// byte offset fitting the lane (high half zero, so non-negative), and no carry
/// out of the lane. It holds for every in-bounds access of an allocation that
/// fits the lane, and it is false exactly when the lane result is not the
/// exact address, which is an out-of-bounds access. Callers emit it as a
/// memory-safety check.
pub(in crate::codegen_ay::chc) fn step_split_pointer_index(
    ptr: Expr,
    idx: Expr,
    elem_size: u64,
) -> PointerStep {
    let width = idx.sort().bitvec_width().unwrap_or(POINTER_WIDTH);
    let (byte_offset, mul_ok) = if elem_size <= 1 {
        (idx, None)
    } else {
        let size = Expr::bitvec_const(elem_size as u128, width);
        (idx.clone().bvmul(size.clone()), Some(idx.bvmul_no_overflow_unsigned(size)))
    };
    let step = step_split_pointer(ptr, byte_offset.clone());
    let Some(lane_ok) = step.same_object_ok else {
        return step;
    };
    let non_negative = if width == 64 {
        Some(byte_offset.extract(63, 63).eq(Expr::bitvec_const(0u128, 1)))
    } else {
        None
    };
    let exact = [mul_ok, non_negative].into_iter().flatten().fold(lane_ok, Expr::and);
    let exact = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&exact).unwrap_or(exact);
    PointerStep { result: step.result, same_object_ok: Some(exact) }
}

/// The address view of an identity term, and back (the map is its own
/// inverse): the identity `concat(h16, object16, offset32)` — `h16` the high
/// part of a 48-bit offset — is read as `concat(object16, h16, offset32)`,
/// Kani's `object << 48 | offset48`. `ChcCtx::ptr_to_int_value` maps the object
/// field to its address region on top of this.
pub(in crate::codegen_ay::chc) fn identity_address_view(ptr: Expr) -> Expr {
    ptr.clone().extract(47, 32).concat(ptr.clone().extract(63, 48)).concat(ptr.extract(31, 0))
}

/// [`identity_address_view`] on a constant.
fn identity_address_view_value(value: &BigInt) -> BigInt {
    let mask16: BigInt = (BigInt::from(1u8) << 16u32) - 1u8;
    let mask32: BigInt = (BigInt::from(1u8) << 32u32) - 1u8;
    let object = (value >> 32u32) & &mask16;
    let high = (value >> 48u32) & &mask16;
    (object << 48u32) | (high << 32u32) | (value & &mask32)
}

/// Exact-address pointer step for the WRAPPING family (`wrapping_offset`,
/// `wrapping_byte_offset`, `wrapping_add`, `wrapping_sub`, `wrapping_byte_add`,
/// `wrapping_byte_sub`, and `with_addr`, which is a wrapping byte offset).
///
/// # Why the wrapping family cannot use the split step
///
/// [`step_split_pointer`] adds into the LOW 32-BIT LANE ONLY, truncating the
/// byte offset with `extract(31, 0)` and dropping any carry out of that lane.
/// The offset's high 32 bits are DISCARDED, so every offset that is a nonzero
/// multiple of 2^32 encodes as a no-op: `p.wrapping_byte_offset(1 << 32) == p`
/// is derivable in the lane model but FALSE in Z/2^64. That is Kani's #1150
/// shape, and here the encoder folded the truncated step to a literal and
/// STATICALLY DISCHARGED the false assertion, i.e. proved it. For `offset` /
/// `add` / `sub` leaving the allocation is UB, so the lane model is a sound
/// approximation there; the wrapping family is DEFINED out of bounds.
///
/// # The address the step moves
///
/// The step is address arithmetic mod 2^64 on the ADDRESS VIEW of the identity
/// term ([`identity_address_view`]): Kani's `object << 48 | offset48`. A carry
/// out of the 32-bit offset lands in the lane's high 16 bits, the high part of
/// a 48-bit offset, and leaves the object field alone, as Kani's object bits
/// stay put until an offset passes 2^48.
///
/// The previous step was mod 2^64 on the identity term itself, whose object
/// field sits right above the 32-bit offset. Object ids are small and dense,
/// so a step of 2^32 bytes carried into the NEXT OBJECT: `a.as_ptr()
/// .wrapping_byte_add(1 << 32)` was a pointer into `b`, a dereference of it
/// read `b` in bounds (a clean proof where Kani reports a pointer outside
/// object bounds) and `p != b.as_ptr()` was refuted by a certified
/// counterexample (fourth review of fix/chc-false-certificates, 2026-09-28:
/// `bs_wrapping_2p32_bug`, `bs_heap_2p32_bug`, `bs_ptr_eq_2p32_safe`). A
/// stepped pointer whose high offset bits are set names no object: its lane
/// is no allocation's, so a dereference fails the validity check and it
/// equals no other object's pointer.
///
/// # One model per family — no hybrid
///
/// Mixing the lane model with an exact step within one chain is wrong: the
/// lane step drops the carry, so after an exact step leaves the pointer near
/// the top of its lane, a following lane step loses it
/// (`check_wrap_around_ptr` in `expected/offset-wraps-around`:
/// `p.wrapping_byte_add(usize::MAX).wrapping_byte_add(1)` must return `p`).
/// The wrapping family therefore gets ONE model, exact mod 2^64 on the address
/// view, end to end, and constant operands fold to a literal of it.
///
/// This free function is the step when no address region is remapped: an
/// untracked object's region is its id. `ChcCtx::step_wrapping_address` is the
/// step callers use; it adds the region map of tracked locals when a step can
/// change region.
///
/// For a symbolic offset the `obj_id` lane stops folding, so a later deref of
/// the result gets symbolic `obj_valid` and `obj_size` selects from
/// `heap_access_checks` rather than a resolved allocation bound. The bounds
/// half of that check used to be SKIPPED for a symbolic lane, so a read past
/// a `Box` through `p.wrapping_add(2)` verified clean (review of
/// fix/chc-lost-writes, lostwrite round 1, finding 4); it is now the size of
/// the object the lane names, one certified check over a choice of the objects
/// whose size the encoder records (`symbolic_lane_bounds`: address-taken stack
/// slots, heap allocations, statics and the global objects the harness reads),
/// and a lane naming an object with no recorded size stays unbounded. Provenance is
/// unaffected — `offset_walk_identity_callee` already resolves the
/// allocation through the whole `wrapping_*` family via the `known_alloc_ids`
/// side-channel, which is keyed by local rather than by expression shape.
pub(in crate::codegen_ay::chc) fn step_wrapping_pointer(
    ptr: Expr,
    byte_offset: Expr,
    is_sub: bool,
) -> Expr {
    if ptr.sort().bitvec_width() != Some(POINTER_WIDTH) || POINTER_WIDTH != 64 {
        return if is_sub { ptr.bvsub(byte_offset) } else { ptr.bvadd(byte_offset) };
    }
    if let Some(result) = const_fold_wrapping_step(&ptr, &byte_offset, is_sub) {
        return result;
    }
    let view = identity_address_view(ptr);
    let moved = if is_sub { view.bvsub(byte_offset) } else { view.bvadd(byte_offset) };
    identity_address_view(moved)
}

/// The wrapping step on constants: a zero offset returns `ptr` itself (memory
/// scalarization and select-over-store matching rely on the expression
/// identity), and a constant pointer and offset fold to a literal.
fn const_fold_wrapping_step(ptr: &Expr, byte_offset: &Expr, is_sub: bool) -> Option<Expr> {
    let folded_off = trust_mc_core::chc_const_prop::eval::try_eval_to_const(byte_offset);
    let byte_offset = folded_off.as_ref().unwrap_or(byte_offset);
    let (off_v, off_w) = const_bv_value(byte_offset)?;
    if off_w != 64 {
        return None;
    }
    if off_v == BigInt::from(0u8) {
        return Some(ptr.clone());
    }
    let folded_ptr = trust_mc_core::chc_const_prop::eval::try_eval_to_const(ptr);
    let ptr = folded_ptr.as_ref().unwrap_or(ptr);
    let (ptr_v, ptr_w) = const_bv_value(ptr)?;
    if ptr_w != 64 {
        return None;
    }
    let modulus: BigInt = BigInt::from(1u8) << 64u32;
    let view = identity_address_view_value(&ptr_v);
    let moved = if is_sub { view - off_v } else { view + off_v };
    let moved = ((moved % &modulus) + &modulus) % &modulus;
    Some(Expr::bitvec_const(identity_address_view_value(&moved), 64))
}

/// Whether a constant wrapping step keeps its pointer's address region (the
/// top 16 bits of the address view): `None` when an operand is not constant.
pub(in crate::codegen_ay::chc) fn wrapping_step_keeps_region(
    ptr: &Expr,
    byte_offset: &Expr,
    is_sub: bool,
) -> Option<bool> {
    let folded_off = trust_mc_core::chc_const_prop::eval::try_eval_to_const(byte_offset);
    let (off_v, _) = const_bv_value(folded_off.as_ref().unwrap_or(byte_offset))?;
    let folded_ptr = trust_mc_core::chc_const_prop::eval::try_eval_to_const(ptr);
    let (ptr_v, _) = const_bv_value(folded_ptr.as_ref().unwrap_or(ptr))?;
    let modulus: BigInt = BigInt::from(1u8) << 64u32;
    let view = identity_address_view_value(&ptr_v);
    let moved = if is_sub { &view - off_v } else { &view + off_v };
    let moved = ((moved % &modulus) + &modulus) % &modulus;
    Some((view >> 48u32) == (moved >> 48u32))
}

/// Byte-step a pointer that may be WIDE, keeping a slice/str/dyn pointer's
/// metadata.
///
/// `<*const [T]>::wrapping_byte_add(n)` is
/// `self.cast::<u8>().wrapping_add(n).with_metadata_of(self)`: the data word
/// moves and the metadata does not. The byte-step stubs used to coerce the
/// operand to `POINTER_WIDTH` first, which for a `bv128` fat pointer keeps the
/// data word and DROPS the length. The destination slot then held a widened
/// thin pointer whose high half `PtrMetadata` reads back as a fabricated `0`,
/// so `ptr.wrapping_byte_add(k).wrapping_byte_sub(k)` lost `len()` and a true
/// `val.len() == data.len()` was refuted as a Genuine counterexample
/// (tests/expected/ptr_to_ref_cast/slice/test.rs, check_with_byte_add_sub_pass).
///
/// `step` is the family's own data-word step, applied to a `POINTER_WIDTH`
/// address, so the thin behaviour is unchanged. Only a structurally FAT operand
/// (`PtrRepr::Fat`) keeps its metadata half; a widened thin pointer has none to
/// keep, and every other shape takes the pre-existing coercion inside `step`.
pub(in crate::codegen_ay::chc) fn step_pointer_data_keep_metadata(
    ptr: Expr,
    step: impl FnOnce(Expr) -> Option<Expr>,
) -> Option<Expr> {
    use crate::codegen_ay::provenance::Loc;
    use crate::codegen_ay::ptr_repr::PtrRepr;
    match PtrRepr::classify(&ptr) {
        Some(PtrRepr::Fat { data, meta }) => {
            let stepped = step(data.into_expr())?;
            if stepped.sort().bitvec_width() != Some(POINTER_WIDTH) {
                return None;
            }
            PtrRepr::from_declared_roles(Loc::of_address(stepped), meta).into_packed()
        }
        _ => step(ptr),
    }
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
        // Strict for the negative path, as in `step_split_pointer`: `-2^32`
        // leaves the low lane unchanged but is a whole-lane move.
        let ok = if is_negative {
            new_lo < lo && off_hi == lane_mask
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
    use ay_bindings::Sort;

    use super::*;

    /// The wrapping family must NOT truncate the offset to the low 32-bit lane.
    /// `step_split_pointer` discards `extract(63, 32)` of the offset, which makes
    /// every nonzero multiple of 2^32 an additive identity — the Kani #1150 shape.
    #[test]
    fn test_wrapping_step_does_not_truncate_symbolic_offset() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0000u128, 64);
        let sym_offset = Expr::var("off", Sort::bitvec(64));

        let split = step_split_pointer(ptr.clone(), sym_offset.clone()).result;
        let wrapping = step_wrapping_pointer(ptr.clone(), sym_offset.clone(), false);

        // The split step truncates: the offset's high lane never reaches the result.
        assert!(
            split.to_string().contains("extract"),
            "split step should truncate the offset to the low lane: {split}"
        );
        // The wrapping step keeps the whole 64-bit offset, added to the address
        // view of the identity term.
        assert_eq!(
            wrapping,
            identity_address_view(identity_address_view(ptr).bvadd(sym_offset)),
            "wrapping step must be a full-width add on the address view"
        );
    }

    /// A constant step of exactly 2^32 must MOVE the pointer. Under the lane
    /// model this folded to the base address and statically discharged
    /// `assert_eq!(ptr, ptr.wrapping_byte_offset(1 << 32))` — a fabricated proof.
    #[test]
    fn test_wrapping_step_by_two_pow_32_moves_the_pointer() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0000u128, 64);
        let two_pow_32 = Expr::bitvec_const(1u128 << 32, 64);

        let moved = step_wrapping_pointer(ptr.clone(), two_pow_32, false);

        assert_ne!(moved, ptr, "a 2^32 step must not fold back to the base pointer");
        // The carry lands in the high offset bits, not in the object field: the
        // result is object 2 at offset 2^32, not object 3 (fourth review of
        // fix/chc-false-certificates: `bs_wrapping_2p32_bug`).
        assert_eq!(moved, Expr::bitvec_const(0x0001_0002_0000_0000u128, 64));
    }

    /// A step that carries past a 48-bit offset moves to the next address
    /// region (Kani's object bits), and the reverse step comes back.
    #[test]
    fn test_wrapping_step_carries_into_the_object_field_only_past_2_pow_48() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0000u128, 64);
        let two_pow_48 = Expr::bitvec_const(1u128 << 48, 64);
        let moved = step_wrapping_pointer(ptr.clone(), two_pow_48.clone(), false);
        assert_eq!(moved, Expr::bitvec_const(0x0000_0003_0000_0000u128, 64));
        assert_eq!(step_wrapping_pointer(moved, two_pow_48, true), ptr);
    }

    /// One byte below offset 0 is the top of the previous region: its lane is
    /// no object's, and one byte up is the pointer again.
    #[test]
    fn test_wrapping_step_below_offset_zero_names_no_object() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0000u128, 64);
        let one = Expr::bitvec_const(1u128, 64);
        let below = step_wrapping_pointer(ptr.clone(), one.clone(), true);
        assert_eq!(below, Expr::bitvec_const(0xFFFF_0001_FFFF_FFFFu128, 64));
        assert_eq!(step_wrapping_pointer(below, one, false), ptr);
    }

    /// Chained wrapping steps must compose exactly: `+usize::MAX` then `+1` is a
    /// full 2^64 wrap back to the original address. A lane step at the second
    /// hop drops the carry out of the low lane and lands on `obj_id - 1`
    /// (`check_wrap_around_ptr` in `expected/offset-wraps-around`).
    #[test]
    fn test_wrapping_step_chain_wraps_around_to_base() {
        let ptr = Expr::var("p", Sort::bitvec(64));
        let usize_max = Expr::bitvec_const(u64::MAX as u128, 64);
        let one = Expr::bitvec_const(1u128, 64);

        let step1 = step_wrapping_pointer(ptr.clone(), usize_max, false);
        let step2 = step_wrapping_pointer(step1, one.clone(), false);

        // Both hops stay in the same (full-width) model, so the carry survives.
        let view = identity_address_view(ptr);
        let step1_expected = identity_address_view(
            view.bvadd(Expr::bitvec_const(u64::MAX as u128, 64)),
        );
        assert_eq!(
            step2,
            identity_address_view(identity_address_view(step1_expected).bvadd(one))
        );
    }

    /// The constant chain folds back to the base literal.
    #[test]
    fn test_wrapping_step_constant_chain_wraps_around_to_base() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0010u128, 64);
        let usize_max = Expr::bitvec_const(u64::MAX as u128, 64);
        let one = Expr::bitvec_const(1u128, 64);
        let step1 = step_wrapping_pointer(ptr.clone(), usize_max, false);
        assert_eq!(step_wrapping_pointer(step1, one, false), ptr);
    }

    /// A zero step is the identity in the wrapping model too.
    #[test]
    fn test_wrapping_step_by_zero_is_identity() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0010u128, 64);
        let zero = Expr::bitvec_const(0u128, 64);
        assert_eq!(step_wrapping_pointer(ptr.clone(), zero, false), ptr);
    }

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

    /// An index step of exactly `2^32` bytes lands on the base lane offset;
    /// its exactness condition must not hold.
    #[test]
    fn test_index_step_two_pow_32_is_not_exact() {
        let ptr = Expr::var("p", Sort::bitvec(64));
        let idx = Expr::bitvec_const(1u128 << 32, 64);
        let step = step_split_pointer_index(ptr, idx, 1);
        let exact = step.same_object_ok.expect("64-bit index step surfaces exactness");
        let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&exact);
        assert!(
            folded.is_none_or(|v| v == Expr::bool_const(false)),
            "a 2^32-byte index step is not lane-exact: {exact}"
        );
    }

    /// A small constant index step on a constant in-lane pointer is exact and
    /// folds to `true`, so fully concrete accesses add no obligation.
    #[test]
    fn test_index_step_small_const_is_exact_and_folds() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0010u128, 64);
        let idx = Expr::bitvec_const(3u128, 64);
        let step = step_split_pointer_index(ptr, idx, 4);
        assert_eq!(step.result, Expr::bitvec_const(0x0000_0002_0000_001Cu128, 64));
        // The exactness condition conjoins lane_ok (which folds to true), the
        // `idx * size` overflow check and the sign-bit test. `try_eval_to_const`
        // has arms for BvAddNoOverflowUnsigned and BvSubNoUnderflowUnsigned but
        // NOT for BvMulNoOverflowUnsigned, so for constants the conjunction does
        // not collapse to a literal `true`. Assert what actually holds -- the step
        // is exact, i.e. its exactness condition never folds to false -- using the
        // same idiom as the sibling tests below.
        let exact = step.same_object_ok.expect("index step surfaces exactness");
        let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&exact);
        assert!(
            folded.is_none_or(|v| v == Expr::bool_const(true)),
            "a small in-lane constant index step is exact: {exact}"
        );
    }

    /// `idx * size` overflowing usize is an out-of-bounds index, not an exact
    /// step: `2^62 * 4 == 0 (mod 2^64)` would alias the base element.
    #[test]
    fn test_index_step_multiplication_overflow_is_not_exact() {
        let ptr = Expr::bitvec_const(0x0000_0002_0000_0010u128, 64);
        let idx = Expr::bitvec_const(1u128 << 62, 64);
        let step = step_split_pointer_index(ptr, idx, 4);
        let exact = step.same_object_ok.expect("index step surfaces exactness");
        let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&exact);
        assert!(
            folded.is_none_or(|v| v == Expr::bool_const(false)),
            "an overflowing index product is not exact: {exact}"
        );
    }

    /// `-2^32` has a zero low lane, so the lane step leaves the offset lane
    /// unchanged; the exact address moves down one whole lane. The constant
    /// fold must take the full-width path, not report a same-object no-op.
    #[test]
    fn test_split_pointer_step_minus_two_pow_32_is_not_same_object_const() {
        let ptr = Expr::bitvec_const(0x0000_0042_0000_0100u128, 64);
        let minus_two_pow_32 = Expr::bitvec_const(0xFFFF_FFFF_0000_0000u128, 64);

        let step = step_split_pointer(ptr, minus_two_pow_32);

        assert_eq!(step.result, Expr::bitvec_const(0x0000_0041_0000_0100u128, 64));
        assert_eq!(
            step.same_object_ok.expect("const fold must surface same_object_ok"),
            Expr::bool_const(false),
        );
    }

    /// Symbolic twin of the constant `-2^32` case: `same_object_ok` must be
    /// false for that offset whatever the pointer is, because the lane result
    /// (`ptr` unchanged) is not the exact address `ptr - 2^32`.
    #[test]
    fn test_split_pointer_step_minus_two_pow_32_is_not_same_object_symbolic() {
        let ptr = Expr::var("p", Sort::bitvec(64));
        let minus_two_pow_32 = Expr::bitvec_const(0xFFFF_FFFF_0000_0000u128, 64);

        let step = step_split_pointer(ptr, minus_two_pow_32);
        let same_object_ok = step.same_object_ok.expect("symbolic step surfaces same_object_ok");

        let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&same_object_ok);
        assert!(
            folded.is_none_or(|v| v == Expr::bool_const(false)),
            "same_object_ok must not fold to true for -2^32: {same_object_ok}"
        );
        let rendered = same_object_ok.to_string();
        assert!(rendered.contains("bvult"), "negative path must be strict: {rendered}");
    }
}
