// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Lexicographic comparison for fixed-size arrays (SIMD PartialOrd support).
//!
//! Part of #3806: handles `[T; N]::partial_cmp`, `ge`, `le`, `lt`, `gt`
//! where the operands are encoded as SMT Array sorts with BV elements.

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};

use super::super::ChcCtx;
use super::super::codegen_types::CodegenTypes;
use super::super::ptr_receiver_mem;
use crate::codegen_ay::provenance::MaybeLoc;

/// Maximum number of array lanes for unrolled lexicographic comparison.
/// Beyond this, fall back to sound over-approximation.
pub(in crate::codegen_ay::chc) const MAX_LEXICO_LANES: usize = 16;

/// Extract the fixed-array length from a comparison operand type.
///
/// Comparison args are typically `&[T; N]` or `&[T]`. This peels through
/// references and returns `Some(N)` for `[T; N]`, `None` otherwise.
pub(in crate::codegen_ay::chc) fn array_len_from_operand(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<usize> {
    let ty = arg.ty(locals).ok()?;
    // Peel through multiple reference levels: &&[T; N] → &[T; N] → [T; N]
    // This handles the `<&A as PartialOrd<&B>>::partial_cmp` blanket impl
    // which produces double-referenced operands. Part of #3806.
    let mut inner = ty;
    for _ in 0..5 {
        match inner.kind() {
            TyKind::RigidTy(RigidTy::Array(_, const_len)) => {
                let len = const_len.eval_target_usize().ok()?;
                return Some(len as usize);
            }
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
            // Part of #4086: peel through single-field ADTs (repr(simd) types like
            // `i64x2([i64; 2])`) to find the inner [T; N] array length.
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let variants = def.variants();
                if variants.len() == 1 && variants[0].fields().len() == 1 {
                    inner = variants[0].fields()[0].ty_with_args(&args);
                } else {
                    return None;
                }
            }
            _ => return None,
        }
    }
    None
}

/// Fallback: extract array length by scanning body locals for `[T; N]` types.
///
/// When `partial_cmp` is called on `&[T]` (slice), the MIR type loses the
/// array length N. But the body typically has a local with type `[T; N]`
/// (the original array before unsizing). This scans all locals for a unique
/// array declaration with matching element type.
///
/// Part of #3806: handles the MIR unsizing coercion chain where
/// `[T; N]::partial_cmp` delegates to `[T]::partial_cmp`.
pub(in crate::codegen_ay::chc) fn array_len_from_body_locals(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<usize> {
    let ty = arg.ty(locals).ok()?;
    // Extract element type from Slice, peeling multiple reference levels.
    // Handles &&[T] → &[T] → [T] → T (from blanket `<&A as PartialOrd<&B>>`).
    // Part of #3806.
    let elem_ty = peel_refs_to_slice_elem(ty)?;
    // Scan all locals for [elem_ty; N] declarations.
    // Also scans through SIMD ADT single-field wrappers like i64x2([i64; 2]).
    // Part of #3806.
    let mut found_len: Option<usize> = None;
    for local_decl in locals {
        if let Some(len) = extract_array_len_from_ty(local_decl.ty, elem_ty) {
            match found_len {
                None => found_len = Some(len),
                Some(existing) if existing == len => {}
                Some(_) => return None, // ambiguous — multiple different lengths
            }
        }
    }
    found_len
}

/// Peel through up to 3 reference levels to find a Slice element type.
/// `&&[T]` → `&[T]` → `[T]` → `T`. Part of #3806.
fn peel_refs_to_slice_elem(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
    let mut inner = ty;
    for _ in 0..3 {
        match inner.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => return Some(elem),
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
            _ => return None,
        }
    }
    None
}

/// Recursively extract `[T; N]` length from a type, peeling through
/// references, raw pointers, and single-field ADT wrappers (e.g. SIMD repr types).
///
/// Part of #3806: handles `i64x2([i64; 2])` → `[i64; 2]` → len=2.
fn extract_array_len_from_ty(
    ty: rustc_public::ty::Ty,
    elem_ty: rustc_public::ty::Ty,
) -> Option<usize> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Array(arr_elem, const_len)) => {
            if arr_elem == elem_ty {
                const_len.eval_target_usize().ok().map(|n| n as usize)
            } else {
                None
            }
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            extract_array_len_from_ty(inner, elem_ty)
        }
        TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
            let variants = adt_def.variants();
            if variants.len() == 1 && variants[0].fields().len() == 1 {
                let field_ty = variants[0].fields()[0].ty_with_args(&args);
                extract_array_len_from_ty(field_ty, elem_ty)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Build a lexicographic ordering ITE chain for fixed-size arrays.
///
/// For arrays `lhs[0..N]` and `rhs[0..N]`, produces:
/// ```text
/// if lhs[0] < rhs[0] then -1
/// elif lhs[0] > rhs[0] then 1
/// elif lhs[1] < rhs[1] then -1
/// elif lhs[1] > rhs[1] then 1
/// ...
/// else 0  (equal)
/// ```
///
/// Returns BV32 ordering discriminant (-1, 0, 1) matching Rust's Ordering enum.
pub(in crate::codegen_ay::chc) fn build_lexicographic_cmp(
    lhs: &Expr,
    rhs: &Expr,
    len: usize,
    is_signed: bool,
) -> Option<Expr> {
    let arr = lhs.sort().array_sort()?;
    if !arr.element_sort.is_bitvec() {
        return None;
    }
    let idx_width = arr.index_sort.bitvec_width()?;
    let neg1 = Expr::bitvec_const(-1i128, 32);
    let pos1 = Expr::bitvec_const(1, 32);

    // Build from the innermost (equal) outward.
    let mut result = Expr::bitvec_const(0, 32);
    for i in (0..len).rev() {
        let idx = Expr::bitvec_const(i as u64, idx_width);
        let l = lhs.clone().select(idx.clone());
        let r = rhs.clone().select(idx);
        let lt = if is_signed { l.clone().bvslt(r.clone()) } else { l.clone().bvult(r.clone()) };
        let gt = if is_signed { l.bvsgt(r) } else { l.bvugt(r) };
        result = Expr::ite(lt, neg1.clone(), Expr::ite(gt, pos1.clone(), result));
    }
    Some(result)
}

/// Build a lexicographic boolean comparison for fixed-size arrays.
///
/// For `lt`: true iff lhs is lexicographically less than rhs.
/// For `le`/`gt`/`ge`: analogous.
pub(in crate::codegen_ay::chc) fn build_lexicographic_ord(
    lhs: &Expr,
    rhs: &Expr,
    len: usize,
    method: &str,
    is_signed: bool,
) -> Option<Expr> {
    let cmp = build_lexicographic_cmp(lhs, rhs, len, is_signed)?;
    let zero = Expr::bitvec_const(0i128, 32);
    let neg1 = Expr::bitvec_const(-1i128, 32);
    let pos1 = Expr::bitvec_const(1, 32);
    Some(match method {
        "lt" => cmp.eq(neg1),
        "le" => cmp.clone().eq(neg1).or(cmp.eq(zero)),
        "gt" => cmp.eq(pos1),
        "ge" => cmp.clone().eq(pos1).or(cmp.eq(zero)),
        _ => return None,
    })
}

/// Load array elements from heap memory via BV64 data pointer.
///
/// When CHC encodes `&&[T; N]` comparisons, the operands resolve to BV64
/// pointers (addresses in heap memory). This function loads each element
/// individually from the heap using the pointer as a base address.
///
/// Part of #3806: enables element-wise comparison for SIMD PartialOrd
/// when operands are heap-stored (not Array-sort state vars).
pub(in crate::codegen_ay::chc) fn try_load_array_elements(
    ctx: &mut ChcCtx<'_, '_>,
    data_ptr: &Expr,
    arg: &Operand,
    len: usize,
) -> Option<Vec<Expr>> {
    if data_ptr.sort().bitvec_width() != Some(64) {
        return None;
    }
    let ty = arg.ty(ctx.body.locals()).ok()?;
    let elem_ty = peel_refs_to_element(ty)?;

    let elem_sort = ChcCtx::translate_ty(elem_ty)?;
    let elem_bytes = elem_sort.bitvec_width()? / 8;
    if elem_bytes == 0 {
        return None;
    }

    let mut elements = Vec::with_capacity(len);
    for i in 0..len {
        let offset = Expr::bitvec_const(i as u64 * elem_bytes as u64, 64);
        let addr = data_ptr.clone().bvadd(offset);
        // `data_ptr` is a bare parameter and this is byte arithmetic on it: the
        // caller never told us it was an address, so say so rather than imply it.
        let loaded =
            ptr_receiver_mem::load_from_memory(ctx, &MaybeLoc::Unknown(addr), elem_ty)?.into_expr();
        elements.push(loaded);
    }
    Some(elements)
}

/// Peel through references, slices, and arrays to find the innermost element type.
/// `&&[T]` → `&[T]` → `[T]` → T
/// `&&[T; N]` → `&[T; N]` → `[T; N]` → T
/// Part of #3806.
fn peel_refs_to_element(ty: rustc_public::ty::Ty) -> Option<rustc_public::ty::Ty> {
    let mut inner = ty;
    for _ in 0..4 {
        match inner.kind() {
            TyKind::RigidTy(RigidTy::Slice(elem)) => return Some(elem),
            TyKind::RigidTy(RigidTy::Array(elem, _)) => return Some(elem),
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
            _ => return None,
        }
    }
    None
}

/// Build a lexicographic cmp ITE chain from pre-loaded element vectors.
///
/// Unlike `build_lexicographic_cmp` (which operates on SMT Array sorts),
/// this takes element Vec<Expr> already loaded from heap memory.
/// Returns BV32 ordering discriminant (-1, 0, 1).
/// Part of #3806.
pub(in crate::codegen_ay::chc) fn build_lexicographic_cmp_from_elements(
    lhs_elems: &[Expr],
    rhs_elems: &[Expr],
    is_signed: bool,
) -> Option<Expr> {
    if lhs_elems.is_empty() || lhs_elems.len() != rhs_elems.len() {
        return None;
    }
    if !lhs_elems[0].sort().is_bitvec() {
        return None;
    }
    let neg1 = Expr::bitvec_const(-1i128, 32);
    let pos1 = Expr::bitvec_const(1, 32);
    let mut result = Expr::bitvec_const(0, 32);
    for i in (0..lhs_elems.len()).rev() {
        let l = &lhs_elems[i];
        let r = &rhs_elems[i];
        let lt = if is_signed { l.clone().bvslt(r.clone()) } else { l.clone().bvult(r.clone()) };
        let gt = if is_signed { l.clone().bvsgt(r.clone()) } else { l.clone().bvugt(r.clone()) };
        result = Expr::ite(lt, neg1.clone(), Expr::ite(gt, pos1.clone(), result));
    }
    Some(result)
}

/// Part of #4086: Extract elements from a packed BV representing a fixed-size array.
///
/// For BV(N*W) representing `[T; N]` where T is W bits, extract each element
/// using `extract(hi, lo)`. Elements are in little-endian layout:
/// element 0 occupies bits [W-1:0], element 1 occupies bits [2W-1:W], etc.
pub(in crate::codegen_ay::chc) fn extract_packed_bv_elements(
    packed: &Expr,
    num_elements: usize,
    elem_width: u32,
) -> Option<Vec<Expr>> {
    let total_width = packed.sort().bitvec_width()?;
    if total_width != (num_elements as u32) * elem_width {
        return None;
    }
    let mut elements = Vec::with_capacity(num_elements);
    for i in 0..num_elements {
        let lo = (i as u32) * elem_width;
        let hi = lo + elem_width - 1;
        elements.push(packed.clone().extract(hi, lo));
    }
    Some(elements)
}

/// Part of #4086: Determine the element width for a packed SIMD BV operand.
///
/// Given a MIR operand whose type is `&&SimdType` or `&SimdType`, peel through
/// references and single-field ADTs to find the inner `[T; N]` array and return
/// the element bit width.
pub(in crate::codegen_ay::chc) fn packed_simd_element_width(
    arg: &Operand,
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<u32> {
    let ty = arg.ty(locals).ok()?;
    let mut inner = ty;
    for _ in 0..5 {
        match inner.kind() {
            TyKind::RigidTy(RigidTy::Array(elem_ty, _))
            | TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                let sort = ChcCtx::translate_ty(elem_ty)?;
                return sort.bitvec_width();
            }
            TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => inner = pointee,
            TyKind::RigidTy(RigidTy::Adt(def, args)) => {
                let variants = def.variants();
                if variants.len() == 1 && variants[0].fields().len() == 1 {
                    inner = variants[0].fields()[0].ty_with_args(&args);
                } else {
                    return None;
                }
            }
            _ => return None,
        }
    }
    None
}

/// Build a lexicographic boolean comparison from pre-loaded element vectors.
/// Part of #3806.
pub(in crate::codegen_ay::chc) fn build_lexicographic_ord_from_elements(
    lhs_elems: &[Expr],
    rhs_elems: &[Expr],
    method: &str,
    is_signed: bool,
) -> Option<Expr> {
    let cmp = build_lexicographic_cmp_from_elements(lhs_elems, rhs_elems, is_signed)?;
    let zero = Expr::bitvec_const(0i128, 32);
    let neg1 = Expr::bitvec_const(-1i128, 32);
    let pos1 = Expr::bitvec_const(1, 32);
    Some(match method {
        "lt" => cmp.eq(neg1),
        "le" => cmp.clone().eq(neg1).or(cmp.eq(zero)),
        "gt" => cmp.eq(pos1),
        "ge" => cmp.clone().eq(pos1).or(cmp.eq(zero)),
        _ => return None,
    })
}
