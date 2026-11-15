// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A transmute between a multi-field struct (or tuple) and a bitvector follows
//! the MEMORY layout, or the result is fresh.
//!
//! `flatten_datatype_to_bitvec` and `unflatten_bitvec_to_datatype` are the
//! encoder's internal flat form of a datatype: fields concatenated MSB-first in
//! declaration order. That form is not what `transmute` means. On a
//! little-endian target the field at byte offset 0 is the LOW end of the
//! integer, and rustc may reorder a `repr(Rust)` struct's fields, so declaration
//! order says nothing either. The transmute cast used the internal form as a
//! "precise" reinterpretation, which transposed the words of every two-field
//! struct:
//!
//! * `transmute::<P { a: 1, b: 0 }, u128>(..) != 1` PROVED (the model computed
//!   `1 << 64`), and its safe twin `== 1` failed with a certified counterexample;
//! * `#[repr(C)] struct FatPtr { data, len }` transmuted to `&[u8]` put the DATA
//!   word in the length half: `s[2]` on a two-element slice was proved in
//!   bounds, and `transmute::<&[u8], FatPtr>(s).len` read the address.
//!
//! This module builds the reinterpretation from the MIR layout instead: field
//! offsets and sizes from rustc, the little-endian byte order, and the word
//! roles of the other side (a slice pointer's low word is an address, its high
//! word a length). Padding bytes read as data are fresh (they are uninitialized).
//! Any shape it does not model exactly (a nested aggregate, a `bool` or `char`
//! read out of raw bits, a pointer word split across fields or padded) is
//! [`AggregateTransmute::Unsupported`], and the caller writes a fresh value: a
//! sound over-approximation, never the transposed guess.

use crate::codegen_ay::chc::codegen_ctx::ExactVar;
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::abi::FieldsShape;
use rustc_public::ty::{AdtKind, RigidTy, Ty, TyKind};
use tracing::debug;

use crate::codegen_ay::chc::call::canonical_zst_expr_for_sort;
use crate::codegen_ay::types::{POINTER_WIDTH, datatype_field_select};

use super::codegen_stmt_slice_len_write::{is_slice_len_pointer_ty, slice_slot_has_widened_leaf};
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name};

/// What the memory-order lane decided for one transmute.
#[derive(Debug)]
pub(in crate::codegen_ay::chc) enum AggregateTransmute {
    /// Not a multi-field aggregate facing a bitvector: the caller's own lanes
    /// apply unchanged.
    NotApplicable,
    /// The reinterpretation, built from the MIR layout.
    Precise(Expr),
    /// A multi-field aggregate facing a bitvector in a layout this lane does
    /// not model. The caller must write a fresh value (fail closed), never the
    /// declaration-order flatten.
    Unsupported(&'static str),
}

/// What a field (or a word of the bitvector side) holds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Role {
    /// An integer or float: its bits pass through unchanged.
    Int,
    /// A thin pointer: an address in the encoder's pointer representation.
    Ptr,
    /// `bool`: one byte, valid only as 0 or 1.
    Bool,
    /// `char`: four bytes, valid only as a scalar value.
    Char,
    /// A zero-sized field: no bytes.
    Zst,
    /// Anything else (a nested aggregate, an array, an enum, a wide pointer).
    Other,
}

/// One field of the aggregate as it lies in memory.
#[derive(Clone, Debug)]
struct Slot {
    /// Index in the datatype constructor, which is the MIR declaration order.
    decl_idx: usize,
    offset: u64,
    size: u64,
    role: Role,
    ty: Ty,
}

/// The bitvector side of the transmute.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BitsSide {
    /// An integer, float or `char`: every byte is data.
    Integer,
    /// A thin pointer: bytes `0..8` are one address.
    ThinPtr,
    /// A `&[T]` / `&str` / slice-tail pointer: bytes `0..8` are the data
    /// address, bytes `8..16` the length.
    SlicePtr,
}

impl BitsSide {
    /// The role of the bytes `offset..offset + size` on this side, or `None`
    /// when the range straddles an address word (it must be exactly one).
    fn role_of(self, offset: u64, size: u64) -> Option<Role> {
        let word = u64::from(POINTER_WIDTH / 8);
        let in_addr_word = match self {
            Self::Integer => return Some(Role::Int),
            Self::ThinPtr | Self::SlicePtr => offset < word,
        };
        if !in_addr_word {
            return Some(Role::Int);
        }
        (offset == 0 && size == word).then_some(Role::Ptr)
    }
}

fn field_role(ty: Ty, size: u64) -> Role {
    if size == 0 {
        return Role::Zst;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_)) => Role::Int,
        TyKind::RigidTy(RigidTy::Bool) => Role::Bool,
        TyKind::RigidTy(RigidTy::Char) => Role::Char,
        TyKind::RigidTy(RigidTy::FnPtr(_)) => Role::Ptr,
        TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..))
            if size == u64::from(POINTER_WIDTH / 8) =>
        {
            Role::Ptr
        }
        _ => Role::Other,
    }
}

/// The memory slots of a struct or tuple with at least two non-ZST fields,
/// with its total size. `None` for any other type: those are not what this
/// lane is about.
fn aggregate_slots(ty: Ty, resolve: &dyn Fn(Ty) -> Ty) -> Option<(Vec<Slot>, u64)> {
    let field_tys: Vec<Ty> = match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) if def.kind() == AdtKind::Struct => {
            let variants = def.variants();
            let [variant] = variants.as_slice() else { return None };
            variant
                .fields()
                .iter()
                .map(|field| mono_ty::field_ty(field, &args).map(resolve))
                .collect::<Option<Vec<Ty>>>()?
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => tys.iter().map(|ty| resolve(*ty)).collect(),
        _ => return None,
    };
    if field_tys.len() < 2 {
        return None;
    }
    let shape = ty.layout().ok()?.shape();
    let FieldsShape::Arbitrary { offsets } = &shape.fields else { return None };
    if offsets.len() != field_tys.len() {
        return None;
    }
    let mut slots = Vec::with_capacity(field_tys.len());
    for (decl_idx, (field_ty, offset)) in field_tys.into_iter().zip(offsets).enumerate() {
        let size = field_ty.layout().ok()?.shape().size.bytes() as u64;
        slots.push(Slot {
            decl_idx,
            offset: offset.bytes() as u64,
            size,
            role: field_role(field_ty, size),
            ty: field_ty,
        });
    }
    if slots.iter().filter(|slot| slot.role != Role::Zst).count() < 2 {
        return None;
    }
    Some((slots, shape.size.bytes() as u64))
}

fn bits_side(ty: Ty) -> Option<BitsSide> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_) | RigidTy::Float(_) | RigidTy::Char) => {
            Some(BitsSide::Integer)
        }
        TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)) if is_slice_len_pointer_ty(ty) => {
            Some(BitsSide::SlicePtr)
        }
        TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..) | RigidTy::FnPtr(_)) => {
            Some(BitsSide::ThinPtr)
        }
        _ => None,
    }
}

/// The datatype sort of an aggregate whose constructor fields are its MIR
/// fields in declaration order, or `None` for any other encoding.
fn aggregate_datatype(sort: &Sort, field_count: usize) -> Option<()> {
    let dt = sort.datatype_sort()?;
    let [cons] = dt.constructors.as_slice() else { return None };
    (cons.fields.len() == field_count).then_some(())
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The memory-order reinterpretation of `value` (of MIR type `src_ty`) as
    /// `target_ty`, when exactly one side is a multi-field struct or tuple and
    /// the other a bitvector. See the module documentation.
    pub(in crate::codegen_ay::chc) fn transmute_aggregate_memory_order(
        &self,
        value: &Expr,
        src_ty: Ty,
        target_ty: Ty,
    ) -> AggregateTransmute {
        let resolve = |ty: Ty| self.resolve_body_ty(ty);
        let src_ty = resolve(src_ty);
        let target_ty = resolve(target_ty);
        let Some(target_sort) = Self::translate_ty(target_ty) else {
            return AggregateTransmute::NotApplicable;
        };
        match (aggregate_slots(src_ty, &resolve), aggregate_slots(target_ty, &resolve)) {
            (Some((slots, size)), None) => {
                if aggregate_datatype(value.sort(), slots.len()).is_none() {
                    return AggregateTransmute::NotApplicable;
                }
                let Some(width) = target_sort.bitvec_width() else {
                    return AggregateTransmute::NotApplicable;
                };
                if u64::from(width) != 8 * size {
                    return AggregateTransmute::Unsupported("aggregate size differs from the bits");
                }
                let Some(side) = bits_side(target_ty) else {
                    return AggregateTransmute::Unsupported(
                        "bits side is not an integer or pointer",
                    );
                };
                self.aggregate_to_bits(value, &slots, size, side)
            }
            (None, Some((slots, size))) => {
                if aggregate_datatype(&target_sort, slots.len()).is_none() {
                    return AggregateTransmute::NotApplicable;
                }
                let Some(width) = value.sort().bitvec_width() else {
                    return AggregateTransmute::NotApplicable;
                };
                if u64::from(width) != 8 * size {
                    return AggregateTransmute::Unsupported("aggregate size differs from the bits");
                }
                let Some(side) = bits_side(src_ty) else {
                    return AggregateTransmute::Unsupported(
                        "bits side is not an integer or pointer",
                    );
                };
                if side == BitsSide::SlicePtr && slice_slot_has_widened_leaf(value) {
                    return AggregateTransmute::Unsupported("slice pointer without a length");
                }
                self.bits_to_aggregate(value, &slots, side, &target_sort)
            }
            _ => AggregateTransmute::NotApplicable,
        }
    }

    /// Whether [`Self::transmute_aggregate_memory_order`] can build a precise
    /// value for `src_ty` read as `target_ty`, decided from the types alone:
    /// exactly one side a multi-field struct or tuple, the other an integer or
    /// pointer of the same size. A caller that must translate an operand only
    /// for the lane asks first, so a declined lane leaves no trace.
    pub(in crate::codegen_ay::chc) fn transmute_aggregate_memory_order_applies(
        &self,
        src_ty: Ty,
        target_ty: Ty,
    ) -> bool {
        let resolve = |ty: Ty| self.resolve_body_ty(ty);
        let src_ty = resolve(src_ty);
        let target_ty = resolve(target_ty);
        let bits_of = |ty: Ty| Self::translate_ty(ty).and_then(|sort| sort.bitvec_width());
        match (aggregate_slots(src_ty, &resolve), aggregate_slots(target_ty, &resolve)) {
            (Some((_, size)), None) => {
                bits_side(target_ty).is_some() && bits_of(target_ty) == Some(8 * size as u32)
            }
            (None, Some((_, size))) => {
                bits_side(src_ty).is_some() && bits_of(src_ty) == Some(8 * size as u32)
            }
            _ => false,
        }
    }

    /// Struct to bits: the field at the highest offset is the most significant.
    ///
    /// Padding bytes are uninitialized memory: their value is unspecified, and
    /// reading them is undefined behaviour that `-Z uninit-checks` reports on
    /// its own. Each gap is a fresh bitvector, which is the model of "any
    /// value", not an approximation of a value the program computes, so it
    /// books no fallback reason. A gap inside an address word is refused.
    fn aggregate_to_bits(
        &self,
        value: &Expr,
        slots: &[Slot],
        size: u64,
        side: BitsSide,
    ) -> AggregateTransmute {
        let mut data: Vec<&Slot> = slots.iter().filter(|slot| slot.role != Role::Zst).collect();
        data.sort_by_key(|slot| slot.offset);
        let mut pieces = Vec::with_capacity(2 * data.len() + 1);
        let mut end = 0;
        for slot in data {
            if slot.offset < end {
                return AggregateTransmute::Unsupported("aggregate fields overlap");
            }
            if slot.offset > end {
                let Some(piece) = self.padding_piece(end, slot.offset - end, side) else {
                    return AggregateTransmute::Unsupported("padding inside an address word");
                };
                pieces.push(piece);
            }
            end = slot.offset + slot.size;
            let Some(field) = datatype_field_select(value.clone(), 0, slot.decl_idx) else {
                return AggregateTransmute::Unsupported("aggregate field not selectable");
            };
            let Some(word) = side.role_of(slot.offset, slot.size) else {
                return AggregateTransmute::Unsupported("address word split across fields");
            };
            let bits = 8 * slot.size as u32;
            let piece = match slot.role {
                Role::Int | Role::Ptr | Role::Char if field.sort().bitvec_width() == Some(bits) => {
                    match (slot.role, word) {
                        (Role::Ptr, Role::Int) => self.ptr_to_int_value(field),
                        (Role::Int, Role::Ptr) => self.int_to_ptr_value(field),
                        (Role::Char, Role::Ptr) => {
                            return AggregateTransmute::Unsupported("char in an address word");
                        }
                        _ => field,
                    }
                }
                Role::Bool if field.sort().is_bool() && bits == 8 && word == Role::Int => {
                    Expr::ite(field, Expr::bitvec_const(1u64, 8), Expr::bitvec_const(0u64, 8))
                }
                _ => return AggregateTransmute::Unsupported("field is not a scalar"),
            };
            pieces.push(piece);
        }
        if end > size {
            return AggregateTransmute::Unsupported("aggregate fields exceed its size");
        }
        if end < size {
            let Some(piece) = self.padding_piece(end, size - end, side) else {
                return AggregateTransmute::Unsupported("padding inside an address word");
            };
            pieces.push(piece);
        }
        // Little-endian: fold from the highest offset down, so the field at
        // offset 0 ends up in the low bits.
        let mut iter = pieces.into_iter().rev();
        let Some(first) = iter.next() else {
            return AggregateTransmute::Unsupported("aggregate has no data");
        };
        let bits = iter.fold(first, Expr::concat);
        debug!(?side, "CHC: transmute of an aggregate to bits in memory order");
        AggregateTransmute::Precise(bits)
    }

    /// Fresh bits for `len` padding bytes at `offset`, or `None` when they
    /// fall inside an address word of the bitvector side.
    fn padding_piece(&self, offset: u64, len: u64, side: BitsSide) -> Option<Expr> {
        let word = u64::from(POINTER_WIDTH / 8);
        if side != BitsSide::Integer && offset < word {
            return None;
        }
        Some(ExactVar::nondet(chc_fresh_name("__transmute_padding"), Sort::bitvec(8 * len as u32)))
    }

    /// Bits to struct: each field is the byte range at its offset.
    fn bits_to_aggregate(
        &self,
        value: &Expr,
        slots: &[Slot],
        side: BitsSide,
        target_sort: &Sort,
    ) -> AggregateTransmute {
        let Some(dt) = target_sort.datatype_sort() else {
            return AggregateTransmute::NotApplicable;
        };
        let cons = &dt.constructors[0];
        let mut fields = Vec::with_capacity(slots.len());
        for (slot, decl) in slots.iter().zip(cons.fields.iter()) {
            if slot.role == Role::Zst {
                let Some(zst) = canonical_zst_expr_for_sort(slot.ty, &decl.sort) else {
                    return AggregateTransmute::Unsupported(
                        "zero-sized field has no canonical value",
                    );
                };
                fields.push(zst);
                continue;
            }
            let bits = 8 * slot.size as u32;
            if !matches!(slot.role, Role::Int | Role::Ptr) || decl.sort.bitvec_width() != Some(bits)
            {
                return AggregateTransmute::Unsupported("field is not an integer or pointer");
            }
            let Some(word) = side.role_of(slot.offset, slot.size) else {
                return AggregateTransmute::Unsupported("address word split across fields");
            };
            let lo = 8 * slot.offset as u32;
            let piece = value.clone().extract(lo + bits - 1, lo);
            fields.push(match (slot.role, word) {
                (Role::Ptr, Role::Int) => self.int_to_ptr_value(piece),
                (Role::Int, Role::Ptr) => self.ptr_to_int_value(piece),
                _ => piece,
            });
        }
        debug!(?side, "CHC: transmute of bits to an aggregate in memory order");
        AggregateTransmute::Precise(Expr::datatype_constructor(
            &*dt.name,
            &*cons.name,
            fields,
            target_sort.clone(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::{BitsSide, Role};

    #[test]
    fn slice_pointer_words_are_address_then_length() {
        assert_eq!(BitsSide::SlicePtr.role_of(0, 8), Some(Role::Ptr));
        assert_eq!(BitsSide::SlicePtr.role_of(8, 8), Some(Role::Int));
        assert_eq!(BitsSide::SlicePtr.role_of(12, 4), Some(Role::Int));
        // A field that covers only part of the address word has no role.
        assert_eq!(BitsSide::SlicePtr.role_of(0, 4), None);
        assert_eq!(BitsSide::SlicePtr.role_of(4, 4), None);
        assert_eq!(BitsSide::ThinPtr.role_of(0, 8), Some(Role::Ptr));
        assert_eq!(BitsSide::Integer.role_of(0, 8), Some(Role::Int));
        assert_eq!(BitsSide::Integer.role_of(8, 8), Some(Role::Int));
    }
}
