// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A wide slice pointer's length reaches its slot exactly, or not at all.
//!
//! Design 4 of `docs/chc-hole-fix-designs-2026-09-24.md` ("Array-to-slice length
//! lost"). `translate_ty` gives `&[T]`, `*const [T]`, `&str` and pointers to
//! slice-tail ADTs a `2 * POINTER_WIDTH` slot laid out `[len : upper | data :
//! lower]`. Every reader of that slot that finds no side-table fact
//! (`resolve_ptr_metadata_known`'s last lane, and every reader of a loop-carried
//! or joined slice local) takes the high half as the length. So a producer that
//! writes a thin address widened into the slot writes a length of `0`, which the
//! program never computed:
//!
//! * the unsize cast `&[u8; 10] -> &[u8]` zero-extended the thin operand, so a
//!   slice-pattern loop over the result read `len >= 1` as false at entry and was
//!   pruned as dead, and a false post-loop assertion PROVED
//!   (`tools/soundness-duals/chc_slice_pattern_loop_dead_dual.rs`);
//! * a join `let s: &[u8] = if c { &a } else { &b }` read `s.len() == 0` as
//!   true on both paths and PROVED (`chc_slice_len_join_dual.rs`);
//! * the subslice borrow `rest = &(*bytes)[1..]` produced the thin address of
//!   the subslice, so the second trip round the loop read length `0` again.
//!
//! This module is the producer side (A: unsize, C: unsized borrow) and the
//! write boundary (D) that fails closed on every other producer: a value whose
//! high half is extension padding becomes a counted FRESH length, never `0`.

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::HashSet;
use tracing::debug;

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::{PtrRepr, PtrSlot};
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};
use crate::kani_middle::abi::LayoutOf;

use super::codegen_stmt_slice_metadata::projected_subslice_len;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name};

/// Fail-close reason for a slice slot whose length no producer supplied. It is
/// deliberately NOT a blessed sound-havoc reason: a proof that rests on the
/// fresh length is demoted (Step C), because the fresh value stands for a
/// length the encoder failed to carry, and a precision fix belongs at the
/// producer.
pub(in crate::codegen_ay::chc) const SLICE_LEN_UNRESOLVED_REASON: &str =
    "slice_len_unresolved_at_write";

/// `true` for `[T]`, `str`, and ADTs whose unsized tail is one of those: the
/// pointees `translate_ty` gives a `[len : upper | data : lower]` wide slot.
pub(in crate::codegen_ay::chc) fn is_slice_like_unsized(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Slice(_) | RigidTy::Str) => true,
        TyKind::RigidTy(RigidTy::Adt(..)) => LayoutOf::new(ty).has_slice_tail(),
        _ => false,
    }
}

/// `true` for a `&`/`*` pointer to a slice-like pointee. Mirrors the
/// `RawPtr | Ref` arm of `translate_ty` exactly, so a `true` here is a
/// `2 * POINTER_WIDTH` slot whose high half is a LENGTH (never a vtable).
pub(in crate::codegen_ay::chc) fn is_slice_len_pointer_ty(ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
            is_slice_like_unsized(pointee)
        }
        _ => false,
    }
}

/// Packs a `Slice_*`-like datatype's DECLARED roles into the wide slot.
///
/// A single-constructor datatype with `fld_ptr` and `fld_len` pointer-width
/// fields is a slice view (`Slice_*`, or a `Vec` read as its slice). Its
/// flattened form must be `[fld_len : upper | fld_ptr : lower]`;
/// `flatten_datatype_to_bitvec` is MSB-first and would transpose the two, and
/// the `fld_ptr`-only coercions write a widened thin pointer. `None` when the
/// value is not such a datatype or the target is not a wide slot.
pub(in crate::codegen_ay::chc) fn pack_declared_slice_roles(
    value: &Expr,
    target_width: u32,
) -> Option<Expr> {
    if target_width != 2 * POINTER_WIDTH {
        return None;
    }
    let dt = value.sort().datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let cons = &dt.constructors[0];
    let field_sort = |name: &str| {
        cons.fields.iter().find(|field| &*field.name == name).map(|field| field.sort.clone())
    };
    let ptr_sort_decl = field_sort("fld_ptr")?;
    let len_sort_decl = field_sort("fld_len")?;
    if ptr_sort_decl.bitvec_width() != Some(POINTER_WIDTH)
        || len_sort_decl.bitvec_width() != Some(POINTER_WIDTH)
    {
        return None;
    }
    let data = Loc::of_address(value.clone().field_select(&dt.name, "fld_ptr", ptr_sort_decl));
    let meta = Val::of_value(value.clone().field_select(&dt.name, "fld_len", len_sort_decl));
    PtrRepr::from_declared_roles(data, meta).into_packed()
}

/// A leaf whose high half is not a length the program computed: a thin
/// address widened into the slot (structurally, or folded to a constant whose
/// high half is zero), or an `int2bv` of an unbounded integer, which has no
/// pointer structure at all. No exemption for a folded zero-high constant: an
/// empty slice built that way is indistinguishable from a widened address.
fn slice_slot_leaf_unresolved(leaf: &Expr) -> bool {
    if matches!(leaf.value(), ExprValue::Int2Bv(..)) {
        return true;
    }
    matches!(PtrRepr::classify(leaf), Some(PtrRepr::WidenedThin(_)))
}

/// `true` when some `ite` leaf of a wide value has no length in its high half.
/// A reader must not take the high half of such a value as a length: on the
/// widened leaf's path it is extension padding. `classify` calls a whole `ite`
/// an opaque (fat) pointer, so it cannot answer this.
pub(in crate::codegen_ay::chc) fn slice_slot_has_widened_leaf(value: &Expr) -> bool {
    if value.sort().bitvec_width() != Some(2 * POINTER_WIDTH) {
        return false;
    }
    let mut unresolved = false;
    let _ = map_ite_leaves(value, &mut |leaf| {
        unresolved |= slice_slot_leaf_unresolved(leaf);
        leaf.clone()
    });
    unresolved
}

/// Rebuilds `value` with `f` applied to every `ite` leaf of the same sort. A
/// join writes `ite(c, a, b)` into the slot; its high half is the length only
/// if it is the length on EACH branch, so the guard looks at the leaves.
fn map_ite_leaves(value: &Expr, f: &mut dyn FnMut(&Expr) -> Expr) -> Expr {
    if let ExprValue::Ite { cond, then_expr, else_expr } = value.value()
        && then_expr.sort() == value.sort()
        && else_expr.sort() == value.sort()
    {
        let then_mapped = map_ite_leaves(then_expr, f);
        let else_mapped = map_ite_leaves(else_expr, f);
        if &then_mapped == then_expr && &else_mapped == else_expr {
            return value.clone();
        }
        return Expr::ite(cond.clone(), then_mapped, else_mapped);
    }
    f(value)
}

/// The length word of a constant wide slice pointer (`&str`, `&[T]`, or a
/// pointer to a slice-tail ADT): its allocation holds `[data, len]`, one word
/// each. `None` for any other operand, or an allocation that does not spell
/// the length out in initialized bytes.
fn const_operand_slice_len(operand: &Operand) -> Option<u64> {
    use crate::codegen_ay::shared::const_pointer::{self, ConstRead};

    let Operand::Constant(const_op) = operand else { return None };
    if !is_slice_len_pointer_ty(const_op.ty()) {
        return None;
    }
    // The metadata word beside the data pointer, as initialized data.
    const_pointer::const_bytes(&const_op.const_)?.stored_word((POINTER_WIDTH / 8) as usize)
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// `[len : upper | data : lower]` for a thin address and a length, or the
    /// address widened (for the write-boundary guard to fail closed) when the
    /// two are not pointer-width words.
    pub(in crate::codegen_ay::chc) fn pack_slice_slot(&self, addr: Expr, len: Expr) -> Expr {
        if addr.sort().bitvec_width() == Some(POINTER_WIDTH)
            && len.sort().bitvec_width() == Some(POINTER_WIDTH)
            && let Some(packed) =
                PtrRepr::from_declared_roles(Loc::of_address(addr.clone()), Val::of_value(len))
                    .into_packed()
        {
            return packed;
        }
        coerce_bitvec_width_safe(addr, 2 * POINTER_WIDTH, SignExtension::ZeroExtend)
    }

    /// The length of a promoted constant slice or `str` that `rhs` writes into
    /// the wide slot of `local_idx`, when some route knows it: the constant's
    /// own length word, or the metadata of a sole-producer local it copies.
    pub(in crate::codegen_ay::chc) fn promoted_const_slice_len(
        &self,
        rhs: &rustc_public::mir::Rvalue,
        local_idx: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use rustc_public::mir::Rvalue;

        if !is_slice_len_pointer_ty(self.body.locals().get(local_idx)?.ty) {
            return None;
        }
        match rhs {
            Rvalue::Use(operand @ Operand::Constant(_), ..) => const_operand_slice_len(operand)
                .map(|len| Expr::bitvec_const(len as u128, POINTER_WIDTH)),
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..)
                if src.projection.is_empty()
                    && !self.local_has_multiple_whole_definitions(src.local)
                    && !self.pointer_value_is_path_dependent(src.local) =>
            {
                self.resolve_ptr_metadata_known(&Operand::Copy(src.clone()), modified_locals)
            }
            _ => None,
        }
    }

    /// `operand` as the value of a WHOLE slice (`&x[..]`): a wide pointer
    /// operand that carries its length is returned as is, and a thin pointer to
    /// an array (or an array-tail ADT) is packed with the array's length. `None`
    /// for any other shape, which the write boundary then fails closed.
    pub(in crate::codegen_ay::chc) fn whole_slice_value_of(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let value = self.translate_operand_with_modified(operand, modified_locals)?;
        match PtrRepr::classify(&value)? {
            PtrRepr::Thin(addr) => {
                let len = Self::extract_array_len_from_ref(operand.ty(self.body.locals()).ok()?)?;
                PtrRepr::from_declared_roles(
                    addr,
                    Val::of_value(Expr::bitvec_const(len as u128, POINTER_WIDTH)),
                )
                .into_packed()
            }
            PtrRepr::Fat { .. } if !slice_slot_has_widened_leaf(&value) => Some(value),
            PtrRepr::Fat { .. } | PtrRepr::WidenedThin(_) => None,
        }
    }

    /// A counted fresh length, booked fail-closed.
    pub(in crate::codegen_ay::chc) fn fresh_unresolved_slice_len(&mut self, site: &str) -> Expr {
        debug!(fn_name = %self.fn_name, site, "slice length unresolved: fresh length, fail-closed");
        let booked = self.record_sound_fallback_reason(SLICE_LEN_UNRESOLVED_REASON);
        Havoc::booked(booked, chc_fresh_name("__slice_len_unresolved"), ptr_sort())
    }

    /// Design 4 A (statement path): the unsize cast `&[T; N] -> &[T]` (and a
    /// `*const`/`*mut` or slice-tail ADT version of it) writes `N`, the source's
    /// compile-time length, into the metadata half.
    ///
    /// `None` leaves the caller on its old lane: the target slot is not wide,
    /// the source has no array tail, or the operand is not a thin pointer term.
    /// Whatever that lane writes still passes the write-boundary guard.
    pub(in crate::codegen_ay::chc) fn pack_array_unsize_len(
        &mut self,
        operand: &Operand,
        target_ty: Ty,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if !is_slice_len_pointer_ty(target_ty) {
            return None;
        }
        let target_sort = Self::translate_ty(target_ty)?;
        if PtrSlot::of_sort(&target_sort) != Some(PtrSlot::Fat) {
            return None;
        }
        let src_ty = operand.ty(self.body.locals()).ok()?;
        let len = Self::extract_array_len_from_ref(src_ty)?;
        let value = self.translate_operand_with_modified(operand, modified_locals)?;
        let PtrRepr::Thin(addr) = PtrRepr::classify(&value)? else {
            return None;
        };
        debug!(len, ?target_ty, "CHC: array-to-slice unsize packs its length (design 4 A)");
        PtrRepr::from_declared_roles(
            addr,
            Val::of_value(Expr::bitvec_const(len as u128, POINTER_WIDTH)),
        )
        .into_packed()
    }

    /// Design 4 C: a borrow of an unsized slice-like place through a wide
    /// pointer carries a length.
    ///
    /// `value` is what `translate_ref_or_addressof` produced. When the borrowed
    /// place is slice-like unsized and `value` is a thin address, the result is
    /// packed with the length of the borrowed place:
    ///
    /// * `&(*p).f.g` ending at the unsized tail: the length of `p`, unchanged;
    /// * `&(*p)[from..to]` / `&(*p)[from..len-to]` (optionally after such a
    ///   field chain): `projected_subslice_len` of it.
    ///
    /// Any other shape returns `value` unchanged, and the write boundary fails
    /// it closed.
    pub(in crate::codegen_ay::chc) fn pack_unsized_borrow_len(
        &mut self,
        place: &Place,
        value: Expr,
        modified_locals: &HashSet<usize>,
    ) -> Expr {
        let Ok(place_ty) = place.ty(self.body.locals()) else {
            return value;
        };
        if !is_slice_like_unsized(place_ty) {
            return value;
        }
        let Some(PtrRepr::Thin(addr)) = PtrRepr::classify(&value) else {
            return value;
        };
        let Some(len) = self.unsized_borrow_len(place, modified_locals) else {
            return value;
        };
        debug!(?place, "CHC: unsized borrow carries its length (design 4 C)");
        PtrRepr::from_declared_roles(addr, Val::of_value(len)).into_packed().unwrap_or(value)
    }

    /// The length of the unsized place `place`, or `None` for a shape this
    /// does not model. See [`Self::pack_unsized_borrow_len`].
    fn unsized_borrow_len(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let [ProjectionElem::Deref, rest @ ..] = place.projection.as_slice() else {
            return None;
        };
        let base = place.local;
        let base_ty = self.body.locals().get(base)?.ty;
        if !is_slice_len_pointer_ty(base_ty) {
            return None;
        }
        // `[Field*]` down the unsized tail, then at most one `Subslice`.
        let (fields, subslice) = match rest {
            [fields @ .., ProjectionElem::Subslice { from, to, from_end }] => {
                (fields, Some((*from, *to, *from_end)))
            }
            fields => (fields, None),
        };
        if !fields.iter().all(|proj| matches!(proj, ProjectionElem::Field(..))) {
            return None;
        }
        // Every step of the field chain must stay unsized: only the tail field
        // of an unsized ADT is, so this is exactly "the path to the tail".
        let mut prefix = Place { local: base, projection: vec![ProjectionElem::Deref] };
        for field in fields {
            prefix.projection.push(field.clone());
            if !is_slice_like_unsized(prefix.ty(self.body.locals()).ok()?) {
                return None;
            }
        }
        let base_len = self.slice_base_len(base, modified_locals);
        match subslice {
            None => Some(base_len),
            Some((from, to, from_end)) => {
                match projected_subslice_len(base_len.clone(), from, to, from_end) {
                    Some(len) => Some(len),
                    // Statically out of bounds for a constant base length: the
                    // borrow is unreachable in a well-typed run, but a fresh
                    // length is the honest value, not a guess.
                    None => Some(self.fresh_unresolved_slice_len("subslice_bounds")),
                }
            }
        }
    }

    /// The length of the wide pointer local `base` at this program point.
    ///
    /// A local with several definitions, or one whose value depends on the
    /// path, is read from its CURRENT value: the path-insensitive side tables
    /// behind `resolve_ptr_metadata_known` name whichever producer was encoded
    /// last. A sole-producer local may use those tables. Either way a length
    /// nothing supplies is a counted fresh value.
    fn slice_base_len(&mut self, base: usize, modified_locals: &HashSet<usize>) -> Expr {
        let base_place = Place { local: base, projection: vec![] };
        let path_sensitive = self.local_has_multiple_whole_definitions(base)
            || self.pointer_value_is_path_dependent(base);
        if !path_sensitive
            && let Some(len) =
                self.resolve_ptr_metadata_known(&Operand::Copy(base_place.clone()), modified_locals)
        {
            return len;
        }
        if let Some(current) = self.translate_place_with_modified(&base_place, modified_locals)
            && let Some(meta) = self
                .guarded_slice_slot_value(current)
                .and_then(|v| PtrRepr::classify(&v).and_then(PtrRepr::into_metadata))
        {
            return meta.into_expr();
        }
        self.fresh_unresolved_slice_len("unsized_borrow_base")
    }

    /// The current value of a slice slot, if every `ite` leaf of it carries a
    /// length. Used to read a base length: a value with any widened leaf has
    /// no length to read on that path.
    fn guarded_slice_slot_value(&self, value: Expr) -> Option<Expr> {
        if value.sort().bitvec_width() != Some(2 * POINTER_WIDTH)
            || slice_slot_has_widened_leaf(&value)
        {
            return None;
        }
        Some(value)
    }

    /// Design 4 D: the write boundary of a slice slot.
    ///
    /// `dest_ty` is the MIR type of the place being written. For any type other
    /// than a `&`/`*` to a slice-like pointee, `value` is returned unchanged.
    /// Otherwise the value is first coerced to the wide slot exactly as the
    /// downstream coercions would (a `Slice_*` datatype through its declared
    /// roles, a narrower bitvector by zero extension), and then every `ite`
    /// leaf whose high half is not a computed length gets a counted FRESH
    /// length, keeping its data address. One fresh value per leaf, returned in
    /// the value itself, so every consumer of the returned expression (the
    /// destination equality, `local_expr_env`, memory mirrors) agrees on it.
    pub(in crate::codegen_ay::chc) fn guard_slice_len_slot_write(
        &mut self,
        dest_ty: Ty,
        value: Expr,
        site: &'static str,
    ) -> Expr {
        if !is_slice_len_pointer_ty(dest_ty) {
            return value;
        }
        let wide = 2 * POINTER_WIDTH;
        let value = if let Some(packed) = pack_declared_slice_roles(&value, wide) {
            packed
        } else {
            match value.sort().bitvec_width() {
                Some(width) if width == wide => value,
                Some(width) if width < wide => {
                    coerce_bitvec_width_safe(value, wide, SignExtension::ZeroExtend)
                }
                // Some other sort: the downstream coercion decides (and fails
                // closed on a mismatch); there is no length to guard here.
                _ => return value,
            }
        };
        map_ite_leaves(&value, &mut |leaf| {
            if !slice_slot_leaf_unresolved(leaf) {
                return leaf.clone();
            }
            debug!(site, %leaf, "slice slot write: widened leaf gets a fresh length (design 4 D)");
            // A widened pointer-width address keeps its own term as the data
            // lane; anything else keeps its low half.
            let data = match leaf.value() {
                ExprValue::BvZeroExtend { expr: inner, .. }
                | ExprValue::BvSignExtend { expr: inner, .. }
                    if inner.sort().bitvec_width() == Some(POINTER_WIDTH) =>
                {
                    Loc::of_address(inner.clone())
                }
                _ => PtrRepr::classify(leaf)
                    .map(PtrRepr::into_data)
                    .unwrap_or_else(|| Loc::of_address(leaf.clone().extract(POINTER_WIDTH - 1, 0))),
            };
            let len = self.fresh_unresolved_slice_len(site);
            PtrRepr::from_declared_roles(data, Val::of_value(len))
                .into_packed()
                .unwrap_or_else(|| leaf.clone())
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{map_ite_leaves, pack_declared_slice_roles, slice_slot_leaf_unresolved};
    use crate::codegen_ay::ptr_repr::PtrRepr;
    use crate::codegen_ay::types::POINTER_WIDTH;
    use ay_bindings::{Expr, Sort};

    fn addr(name: &str) -> Expr {
        Expr::var(name, Sort::bitvec(POINTER_WIDTH))
    }

    #[test]
    fn widened_and_int2bv_leaves_are_unresolved() {
        assert!(slice_slot_leaf_unresolved(&addr("_1").zero_extend(POINTER_WIDTH)));
        assert!(slice_slot_leaf_unresolved(&Expr::bitvec_const(0x1000u64, 2 * POINTER_WIDTH)));
        assert!(slice_slot_leaf_unresolved(
            &Expr::var("_i", Sort::int()).int2bv(2 * POINTER_WIDTH)
        ));
    }

    #[test]
    fn packed_and_opaque_leaves_are_resolved() {
        let packed = Expr::bitvec_const(10u64, POINTER_WIDTH).concat(addr("_2"));
        assert!(!slice_slot_leaf_unresolved(&packed));
        assert!(!slice_slot_leaf_unresolved(&Expr::var("_s", Sort::bitvec(2 * POINTER_WIDTH))));
    }

    #[test]
    fn ite_leaves_are_visited_per_branch() {
        let good = Expr::bitvec_const(3u64, POINTER_WIDTH).concat(addr("_a"));
        let bad = addr("_b").zero_extend(POINTER_WIDTH);
        let joined = Expr::ite(Expr::var("c", Sort::bool()), good.clone(), bad.clone());
        let mut seen = Vec::new();
        let rebuilt = map_ite_leaves(&joined, &mut |leaf| {
            seen.push(slice_slot_leaf_unresolved(leaf));
            leaf.clone()
        });
        assert_eq!(seen, vec![false, true]);
        assert_eq!(rebuilt, joined, "an identity map keeps the expression");
    }

    #[test]
    fn slice_datatype_packs_len_high_ptr_low() {
        let slice_sort = Sort::struct_type(
            "Slice_bv8_len_pack_test",
            vec![
                ("fld_ptr".to_string(), Sort::bitvec(POINTER_WIDTH)),
                ("fld_len".to_string(), Sort::bitvec(POINTER_WIDTH)),
                ("fld_data".to_string(), Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(8))),
            ],
        );
        let value = Expr::var("_v", slice_sort);
        let packed = pack_declared_slice_roles(&value, 2 * POINTER_WIDTH).expect("slice roles");
        let repr = PtrRepr::classify(&packed).expect("wide pointer");
        let meta = repr.metadata().expect("declared length").as_expr().to_string();
        assert!(meta.contains("fld_len"), "high half is fld_len: {meta}");
        assert!(repr.data().as_expr().to_string().contains("fld_ptr"));
        assert!(pack_declared_slice_roles(&value, POINTER_WIDTH).is_none());
    }
}
