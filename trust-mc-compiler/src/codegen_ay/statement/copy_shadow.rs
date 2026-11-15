// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed-environment encoding of the copy-family intrinsics, and the
//! object-bounds obligation of checked pointer offsets (default BMC lane).
//!
//! # The desync this closes
//!
//! The BMC lane keeps two views of an address-taken stack local: its value in
//! the SSA environment (`current_env`, which every `x`, `arr[i]` and
//! ref-resolved `*p` read consults) and a byte image in the `memory` array
//! (written once, when the address is taken — #1246). `copy`,
//! `copy_nonoverlapping` and `write_bytes` were unrolled into `memory` ONLY,
//! and `copy` also read its source bytes from `memory`, so neither direction
//! ever reached the environment:
//!
//! ```text
//! let mut val: u64 = 0;
//! write_bytes(&mut val as *mut u64, 0xFF, 1);
//! assert_eq!(val, 0);          // VERIFICATION:- SUCCESSFUL, PROOF_QUALIFIERS:clean
//! ```
//!
//! and `copy(arr.as_ptr(), arr.as_ptr().add(1), 2)` on `[0, 1, 0]` left
//! `arr[2] == 0` provable. Both are clean proofs of false statements
//! (soundness duals `dual_write_bytes_nonzero_count_invalid.rs` and
//! `dual_p4_copy.rs`).
//!
//! # The rule
//!
//! A copy-family write that is not provably empty is ENCODED EXACTLY when every
//! object it reads or writes resolves to an address-taken local of the current
//! body, of primitive-integer (or primitive-integer array) type, whose
//! environment value is the only typed view of that storage. Everything else is
//! recorded through `unsupported_with_fallback`, which demotes the proof. There
//! is no third outcome: a write this module cannot place is never dropped
//! silently.
//!
//! "Exactly" is byte-exact: the environment value of an integer local IS its
//! little-endian byte image, which is the layout `memory` uses, so a byte-level
//! splice of that value is the write itself — for any `T` the pointers claim.
//! The rebuilt value is committed through `assert_ssa_def`, so a write under a
//! path condition keeps the pre-state on the untaken path.

use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, Ty, TyKind};

use super::codegen_copy::MAX_PTR_PEEL;
use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

/// Largest local, in bytes, whose byte image an exact write rebuilds.
const MAX_SHADOW_BYTES: u128 = 128;

/// Demotion key for a copy-family write that cannot be placed exactly.
const SHADOW_DESYNC: &str = "copy-family write not encoded into the typed environment";

/// Kani's wording for the `ptr::offset` allocation obligation (kani_core models.rs).
const OFFSET_SAME_ALLOCATION: &str =
    "Offset result and original pointer must point to the same allocation";

/// What a copy-family intrinsic writes into its destination.
#[derive(Clone, Copy)]
pub(super) enum CopyFamilySource<'e> {
    /// `write_bytes`: every destination byte receives this `u8`.
    Fill(&'e Expr),
    /// `copy` / `copy_nonoverlapping`: bytes are read through this pointer.
    Pointer(&'e Expr),
}

/// Byte count of a copy-family write.
enum ByteCount {
    Const(u128),
    Symbolic(Expr),
}

/// An address-taken local addressed by a pointer at a constant displacement.
struct LocalView {
    /// Environment base name of the local (`fn::local_N`).
    base: Arc<str>,
    /// Root the pointer peeled to (for de-duplicating the overlap check).
    root: Expr,
    /// Environment value of the local at this program point.
    value: Expr,
    /// Byte displacement of the pointer from the start of the local.
    offset: u128,
    /// Bytes the pointer may address: the local, or the slice view it came from.
    extent: u128,
    /// `emit_copy_region_validity_check` already carries the escape obligation
    /// (it decides slice-rooted pointers and abstains on the rest).
    region_checked: bool,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Encode a copy-family write into the typed environment, or demote.
    ///
    /// Returns `true` when the write was encoded exactly — environment AND
    /// byte memory updated here — so the caller must not unroll it again.
    /// Returns `false` after recording a demotion; the caller then performs its
    /// byte-level unroll as before, and the proof no longer stands on it.
    ///
    /// Call AFTER the shared obligations (byte-count overflow, alignment,
    /// region validity, root-based overlap): this adds only the region and
    /// overlap obligations those abstain on.
    pub(super) fn encode_copy_family_write(
        &mut self,
        intrinsic: &'static str,
        dst: &Operand,
        dst_ptr: &Expr,
        source: CopyFamilySource<'_>,
        count: &Operand,
        element_size: usize,
        nonoverlapping: bool,
    ) -> bool {
        // A constant zero count writes nothing, whatever the element type.
        if self.try_eval_const_operand(count) == Some(0) {
            return true;
        }
        // The callers default an undeterminable element size to 1; an exact
        // encoding must not inherit that guess.
        let pointee_size = dst.ty(self.body.locals()).into_option().and_then(|ty| {
            if let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = ty.kind() {
                LayoutOf::new(pointee).size_of()
            } else {
                None
            }
        });
        if pointee_size != Some(element_size) {
            return self.demote_copy_family(intrinsic, "element size not established");
        }
        if element_size == 0 {
            return true;
        }
        let count = match self.try_eval_const_operand(count) {
            Some(n) => ByteCount::Const((n as u128).saturating_mul(element_size as u128)),
            None => {
                let Some(count_expr) = self.codegen_operand(count) else {
                    return self.demote_copy_family(intrinsic, "count operand untranslatable");
                };
                let count_bv = self.coerce_to_ptr_width(count_expr);
                let elem = Expr::bitvec_const(element_size as u128, POINTER_WIDTH);
                ByteCount::Symbolic(count_bv.bvmul(elem))
            }
        };
        if matches!(count, ByteCount::Const(0)) {
            return true;
        }

        let Some(dst_view) = self.resolve_local_view(dst_ptr) else {
            return self
                .demote_copy_family(intrinsic, "destination is not an exclusively-viewed local");
        };
        let src_view = match source {
            CopyFamilySource::Fill(_) => None,
            CopyFamilySource::Pointer(src_ptr) => match self.resolve_local_view(src_ptr) {
                Some(view) => Some(view),
                None => {
                    return self.demote_copy_family(
                        intrinsic,
                        "source is not an exclusively-viewed local",
                    );
                }
            },
        };

        // Escape obligations the slice-rooted region check abstained on: the
        // object here is the local itself, so its size is the room.
        if !dst_view.region_checked {
            self.emit_local_view_region_check(
                &dst_view,
                &count,
                intrinsic,
                "destination region writeable",
            );
        }
        if let Some(src) = &src_view
            && !src.region_checked
        {
            self.emit_local_view_region_check(src, &count, intrinsic, "source region readable");
        }

        // Two views of ONE local overlap exactly when their displacement gap is
        // below the byte count. Distinct locals never overlap. When both
        // pointers peel to the same root, `emit_copy_nonoverlapping_overlap_check`
        // already decided this; only separately-derived pointers are new here.
        if nonoverlapping
            && let Some(src) = &src_view
            && src.base == dst_view.base
            && src.root != dst_view.root
        {
            let gap = src.offset.abs_diff(dst_view.offset);
            let violation = match &count {
                ByteCount::Const(n) => (*n > gap).then(|| Expr::bool_const(true)),
                ByteCount::Symbolic(total) => {
                    Some(total.clone().bvugt(Expr::bitvec_const(gap, POINTER_WIDTH)))
                }
            };
            if let Some(violation) = violation {
                self.record_violation_guarded_with_message(
                    violation,
                    "copy_overlap_check",
                    Some("memcpy src/dst overlap".to_string()),
                );
            }
        }

        let Some(old_bytes) = Self::local_view_bytes(&dst_view) else {
            return self.demote_copy_family(intrinsic, "destination value has no byte image");
        };
        // Read the source from the SAME pre-state before anything is written:
        // this is what makes an overlapping `copy` memmove.
        let src_bytes = match &src_view {
            None => None,
            Some(view) => match Self::local_view_bytes(view) {
                Some(bytes) => Some(bytes),
                None => {
                    return self.demote_copy_family(intrinsic, "source value has no byte image");
                }
            },
        };

        let mut new_bytes = old_bytes.clone();
        let mut memory_writes = Vec::new();
        let room = dst_view.extent - dst_view.offset;
        for rel in 0..room {
            if let ByteCount::Const(n) = &count
                && rel >= *n
            {
                break;
            }
            let byte = match (&source, &src_view, &src_bytes) {
                (CopyFamilySource::Fill(fill), _, _) => (*fill).clone(),
                (CopyFamilySource::Pointer(_), Some(view), Some(bytes)) => {
                    let at = view.offset + rel;
                    // Past the source object: every trace reaching here has
                    // already violated the source region obligation.
                    if at >= view.extent {
                        break;
                    }
                    bytes[at as usize].clone()
                }
                (CopyFamilySource::Pointer(_), _, _) => {
                    return self.demote_copy_family(intrinsic, "source view lost");
                }
            };
            let at = (dst_view.offset + rel) as usize;
            let addr = dst_ptr.clone().bvadd(Expr::bitvec_const(rel, POINTER_WIDTH));
            match &count {
                ByteCount::Const(_) => {
                    new_bytes[at] = byte.clone();
                    memory_writes.push((addr, byte));
                }
                ByteCount::Symbolic(total) => {
                    let taken = total.clone().bvugt(Expr::bitvec_const(rel, POINTER_WIDTH));
                    new_bytes[at] = Expr::ite(taken.clone(), byte.clone(), old_bytes[at].clone());
                    let old_memory = self.ctx.load_memory(addr.clone());
                    memory_writes.push((addr, Expr::ite(taken, byte, old_memory)));
                }
            }
        }

        let Some(new_value) = Self::rebuild_local_value(&dst_view.value, &old_bytes, &new_bytes)
        else {
            return self.demote_copy_family(intrinsic, "destination value could not be rebuilt");
        };
        let ssa_name = self.ssa_name_from_base(dst_view.base.as_ref(), true);
        let var = self.ctx.declare_var(&ssa_name, new_value.sort().clone());
        self.assert_ssa_def(var.clone(), new_value, dst_view.base.as_ref());
        self.env_update(Arc::clone(&dst_view.base), var);
        // Keep the byte image in step, so a memory-resolved read agrees — under
        // the same path condition the environment definition carries.
        for (addr, byte) in memory_writes {
            let byte = match self.current_path_condition.clone() {
                None => byte,
                Some(pc) => Expr::ite(pc, byte, self.ctx.load_memory(addr.clone())),
            };
            self.ctx.store_memory(addr, byte);
        }
        true
    }

    fn demote_copy_family(&mut self, intrinsic: &'static str, reason: &str) -> bool {
        self.ctx.unsupported_with_fallback(SHADOW_DESYNC, format!("{intrinsic}: {reason}"));
        false
    }

    fn emit_local_view_region_check(
        &mut self,
        view: &LocalView,
        count: &ByteCount,
        intrinsic: &str,
        what: &str,
    ) {
        let room = view.extent - view.offset;
        let violation = match count {
            ByteCount::Const(n) if *n <= room => return,
            ByteCount::Const(_) => Expr::bool_const(true),
            ByteCount::Symbolic(total) => {
                total.clone().bvugt(Expr::bitvec_const(room, POINTER_WIDTH))
            }
        };
        self.record_violation_guarded_with_message(
            violation,
            "region_validity_check",
            Some(format!("{intrinsic} {what}")),
        );
    }

    /// Resolve a pointer to the address-taken local it lands in, or `None`
    /// when that local is not provably the only typed view of its storage.
    fn resolve_local_view(&self, ptr: &Expr) -> Option<LocalView> {
        let (root, offset) = self.resolve_ptr_root_expr(ptr, MAX_PTR_PEEL)?;
        let offset = u128::try_from(offset).ok()?;
        let (base, view_extent, region_checked) = match self.slice_view_of_local(&root) {
            Some((base, extent)) => (base, Some(extent), true),
            None => (self.addr_symbol_base(&root)?, None, false),
        };
        let local_ty = self.local_decl_ty(base.as_ref())?;
        let local_bytes = u128::try_from(LayoutOf::new(local_ty).size_of()?).ok()?;
        let value = self.env_lookup(base.as_ref())?.clone();

        let extent = match local_ty.kind() {
            TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_)) => {
                let width = value.sort().bitvec_width()?;
                if u128::from(width) != local_bytes * 8 {
                    return None;
                }
                view_extent.unwrap_or(local_bytes)
            }
            TyKind::RigidTy(RigidTy::Array(elem_ty, _)) => {
                if !matches!(elem_ty.kind(), TyKind::RigidTy(RigidTy::Int(_) | RigidTy::Uint(_))) {
                    return None;
                }
                let elem_bytes = u128::try_from(LayoutOf::new(elem_ty).size_of()?).ok()?;
                let arr = value.sort().array_sort()?;
                if u128::from(arr.element_sort.bitvec_width()?) != elem_bytes * 8 {
                    return None;
                }
                // A thin pointer to an array states no length; only a slice
                // view carries one, and a view larger than the local is not
                // a view of it.
                let extent = view_extent?;
                if extent > local_bytes {
                    return None;
                }
                extent
            }
            _ => return None,
        };
        if extent > local_bytes || extent > MAX_SHADOW_BYTES || offset > extent {
            return None;
        }
        if self.local_has_other_typed_views(&base) {
            return None;
        }
        Some(LocalView { base, root, value, offset, extent, region_checked })
    }

    /// `fld_ptr(C)` where `C` is a slice/Vec constructor whose own `fld_ptr`
    /// is the undisplaced address symbol of a local: that local, and the
    /// constructor's byte extent.
    fn slice_view_of_local(&self, root: &Expr) -> Option<(Arc<str>, u128)> {
        let extent = self.root_object_extent(root)?;
        let root = self.follow_ssa(root, MAX_PTR_PEEL);
        let ExprValue::DatatypeSelector { selector_name, expr, .. } = root.value() else {
            return None;
        };
        if selector_name != "fld_ptr" {
            return None;
        }
        let built = self.follow_ssa(expr, MAX_PTR_PEEL);
        let ExprValue::DatatypeConstructor { args, .. } = built.value() else {
            return None;
        };
        let fields = &built.sort().datatype_sort()?.constructors.first()?.fields;
        let ptr_arg = args.get(fields.iter().position(|f| f.name == "fld_ptr")?)?;
        let (addr, 0) = self.resolve_ptr_root_expr(ptr_arg, MAX_PTR_PEEL)? else {
            return None;
        };
        Some((self.addr_symbol_base(&addr)?, extent))
    }

    /// The local whose stable address symbol `addr` is.
    fn addr_symbol_base(&self, addr: &Expr) -> Option<Arc<str>> {
        if !matches!(addr.value(), ExprValue::Var { .. }) {
            return None;
        }
        self.addr_symbols.iter().find(|(_, sym)| *sym == addr).map(|(base, _)| Arc::clone(base))
    }

    /// MIR type of a plain local of the body being encoded (`<fn>::local_N`).
    /// Field-, index- and deref-derived names, and an inlined callee's locals,
    /// are `None`.
    fn local_decl_ty(&self, base: &str) -> Option<Ty> {
        let index: usize = base
            .strip_prefix(self.ctx.current_fn_name())?
            .strip_prefix("::local_")?
            .parse()
            .ok()?;
        self.body.locals().get(index).map(|decl| decl.ty)
    }

    /// Whether any typed view OTHER than `current_env[base]` could hold this
    /// local's value. Each is a table a read can resolve through before (or
    /// instead of) the environment entry an exact write updates.
    fn local_has_other_typed_views(&self, base: &Arc<str>) -> bool {
        // Raw-pointer stores (#1210) key a value by POINTER name, and a later
        // `*p` returns it; nothing ties those keys to storage.
        if !self.heap_pointees.is_empty() {
            return true;
        }
        // A write inside a contract frame needs the assigns check the
        // raw-store path runs; that is not modelled here.
        if !self.modifies_frames.is_empty() {
            return true;
        }
        if self.repeat_array_values.contains_key(base.as_ref())
            || self.flattened_tuples.contains_key(base.as_ref())
            || self.stub_indexed_refs.values().any(|(container, _)| **container == **base)
        {
            return true;
        }
        // Derived environment names (field, index, materialized deref copies).
        let derived = format!("{base}_");
        if self.current_env.keys().any(|name| name.starts_with(derived.as_str())) {
            return true;
        }
        // `_deref` aliases holding their own environment value, unless they
        // provably resolve to some OTHER local.
        for pointee in self.ref_pointees.values() {
            if !pointee.contains("_deref") {
                continue;
            }
            let chain = self.resolve_deref_pointee_chain(pointee.as_ref());
            let elsewhere = chain
                .first()
                .is_some_and(|root| root.as_str() != &**pointee && root.as_str() != &**base);
            if elsewhere {
                continue;
            }
            if chain.iter().any(|name| name.as_str() != &**base && self.env_lookup(name).is_some())
            {
                return true;
            }
        }
        // A non-byte image of the local in memory is read by the ptr_source_map
        // chain terminal and would not see the write.
        self.addr_symbols
            .get(base.as_ref())
            .is_some_and(|addr| self.ctx.load_symbolic_memory_value(addr.clone()).is_some())
    }

    /// Little-endian byte image of the view's first `extent` bytes.
    fn local_view_bytes(view: &LocalView) -> Option<Vec<Expr>> {
        let value = &view.value;
        if let Some(width) = value.sort().bitvec_width() {
            if width % 8 != 0 || u128::from(width / 8) < view.extent {
                return None;
            }
            return Some((0..width / 8).map(|b| value.clone().extract(8 * b + 7, 8 * b)).collect());
        }
        let arr = value.sort().array_sort()?;
        let index_width = arr.index_sort.bitvec_width()?;
        let elem_width = arr.element_sort.bitvec_width()?;
        if elem_width == 0 || elem_width % 8 != 0 {
            return None;
        }
        let elem_bytes = u128::from(elem_width / 8);
        if view.extent % elem_bytes != 0 {
            return None;
        }
        let mut bytes = Vec::with_capacity(view.extent as usize);
        for k in 0..view.extent / elem_bytes {
            let elem = value.clone().select(Expr::bitvec_const(k, index_width));
            for b in 0..elem_width / 8 {
                bytes.push(elem.clone().extract(8 * b + 7, 8 * b));
            }
        }
        Some(bytes)
    }

    /// Inverse of `local_view_bytes`: splice `new` into `value`, storing only
    /// the array elements whose bytes changed.
    fn rebuild_local_value(value: &Expr, old: &[Expr], new: &[Expr]) -> Option<Expr> {
        fn concat_le(bytes: &[Expr]) -> Option<Expr> {
            let (first, rest) = bytes.split_first()?;
            Some(rest.iter().fold(first.clone(), |acc, byte| byte.clone().concat(acc)))
        }
        if old.len() != new.len() {
            return None;
        }
        if value.sort().bitvec_width().is_some() {
            return concat_le(new);
        }
        let arr = value.sort().array_sort()?;
        let index_width = arr.index_sort.bitvec_width()?;
        let elem_bytes = usize::try_from(arr.element_sort.bitvec_width()? / 8).ok()?;
        if elem_bytes == 0 {
            return None;
        }
        let mut rebuilt = value.clone();
        for (k, (old_elem, new_elem)) in
            old.chunks(elem_bytes).zip(new.chunks(elem_bytes)).enumerate()
        {
            if new_elem.len() != elem_bytes {
                return None;
            }
            if old_elem != new_elem {
                let index = Expr::bitvec_const(k as u128, index_width);
                rebuilt = rebuilt.store(index, concat_le(new_elem)?);
            }
        }
        Some(rebuilt)
    }

    /// The allocation obligation of a CHECKED pointer offset: `base + count *
    /// size` must stay inside the object `base` points into, one-past-the-end
    /// included (Kani `offset` model: `same_allocation(orig, new)`).
    ///
    /// The numeric wrap checks (`emit_offset_overflow_check`) never implied
    /// this: `arr.as_ptr().add(1).sub(2)` on `[i32; 4]` lands four bytes below
    /// the array without wrapping, and printed VERIFICATION:- SUCCESSFUL
    /// (dual `offs52_dual_f_chain_underflow.rs`).
    ///
    /// Decided only where the object is structural: the base peels to a
    /// constant displacement from a slice view that starts at an address-taken
    /// local AND covers all of it (a shorter view would reject legal offsets
    /// that stay inside the local). A base already outside that object came
    /// from arithmetic this check cannot vouch for, so it abstains. The count
    /// stays symbolic; `count == 0` is exempt, as in Kani's model.
    pub(super) fn emit_offset_object_bounds_check(
        &mut self,
        base: &Expr,
        count: &Expr,
        pointee_size: usize,
    ) -> bool {
        if pointee_size == 0 {
            return true;
        }
        if base.sort().bitvec_width() != Some(POINTER_WIDTH) || count.sort().bitvec_width().is_none()
        {
            return false;
        }
        let Some((root, base_offset)) = self.resolve_ptr_root_expr(base, MAX_PTR_PEEL) else {
            return false;
        };
        let Some((local, extent)) = self.slice_view_of_local(&root) else {
            return false;
        };
        let Some(local_ty) = self.local_decl_ty(local.as_ref()) else {
            return false;
        };
        if LayoutOf::new(local_ty).size_of().and_then(|s| u128::try_from(s).ok()) != Some(extent) {
            return false;
        }
        let Ok(base_offset) = u128::try_from(base_offset) else {
            return false;
        };
        if base_offset > extent {
            return false;
        }
        // Signed arithmetic is exact here: `offset_bytes_overflow` owns the
        // `count * size` wrap, and with `base_offset <= extent` a sum that
        // wraps can only wrap negative, which is outside the object anyway.
        let count = Self::coerce_to_width_typed(count.clone(), POINTER_WIDTH, true);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let size = Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH);
        let delta = Expr::bitvec_const(base_offset, POINTER_WIDTH).bvadd(count.clone().bvmul(size));
        let outside = delta
            .clone()
            .bvslt(zero.clone())
            .or(delta.bvsgt(Expr::bitvec_const(extent, POINTER_WIDTH)));
        let violation = count.eq(zero).not().and(outside);
        self.record_violation_guarded_with_message(
            violation,
            "pointer_bounds_check",
            Some(OFFSET_SAME_ALLOCATION.to_string()),
        );
        true
    }
}
