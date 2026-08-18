// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CopyNonOverlapping intrinsic encoding for CHC (#2226, #2306).

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashSet;
use std::sync::Arc;

use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::types::{
    SignExtension, coerce_bitvec_width_safe, coerce_datatype_structural,
};

use super::codegen_ctx::globals::{chc_fresh_name, declare_pending_var};
use super::{ChcCtx, stmt_accumulator::StmtAccumulator};

pub(super) struct CopyDestination {
    pub(super) local_idx: Option<usize>,
    pub(super) pointee_vec_idx: Option<usize>,
    pub(super) constraint_key: usize,
    pub(super) offset: usize,
    pub(super) expr_in: Expr,
    pub(super) out_name: Arc<str>,
    pub(super) out_sort: Sort,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Coerce Bool rvalues to bitvector destinations for statement assignments.
    ///
    /// Returns `Some(bv_expr)` when `rhs_expr` is Bool and `out_sort` is BitVec,
    /// otherwise returns `None` so callers can continue other fallback paths.
    pub(in crate::codegen_ay::chc) fn coerce_bool_to_bitvec_assignment(
        rhs_expr: Expr,
        out_sort: &Sort,
    ) -> Option<Expr> {
        if !rhs_expr.sort().is_bool() {
            return None;
        }
        let out_width = out_sort.bitvec_width()?;
        Some(Expr::ite(
            rhs_expr,
            Expr::bitvec_const(1u64, out_width),
            Expr::bitvec_const(0u64, out_width),
        ))
    }

    /// Coerce a simple assignment RHS to a destination sort.
    ///
    /// Handles:
    /// - same-sort passthrough
    /// - single-field datatype unwrapping when inner sort matches destination
    /// - BV width mismatch coercion
    /// - Bool↔BV assignment coercions
    /// - Int↔BV coercions (for Range Int-lifted state vars, Part of #2875)
    ///
    /// Returns `None` when coercion is not possible.
    pub(in crate::codegen_ay::chc) fn coerce_assignment_rhs_to_sort(
        rhs_expr: Expr,
        out_sort: &Sort,
        signed: Option<bool>,
    ) -> Option<Expr> {
        let rhs_expr =
            crate::codegen_ay::types::unwrap_single_field_datatype_to_sort(&rhs_expr, out_sort)
                .unwrap_or(rhs_expr);

        if rhs_expr.sort() == out_sort {
            return Some(rhs_expr);
        }
        if let (Some(_rhs_width), Some(out_width)) =
            (rhs_expr.sort().bitvec_width(), out_sort.bitvec_width())
        {
            let signed = signed.unwrap_or_else(|| {
                crate::codegen_ay::shared::signedness_fallback_for_cast_or_coerce("assign_coerce")
            });
            return Some(coerce_bitvec_width_safe(
                rhs_expr,
                out_width,
                SignExtension::for_signedness(signed),
            ));
        }
        if let Some(coerced_bool) =
            Self::coerce_bool_to_bitvec_assignment(rhs_expr.clone(), out_sort)
        {
            return Some(coerced_bool);
        }
        if rhs_expr.sort().is_bitvec()
            && out_sort.is_bool()
            && let Some(rhs_width) = rhs_expr.sort().bitvec_width()
        {
            return Some(rhs_expr.ne(Expr::bitvec_const(0u64, rhs_width)));
        }
        // Int→BV: truncate integer to bitvector (Part of #2875).
        // Range state vars are declared as Int for PDR invariant synthesis,
        // but MIR assignments may target BV-typed locals.
        if rhs_expr.sort().is_int()
            && let Some(out_width) = out_sort.bitvec_width()
        {
            return Some(rhs_expr.int2bv(out_width));
        }
        // BV→Int: lift bitvector to integer (Part of #2875).
        // Part of #3055: use signed/unsigned conversion based on source type.
        if rhs_expr.sort().is_bitvec() && out_sort.is_int() {
            return Some(if signed.unwrap_or(true) {
                rhs_expr.bv2int_signed()
            } else {
                rhs_expr.bv2int()
            });
        }
        // Part of #4086: BV→Array coercion for Discriminant→Array sort mismatch.
        // When a MIR local typed as Array (e.g. [i64; 2] from repr(simd)
        // transmute) is also the target of a Discriminant read in another block,
        // wrap the BV value as a constant-valued array so it propagates through
        // subsequent element selections.
        if rhs_expr.sort().is_bitvec()
            && let Some(arr) = out_sort.array_sort()
            && let Some(elem_width) = arr.element_sort.bitvec_width()
        {
            let coerced = coerce_bitvec_width_safe(rhs_expr, elem_width, SignExtension::ZeroExtend);
            return Some(Expr::const_array(arr.index_sort.clone(), coerced));
        }
        // Part of #4181: Bool→Array coercion for coroutine Discriminant→Array sort
        // mismatch. Coroutine drop-glue paths read the discriminant (Bool) and store
        // it into a local whose sort is Array(BV64, BV8) because the coroutine state
        // includes large [u8; N] fields. Convert Bool to BV(elem_width) and wrap as
        // a constant array, consistent with the BV→Array path above.
        if rhs_expr.sort().is_bool()
            && let Some(arr) = out_sort.array_sort()
            && let Some(elem_width) = arr.element_sort.bitvec_width()
        {
            let bv_expr = Expr::ite(
                rhs_expr,
                Expr::bitvec_const(1u64, elem_width),
                Expr::bitvec_const(0u64, elem_width),
            );
            return Some(Expr::const_array(arr.index_sort.clone(), bv_expr));
        }
        // Part of #3159: Dyn_Trait DT → BV coercion.
        // When the RHS is a Dyn_Trait{fld_ptr, fld_vtable} expression and the
        // destination is BV64 (thin pointer), extract the data pointer field.
        // The vtable discriminant is preserved separately in ChcCtx::dyn_vtable_ids.
        // Guard: only extract fld_ptr when the target is narrower than the full
        // DT flatten width. When the target is BV128 (Box<dyn Trait> fat pointer),
        // fall through to the Dyn_Trait-specific concat path below.
        if let Some(out_width) = out_sort.bitvec_width() {
            let rhs_sort_check = rhs_expr.sort().clone();
            if let Some(dt) = rhs_sort_check.datatype_sort() {
                if let Some(cons) = dt.constructors.first() {
                    if cons.fields.iter().any(|f| f.name == "fld_ptr") {
                        let dt_total_width: u32 =
                            cons.fields.iter().filter_map(|f| f.sort.bitvec_width()).sum();
                        // Only extract fld_ptr when the target cannot hold the
                        // full Dyn_Trait (e.g., BV64 target for a 128-bit DT).
                        if out_width < dt_total_width {
                            let ptr_expr = rhs_expr.field_select(
                                &dt.name,
                                "fld_ptr",
                                Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
                            );
                            return Some(coerce_bitvec_width_safe(
                                ptr_expr,
                                out_width,
                                SignExtension::ZeroExtend,
                            ));
                        }
                    }
                }
            }
        }
        // Dyn_Trait DT → BV128 coercion with correct fat-pointer field order.
        // The codebase convention for BV128 dyn fat pointers is
        // [vtable:64 | data_ptr:64] (vtable in upper bits, data pointer in lower).
        // flatten_datatype_to_bitvec produces MSB-first field order which would
        // give [fld_ptr:64 | fld_vtable:64] — the opposite convention.
        // Intercept Dyn_Trait specifically and construct concat(vtable, ptr).
        if let Some(out_width) = out_sort.bitvec_width() {
            if let Some(dt) = rhs_expr.sort().datatype_sort() {
                if let Some(cons) = dt.constructors.first() {
                    let has_ptr = cons.fields.iter().any(|f| f.name == "fld_ptr");
                    let has_vtable = cons.fields.iter().any(|f| f.name == "fld_vtable");
                    if has_ptr
                        && has_vtable
                        && out_width == 2 * crate::codegen_ay::types::POINTER_WIDTH
                    {
                        // Wave 4: the two halves are DECLARED roles — the
                        // fields are literally named `fld_ptr` and `fld_vtable`
                        // — so report them to `PtrRepr` as `(Loc, Val)` and let
                        // it state the `[vtable:upper | ptr:lower]` byte order.
                        // Handing a bare `concat` two same-sorted operands is
                        // the slot-misalign shape: swapping them writes a vtable
                        // id where consumers read a data pointer, silently.
                        let data = Loc::of_address(rhs_expr.clone().field_select(
                            &dt.name,
                            "fld_ptr",
                            Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
                        ));
                        let meta = Val::of_value(rhs_expr.clone().field_select(
                            &dt.name,
                            "fld_vtable",
                            Sort::bitvec(crate::codegen_ay::types::POINTER_WIDTH),
                        ));
                        return PtrRepr::from_declared_roles(data, meta).into_packed();
                    }
                }
            }
        }
        // Part of #4022, Part of #4099: Datatype → BV coercion via flatten.
        // Handles both multi-constructor enums (ControlFlow, Result) and
        // single-constructor multi-field structs being assigned to BV-flattened
        // locals. Uses flatten_datatype_to_bitvec which encodes as
        // [tag:8 | payload:(width-8)] for enums, or concatenated fields for structs.
        // Placed before DT→DT structural coercion because that path takes
        // ownership of rhs_expr and only handles single-constructor DTs.
        if let Some(out_width) = out_sort.bitvec_width() {
            if rhs_expr.sort().is_datatype() {
                if let Some(flattened) =
                    trust_mc_codegen_types::types::flatten_datatype_to_bitvec(&rhs_expr, out_width)
                {
                    return Some(flattened);
                }
            }
        }
        // Part of #4173: BV→DT coercion via unflatten for niche-packed enums
        // and single-constructor structs. Handles BV128 → Option<NonZeroU128>
        // and similar niche-packed types where the BV width matches the payload.
        if rhs_expr.sort().is_bitvec() && out_sort.is_datatype() {
            if let Some(unflattened) =
                trust_mc_codegen_types::types::unflatten_bitvec_to_datatype(&rhs_expr, out_sort)
            {
                return Some(unflattened);
            }
        }
        // Part of #3198: DT→DT structural coercion via shared utility.
        // Handles multi-field single-constructor datatypes (e.g., Box<T>→Box<dyn Trait>).
        let rhs_sort_owned = rhs_expr.sort().clone();
        if let (Some(src_dt), Some(tgt_dt)) =
            (rhs_sort_owned.datatype_sort(), out_sort.datatype_sort())
        {
            if let Some(coerced) = coerce_datatype_structural(
                rhs_expr,
                src_dt,
                tgt_dt,
                out_sort.clone(),
                SignExtension::for_signedness(signed.unwrap_or(false)),
            ) {
                return Some(coerced);
            }
        }
        None
    }

    /// Resolve a CopyNonOverlapping pointer operand to the local it points at.
    ///
    /// This uses ref_targets collected during declaration pass plus any tracked
    /// element offset carried in `subslice_offset`.
    ///
    /// Returns `(target_local, element_offset)`. Only constant non-negative
    /// offsets are supported here; symbolic or negative offsets stay on the
    /// fallback path.
    pub(super) fn resolve_copy_intrinsic_target(
        &self,
        operand: &Operand,
    ) -> Option<(usize, usize)> {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            Operand::Constant(_) => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let target_local =
            self.ref_resolution.ref_targets.get(&place.local).map(|target| target.local)?;
        let offset = match self.ref_resolution.subslice_offset.get(&place.local) {
            Some(expr) => Self::const_usize_from_expr(expr)?,
            None => 0,
        };
        Some((target_local, offset))
    }

    /// Part of #3798: Resolve a copy source operand as an arg-ref pointee.
    ///
    /// When `resolve_copy_intrinsic_target` returns None because the operand is a
    /// function parameter (&T / &mut T) with no ref_targets entry, this function
    /// looks up the parameter's pointee via `ref_arg_pointee_idx` and returns the
    /// current pointee expression. This handles patterns like:
    ///   fn swap(x: &mut T, y: &mut T) { copy_nonoverlapping(x, &mut t, 1); }
    /// where `x` is a parameter reference.
    pub(super) fn resolve_copy_src_arg_ref(&self, operand: &Operand) -> Option<Expr> {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            _ => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let (_pointee_vec_idx, _track_key, pointee_expr) =
            self.resolve_arg_ref_pointee_expr(place.local)?;
        Some(pointee_expr)
    }

    /// Resolve a copy destination through an argument-reference pointee slot.
    ///
    /// This mirrors the arg-ref store path: function parameters of type `&mut T`
    /// have no `ref_targets` entry, so writes must target their auxiliary pointee
    /// state vars instead of a normal MIR local.
    pub(super) fn resolve_copy_dst_arg_ref(
        &self,
        operand: &Operand,
    ) -> Option<(usize, usize, usize, Expr)> {
        let place = match operand {
            Operand::Copy(place) | Operand::Move(place) => place,
            _ => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let (pointee_vec_idx, track_key, pointee_expr) =
            self.resolve_arg_ref_pointee_expr(place.local)?;
        let offset = match self.ref_resolution.subslice_offset.get(&place.local) {
            Some(expr) => Self::const_usize_from_expr(expr)?,
            None => 0,
        };
        Some((pointee_vec_idx, track_key, offset, pointee_expr))
    }

    pub(super) fn resolve_copy_destination(
        &self,
        operand: &Operand,
        modified: &HashSet<usize>,
    ) -> Option<CopyDestination> {
        if let Some((local_idx, offset)) = self.resolve_copy_intrinsic_target(operand) {
            let expr_in = self.local_expr_with_modified(local_idx, modified)?;
            // Part of #3768: graceful fallback instead of panic
            let state_var_idx = self.try_state_idx_for_local(local_idx)?;
            let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(state_var_idx)?;
            return Some(CopyDestination {
                local_idx: Some(local_idx),
                pointee_vec_idx: None,
                constraint_key: local_idx,
                offset,
                expr_in,
                out_name: out_name.clone(),
                out_sort: out_sort.clone(),
            });
        }

        let (pointee_vec_idx, track_key, offset, expr_in) =
            self.resolve_copy_dst_arg_ref(operand)?;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(pointee_vec_idx)?;
        Some(CopyDestination {
            local_idx: None,
            pointee_vec_idx: Some(pointee_vec_idx),
            constraint_key: track_key,
            offset,
            expr_in,
            out_name: out_name.clone(),
            out_sort: out_sort.clone(),
        })
    }

    /// P3-uninit byte-splice: precise value model for constant-size,
    /// offset-0 copies through (possibly punned) pointers into BV-sorted
    /// scalar destinations.
    ///
    /// Models `copy(src as *T, dst as *T, n)` with `nbytes = n * size_of::<T>()`
    /// as a little-endian byte splice on the destination scalar:
    ///
    /// ```text
    /// dst_out = concat(extract(Wd-1, nbytes*8, dst_in), image[nbytes*8-1 : 0])
    /// ```
    ///
    /// where `image` is the source's memory-byte image in the scalar LE
    /// convention (memory byte `k` == bits `[8k+7 : 8k]`), matching how
    /// scalar constants are materialized from allocations
    /// (`alloc.read_uint()`, little-endian target).
    ///
    /// Struct sources are laid out per rustc layout field offsets
    /// (`get_field_offset`); padding / gap bytes are FRESH NONDET bits.
    /// That is exact value semantics — padding content is unspecified —
    /// and the padding's INIT-ness is tracked independently by the
    /// `-Z uninit-checks` shadow-memory instrumentation (`CopyInitState`),
    /// so this path must NOT `record_fallback`.
    ///
    /// Returns `false` when the shape is not covered — the caller keeps
    /// the demoting `copy_destination_self_loop` fallback for everything
    /// else (fail-closed).
    pub(super) fn try_copy_scalar_byte_splice(
        &mut self,
        copy: &rustc_public::mir::CopyNonOverlapping,
        dst: &CopyDestination,
        src_local_idx: usize,
        src_offset: usize,
        src_expr: &Expr,
        const_count: Option<usize>,
        acc: &mut StmtAccumulator<'_>,
    ) -> bool {
        let Some(count) = const_count else { return false };
        // count == 0 is already handled precisely by the caller's identity path.
        if count == 0 || src_offset != 0 || dst.offset != 0 {
            return false;
        }
        // Element type of the copy: the (possibly punned) pointer's pointee.
        let elem_ty = copy.src.ty(self.body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::RawPtr(inner, _))
            | TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => Some(inner),
            _ => None,
        });
        let Some(elem_size) = elem_ty.and_then(|ty| self.get_type_size(ty)).filter(|s| *s > 0)
        else {
            return false;
        };
        let Some(nbytes) = count.checked_mul(elem_size) else { return false };
        let Some(splice_bits) = u32::try_from(nbytes).ok().and_then(|b| b.checked_mul(8)) else {
            return false;
        };
        let Some(dst_width) = dst.out_sort.bitvec_width() else { return false };
        // The full copy must land inside the destination scalar; an
        // out-of-bounds count is a bug for the span checks + fallback path.
        if dst_width % 8 != 0 || splice_bits > dst_width {
            return false;
        }
        let dst_in = dst.expr_in.clone();
        if dst_in.sort() != &dst.out_sort {
            return false;
        }
        // Underlying source type, when src resolved to a real local (the
        // arg-ref sentinel `usize::MAX` carries no type — and without the
        // type the byte-order of the source expression is NOT knowable:
        // scalar locals are LE images of their value, but flattened-struct
        // BV locals are MSB-first field concats. Fail closed).
        let src_ty = (src_local_idx != usize::MAX)
            .then(|| self.body.locals().get(src_local_idx).map(|decl| decl.ty))
            .flatten();
        let Some(src_ty) = src_ty else { return false };
        let src_ty = self.resolve_body_ty(src_ty);
        // Struct sources may be tracked as flattened per-field leaf state
        // vars (#2989) — the local expr is then a single leaf, not the
        // struct. Reconstruct the datatype expression from the leaves so
        // the image is assembled from ALL fields at their layout offsets.
        let image = if Self::pun_image_primitive_ty(src_ty) {
            self.scalar_le_byte_image(src_expr, Some(src_ty), nbytes)
        } else if src_expr.sort().is_datatype() {
            self.scalar_le_byte_image(src_expr, Some(src_ty), nbytes)
        } else if let Some(dt_expr) = self.reconstruct_flattened_root(src_local_idx, acc.modified) {
            self.scalar_le_byte_image(&dt_expr, Some(src_ty), nbytes)
        } else {
            None
        };
        let Some(image) = image else {
            return false;
        };
        let Some(image_width) = image.sort().bitvec_width() else { return false };
        let slice =
            if image_width == splice_bits { image } else { image.extract(splice_bits - 1, 0) };
        let new_dst = if splice_bits == dst_width {
            slice
        } else {
            dst_in.extract(dst_width - 1, splice_bits).concat(slice)
        };

        let out_var = Expr::var(&*dst.out_name, dst.out_sort.clone());
        acc.replace_constraint(dst.constraint_key, out_var.eq(new_dst.clone()));
        self.encode.local_expr_env.insert(dst.constraint_key, new_dst);
        if let Some(local_idx) = dst.local_idx {
            acc.modified.insert(local_idx);
            self.encode.local_signedness.remove(&local_idx);
            // Stale-constant invalidation: subsequent blocks must read the
            // post-splice state variable (Part of #3938 pattern).
            self.encode.invalidate_local_cache(local_idx);
        }
        if let Some(pointee_vec_idx) = dst.pointee_vec_idx {
            self.mark_state_var_modified(pointee_vec_idx);
        }
        tracing::debug!(
            nbytes,
            elem_size,
            count,
            dst_width,
            "CHC: copy encoded as scalar LE byte splice (P3-uninit)"
        );
        true
    }

    /// Build the little-endian memory-byte image of a value expression as a
    /// single BitVec: memory byte `k` == image bits `[8k+7 : 8k]`.
    ///
    /// Covered shapes:
    /// - byte-multiple BitVec scalars (the value IS the LE image),
    /// - Bool (1 byte, 0/1),
    /// - single-constructor struct datatypes with rustc layout: each field's
    ///   image is placed at its layout byte offset; padding / gap bytes are
    ///   fresh nondet BVs (unspecified value). Requires the datatype's field
    ///   list to match the MIR ADT field list 1:1 and each field image to
    ///   fill exactly its layout size (fail-closed `None` otherwise).
    ///
    /// `min_bytes` is the number of low image bytes the caller will consume;
    /// shapes smaller than that return `None`.
    fn scalar_le_byte_image(
        &mut self,
        expr: &Expr,
        ty: Option<rustc_public::ty::Ty>,
        min_bytes: usize,
    ) -> Option<Expr> {
        if let Some(width) = expr.sort().bitvec_width() {
            // A BV value is only a valid LE byte image for PRIMITIVE scalar
            // types (their BV is the integer/bit value; LE target ⇒ byte k is
            // bits [8k+7:8k]). Flattened-struct BV locals concat fields
            // MSB-first and pointer locals carry split obj/off encodings —
            // both are NOT memory images. Fail closed on those.
            let ty = ty?;
            if !Self::pun_image_primitive_ty(ty) {
                return None;
            }
            let size = self.get_type_size(ty)?;
            if u32::try_from(size).ok()?.checked_mul(8)? != width || min_bytes > size {
                return None;
            }
            return Some(expr.clone());
        }
        if expr.sort().is_bool() {
            if min_bytes > 1 {
                return None;
            }
            return Some(Expr::ite(
                expr.clone(),
                Expr::bitvec_const(1u64, 8),
                Expr::bitvec_const(0u64, 8),
            ));
        }

        // Single-constructor struct datatype: per-field layout placement.
        let ty = self.resolve_body_ty(ty?);
        let total_size = self.get_type_size(ty)?;
        if total_size == 0 || min_bytes > total_size {
            return None;
        }
        let dt_sort = expr.sort().clone();
        let dt = dt_sort.datatype_sort()?;
        if dt.constructors.len() != 1 {
            return None;
        }
        let cons_field_count = dt.constructors.first()?.fields.len();
        let TyKind::RigidTy(RigidTy::Adt(adt_def, args)) = ty.kind() else { return None };
        let variants = adt_def.variants();
        if variants.len() != 1 {
            return None;
        }
        let fields = variants.first()?.fields();
        if fields.len() != cons_field_count {
            return None;
        }

        let mut segments: Vec<(usize, usize, Expr)> = Vec::with_capacity(fields.len());
        for (idx, field) in fields.iter().enumerate() {
            let field_ty = field.ty_with_args(&args);
            let field_off = usize::try_from(self.get_field_offset(ty, idx)?).ok()?;
            let field_size = self.get_type_size(field_ty)?;
            if field_size == 0 || field_off.checked_add(field_size)? > total_size {
                return None;
            }
            let field_expr =
                trust_mc_codegen_types::types::datatype_field_select(expr.clone(), 0, idx)?;
            let field_img = self.scalar_le_byte_image(&field_expr, Some(field_ty), field_size)?;
            // The field image must fill exactly its layout footprint —
            // anything else would misplace neighboring bytes.
            if field_img.sort().bitvec_width()? != u32::try_from(field_size).ok()?.checked_mul(8)? {
                return None;
            }
            segments.push((field_off, field_size, field_img));
        }
        segments.sort_by_key(|(off, _, _)| *off);

        // Assemble LSB-first: fields at their offsets, fresh nondet padding
        // for the gaps and the tail.
        let mut parts_lsb_first: Vec<Expr> = Vec::with_capacity(segments.len() * 2 + 1);
        let mut cursor = 0usize;
        for (off, size, img) in segments {
            if off < cursor {
                // Overlapping fields (union-like layout) — not a struct image.
                return None;
            }
            if off > cursor {
                parts_lsb_first.push(Self::fresh_padding_bits((off - cursor) * 8)?);
            }
            parts_lsb_first.push(img);
            cursor = off + size;
        }
        if cursor < total_size {
            parts_lsb_first.push(Self::fresh_padding_bits((total_size - cursor) * 8)?);
        }
        // concat(a, b) puts `a` in the upper bits — fold from the
        // highest-offset part down.
        let mut iter = parts_lsb_first.into_iter().rev();
        let first = iter.next()?;
        Some(iter.fold(first, |acc_img, part| acc_img.concat(part)))
    }

    /// Fresh nondet bits standing for padding bytes' unspecified VALUE.
    /// (Their INIT-ness is tracked by the shadow-memory instrumentation.)
    fn fresh_padding_bits(width_bits: usize) -> Option<Expr> {
        let width = u32::try_from(width_bits).ok()?;
        Some(declare_pending_var(chc_fresh_name("copy_splice_pad"), Sort::bitvec(width)))
    }

    /// Types whose BV expression IS its little-endian memory byte image:
    /// primitive integers/floats/char/bool. Pointers are excluded — their
    /// BV carries the split obj/off provenance encoding, not address bytes.
    fn pun_image_primitive_ty(ty: rustc_public::ty::Ty) -> bool {
        matches!(
            ty.kind(),
            TyKind::RigidTy(RigidTy::Bool)
                | TyKind::RigidTy(RigidTy::Char)
                | TyKind::RigidTy(RigidTy::Int(_))
                | TyKind::RigidTy(RigidTy::Uint(_))
                | TyKind::RigidTy(RigidTy::Float(_))
        )
    }

    pub(super) fn copy_destination_self_loop(
        &mut self,
        dst: &CopyDestination,
        acc: &mut StmtAccumulator<'_>,
    ) {
        self.record_fallback();
        if let Some(local_idx) = dst.local_idx {
            acc.modified.insert(local_idx);
            self.encode.local_expr_env.remove(&local_idx);
            self.encode.local_signedness.remove(&local_idx);
            // Part of #3938: when a copy destination is havoced, the local becomes
            // nondeterministic. Clear any stale constant to prevent subsequent
            // blocks from reading the pre-havoc value.
            self.encode.invalidate_local_cache(local_idx);
            if !self.emit_self_loop_constraint(local_idx, acc) {
                acc.replace_constraint(local_idx, Expr::bool_const(true));
            }
            return;
        }

        let out_var = Expr::var(&*dst.out_name, dst.out_sort.clone());
        acc.replace_constraint(dst.constraint_key, out_var.eq(dst.expr_in.clone()));
        self.encode.local_expr_env.insert(dst.constraint_key, dst.expr_in.clone());
        if let Some(pointee_vec_idx) = dst.pointee_vec_idx {
            self.mark_state_var_modified(pointee_vec_idx);
        }
    }

    /// Read a local's current expression, using output state when already modified.
    pub(in crate::codegen_ay::chc) fn local_expr_with_modified(
        &self,
        local_idx: usize,
        modified: &HashSet<usize>,
    ) -> Option<Expr> {
        // Keep intra-block read-after-write semantics stable by preferring the
        // current expression environment for modified locals.
        if modified.contains(&local_idx)
            && let Some(env_expr) = self.encode.local_expr_env.get(&local_idx)
        {
            return Some(env_expr.clone());
        }

        // Part of #3768: graceful fallback instead of panic
        let vec_idx = self.try_state_idx_for_local(local_idx)?;
        let (name, sort) = if modified.contains(&local_idx) {
            self.state_var_mgr.output_state_vars.get(vec_idx)?
        } else {
            self.state_var_mgr.state_vars.get(vec_idx)?
        };
        Some(Expr::var(&**name, sort.clone()))
    }

    /// Coerce an expression into the requested target sort (bitvec/int only).
    /// Part of #3247: `signed` controls BV coercion and BV→Int conversion.
    pub(in crate::codegen_ay::chc) fn coerce_expr_to_target_sort(
        expr: Expr,
        target: &Sort,
        signed: bool,
    ) -> Option<Expr> {
        if expr.sort() == target {
            return Some(expr);
        }
        if let Some(target_width) = target.bitvec_width() {
            if expr.sort().is_bool() {
                return Some(Expr::ite(
                    expr,
                    Expr::bitvec_const(1u64, target_width),
                    Expr::bitvec_const(0u64, target_width),
                ));
            }
            if expr.sort().is_bitvec() {
                return Some(coerce_bitvec_width_safe(
                    expr,
                    target_width,
                    SignExtension::for_signedness(signed),
                ));
            }
            if expr.sort().is_int() {
                return Some(expr.int2bv(target_width));
            }
            return None;
        }
        if target.is_int() {
            if expr.sort().is_int() {
                return Some(expr);
            }
            if expr.sort().is_bitvec() {
                return Some(if signed { expr.bv2int_signed() } else { expr.bv2int() });
            }
        }
        None
    }

    /// Build `idx < count` guard for bitvector/int index sorts.
    pub(in crate::codegen_ay::chc) fn build_copy_index_guard(
        idx: Expr,
        count: Expr,
    ) -> Option<Expr> {
        if idx.sort().is_bitvec() && count.sort().is_bitvec() {
            return Some(idx.bvult(count));
        }
        if idx.sort().is_int() && count.sort().is_int() {
            return Some(idx.int_lt(count));
        }
        None
    }

    pub(in crate::codegen_ay::chc) fn const_usize_from_expr(expr: &Expr) -> Option<usize> {
        match expr.value() {
            ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok().map(|v| v as usize),
            ExprValue::IntConst(value) => u64::try_from(value).ok().map(|v| v as usize),
            _ => None,
        }
    }

    pub(super) fn shift_copy_index(idx: Expr, offset: usize) -> Option<Expr> {
        if offset == 0 {
            return Some(idx);
        }
        if let Some(width) = idx.sort().bitvec_width() {
            return Some(idx.bvadd(Expr::bitvec_const(offset as u64, width)));
        }
        if idx.sort().is_int() {
            return Some(idx.int_add(Expr::int_const(offset as i64)));
        }
        None
    }
}
