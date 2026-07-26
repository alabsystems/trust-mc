// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//! Address-of / reference codegen for AY.
//!
//! Extracted from `rvalue.rs` per #2246 to keep each file single-responsibility.
//! Handles `Rvalue::Ref` and `Rvalue::AddressOf` translation: raw pointer field
//! offset computation, ref_pointees resolution, address symbol creation with
//! validity constraints (non-null, alignment, wrap-around), memory stores for
//! stack locals, and fat pointer construction.

use std::sync::Arc;

use ay_bindings::{Expr, SortInner};
use rustc_public::mir::{Place, ProjectionElem, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Translate `Rvalue::Ref` or `Rvalue::AddressOf` into a AY pointer expression.
    ///
    /// Creates a symbolic address with validity constraints.
    /// Stack locals always have valid, non-null, aligned addresses (#761).
    ///
    /// #1124: Uses stable address symbols keyed by base name (not SSA version)
    /// so the same place always maps to the same address symbol across blocks.
    pub(super) fn codegen_address_of(&mut self, place: &Place, rvalue: &Rvalue) -> Option<Expr> {
        let base_name: Arc<str> = if let Some(ProjectionElem::Deref) = place.projection.first() {
            // Place is *ref - look up what the reference points to
            let ref_base = self.ssa_base_name_for_prefix(place, 0);
            let local_ty = self.body.locals()[place.local].ty;

            // #1224: Check for raw pointer field offset FIRST, before ref_pointees.
            if place.projection.len() > 1
                && let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = local_ty.kind()
                && let Some(result) = self.codegen_raw_ptr_field_offset(place, pointee_ty)
            {
                return Some(result);
            }

            // Continue with ref_pointees lookup or identity case
            if let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()) {
                debug!(
                    "addr_of_place: resolved *ref through ref_pointees: {} -> {}",
                    ref_base, pointee_base
                );
                Arc::clone(pointee_base)
            } else if place.projection.len() == 1 {
                // Identity case: &*ptr == ptr (for raw pointers)
                if let TyKind::RigidTy(RigidTy::RawPtr(..)) = local_ty.kind() {
                    debug!(
                        "addr_of_place: raw pointer deref identity - returning ptr value for {}",
                        ref_base
                    );
                    let ptr_place = Place { local: place.local, projection: vec![] };
                    if let Some(ptr_expr) = self.codegen_place(&ptr_place) {
                        return Some(ptr_expr);
                    }
                }
                self.ssa_base_name(place).into()
            } else {
                debug!("addr_of_place: *ref pattern but no ref_pointees entry for {}", ref_base);
                self.ssa_base_name(place).into()
            }
        } else {
            self.ssa_base_name(place).into()
        };

        // #1129: Check if we need a fat pointer for unsized types
        let pointee_ty = place.ty(self.body.locals()).into_option();
        let use_thin = if let Some(ty) = pointee_ty.as_ref() {
            Self::use_thin_pointer_for_pointee(*ty)
        } else {
            warn!(
                ?place,
                "addr_of_place: missing pointee type metadata; defaulting to thin-pointer model"
            );
            self.ctx.unsupported_with_fallback(
                "AddressOf pointee type",
                format!(
                    "missing pointee type for {:?}; thin-pointer fallback loses fat-pointer metadata for unsized types",
                    place
                ),
            );
            true
        };

        // Create or reuse stable address symbol (thin data pointer)
        let addr = self.get_or_create_address_symbol(base_name.as_ref(), place, pointee_ty)?;

        if !use_thin
            && let Some(fat) = self.try_build_fat_pointer(base_name.as_ref(), &addr, rvalue)
        {
            return Some(fat);
        }

        Some(addr)
    }

    /// Compute `ptr + offset_of(field)` for `&(*ptr).field` patterns.
    ///
    /// Returns `Some(expr)` if the raw pointer field offset was successfully computed,
    /// `None` if the pattern doesn't match or offset computation failed.
    fn codegen_raw_ptr_field_offset(
        &mut self,
        place: &Place,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let cache_key = self.ssa_base_name(place);
        if let Some(cached) = self.addr_symbols.get(cache_key.as_str()) {
            debug!("#1224: reusing cached raw ptr field address for {:?}", place);
            return Some(cached.clone());
        }
        debug!(
            "#1224: raw ptr field offset path for {:?}, projection: {:?}",
            place.local, place.projection
        );
        let mut current_ty = pointee_ty;
        let mut total_offset: usize = 0;
        let mut all_fields = true;

        for proj in place.projection.iter().skip(1) {
            if let ProjectionElem::Field(field_idx, field_ty) = proj {
                let layout = LayoutOf::new(current_ty);
                if let Some(offset) = layout.field_offset(*field_idx) {
                    total_offset += offset;
                    current_ty = *field_ty;
                } else {
                    debug!(
                        "#1224: Could not compute field offset for {:?} in type {:?}",
                        field_idx, current_ty
                    );
                    all_fields = false;
                    break;
                }
            } else {
                // external enum: ProjectionElem
                debug!("#1224: Unsupported projection {:?} in &(*ptr).field pattern", proj);
                all_fields = false;
                break;
            }
        }

        debug!("#1224: all_fields={}, total_offset={}", all_fields, total_offset);
        if !all_fields {
            return None;
        }

        let ptr_place = Place { local: place.local, projection: vec![] };
        let ptr_expr = self.codegen_place(&ptr_place)?;

        // Assert base pointer is non-null (dereferencing null is UB).
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let ptr_non_null = ptr_expr.clone().eq(zero).not();
        self.assert_guarded(ptr_non_null);

        let result = if total_offset > 0 {
            let offset_expr = Expr::bitvec_const(total_offset as u128, POINTER_WIDTH);
            ptr_expr.bvadd(offset_expr)
        } else {
            ptr_expr
        };
        debug!("#1224: AddressOf(*ptr).field => ptr + {} for {:?}", total_offset, place);
        self.addr_symbols.insert(cache_key.into(), result.clone());
        Some(result)
    }

    /// Create or reuse a stable address symbol for a place, emitting validity constraints.
    fn get_or_create_address_symbol(
        &mut self,
        base_name: &str,
        place: &Place,
        pointee_ty: Option<rustc_public::ty::Ty>,
    ) -> Option<Expr> {
        if let Some(cached_addr) = self.addr_symbols.get(base_name) {
            debug!("addr_of_place: reusing cached address for {} (stable aliasing)", base_name);
            return Some(cached_addr.clone());
        }

        let addr_name = crate::codegen_ay::names::addr_name(base_name);
        let addr = self.ctx.declare_var(&addr_name, ptr_sort());
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);

        self.addr_symbols.insert(base_name.into(), addr.clone());
        debug!("addr_of_place: created stable address {} for {}", addr_name, base_name);

        // #1124: Emit validity constraints UNCONDITIONALLY.
        self.ctx.assert(addr.clone().eq(zero.clone()).not());

        // Alignment + wrap constraints if we know the pointee type.
        if let Some(ty) = pointee_ty {
            let layout = LayoutOf::new(ty);
            if let Some(align) = layout.align_of()
                && align > 1
            {
                let align_mask = Expr::bitvec_const((align - 1) as u128, POINTER_WIDTH);
                self.ctx.assert(addr.clone().bvand(align_mask).eq(zero));
            }

            if layout.is_sized() {
                let size = layout.size_of_head();
                if size > 0 {
                    let ptr_width = POINTER_WIDTH;
                    let max = if ptr_width >= 128 { u128::MAX } else { (1u128 << ptr_width) - 1 };
                    let size_u128 = size as u128;
                    let size_minus_one = size_u128.saturating_sub(1);
                    if size_minus_one <= max {
                        let limit = max - size_minus_one;
                        let limit_expr = Expr::bitvec_const(limit, ptr_width);
                        self.ctx.assert(addr.clone().bvule(limit_expr));
                    }

                    // Part of #4101: Constrain stack address to stay within a
                    // single heap region so raw-pointer dereferences of stack
                    // locals pass the same-allocation (use_after_free) check.
                    self.ctx.heap_constrain_within_region(addr.clone(), size as u64);
                }
            }
        }

        // #1246: Store stack local's value to memory when its address is taken.
        if place.projection.first() != Some(&ProjectionElem::Deref) {
            if let Some(local_value) = self.codegen_place(place) {
                debug!(
                    "#1246: Storing stack local {} to memory at address {}",
                    base_name, addr_name
                );
                let materialized = if let Some(ty) = pointee_ty {
                    self.try_materialize_array_to_memory(&addr, &local_value, ty)
                } else {
                    false
                };
                if !materialized {
                    self.ctx.store_memory_bytes(addr.clone(), local_value);
                }
            } else {
                debug!("#1246: Could not get value for {} to store to memory", base_name);
            }
        }

        Some(addr)
    }

    /// Try to build a fat pointer (data + metadata) for unsized types.
    ///
    /// Slice-like fat pointers may include an extra `fld_data` backing array.
    /// When no precise backing is available at this layer, emit a symbolic
    /// const-array with the correct element sort to preserve constructor shape.
    fn try_build_fat_pointer(
        &mut self,
        base_name: &str,
        addr: &Expr,
        rvalue: &Rvalue,
    ) -> Option<Expr> {
        debug!("addr_of_place: unsized type, creating fat pointer for {}", base_name);
        let ref_ty = rvalue.ty(self.body.locals()).into_option()?;
        let fat_sort = Self::infer_sort_from_ty(ref_ty)?;
        // Clone Sort (O(1) Arc bump) so dt borrows from sort_ref, not fat_sort.
        // This avoids 2 String clones for dt.name and cons.name.
        let sort_ref = fat_sort.clone();
        let SortInner::Datatype(dt) = sort_ref.inner() else {
            return None;
        };
        let cons = dt.constructors.first()?;
        let meta_sort = cons.fields.get(1).map_or_else(ptr_sort, |field| field.sort.clone());
        let meta = if let Some(cached_meta) = self.addr_metadata_symbols.get(base_name) {
            cached_meta.clone()
        } else {
            let meta_name = crate::codegen_ay::names::meta_name(base_name);
            let meta_var = self.ctx.declare_var(&meta_name, meta_sort);
            self.addr_metadata_symbols.insert(base_name.into(), meta_var.clone());
            meta_var
        };
        let mut args = vec![self.coerce_to_ptr_width(addr.clone()), meta];
        if let Some(data_field) = cons.fields.get(2) {
            let data = if let Some(array_sort) = data_field.sort.array_sort() {
                let default_name = self.ctx.fresh_name("slice_default");
                let default_elem =
                    self.ctx.declare_var(&default_name, array_sort.element_sort.clone());
                Expr::const_array(ptr_sort(), default_elem)
            } else {
                let fresh_name = self.ctx.fresh_name("fat_ptr_field");
                self.ctx.declare_var(&fresh_name, data_field.sort.clone())
            };
            args.push(data);
        }

        Some(Expr::datatype_constructor(&*dt.name, &*cons.name, args, fat_sort))
    }
}
