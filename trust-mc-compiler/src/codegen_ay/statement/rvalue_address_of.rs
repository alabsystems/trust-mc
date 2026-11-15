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

use ay_bindings::{Expr, ExprValue, SortInner};
use rustc_public::mir::{BorrowKind, Place, ProjectionElem, Rvalue};
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

        // Create or reuse stable address symbol (thin data pointer). A field or
        // an element of a local, and the payload of a `Box` local, are placed
        // inside the object they belong to rather than getting a symbol of their
        // own (`derived_place_address`).
        let addr = match self.derived_place_address(place, pointee_ty) {
            Some(addr) => addr,
            None => self.get_or_create_address_symbol(base_name.as_ref(), place, pointee_ty)?,
        };

        if !use_thin {
            // `&*p`, `&mut *p` and `&raw const *p` (the `FakeForPtrMetadata`
            // borrow every bounds check on a `&mut [T]` takes) carry exactly
            // the metadata of `p`. Read `p`'s own value here, before the fat
            // pointer is built from the REFERENT: an array local behind the
            // reference has no length of its own, and the fresh length symbol
            // built for it was unrelated to `p`'s, so `source.len() == 2` and
            // `source[0] = 9` for `let source: &mut [u8] = &mut [1u8, 2]`
            // FAILED with a Genuine counterexample (main 31793ccc3).
            let reborrowed_wide = (place.projection.len() == 1
                && Self::is_wide_pointer_ty(self.body.locals()[place.local].ty))
            .then(|| self.codegen_place(&Place { local: place.local, projection: vec![] }))
            .flatten();
            if let Some(fat) = self.try_build_fat_pointer(
                base_name.as_ref(),
                &addr,
                rvalue,
                reborrowed_wide.as_ref(),
            ) {
                return Some(fat);
            }
        }

        Some(addr)
    }

    /// The address of a place INSIDE another object, derived from that object's
    /// address instead of minted as an unrelated symbol:
    ///
    /// - `&s.a`, `&a[i]`, `&s.inner.buf[K]` on a local: the local's own stable
    ///   address (which registers it as a stack object, disjoint from every
    ///   other) plus rustc's field offsets and `index * size_of::<T>()`;
    /// - `&*b`, `&(*b).f` for a `Box` local: the heap allocation the box holds
    ///   (its value after `Box::new`) plus the field offsets.
    ///
    /// Two fields of one struct, two elements of one array, two boxes and a local
    /// beside a box each got a fresh address with only non-null / alignment
    /// constraints, so `ptr::eq(&s.a, &s.b)`, `ptr::eq(&*b1, &*b2)` and
    /// `ptr::eq(&x, &*b)` were satisfiable and `&a[1] as usize == &a[0] as usize
    /// + 1` was not: the safe harnesses FAILED with a Genuine counterexample
    /// (negative/alloc_id_fields_offsets.rs, main 31793ccc3). Cached under the
    /// place's base name like every other address. `None` (the caller keeps the
    /// unrelated symbol) for a place this cannot place: a symbolic index with no
    /// value, an index from the end, a `Downcast`, an unsized or unlaid-out
    /// field, a dereference of anything but a `Box` local.
    pub(super) fn derived_place_address(
        &mut self,
        place: &Place,
        pointee_ty: Option<rustc_public::ty::Ty>,
    ) -> Option<Expr> {
        if place.projection.is_empty() {
            return None;
        }
        let cache_key = self.ssa_base_name(place);
        if let Some(cached) = self.addr_symbols.get(cache_key.as_str()) {
            return Some(cached.clone());
        }
        let root_ty = self.body.locals()[place.local].ty;
        let root_place = Place { local: place.local, projection: vec![] };
        let (mut addr, mut current_ty, rest): (Expr, rustc_public::ty::Ty, &[ProjectionElem]) =
            match place.projection.first()? {
                ProjectionElem::Deref => {
                    // A Box local: its value is the allocation's address.
                    if let Some(pointee) = Self::box_pointee_ty(root_ty) {
                        let ptr = self.codegen_place(&root_place)?;
                        if ptr.sort().bitvec_width() != Some(POINTER_WIDTH) {
                            return None;
                        }
                        (ptr, pointee, &place.projection[1..])
                    } else {
                        // A reference to a CONSTANT ALLOCATION (a `static`, a
                        // promoted constant). Its object is keyed on the
                        // allocation, so two borrows of one static agree and two
                        // statics are disjoint; `&S[i]` is then placed inside it
                        // instead of getting a symbol of its own.
                        let TyKind::RigidTy(
                            RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _),
                        ) = root_ty.kind()
                        else {
                            return None;
                        };
                        let ref_base = self.ssa_base_name(&root_place);
                        if self.ref_pointees.is_poisoned(ref_base.as_str()) {
                            return None;
                        }
                        let pointee_base = self.ref_pointees.get(ref_base.as_str()).cloned()?;
                        let ptr = self.const_pointee_objects.get(pointee_base.as_ref()).copied()?;
                        let naming = self.global_alloc_naming();
                        let target_base = super::global_alloc::global_alloc_address(
                            self.ctx,
                            &ptr.key()?,
                            naming,
                        )?;
                        let base = ptr.address(&target_base, POINTER_WIDTH)?;
                        (base, pointee, &place.projection[1..])
                    }
                }
                _ => {
                    let root_base = self.ssa_base_name(&root_place);
                    let base =
                        self.get_or_create_address_symbol(&root_base, &root_place, Some(root_ty))?;
                    (base, root_ty, &place.projection[..])
                }
            };
        for proj in rest {
            match proj {
                ProjectionElem::Field(field_idx, field_ty) => {
                    let offset = LayoutOf::new(current_ty).field_offset(*field_idx)?;
                    if offset > 0 {
                        addr = addr.bvadd(Expr::bitvec_const(offset as u128, POINTER_WIDTH));
                    }
                    current_ty = *field_ty;
                }
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                    let elem_ty = match current_ty.kind() {
                        TyKind::RigidTy(RigidTy::Array(elem, _)) => elem,
                        _ => return None, // external enum: TyKind (a slice has no static layout here)
                    };
                    let elem_size = LayoutOf::new(elem_ty).size_of()?;
                    let idx = self.projection_index_value(proj, POINTER_WIDTH)?;
                    if elem_size > 0 {
                        addr = addr.bvadd(
                            idx.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH)),
                        );
                    }
                    current_ty = elem_ty;
                }
                _ => return None, // external enum: ProjectionElem (Downcast, Deref, Subslice, ...)
            }
        }
        let _ = pointee_ty;
        self.addr_symbols.insert(cache_key.into(), addr.clone());
        debug!(?place, "addr_of_place: derived the address from the enclosing object");
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
        if let Some(cached_addr) = self.addr_symbols.get(base_name).cloned() {
            debug!("addr_of_place: reusing cached address for {} (stable aliasing)", base_name);
            self.revalidate_alloc_view(&cached_addr, place, base_name);
            return Some(cached_addr);
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
                    // A whole local is its own object: keep it off heap objects
                    // and other stack objects. A field or a place under a
                    // dereference gets its own unrelated symbol here (it lies
                    // inside another object), so separating it would be false.
                    if place.projection.is_empty() {
                        self.ctx.register_stack_object(addr.clone(), size as u64);
                    }
                }
            }
        }

        // Name the allocation this symbol points into, for the exact
        // same-allocation obligation of pointer offsets (alloc_view.rs).
        self.register_alloc_view(&addr, place);

        // The address of a PROJECTED place (`&a[3]`, `&s.f`) is a pointer into
        // its root local, and pointer arithmetic from it reads the root's other
        // bytes. Only the projected value was stored below, so
        // `(&a[3] as *const i32).sub(1)` read an unconstrained byte of `memory`
        // and `assert_eq!(*before, 2)` failed certified Genuine
        // (kani/PointerOffset/offset_sub.rs). Store the whole root at its base
        // first, when the view is known; the projected store below then writes
        // the same bytes again.
        self.materialize_root_of_projected_view(&addr, place);

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
                    match pointee_ty {
                        Some(ty) => self.store_typed_value_to_memory(addr.clone(), local_value, ty),
                        None => self.ctx.store_memory_bytes(addr.clone(), local_value),
                    }
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
    ///
    /// `reborrowed_wide` is the value of the wide pointer `p` when the borrowed
    /// place is exactly `*p`; its metadata is the result's metadata.
    fn try_build_fat_pointer(
        &mut self,
        base_name: &str,
        addr: &Expr,
        rvalue: &Rvalue,
        reborrowed_wide: Option<&Expr>,
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
        // Prefer the REAL length over a fabricated one. When the pointee's env
        // value resolves to a constructor of this same fat sort — a `&str`
        // literal, a slice the caller already holds — its `fld_len` is the true
        // metadata, and a slice's length cannot change through a reference, so
        // a length snapshot cannot go stale. A fresh unconstrained variable
        // here is what made every fat-pointer view's extent unknowable: the
        // bounds check could never fire through `as_ptr` on a `&str`, and the
        // solver was free to pick any length at all.
        //
        // The value's DATA array is reused only for a SHARED borrow. While a
        // `&T` lives, Rust's aliasing rules forbid every write to the pointee
        // through any alias, so a data snapshot taken here cannot go stale for
        // the reads this pointer can perform. Through a `&mut` the snapshot CAN
        // go stale — later writes through the reference would not update it,
        // and a stale concrete array proves assertions about overwritten
        // values, which is a false-proof shape — so `&mut` keeps the
        // fabricated over-approximating array.
        let is_shared_borrow = matches!(
            rvalue,
            Rvalue::Ref(_, BorrowKind::Shared, _)
        ) || matches!(
            ref_ty.kind(),
            TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Not))
        );
        let (real_len, real_data) = self
            .env_lookup(base_name)
            .cloned()
            .map(|v| self.follow_ssa(&v, 64))
            .and_then(|v| match v.value() {
                ExprValue::DatatypeConstructor { args, .. } if *v.sort() == fat_sort => {
                    let fields = &sort_ref.datatype_sort()?.constructors.first()?.fields;
                    let len_idx = fields.iter().position(|f| f.name == "fld_len")?;
                    let len = args.get(len_idx)?;
                    let len_ok = (*len.sort() == meta_sort).then(|| len.clone());
                    let data_ok = if is_shared_borrow {
                        fields
                            .iter()
                            .position(|f| f.name == "fld_data")
                            .and_then(|i| args.get(i))
                            .cloned()
                    } else {
                        None
                    };
                    Some((len_ok, data_ok))
                }
                _ => None,
            })
            .unwrap_or((None, None));
        // A reborrow of a wide pointer keeps that pointer's metadata exactly:
        // take it from a constructor value (the fat pointer an unsize cast or
        // `&str` literal built) or select it off any other fat-sorted value.
        // Only a value of this same fat sort is read, so `fld_len` means the
        // same thing on both sides.
        let reborrowed_len = reborrowed_wide
            .map(|w| self.follow_ssa(w, 64))
            .filter(|w| *w.sort() == fat_sort)
            .and_then(|w| {
                let fields = &sort_ref.datatype_sort()?.constructors.first()?.fields;
                let len_idx = fields.iter().position(|f| f.name == "fld_len")?;
                let len = match w.value() {
                    ExprValue::DatatypeConstructor { args, .. } => args.get(len_idx)?.clone(),
                    _ => super::extract_fat_ptr_metadata(&w)?,
                };
                (*len.sort() == meta_sort).then_some(len)
            });
        let meta = if let Some(len) = real_len.or(reborrowed_len) {
            len
        } else if let Some(cached_meta) = self.addr_metadata_symbols.get(base_name) {
            cached_meta.clone()
        } else {
            let meta_name = crate::codegen_ay::names::meta_name(base_name);
            let meta_var = self.ctx.declare_var(&meta_name, meta_sort);
            // A fabricated length (or vtable) for a view whose real metadata
            // is not in scope: a stand-in the program did not produce, so a
            // counterexample that reads it must not be certified Genuine
            // (bmc_fresh_value_certificate_dual.rs: `s.len() == 3` on `&mut a`).
            self.ctx.bmc_sound_havoc("fat_ptr_metadata");
            self.addr_metadata_symbols.insert(base_name.into(), meta_var.clone());
            meta_var
        };
        let mut args = vec![self.coerce_to_ptr_width(addr.clone()), meta];
        if let Some(data_field) = cons.fields.get(2) {
            let real = real_data.filter(|d| *d.sort() == data_field.sort);
            let data = if let Some(real) = real {
                real
            } else if data_field.sort.array_sort().is_some() {
                // A fresh ARRAY. `const_array(one fresh element)` made every
                // element of the view EQUAL — `"123".as_ptr()` could not read
                // '1' then '2', and `assert!(s[0] == s[1])` held for any slice:
                // an under-approximation, not a havoc.
                let default_name = self.ctx.fresh_name("slice_default");
                self.ctx.bmc_sound_havoc("fat_ptr_slice_data");
                self.ctx.declare_var(&default_name, data_field.sort.clone())
            } else {
                let fresh_name = self.ctx.fresh_name("fat_ptr_field");
                self.ctx.bmc_sound_havoc("fat_ptr_field");
                self.ctx.declare_var(&fresh_name, data_field.sort.clone())
            };
            args.push(data);
        }

        Some(Expr::datatype_constructor(&*dt.name, &*cons.name, args, fat_sort))
    }
}
