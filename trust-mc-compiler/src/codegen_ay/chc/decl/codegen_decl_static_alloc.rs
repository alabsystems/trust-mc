// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Allocation-aware readers and sort utilities for static/const decoding.
//! Split from `codegen_decl_static.rs` for file-size compliance (Part of #4196).
//! Contains: provenance-aware readers, `scalar_from_alloc`, `read_composite_from_bytes`,
//! `sort_byte_width`, `sort_alignment`, `sort_default_expr`, pointer resolution helpers.

use rustc_public::mir::alloc::{AllocId, GlobalAlloc};

use super::ChcCtx;
use super::codegen_types::CodegenTypes;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    fn fn_ptr_identity_expr_from_key(key: &str) -> ay_bindings::Expr {
        // Deterministic FNV-1a hash so const-provenance fn pointers get a
        // stable non-zero BV identity without depending on mutable ctx state.
        let mut hash: u64 = 0xcbf29ce484222325;
        for byte in key.as_bytes() {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
        if hash == 0 {
            hash = 1;
        }
        ay_bindings::Expr::bitvec_const(hash as u128, crate::codegen_ay::types::POINTER_WIDTH)
    }

    pub(in crate::codegen_ay::chc) fn fn_ptr_identity_expr_from_alloc_id(
        alloc_id: AllocId,
    ) -> Option<ay_bindings::Expr> {
        let GlobalAlloc::Function(instance) = GlobalAlloc::from(alloc_id) else {
            return None;
        };
        let key = format!("{:?}_{:?}", instance.def, instance.args());
        Some(Self::fn_ptr_identity_expr_from_key(&key))
    }

    pub(in crate::codegen_ay::chc) fn read_scalar_from_allocation(
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
        width: u32,
    ) -> Option<ay_bindings::Expr> {
        if width == crate::codegen_ay::types::POINTER_WIDTH
            && let Some((_, prov)) =
                alloc.provenance.ptrs.iter().find(|(ptr_offset, _)| *ptr_offset == offset)
            && let Some(expr) = Self::fn_ptr_identity_expr_from_alloc_id(prov.0)
        {
            return Some(expr);
        }

        let byte_width = width as usize / 8;
        let mut value: u128 = 0;
        for b in 0..byte_width {
            let byte_val: u8 = alloc.bytes.get(offset + b).copied()?.unwrap_or(0);
            value |= (byte_val as u128) << (b * 8);
        }
        let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
        Some(ay_bindings::Expr::bitvec_const(masked, width))
    }

    /// Like `read_composite_from_bytes` but preserves function provenance.
    pub(in crate::codegen_ay::chc) fn read_composite_from_allocation(
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;

        if sort.is_bool() {
            // A trailing zero-sized field can place a bool leaf past the real
            // bytes (offset >= bytes.len()). Default such an out-of-bytes read
            // to `false` instead of failing the `?` — otherwise the whole
            // composite read bails and the (already-proven) value is spuriously
            // demoted via chc_fallback. Interior in-bounds reads are unchanged.
            let byte_val: u8 = match alloc.bytes.get(offset).copied() {
                Some(b) => b.unwrap_or(0),
                None => 0,
            };
            return Some(Expr::bool_const(byte_val != 0));
        }
        if let Some(width) = sort.bitvec_width() {
            return Self::read_scalar_from_allocation(alloc, offset, width);
        }

        if let Some(arr) = sort.array_sort() {
            let elem_width = Self::sort_byte_width(&arr.element_sort)?;
            if elem_width == 0 {
                return None;
            }
            let remaining = alloc.bytes.len().saturating_sub(offset);
            let array_len = remaining / elem_width;
            if array_len == 0 {
                return None;
            }
            let default_elem = Self::sort_default_expr(&arr.element_sort)?;
            let mut result = Expr::const_array(arr.index_sort.clone(), default_elem);
            let idx_width =
                arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
            for i in 0..array_len {
                let elem_offset = offset + i * elem_width;
                let elem =
                    Self::read_composite_from_allocation(alloc, elem_offset, &arr.element_sort)?;
                let idx = Expr::bitvec_const(i as u128, idx_width);
                result = result.store(idx, elem);
            }
            return Some(result);
        }

        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let mut field_exprs = Vec::with_capacity(ctor.fields.len());
            let mut field_offset = offset;
            for (i, field) in ctor.fields.iter().enumerate() {
                let align = Self::sort_alignment(&field.sort)?;
                field_offset = field_offset.div_ceil(align) * align;
                let field_expr =
                    Self::read_composite_from_allocation(alloc, field_offset, &field.sort)?;
                field_exprs.push(field_expr);
                if i + 1 < ctor.fields.len() {
                    let fw = Self::sort_byte_width(&field.sort)?;
                    field_offset += fw;
                }
            }
            return Some(Expr::datatype_constructor(
                &*dt.name,
                &*ctor.name,
                field_exprs,
                sort.clone(),
            ));
        }

        None
    }

    /// Read a AY expression from allocation + sort (scalar or composite).
    /// Part of #3496 Bug A.
    pub(in crate::codegen_ay::chc) fn scalar_from_alloc(
        alloc: &rustc_public::ty::Allocation,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;

        // Scalar types: use Allocation's built-in readers for whole-allocation values.
        if sort.is_bool() {
            let val = alloc.read_bool().ok()?;
            return Some(Expr::bool_const(val));
        }
        if let Some(width) = sort.bitvec_width() {
            if let Ok(value) = alloc.read_uint() {
                let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
                return Some(Expr::bitvec_const(masked, width));
            }
            // read_uint() errors on ANY uninit byte — which union statics
            // routinely contain (const-eval leaves padding uninit, e.g.
            // `static FOO: Data = Data { a: [0, 1, 0] }` in a 4-byte union).
            // For a provenance-free allocation the byte-wise reader below
            // zero-fills the uninit bytes, matching Kani/CBMC static-image
            // semantics (the zeroed binary image; union_transmute's oracle
            // y == 256 REQUIRES padding == 0). Provenance-bearing failures
            // still bail to the static_init_incomplete demotion.
            if alloc.provenance.ptrs.is_empty() {
                return Self::read_composite_from_bytes(&alloc.bytes, 0, sort);
            }
            return None;
        }
        if sort.is_int() {
            let value = alloc.read_int().ok()?;
            return Some(Expr::int_const(value));
        }

        // Composite types: read from allocation bytes at offsets.
        Self::read_composite_from_bytes(&alloc.bytes, 0, sort)
    }

    /// Read a AY value from raw bytes at a byte offset (recursive decomposition).
    /// Part of #3496 Bug A.
    pub(in crate::codegen_ay::chc) fn read_composite_from_bytes(
        bytes: &[Option<u8>],
        offset: usize,
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;

        if sort.is_bool() {
            // Mirror of read_composite_from_allocation: tolerate a trailing-ZST
            // bool leaf past the real bytes (default false) rather than bailing.
            let byte_val: u8 = match bytes.get(offset).copied() {
                Some(b) => b.unwrap_or(0),
                None => 0,
            };
            return Some(Expr::bool_const(byte_val != 0));
        }
        if let Some(width) = sort.bitvec_width() {
            let byte_width = width as usize / 8;
            let mut value: u128 = 0;
            for b in 0..byte_width {
                let byte_val: u8 = bytes.get(offset + b).copied()?.unwrap_or(0);
                value |= (byte_val as u128) << (b * 8);
            }
            let masked = if width >= 128 { value } else { value & ((1u128 << width) - 1) };
            return Some(Expr::bitvec_const(masked, width));
        }

        // Array: read elements sequentially from bytes.
        if let Some(arr) = sort.array_sort() {
            let elem_width = Self::sort_byte_width(&arr.element_sort)?;
            if elem_width == 0 {
                return None;
            }
            let remaining = bytes.len().saturating_sub(offset);
            let array_len = remaining / elem_width;
            if array_len == 0 {
                return None;
            }
            let default_elem = Self::sort_default_expr(&arr.element_sort)?;
            let mut result = Expr::const_array(arr.index_sort.clone(), default_elem);
            let idx_width =
                arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);
            for i in 0..array_len {
                let elem_offset = offset + i * elem_width;
                let elem = Self::read_composite_from_bytes(bytes, elem_offset, &arr.element_sort)?;
                let idx = Expr::bitvec_const(i as u128, idx_width);
                result = result.store(idx, elem);
            }
            return Some(result);
        }

        // Datatype (single-constructor struct): read fields at computed offsets.
        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let mut field_exprs = Vec::with_capacity(ctor.fields.len());
            let mut field_offset = offset;
            for (i, field) in ctor.fields.iter().enumerate() {
                let align = Self::sort_alignment(&field.sort)?;
                field_offset = field_offset.div_ceil(align) * align;
                let field_expr = Self::read_composite_from_bytes(bytes, field_offset, &field.sort)?;
                field_exprs.push(field_expr);
                // Only advance offset when there are more fields to read.
                // Array sorts have no fixed byte width (abstract maps), so
                // sort_byte_width returns None for them. Part of #3806.
                if i + 1 < ctor.fields.len() {
                    let fw = Self::sort_byte_width(&field.sort)?;
                    field_offset += fw;
                }
            }
            return Some(Expr::datatype_constructor(
                &*dt.name,
                &*ctor.name,
                field_exprs,
                sort.clone(),
            ));
        }

        None
    }

    /// Compute byte width of a AY sort for allocation reading.
    pub(in crate::codegen_ay::chc) fn sort_byte_width(sort: &ay_bindings::Sort) -> Option<usize> {
        if sort.is_bool() {
            return Some(1);
        }
        if let Some(width) = sort.bitvec_width() {
            return Some(width as usize / 8);
        }
        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            if dt.constructors.len() != 1 {
                return None;
            }
            let mut total = 0usize;
            for field in &ctor.fields {
                let align = Self::sort_alignment(&field.sort)?;
                total = total.div_ceil(align) * align;
                total += Self::sort_byte_width(&field.sort)?;
            }
            return Some(total);
        }
        None
    }

    /// Compute alignment of a AY sort in bytes.
    pub(in crate::codegen_ay::chc) fn sort_alignment(sort: &ay_bindings::Sort) -> Option<usize> {
        if sort.is_bool() {
            return Some(1);
        }
        if let Some(width) = sort.bitvec_width() {
            return Some((width as usize / 8).clamp(1, 16));
        }
        // Array: align to element alignment. Part of #3806.
        if let Some(arr) = sort.array_sort() {
            return Self::sort_alignment(&arr.element_sort);
        }
        if let Some(dt) = sort.datatype_sort() {
            let ctor = dt.constructors.first()?;
            let mut max_align = 1usize;
            for field in &ctor.fields {
                max_align = max_align.max(Self::sort_alignment(&field.sort)?);
            }
            return Some(max_align);
        }
        None
    }

    /// Default/zero expression for a sort. Used for const_array base values.
    pub(in crate::codegen_ay::chc) fn sort_default_expr(
        sort: &ay_bindings::Sort,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;
        if sort.is_bool() {
            return Some(Expr::bool_const(false));
        }
        if let Some(width) = sort.bitvec_width() {
            return Some(Expr::bitvec_const(0u64, width));
        }
        if sort.is_int() {
            return Some(Expr::int_const(0));
        }
        None
    }

    pub(in crate::codegen_ay::chc) fn read_array_with_pointer_elements_from_allocation(
        &mut self,
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
        array_sort: &ay_bindings::Sort,
        elem_ty: rustc_public::ty::Ty,
        array_len: usize,
    ) -> Option<ay_bindings::Expr> {
        let arr = array_sort.array_sort()?;
        let elem_byte_width = Self::sort_byte_width(&arr.element_sort)?;
        if elem_byte_width == 0 {
            return None;
        }

        let default_elem = Self::sort_default_expr(&arr.element_sort)?;
        let mut result = ay_bindings::Expr::const_array(arr.index_sort.clone(), default_elem);
        let idx_width =
            arr.index_sort.bitvec_width().unwrap_or(crate::codegen_ay::types::POINTER_WIDTH);

        for i in 0..array_len {
            let elem_offset = offset + i * elem_byte_width;
            let elem_expr = self.read_pointer_like_from_allocation(
                alloc,
                elem_offset,
                &arr.element_sort,
                elem_ty,
            )?;
            let idx = ay_bindings::Expr::bitvec_const(i as u128, idx_width);
            result = result.store(idx, elem_expr);
        }

        Some(result)
    }

    fn read_pointer_like_from_allocation(
        &mut self,
        alloc: &rustc_public::ty::Allocation,
        offset: usize,
        sort: &ay_bindings::Sort,
        rust_ty: rustc_public::ty::Ty,
    ) -> Option<ay_bindings::Expr> {
        use ay_bindings::Expr;
        use rustc_public::ty::{RigidTy, TyKind};

        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _) | RigidTy::RawPtr(pointee_ty, _)) =
            rust_ty.kind()
        else {
            return Self::read_composite_from_allocation(alloc, offset, sort);
        };

        let width = sort.bitvec_width()?;
        let ptr_bytes = (crate::codegen_ay::types::POINTER_WIDTH / 8) as usize;
        let provenance_target = alloc
            .provenance
            .ptrs
            .iter()
            .find(|(ptr_offset, _)| *ptr_offset == offset)
            .map(|(_, prov)| prov.0);

        let data_ptr = if let Some(target_alloc_id) = provenance_target {
            if let Some(fn_ptr) = Self::fn_ptr_identity_expr_from_alloc_id(target_alloc_id) {
                fn_ptr
            } else if let Some((_resolved_id, expr)) =
                self.resolve_static_target_init_expr(target_alloc_id, pointee_ty)
            {
                expr
            } else {
                // Pointee type can't be translated (e.g. `str` is DST). Allocate
                // an address for the target and seed backing memory if possible.
                self.alloc_dst_pointer_fallback(target_alloc_id, pointee_ty).unwrap_or_else(|| {
                    return Self::read_scalar_from_allocation(alloc, offset, width)
                        .unwrap_or_else(|| Expr::bitvec_const(0u64, width));
                })
            }
        } else {
            return Self::read_scalar_from_allocation(alloc, offset, width);
        };

        if width == crate::codegen_ay::types::POINTER_WIDTH {
            return Some(data_ptr);
        }

        if width == 2 * crate::codegen_ay::types::POINTER_WIDTH {
            let metadata = Self::read_scalar_from_allocation(
                alloc,
                offset + ptr_bytes,
                crate::codegen_ay::types::POINTER_WIDTH,
            )?;
            return Some(metadata.concat(data_ptr));
        }

        Self::read_scalar_from_allocation(alloc, offset, width)
    }

    fn seed_static_str_backing_memory(
        &mut self,
        target_alloc_data: &rustc_public::ty::Allocation,
        target_addr: ay_bindings::Expr,
    ) {
        // Elide long strings (panic messages). Same threshold as extract_str_from_const_ref.
        if target_alloc_data.bytes.len() > 64 {
            return;
        }
        let u8_ty = rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8);
        for (idx, byte) in target_alloc_data.bytes.iter().enumerate() {
            let Some(byte) = byte else { continue };
            let addr = Self::static_addr_with_offset(target_addr.clone(), idx as u64);
            self.push_static_memory_init_entry(
                u8_ty,
                ay_bindings::Expr::bitvec_const(*byte as u128, 8),
                addr,
            );
        }
    }

    /// Allocate an address for a DST pointee (e.g. `str`) when
    /// `resolve_static_target_init_expr` fails because `translate_ty` can't
    /// handle the pointee type.
    fn alloc_dst_pointer_fallback(
        &mut self,
        target_alloc_id: AllocId,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<ay_bindings::Expr> {
        let (resolved_id, alloc_data) = self.canonical_static_seed_alloc(target_alloc_id)?;
        if let Some(addr) = self.ref_resolution.static_address_exprs.get(&resolved_id).cloned() {
            return Some(addr);
        }
        let obj_id = self.heap_state.next_alloc_id()?;
        let addr = ay_bindings::Expr::bitvec_const(obj_id as i128, 32)
            .concat(ay_bindings::Expr::bitvec_const(0i128, 32));
        self.ref_resolution.static_address_exprs.insert(resolved_id, addr.clone());
        if matches!(
            pointee_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Str)
        ) {
            self.seed_static_str_backing_memory(&alloc_data, addr.clone());
        }
        Some(addr)
    }

    fn resolve_static_target_init_expr(
        &mut self,
        target_alloc_id: AllocId,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Option<(AllocId, ay_bindings::Expr)> {
        use rustc_public::ty::{RigidTy, TyKind};

        let (resolved_target_alloc_id, target_alloc_data) =
            self.canonical_static_seed_alloc(target_alloc_id)?;

        if let Some(addr) = self.ref_resolution.static_address_exprs.get(&resolved_target_alloc_id)
        {
            return Some((resolved_target_alloc_id, addr.clone()));
        }

        let pointee_sort = Self::translate_ty(pointee_ty)?;
        let obj_id = self.heap_state.next_alloc_id()?;
        let target_addr = ay_bindings::Expr::bitvec_const(obj_id as i128, 32)
            .concat(ay_bindings::Expr::bitvec_const(0i128, 32));

        self.ref_resolution
            .static_address_exprs
            .insert(resolved_target_alloc_id, target_addr.clone());

        if let Some(init_val) =
            self.static_init_from_alloc(&target_alloc_data, &pointee_sort, pointee_ty)
        {
            self.register_static_memory_init_entries(pointee_ty, init_val, target_addr.clone());

            if matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                self.seed_static_str_backing_memory(&target_alloc_data, target_addr.clone());
            }
        }

        Some((resolved_target_alloc_id, target_addr))
    }

    /// Resolve a pointer-typed static's initial value from allocation provenance.
    /// Part of #3496: pointer-typed static provenance resolution.
    pub(in crate::codegen_ay::chc) fn resolve_pointer_static_init(
        &mut self,
        target_alloc_id: AllocId,
        pointee_ty: rustc_public::ty::Ty,
        static_name: &str,
        vec_idx: usize,
    ) -> Option<ay_bindings::Expr> {
        let (resolved_target_alloc_id, target_addr) =
            self.resolve_static_target_init_expr(target_alloc_id, pointee_ty)?;

        tracing::debug!(
            vec_idx,
            static_name = %static_name,
            source_target_alloc_id = ?target_alloc_id,
            ?resolved_target_alloc_id,
            "CHC: resolved pointer static to concrete target address (#3496)"
        );
        Some(target_addr)
    }
}
