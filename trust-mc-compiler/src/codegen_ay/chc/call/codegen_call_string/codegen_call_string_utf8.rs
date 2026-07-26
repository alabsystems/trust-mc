// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! UTF-8-specific string call helpers.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::Operand;
use tracing::debug;

use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::super::codegen_call_misc::CallMisc;
use super::ChcCtx;

pub(in crate::codegen_ay::chc) struct ConcreteByteSlice {
    pub(in crate::codegen_ay::chc) ptr: Expr,
    pub(in crate::codegen_ay::chc) data: Expr,
    pub(in crate::codegen_ay::chc) len: Expr,
    pub(in crate::codegen_ay::chc) offset: Expr,
    pub(in crate::codegen_ay::chc) bytes: Vec<u8>,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn try_resolve_recorded_concrete_slice_local(
        &self,
        local: usize,
    ) -> Option<ConcreteByteSlice> {
        let data = self.ref_resolution.const_ref_values.get(&local)?.clone();
        let len = self.ref_resolution.subslice_len.get(&local)?.clone();
        let len_usize = Self::extract_const_usize_from_expr_utf8(&len)?;
        if len_usize > 256 {
            return None;
        }
        let offset = self
            .ref_resolution
            .subslice_offset
            .get(&local)
            .cloned()
            .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));
        let ptr = self
            .ref_resolution
            .const_ref_slice_views
            .get(&local)
            .and_then(Self::extract_slice_ptr)?;
        let bytes = Self::try_extract_raw_bytes_from_backing_utf8(&data, &offset, len_usize)?;
        Some(ConcreteByteSlice { ptr, data, len, offset, bytes })
    }

    pub(in crate::codegen_ay::chc) fn try_resolve_concrete_str_slice_arg(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<ConcreteByteSlice> {
        let arg = args.first()?;
        let backing = self.resolve_string_backing(arg, modified_locals)?;
        let ptr = self.resolve_byte_slice_ptr(arg, modified_locals)?;
        let len = Self::extract_const_usize_from_expr_utf8(&backing.len)?;
        if len > 256 {
            return None;
        }
        let bytes =
            Self::try_extract_raw_bytes_from_backing_utf8(&backing.data, &backing.offset, len)?;
        Some(ConcreteByteSlice {
            ptr,
            data: backing.data,
            len: backing.len,
            offset: backing.offset,
            bytes,
        })
    }

    pub(in crate::codegen_ay::chc) fn try_resolve_concrete_byte_slice_arg(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<ConcreteByteSlice> {
        let arg = args.first()?;

        // Path 1: Try to resolve from tracked string/slice backing (runtime data).
        if let Some(backing) = self.resolve_byte_slice_backing(arg, modified_locals) {
            let len = Self::extract_const_usize_from_expr_utf8(&backing.len)?;
            if len <= 256 {
                if let Some(bytes) = Self::try_extract_raw_bytes_from_backing_utf8(
                    &backing.data,
                    &backing.offset,
                    len,
                ) {
                    return Some(ConcreteByteSlice {
                        ptr: backing.ptr,
                        data: backing.data,
                        len: backing.len,
                        offset: backing.offset,
                        bytes,
                    });
                }
            }
        }

        // Path 2: Try to resolve from const allocation (promoted byte slice).
        // For `&[u8]` args sourced from const literals like `&[65u8, 122u8]`,
        // the data lives in a promoted const allocation. The ref_resolution
        // tables have a BV pointer (not the array data), so we trace the MIR
        // back to the const allocation and read bytes directly.
        self.try_resolve_const_byte_slice_arg(arg)
    }

    /// Resolve a `&[u8]` argument from a const allocation.
    fn try_resolve_const_byte_slice_arg(&self, arg: &Operand) -> Option<ConcreteByteSlice> {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else { return None };
        if !place.projection.is_empty() {
            return None;
        }
        let arg_local = place.local;

        // Check subslice_len — if we know the length, the arg likely came from a const.
        let len_expr = self.ref_resolution.subslice_len.get(&arg_local)?;
        let len = Self::extract_const_usize_from_expr_utf8(len_expr)?;
        if len > 256 {
            return None;
        }

        // Trace back through MIR Copy/Move/Cast/Ref chains to find a const.
        let bytes = self.extract_const_bytes_for_local(arg_local, len)?;

        // Build the data array expression from the concrete bytes.
        let data = bytes.iter().enumerate().fold(
            Expr::const_array(Sort::bitvec(POINTER_WIDTH), Expr::bitvec_const(0u64, 8)),
            |acc, (idx, &byte)| {
                acc.store(
                    Expr::bitvec_const(idx as u64, POINTER_WIDTH),
                    Expr::bitvec_const(byte as u64, 8),
                )
            },
        );
        let ptr = self
            .ref_resolution
            .const_ref_values
            .get(&arg_local)
            .cloned()
            .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));
        let len_bv = Expr::bitvec_const(len as u64, POINTER_WIDTH);
        let offset = Expr::bitvec_const(0u64, POINTER_WIDTH);

        debug!(arg_local, len, "StrFromUtf8: resolved const byte slice");
        Some(ConcreteByteSlice { ptr, data, len: len_bv, offset, bytes })
    }

    /// Extract raw bytes from a const allocation for a local.
    fn extract_const_bytes_for_local(&self, local: usize, expected_len: usize) -> Option<Vec<u8>> {
        use rustc_public::mir::{Rvalue, StatementKind};

        let mut current = local;
        for _ in 0..8 {
            let mut found_source = false;
            for bb_data in &self.body.blocks {
                for stmt in &bb_data.statements {
                    let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                    if lhs.local != current {
                        continue;
                    }
                    match rhs {
                        Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                        | Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _)
                            if src.projection.is_empty() =>
                        {
                            current = src.local;
                            found_source = true;
                            break;
                        }
                        Rvalue::Use(Operand::Constant(const_op)) => {
                            return Self::bytes_from_mir_const(&const_op.const_, expected_len);
                        }
                        Rvalue::Ref(_, _, ref_place) if ref_place.projection.is_empty() => {
                            current = ref_place.local;
                            found_source = true;
                            break;
                        }
                        _ => {}
                    }
                }
                if found_source {
                    break;
                }
            }
            if !found_source {
                break;
            }
        }
        None
    }

    /// Extract raw bytes from a MIR constant allocation.
    fn bytes_from_mir_const(
        mir_const: &rustc_public::ty::MirConst,
        expected_len: usize,
    ) -> Option<Vec<u8>> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::ty::{ConstantKind, TyConstKind};

        let alloc = match mir_const.kind() {
            ConstantKind::Allocated(alloc) => alloc,
            ConstantKind::Ty(ty_const) => match ty_const.kind() {
                TyConstKind::Value(_ty, alloc) => alloc,
                _ => return None,
            },
            _ => return None,
        };

        // Direct: allocation bytes are the data (e.g., [u8; N] literal).
        if alloc.bytes.len() >= expected_len {
            let bytes: Vec<u8> =
                alloc.bytes.iter().take(expected_len).map(|opt| opt.unwrap_or(0)).collect();
            return Some(bytes);
        }

        // Indirect: follow provenance to the inner allocation.
        let alloc_id = alloc.provenance.ptrs.first()?.1.0;
        let GlobalAlloc::Memory(inner_alloc) = GlobalAlloc::from(alloc_id) else {
            return None;
        };
        if inner_alloc.bytes.len() >= expected_len {
            let bytes: Vec<u8> =
                inner_alloc.bytes.iter().take(expected_len).map(|opt| opt.unwrap_or(0)).collect();
            return Some(bytes);
        }

        None
    }

    pub(in crate::codegen_ay::chc) fn build_slice_value_for_sort(
        &self,
        slice: &ConcreteByteSlice,
        target_sort: &Sort,
    ) -> Option<Expr> {
        if target_sort.is_array() {
            return Some(slice.data.clone());
        }

        if target_sort.is_bitvec() {
            let target_width = target_sort.bitvec_width()?;
            // BV128 fat-pointer target (&str / &[T] payloads): concat(len, ptr)
            // so the length metadata survives instead of zero-extending the
            // thin pointer (which would encode len = 0).
            if target_width == 2 * POINTER_WIDTH {
                let ptr = coerce_bitvec_width_safe(
                    slice.ptr.clone(),
                    POINTER_WIDTH,
                    SignExtension::ZeroExtend,
                );
                let len = coerce_bitvec_width_safe(
                    slice.len.clone(),
                    POINTER_WIDTH,
                    SignExtension::ZeroExtend,
                );
                return Some(len.concat(ptr));
            }
            let ptr = if slice.ptr.sort().bitvec_width() == Some(target_width) {
                slice.ptr.clone()
            } else {
                coerce_bitvec_width_safe(slice.ptr.clone(), target_width, SignExtension::ZeroExtend)
            };
            return Some(ptr);
        }

        let dt = target_sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        let fields: Option<Vec<Expr>> = ctor
            .fields
            .iter()
            .map(|field| match field.name.as_str() {
                "fld_ptr" | "ptr" => Some(slice.ptr.clone()),
                "fld_len" | "len" => Some(slice.len.clone()),
                "fld_data" | "data" => Some(slice.data.clone()),
                _ => None,
            })
            .collect();
        Some(Expr::datatype_constructor(&dt.name, &ctor.name, fields?, target_sort.clone()))
    }

    pub(in crate::codegen_ay::chc) fn record_slice_backing_local(
        &mut self,
        local: usize,
        slice: &ConcreteByteSlice,
    ) {
        self.ref_resolution.const_ref_values.insert(local, slice.data.clone());
        self.ref_resolution.subslice_len.insert(local, slice.len.clone());
        if Self::extract_const_usize_from_expr_utf8(&slice.offset) == Some(0) {
            self.ref_resolution.subslice_offset.remove(&local);
        } else {
            self.ref_resolution.subslice_offset.insert(local, slice.offset.clone());
        }

        let Some(data_sort) = slice.data.sort().array_sort() else {
            return;
        };
        let elem_sort = data_sort.element_sort.clone();
        let slice_name = names::slice_sort_name(&names::sort_short_name(&elem_sort));
        let ctor_name = names::cons_name(&slice_name);
        let slice_sort = struct_sort(
            slice_name.clone(),
            [
                ("fld_ptr", ptr_sort()),
                ("fld_len", ptr_sort()),
                ("fld_data", slice.data.sort().clone()),
            ],
        );
        let slice_view = Expr::datatype_constructor(
            slice_name,
            ctor_name,
            vec![slice.ptr.clone(), slice.len.clone(), slice.data.clone()],
            slice_sort,
        );
        self.ref_resolution.const_ref_slice_views.insert(local, slice_view);
    }

    fn resolve_byte_slice_backing(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<ConcreteByteSlice> {
        let backing = self.resolve_string_backing(arg, modified_locals)?;
        let ptr = self.resolve_byte_slice_ptr(arg, modified_locals)?;
        Some(ConcreteByteSlice {
            ptr,
            data: backing.data,
            len: backing.len,
            offset: backing.offset,
            bytes: Vec::new(),
        })
    }

    fn resolve_byte_slice_ptr(
        &mut self,
        arg: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if let Some(expr) = self.translate_operand_with_modified(arg, modified_locals)
            && let Some(ptr) = Self::extract_slice_ptr(&expr)
        {
            return Some(ptr);
        }

        if let Operand::Copy(place) | Operand::Move(place) = arg
            && place.projection.is_empty()
        {
            let resolved = self.resolve_provenance_local(place.local);
            if let Some(slice_view) = self.ref_resolution.const_ref_slice_views.get(&resolved)
                && let Some(ptr) = Self::extract_slice_ptr(slice_view)
            {
                return Some(ptr);
            }

            let local_expr = if self.flatten.flattened_local_field_count.contains_key(&resolved) {
                self.reconstruct_flattened_root(resolved, modified_locals)
            } else {
                self.try_resolve_local_expr(resolved, modified_locals)
            };
            if let Some(expr) = local_expr
                && let Some(ptr) = Self::extract_slice_ptr(&expr)
            {
                return Some(ptr);
            }
        }

        self.resolve_ref_or_const_referent(arg, modified_locals)
            .and_then(|expr| Self::extract_slice_ptr(&expr))
    }

    fn extract_slice_ptr(expr: &Expr) -> Option<Expr> {
        if expr.sort().is_bitvec() {
            return Some(expr.clone());
        }

        let dt_name = expr.sort().datatype_name()?.to_owned();
        let ptr_sort = Self::get_dt_field_sort(expr, "fld_ptr")?;
        Some(expr.clone().field_select(&dt_name, "fld_ptr", ptr_sort))
    }

    pub(crate) fn extract_const_usize_from_expr_utf8(expr: &Expr) -> Option<usize> {
        if let ExprValue::BitVecConst { value, .. } = expr.value() {
            u64::try_from(value).ok().map(|v| v as usize)
        } else {
            None
        }
    }

    pub(crate) fn try_extract_raw_bytes_from_backing_utf8(
        data: &Expr,
        offset: &Expr,
        len: usize,
    ) -> Option<Vec<u8>> {
        let base_offset = Self::extract_const_usize_from_expr_utf8(offset).unwrap_or(0);
        let mut bytes = vec![0u8; len];
        let mut found = vec![false; len];
        let mut current = data;
        loop {
            match current.value() {
                ExprValue::Store { array, index, value } => {
                    if let ExprValue::BitVecConst { value: idx_val, .. } = index.value()
                        && let ExprValue::BitVecConst { value: byte_val, .. } = value.value()
                    {
                        if let (Ok(idx), Ok(byte)) =
                            (usize::try_from(idx_val.clone()), u8::try_from(byte_val.clone()))
                        {
                            if idx >= base_offset && idx < base_offset + len {
                                let pos = idx - base_offset;
                                if !found[pos] {
                                    bytes[pos] = byte;
                                    found[pos] = true;
                                }
                            }
                        }
                    }
                    current = array;
                }
                ExprValue::ConstArray { value, .. } => {
                    if let ExprValue::BitVecConst { value: byte_val, .. } = value.value()
                        && let Ok(byte) = u8::try_from(byte_val.clone())
                    {
                        for (idx, seen) in found.iter().enumerate() {
                            if !seen {
                                bytes[idx] = byte;
                            }
                        }
                    }
                    break;
                }
                ExprValue::Var { .. } => {
                    if found.iter().any(|seen| !seen) {
                        return None;
                    }
                    break;
                }
                _ => return None,
            }
        }
        Some(bytes)
    }
}
