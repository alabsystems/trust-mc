// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Vec view, pointer, and iterator creation operations for AY codegen.
//!
//! Extracted from `vec.rs`. Handles:
//! - View operations: as_slice, as_ptr, as_mut_ptr
//! - Iterator creation: into_iter, iter, iter_mut
//!
//! Part of #1312: Collection stubs implementation.
//! Part of #1611: Vec iterator support.
//! Part of #1751: Vec::iter/iter_mut support.

use super::super::IntoOption;
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::warn;

use super::super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen Vec view, pointer, and iterator creation operations.
    ///
    /// Delegated from `codegen_vec_stub` for view/iter variants.
    pub(in super::super) fn codegen_vec_view_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        _callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{VecAsMutPtr, VecAsPtr, VecAsSlice, VecIntoIter, VecIter, VecIterMut};

        match stub_kind {
            VecAsSlice => {
                // Vec::as_slice(&self) -> &[T]
                // Returns a slice view of the Vec's contents
                // Modeled as returning (ptr, len, data) tuple stored as Slice
                if args.is_empty() {
                    warn!("Vec::as_slice requires 1 arg (self)");
                    return target;
                }

                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1632: Use typed Vec datatype names
                    let ptr = self.vec_field_select_declared(&vec, "fld_ptr", ptr_sort());
                    let len = self.vec_field_select_declared(&vec, "fld_len", ptr_sort());
                    let data = self.extract_vec_data(&vec);
                    // Part of #1632: Derive element sort from data array to compute
                    // typed slice name (e.g. "Slice_bv32") matching slice_sort().
                    let elem_sort = data
                        .sort()
                        .array_sort()
                        .map_or_else(ptr_sort, |arr| arr.element_sort.clone());
                    let elem_short = names::sort_short_name(&elem_sort);
                    let slice_name = names::slice_sort_name(&elem_short);
                    let ctor_name = names::cons_name(&slice_name);
                    let slice_sort = Self::slice_sort(elem_sort);
                    let slice = Expr::datatype_constructor(
                        slice_name,
                        ctor_name,
                        vec![ptr, len, data],
                        slice_sort,
                    );
                    self.assign_value_to_place(destination, slice);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            VecAsPtr => {
                // Vec::as_ptr(&self) -> *const T
                // Returns pointer to the Vec's buffer
                if args.is_empty() {
                    warn!("Vec::as_ptr requires 1 arg (self)");
                    return target;
                }

                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1632: Use typed Vec datatype names
                    let ptr = self.vec_field_select_declared(&vec, "fld_ptr", ptr_sort());
                    self.assign_value_to_place(destination, ptr);
                } else {
                    let name = self.ctx.fresh_name("vec_ptr");
                    let ptr = self.ctx.declare_var(&name, ptr_sort());
                    self.assign_value_to_place(destination, ptr);
                }
                target
            }

            VecAsMutPtr => {
                // Vec::as_mut_ptr(&mut self) -> *mut T
                // Returns mutable pointer to the Vec's buffer
                if args.is_empty() {
                    warn!("Vec::as_mut_ptr requires 1 arg (self)");
                    return target;
                }

                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1632: Use typed Vec datatype names
                    let ptr = self.vec_field_select_declared(&vec, "fld_ptr", ptr_sort());
                    self.assign_value_to_place(destination, ptr);
                } else {
                    let name = self.ctx.fresh_name("vec_mut_ptr");
                    let ptr = self.ctx.declare_var(&name, ptr_sort());
                    self.assign_value_to_place(destination, ptr);
                }
                target
            }

            VecIntoIter => {
                // Vec::into_iter(self) -> VecIntoIter<T>
                // Part of #2912: 6-field model matching MIR IntoIter<T> layout.
                // Rustc inlines next() which accesses fields 0-5 directly.
                if args.is_empty() {
                    warn!("Vec::into_iter requires 1 arg (self)");
                    return target;
                }

                let vec = self.codegen_operand(&args[0]);
                if let Some(vec) = vec {
                    // Extract element type suffix from Vec sort name for correct
                    // VecIntoIter naming (must match sort_inference_adt).
                    let vec_short = names::sort_short_name(vec.sort());
                    let elem_suffix = vec_short.strip_prefix("Vec_").unwrap_or(&vec_short);
                    let iter_sort_name = names::vec_into_iter_sort_name(elem_suffix);

                    // Extract Vec fields for IntoIter initialization.
                    let buf = self.vec_field_select_declared(&vec, "fld_ptr", ptr_sort());
                    let cap = self.vec_field_select_declared(&vec, "fld_cap", ptr_sort());
                    let len = self.vec_field_select_declared(&vec, "fld_len", ptr_sort());

                    // Compute end pointer: buf + len * elem_size_bytes.
                    // Element size derived from Vec's data array element sort.
                    let elem_bytes = self.vec_element_byte_size(&vec);
                    let end = if elem_bytes == 0 {
                        // ZST: end = buf (same pointer, never advances)
                        buf.clone()
                    } else {
                        let size_expr = Expr::bitvec_const(elem_bytes as u128, POINTER_WIDTH);
                        buf.clone().bvadd(len.bvmul(size_expr))
                    };

                    let iter_sort =
                        struct_sort(iter_sort_name.clone(), names::vec_into_iter_bmc_fields());
                    let ctor_name =
                        crate::codegen_ay::names::resolve_ctor_name(&iter_sort, &iter_sort_name);
                    let iter = Expr::datatype_constructor(
                        iter_sort_name,
                        ctor_name,
                        vec![
                            buf.clone(),            // fld_buf: buffer pointer
                            Expr::bool_const(true), // fld_phantom: ZST
                            cap,                    // fld_cap: capacity
                            Expr::bool_const(true), // fld_alloc: ZST
                            buf,                    // fld_ptr: starts at buf
                            end,                    // fld_end: buf + len*elem_size
                        ],
                        iter_sort,
                    );
                    self.assign_value_to_place(destination, iter);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            VecIter | VecIterMut => {
                // Vec::iter(&self) -> Iter<T> (Part of #1751)
                // Vec::iter_mut(&mut self) -> IterMut<T> (Part of #1751)
                // Model Iter/IterMut<T> as (vec: Vec<T>, pos: usize) — CHC-style 2-field model.
                // VecIntoIter uses a 6-field MIR model (Part of #2912); Iter/IterMut keep
                // the abstract model since they aren't inlined by rustc the same way.
                if args.is_empty() {
                    warn!("Vec::iter/iter_mut requires 1 arg (self)");
                    return target;
                }

                // iter/iter_mut take a reference, so get the vec through the reference
                if let Some((_base, vec)) = self.resolve_collection_base(&args[0]) {
                    // SOUNDNESS: when the source is a *bare backing Array* (e.g.
                    // `for &b in &input` where input: [u8; N], or any &[T;N]/&[T] whose
                    // Slice datatype was not materialized), `vec` is a non-datatype
                    // Array with no fld_len. Storing it raw makes IntoIterNext::next
                    // (collections/iter.rs) field-select fld_len off a non-datatype ->
                    // unconstrained `vec_fld_len_fallback_N` -> unbounded iteration ->
                    // AY timeout/INCONCLUSIVE. Wrap it into the length-carrying Slice
                    // datatype the iterator sort already requires (the {fld_vec,fld_pos}
                    // sort decl is unchanged; we only make the stored VALUE honor it).
                    let vec = self.wrap_bare_array_for_iter(vec, &args[0]);
                    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                    let iter_type = if stub_kind == VecIter { "VecIter" } else { "VecIterMut" };
                    let iter_sort_name = {
                        let short = names::sort_short_name(vec.sort());
                        let mut s = String::with_capacity(iter_type.len() + 1 + short.len());
                        s.push_str(iter_type);
                        s.push('_');
                        s.push_str(&short);
                        s
                    };

                    // Create Iter/IterMut<T> sort with (vec, pos) fields
                    let iter_sort = struct_sort(
                        iter_sort_name.clone(),
                        [("fld_vec", vec.sort().clone()), ("fld_pos", ptr_sort())],
                    );
                    let ctor_name =
                        crate::codegen_ay::names::resolve_ctor_name(&iter_sort, &iter_sort_name);
                    let iter = Expr::datatype_constructor(
                        iter_sort_name,
                        ctor_name,
                        vec![vec, zero],
                        iter_sort,
                    );
                    self.assign_value_to_place(destination, iter);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            _other => {
                // partial dispatch: StubKind
                warn!(
                    ?stub_kind,
                    "codegen_vec_view_stub: unexpected stub kind — update vec.rs routing"
                );
                None
            }
        }
    }

    /// Ensure the value stored in an Iter/IterMut `fld_vec` is a length-carrying
    /// datatype (Vec/Slice), not a bare backing `Array`.
    ///
    /// `resolve_collection_base` returns the raw backing `Array(bv64->elem)` when a
    /// slice/array source (`&[T; N]`, `&[T]`) has no materialized Slice/Vec datatype.
    /// `IntoIterNext::next` reads `fld_len`/`fld_data` off `fld_vec`; a bare Array has
    /// neither -> unconstrained `vec_fld_len_fallback_N` -> AY timeout/INCONCLUSIVE.
    ///
    /// This wraps a bare Array into `Slice_<elem>(fld_ptr, fld_len, fld_data)` with a
    /// *constrained* length: the static `[T; N]` length when known (from the reference
    /// operand type), else fat-pointer metadata (`&[T]`), else a declared symbolic
    /// length (still terminates under BMC unroll). Datatype inputs are returned as-is.
    fn wrap_bare_array_for_iter(&mut self, vec: Expr, src: &Operand) -> Expr {
        use ay_bindings::SortInner;

        // Already a Vec/Slice datatype with fld_len -> nothing to do (the common
        // `vec.iter()` path); byte-for-byte unchanged.
        if vec.sort().is_datatype() {
            return vec;
        }
        // Recover the element sort from the bare backing array; if it is not an array
        // we can wrap, leave it for the existing non-datatype guard to handle. Clone
        // the sort (O(1) Arc) so the match doesn't borrow `vec` across `return vec`.
        let sort = vec.sort().clone();
        let elem_sort = match sort.inner() {
            SortInner::Array(arr) => arr.element_sort.clone(),
            _ => return vec,
        };
        // Derive a constrained length: static [T; N] length first (concrete, zero
        // fallbacks for `&[u8; 8]`), then fat-pointer metadata, then a declared symbol.
        let len = match src
            .ty(self.body.locals())
            .into_option()
            .and_then(Self::array_len_from_pointer_ty)
        {
            Some(n) => Expr::bitvec_const(u128::from(n), POINTER_WIDTH),
            None => self.codegen_ptr_metadata(src).unwrap_or_else(|| {
                let name = self.ctx.fresh_name("iter_slice_len");
                self.ctx.declare_var(&name, ptr_sort())
            }),
        };
        // fld_data is exactly the backing Array(ptr, elem); fld_ptr is a symbolic
        // identity pointer (never dereferenced by the iterator model).
        let slice_sort = Self::slice_sort(elem_sort);
        let sort_name = slice_sort.datatype_name().unwrap_or("Slice").to_owned();
        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&slice_sort, &sort_name);
        let ptr = {
            let name = self.ctx.fresh_name("iter_slice_ptr");
            self.ctx.declare_var(&name, ptr_sort())
        };
        Expr::datatype_constructor(sort_name, ctor_name, vec![ptr, len, vec], slice_sort)
    }

    /// Compute the byte size of a Vec's element type from its data array sort.
    ///
    /// Returns the byte width of the element sort (bitvec_width / 8), or 0 for
    /// non-bitvec elements (ZSTs, complex types). Used for pointer arithmetic
    /// in IntoIter initialization (buf + len * elem_size).
    fn vec_element_byte_size(&self, vec: &Expr) -> usize {
        use ay_bindings::SortInner;
        let sort = vec.sort().clone();
        if let SortInner::Datatype(dt) = sort.inner()
            && let Some(data_field) = dt.constructors.first().and_then(|c| c.field("fld_data"))
        {
            // data_field.sort is Array<bv64, ElemSort>
            if let SortInner::Array(arr) = data_field.sort.inner()
                && let Some(width) = arr.element_sort.bitvec_width()
            {
                return (width as usize) / 8;
            }
        }
        0
    }
}
