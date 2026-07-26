// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Array iterator helpers for Vec iterator stubs.
//!
//! Extracted from stubs_iterators_vec.rs per #4147 (large-file decomposition).
//! Contains: detect_array_inner_iter_next, detect_array_index_range_next,
//! find_parent_array_into_iter_local, translate_array_into_iter_next,
//! translate_array_into_iter_next_core, wrap_bare_array_in_slice.

use std::borrow::Cow;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;
use tracing::debug;

use super::ChcCtx;
use super::types::ptr_sort;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Detects if a function call is an array inner iterator next() call.
    ///
    /// Part of #3984: PolymorphicIter::next and IndexRange::next are called on
    /// inner fields of ArrayIntoIter locals. The receiver is a BV64 heap pointer
    /// (no ref_target mapping), so the standard stub path fails. This detection
    /// allows routing through the parent IntoIter local instead.
    pub(in crate::codegen_ay::chc) fn detect_array_inner_iter_next(&self, func: &Operand) -> bool {
        let Some(path) = self.resolve_callee_path(func) else {
            return false;
        };
        // PolymorphicIter::<[MaybeUninit<T>]>::next — main array iteration path.
        // IMPORTANT: Do NOT match IndexRange::next here. IndexRange::next returns
        // Option<usize> (an index), not Option<T> (an element). The MIR for that
        // path follows IndexRange::next with Option::map to extract the element.
        // Our handler would incorrectly return the element directly, causing
        // sort mismatches when Option::map tries to map the "index" (actually
        // an element) through the element-extraction closure.
        path.contains("PolymorphicIter") && path.ends_with("::next")
    }

    /// Detects if a function call is an IndexRange::next() call on an array iterator.
    ///
    /// Part of #3984: IndexRange::next returns Option<usize> (an index), which the
    /// MIR then feeds through Option::map to extract the actual array element.
    /// We handle IndexRange::next separately from PolymorphicIter::next because
    /// the return type is Option<usize>, not Option<T>.
    pub(in crate::codegen_ay::chc) fn detect_array_index_range_next(&self, func: &Operand) -> bool {
        let Some(path) = self.resolve_callee_path(func) else {
            return false;
        };
        // Match IndexRange::next specifically, only when there's an array IntoIter parent.
        path.contains("IndexRange")
            && path.ends_with("::next")
            && self.find_parent_array_into_iter_local().is_some()
    }

    /// Find the parent ArrayIntoIter local from projection_locals.
    ///
    /// Part of #3984: When PolymorphicIter::next is called, the receiver is a BV64
    /// reference to an inner field. We find the parent IntoIter local which IS in
    /// projection_locals and can be reconstructed from flattened state vars.
    pub(in crate::codegen_ay::chc) fn find_parent_array_into_iter_local(&self) -> Option<usize> {
        use super::codegen_ctx::CollectionProjectionKind;
        self.collections.projection_locals.iter().find_map(|(&local, &kind)| {
            matches!(kind, CollectionProjectionKind::ArrayIntoIter).then_some(local)
        })
    }

    /// Array IntoIter<T, N>::next — resolves receiver via get_collection_arg.
    ///
    /// Part of #3984: Tries direct receiver resolution first. If that fails
    /// (returns non-Datatype BV64), returns None so the caller can try the
    /// parent-local reconstruction path.
    pub(in crate::codegen_ay::chc) fn translate_array_into_iter_next(
        &mut self,
        ctx: &super::StubTranslateArgs<'_>,
    ) -> Option<super::CollectionCallResult> {
        let iter_arg = ctx.args.first()?;
        let iter = self.get_collection_arg(iter_arg, ctx.modified_locals)?;
        if !iter.sort().is_datatype() {
            return None;
        }
        self.translate_array_into_iter_next_core(iter)
    }

    /// Core array IntoIter::next logic operating on a resolved iterator expression.
    ///
    /// Part of #3984: Extracted from translate_array_into_iter_next so it can be
    /// called from both the direct-receiver path and the parent-local reconstruction
    /// path (for PolymorphicIter::next / IndexRange::next inner-field calls).
    ///
    /// Supports two layouts:
    /// - IntoIter { fld_inner: PolymorphicIter { fld_alive, fld_data } }
    /// - PolymorphicIter { fld_alive, fld_data } (direct)
    pub(in crate::codegen_ay::chc) fn translate_array_into_iter_next_core(
        &mut self,
        iter: Expr,
    ) -> Option<super::CollectionCallResult> {
        let sort_ref = iter.sort().clone();
        let dt = sort_ref.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        // Navigate to alive/data level.
        let (poly_expr, poly_dt, poly_ctor, wrap_fn): (Expr, _, _, Box<dyn FnOnce(Expr) -> Expr>) =
            if let Some(inner_f) = ctor.fields.iter().find(|f| f.name == "fld_inner") {
                let inner = iter.clone().field_select(&dt.name, "fld_inner", inner_f.sort.clone());
                let idt = inner_f.sort.datatype_sort()?;
                let ic = idt.constructors.first()?;
                let dt_n = dt.name.clone();
                let c_n = ctor.name.clone();
                let os = iter.sort().clone();
                (
                    inner,
                    idt,
                    ic,
                    Box::new(move |new_inner: Expr| {
                        Expr::datatype_constructor(&dt_n, &c_n, vec![new_inner], os)
                    }),
                )
            } else if ctor.fields.iter().any(|f| f.name == "fld_alive") {
                (iter, dt, ctor, Box::new(|x| x))
            } else {
                return None;
            };

        let alive_f = poly_ctor.fields.iter().find(|f| f.name == "fld_alive")?;
        let data_f = poly_ctor.fields.iter().find(|f| f.name == "fld_data")?;
        data_f.sort.array_sort()?;
        let alive_dt = alive_f.sort.datatype_sort()?;
        let alive_ctor = alive_dt.constructors.first()?;
        alive_ctor.fields.iter().find(|f| f.name == "fld_start")?;
        alive_ctor.fields.iter().find(|f| f.name == "fld_end")?;

        let alive =
            poly_expr.clone().field_select(&poly_dt.name, "fld_alive", alive_f.sort.clone());
        let poly_sort = poly_expr.sort().clone();
        let data = poly_expr.field_select(&poly_dt.name, "fld_data", data_f.sort.clone());
        let start = alive.clone().field_select(&alive_dt.name, "fld_start", ptr_sort());
        let end = alive.field_select(&alive_dt.name, "fld_end", ptr_sort());

        let in_bounds = start.clone().bvult(end.clone());
        let element = data.clone().select(start.clone());
        debug!(elem_sort = %element.sort(), "ArrayIntoIterNext: element");

        let one = Expr::bitvec_const(1u64, super::types::POINTER_WIDTH);
        let new_start = Expr::ite(in_bounds.clone(), start.clone().bvadd(one), start);
        let new_alive = Expr::datatype_constructor(
            &alive_dt.name,
            &alive_ctor.name,
            vec![new_start, end],
            alive_f.sort.clone(),
        );
        let new_poly = Expr::datatype_constructor(
            &poly_dt.name,
            &poly_ctor.name,
            vec![new_alive, data],
            poly_sort,
        );
        let new_iter = wrap_fn(new_poly);

        Some(super::CollectionCallResult {
            map_update: Some(new_iter),
            map_update_fields: None,
            result: Some(element),
            result_is_some: Some(in_bounds),
            len_update: None,
            present_update: None,
            result_fields: None,
            constraints: vec![],
            force_error: false,
            aux_targets_dest: false,
        })
    }

    /// Wrap a bare SMT Array in a Slice Datatype with correct length from MIR type.
    ///
    /// When `into_iter` receives a bare `Array(BV64, T)` (from a `[T; N]` array
    /// literal), `make_vec_into_iter_chc` wraps it in a Slice with `fld_len = 0`
    /// because the Array sort doesn't carry length information. This causes
    /// `next()` to always return None (pos < 0 is false), breaking iteration.
    ///
    /// This method extracts N from the MIR type `[T; N]` of the source local
    /// and constructs a proper `Slice_T { fld_ptr: 0, fld_len: N, fld_data: array }`
    /// before the iterator is constructed.
    pub(super) fn wrap_bare_array_in_slice(&mut self, arg: &Operand, array_expr: Expr) -> Expr {
        use rustc_public::ty::{RigidTy, TyKind};

        // Resolve through references to find the source array local and its type.
        let arg_local = match arg {
            Operand::Copy(p) | Operand::Move(p) => p.local,
            _ => return array_expr,
        };
        let resolved_local =
            self.ref_resolution.ref_targets.get(&arg_local).map_or(arg_local, |rt| rt.local);
        let Some(local_decl) = self.body.locals().get(resolved_local) else {
            return array_expr;
        };

        // Extract N from [T; N].
        let array_len: u64 = match local_decl.ty.kind() {
            TyKind::RigidTy(RigidTy::Array(_, const_len)) => match const_len.eval_target_usize() {
                Ok(n) => n,
                Err(_) => return array_expr,
            },
            _ => return array_expr,
        };

        // Build Slice Datatype with correct fld_len.
        let arr_sort = array_expr.sort().clone();
        let Some(arr_info) = arr_sort.array_sort() else {
            return array_expr;
        };
        let elem_sort = arr_info.element_sort.clone();
        let elem_short = crate::codegen_ay::names::sort_short_name(&elem_sort);
        let slice_sort_name = crate::codegen_ay::names::slice_sort_name(&elem_short);
        let slice_fields: Vec<(Cow<'static, str>, Sort)> = vec![
            ("fld_ptr".into(), ptr_sort()),
            ("fld_len".into(), ptr_sort()),
            ("fld_data".into(), arr_sort),
        ];
        let slice_sort = Sort::struct_type(&slice_sort_name, slice_fields);
        self.declare_datatype_sort_if_needed(&slice_sort);
        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&slice_sort, &slice_sort_name);
        Expr::datatype_constructor(
            &slice_sort_name,
            ctor_name,
            vec![
                Expr::bitvec_const(0u64, super::types::POINTER_WIDTH),
                Expr::bitvec_const(array_len, super::types::POINTER_WIDTH),
                array_expr,
            ],
            slice_sort,
        )
    }
}
