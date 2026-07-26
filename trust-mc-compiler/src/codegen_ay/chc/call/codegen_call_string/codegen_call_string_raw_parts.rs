// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String raw-parts resolution and Result type helpers.
//!
//! Split from `codegen_call_string_backing.rs` to keep files under the
//! 500-line limit. Contains:
//! - `from_raw_parts` / `to_raw_parts` MIR tracing for string backing recovery
//! - Aggregate operand resolution for string backing
//! - Concrete `&str` argument resolution
//! - `Result<T, E>` Ok/Err constructor helpers used by string parse stubs

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, Rvalue, StatementKind, TerminatorKind};

use crate::codegen_ay::names;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::ChcCtx;
use super::super::codegen_call_vec::ChcVecFields;
use super::super::codegen_ctx::types::CollectionProjectionKind;
use super::super::codegen_types::CodegenTypes;
use super::codegen_call_string_backing::StringBacking;

/// Part of #4099: detect String clone/from/to_owned callee paths so
/// `resolve_string_backing_from_call_result` can trace backing data
/// through these identity-on-backing-data calls.
fn is_string_clone_or_from_callee(path: &str) -> bool {
    if path.contains("String") && path.ends_with("::clone") {
        return true;
    }
    if path.contains("ToOwned") && path.ends_with("::to_owned") {
        return true;
    }
    if path.contains("String") && path.contains("From") && path.ends_with("::from") {
        return true;
    }
    if (path.contains("String") || path.contains("string"))
        && path.ends_with("::from_utf8_unchecked")
    {
        return true;
    }
    false
}

fn is_raw_ptr_from_raw_parts_callee_path(path: &str) -> bool {
    path.ends_with("::from_raw_parts")
        && !path.contains("NonNull")
        && (path.contains("ptr::const_ptr::<impl *const")
            || path.contains("ptr::mut_ptr::<impl *mut")
            || path.contains("::ptr::"))
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    pub(in crate::codegen_ay::chc) fn resolve_string_from_raw_parts_vec_fields(
        &self,
        vec_local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<ChcVecFields> {
        if let Some(vec_expr) = self.try_resolve_local_expr(vec_local, modified_locals)
            && let Some(fields) = ChcVecFields::extract(vec_expr)
        {
            return Some(fields);
        }

        if self.collections.projection_locals.get(&vec_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let ptr = self.flattened_local_field_expr(
                vec_local,
                names::vec_layout::IDX_PTR,
                modified_locals,
            )?;
            let len = self.flattened_local_field_expr(
                vec_local,
                names::vec_layout::IDX_LEN,
                modified_locals,
            )?;
            let cap = self.flattened_local_field_expr(
                vec_local,
                names::vec_layout::IDX_CAP,
                modified_locals,
            )?;
            let data = self.flattened_local_field_expr(
                vec_local,
                names::vec_layout::IDX_DATA,
                modified_locals,
            )?;
            let vec_sort = Self::translate_ty(self.body.locals().get(vec_local)?.ty)?;
            return Some(ChcVecFields { vec_sort, ptr, len, cap, data });
        }

        None
    }

    pub(in crate::codegen_ay::chc) fn resolve_string_from_raw_parts_source_local(
        &self,
        args: &[Operand],
    ) -> Option<usize> {
        let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else { return None };
        if !place.projection.is_empty() {
            return None;
        }
        let ptr_local = place.local;
        if let Some(rt) = self.ref_resolution.ref_targets.get(&ptr_local) {
            return Some(rt.local);
        }

        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind
            else {
                continue;
            };
            if destination.local != ptr_local {
                continue;
            }
            let Some(callee_path) = self.resolve_callee_path(func) else {
                continue;
            };
            if !matches!(callee_path.rsplit("::").next(), Some("as_ptr" | "as_mut_ptr")) {
                continue;
            }
            if let Some(vec_local) = self.resolve_collection_local(args) {
                return Some(vec_local);
            }
        }
        None
    }

    pub(super) fn resolve_string_backing_from_call_result(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind
            else {
                continue;
            };
            if destination.local != local {
                continue;
            }
            let Some(callee_path) = self.resolve_callee_path(func) else {
                continue;
            };
            if !callee_path.ends_with("String::from_raw_parts") {
                if is_raw_ptr_from_raw_parts_callee_path(&callee_path) {
                    return self.resolve_string_backing_from_raw_ptr_from_raw_parts(
                        local,
                        args,
                        modified_locals,
                    );
                }
                // Part of #4099: trace through clone/from/to_owned calls.
                if is_string_clone_or_from_callee(&callee_path) {
                    if let Some(source_arg) = args.first() {
                        if let Some(backing) =
                            self.resolve_string_backing(source_arg, modified_locals)
                        {
                            return Some(backing);
                        }
                        // Fallback: ref_target chain for &String references
                        // with projections like &(*_1).0.
                        if let Operand::Copy(place) | Operand::Move(place) = source_arg {
                            let ref_local = place.local;
                            if let Some(rt) =
                                self.ref_resolution.ref_targets.get(&ref_local).cloned()
                            {
                                if let Some(backing) = self
                                    .resolve_string_backing_with_metadata_local(
                                        rt.local,
                                        ref_local,
                                        modified_locals,
                                    )
                                {
                                    return Some(backing);
                                }
                            }
                        }
                    }
                }
                continue;
            }
            let vec_local = self.resolve_string_from_raw_parts_source_local(args)?;
            let fields =
                self.resolve_string_from_raw_parts_vec_fields(vec_local, modified_locals)?;
            return Some(StringBacking {
                data: fields.data,
                len: fields.len,
                offset: Expr::bitvec_const(0u64, POINTER_WIDTH),
            });
        }
        None
    }

    fn resolve_string_backing_from_raw_ptr_from_raw_parts(
        &mut self,
        local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else { return None };
        if !place.projection.is_empty() {
            return None;
        }

        let source_local = self.resolve_provenance_local(place.local);
        if source_local == local {
            return None;
        }

        let metadata_len = self.ref_resolution.subslice_len.get(&local).cloned().or_else(|| {
            args.get(1).and_then(|arg| self.translate_operand_with_modified(arg, modified_locals))
        })?;

        let source_backing = self
            .resolve_string_backing_local(source_local, modified_locals)
            .or_else(|| {
                let value = self.ref_resolution.const_ref_values.get(&source_local)?.clone();
                let offset = self
                    .ref_resolution
                    .subslice_offset
                    .get(&source_local)
                    .cloned()
                    .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));
                Self::backing_from_expr(value, Some(metadata_len.clone()), offset)
            })
            .or_else(|| {
                // Part of #4187: trace arg 0 through a to_raw_parts tuple back
                // to the original source pointer. Pattern:
                //   _5 = from_raw_parts(_3, _4)
                //   _3 = Copy((_2.0))          <- field extraction
                //   _2 = to_raw_parts(_1)      <- Call terminator
                // Resolve backing from _1.
                self.trace_through_to_raw_parts(source_local, &metadata_len, modified_locals)
            })?;

        Some(StringBacking {
            data: source_backing.data,
            len: metadata_len,
            offset: source_backing.offset,
        })
    }

    /// Part of #4187: when `from_raw_parts` arg 0 was produced by extracting
    /// field 0 from a `to_raw_parts` tuple, trace back to the original source
    /// pointer and resolve its string backing.
    fn trace_through_to_raw_parts(
        &mut self,
        source_local: usize,
        metadata_len: &Expr,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        // Find the Call terminator that produced source_local via to_raw_parts.
        // source_local may be the tuple itself (if resolve_provenance_local
        // traced through the field extraction) or the tuple field source.
        let to_raw_parts_source = self.find_to_raw_parts_source(source_local)?;
        let resolved = self.resolve_provenance_local(to_raw_parts_source);
        self.resolve_string_backing_local(resolved, modified_locals).or_else(|| {
            let value = self.ref_resolution.const_ref_values.get(&resolved)?.clone();
            let offset = self
                .ref_resolution
                .subslice_offset
                .get(&resolved)
                .cloned()
                .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));
            Self::backing_from_expr(value, Some(metadata_len.clone()), offset)
        })
    }

    /// Scan MIR for a `to_raw_parts` Call whose destination is `tuple_local`,
    /// and return the source pointer local (arg 0 of the call).
    fn find_to_raw_parts_source(&self, tuple_local: usize) -> Option<usize> {
        for bb_data in &self.body.blocks {
            let TerminatorKind::Call { func, args, destination, .. } = &bb_data.terminator.kind
            else {
                continue;
            };
            if destination.local != tuple_local {
                continue;
            }
            let Some(callee_path) = self.resolve_callee_path(func) else {
                continue;
            };
            if !callee_path.ends_with("::to_raw_parts")
                || (!callee_path.contains("ptr::const_ptr::<impl *const")
                    && !callee_path.contains("ptr::mut_ptr::<impl *mut"))
            {
                continue;
            }
            let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else {
                return None;
            };
            if place.projection.is_empty() {
                return Some(place.local);
            }
        }
        None
    }

    pub(super) fn resolve_string_backing_from_aggregate_operands(
        &mut self,
        local: usize,
        modified_locals: &HashSet<usize>,
    ) -> Option<StringBacking> {
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
                if lhs.local != local || !lhs.projection.is_empty() {
                    continue;
                }
                let Rvalue::Aggregate(_, operands) = rhs else { continue };
                for operand in operands {
                    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
                        continue;
                    };
                    if !place.projection.is_empty() {
                        continue;
                    }
                    if place.local != local {
                        if let Some(backing) =
                            self.resolve_string_backing_local(place.local, modified_locals)
                        {
                            return Some(backing);
                        }
                    }
                    let resolved = self.resolve_provenance_local(place.local);
                    if resolved != place.local {
                        if let Some(backing) = self.resolve_string_backing_with_metadata_local(
                            resolved,
                            place.local,
                            modified_locals,
                        ) {
                            return Some(backing);
                        }
                        if let Some(backing) =
                            self.resolve_string_backing_local(resolved, modified_locals)
                        {
                            return Some(backing);
                        }
                    }
                }
            }
        }
        None
    }

    /// Try to resolve the first `&str` argument to its concrete string content.
    ///
    /// Resolves via `resolve_string_backing` -> extracts concrete bytes from the
    /// backing store chain. Returns `None` if the string is symbolic.
    ///
    /// Part of #3692: concrete IntParse evaluation.
    pub(in crate::codegen_ay::chc) fn try_resolve_concrete_str_arg(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<String> {
        let slice = self.try_resolve_concrete_str_slice_arg(args, modified_locals)?;
        String::from_utf8(slice.bytes).ok()
    }

    /// Extract the Ok inner sort from a Result Datatype sort.
    ///
    /// Result<T, E> has constructors Ok(T) and Err(E). Returns T's sort.
    pub(in crate::codegen_ay::chc) fn result_ok_inner_sort(result_sort: &Sort) -> Option<Sort> {
        use ay_bindings::SortInner;
        let SortInner::Datatype(dt) = result_sort.inner() else { return None };
        for ctor in &dt.constructors {
            if crate::codegen_ay::names::is_ok_constructor(&ctor.name) && ctor.fields.len() == 1 {
                return Some(ctor.fields[0].sort.clone());
            }
        }
        None
    }

    /// Build a `Result::Ok(value)` expression for a Result Datatype sort.
    pub(in crate::codegen_ay::chc) fn build_result_ok_expr(
        &self,
        value: Expr,
        result_sort: &Sort,
    ) -> Option<Expr> {
        use ay_bindings::SortInner;
        let SortInner::Datatype(dt) = result_sort.inner() else { return None };
        for ctor in &dt.constructors {
            if crate::codegen_ay::names::is_ok_constructor(&ctor.name) && ctor.fields.len() == 1 {
                return Some(Expr::datatype_constructor(
                    &*dt.name,
                    &*ctor.name,
                    vec![value],
                    result_sort.clone(),
                ));
            }
        }
        None
    }

    /// Build a `Result::Err(symbolic_error)` expression for a Result Datatype sort.
    pub(in crate::codegen_ay::chc) fn build_result_err_expr(
        &self,
        result_sort: &Sort,
    ) -> Option<Expr> {
        use ay_bindings::SortInner;
        let SortInner::Datatype(dt) = result_sort.inner() else { return None };
        for ctor in &dt.constructors {
            if crate::codegen_ay::names::is_err_constructor(&ctor.name) && ctor.fields.len() == 1 {
                let err_sort = ctor.fields[0].sort.clone();
                let err_val = super::super::codegen_ctx::globals::declare_pending_var(
                    super::super::chc_fresh_name("parse_err"),
                    err_sort,
                );
                // Part of #3447: parse error payload is unconstrained.
                self.record_aggregate_gap("string_parse_error_payload_unconstrained");
                return Some(Expr::datatype_constructor(
                    &*dt.name,
                    &*ctor.name,
                    vec![err_val],
                    result_sort.clone(),
                ));
            }
        }
        None
    }
}
// DST field-ref string backing resolution: codegen_call_string_raw_parts_dst.rs
