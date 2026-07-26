// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Iterator semantic model for AY codegen.
//!
//! VecIntoIter<T> is modeled as a struct with (vec, pos) fields where
//! vec is the backing Vec and pos is the current iteration position.
//! Named VecIntoIter to avoid collision with array IntoIter in statement/iter.rs.
//!
//! Part of #1611: Iterator adapter stubs for nested Vec patterns.
//! Helper methods (construction, field extraction, utilities) in iter_helpers.rs.

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use std::sync::atomic::{AtomicUsize, Ordering};
use tracing::{debug, error, warn};

/// Counter for iterator stub soundness issues in BMC mode (#1920).
/// Tracks when iterator verification is skipped due to sort mismatch.
/// Non-zero count indicates UNSOUND verification - iterator constraints were lost.
pub(super) static BMC_ITERATOR_UNSOUND_SKIP_COUNT: AtomicUsize = AtomicUsize::new(0);

/// Get the current BMC iterator unsoundness skip count (#1929).
/// Returns the number of times iterator verification was skipped due to sort mismatches.
pub(in crate::codegen_ay) fn get_bmc_iterator_unsound_skip_count() -> usize {
    BMC_ITERATOR_UNSOUND_SKIP_COUNT.load(Ordering::Relaxed)
}

/// Reset the BMC iterator unsound skip counter, returning the previous value (Part of #2360).
pub(in crate::codegen_ay::statement) fn take_bmc_iterator_unsound_skip_count() -> usize {
    BMC_ITERATOR_UNSOUND_SKIP_COUNT.swap(0, Ordering::Relaxed)
}

use super::super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen iterator operations (Part of #1611).
    ///
    /// VecIntoIter<T> is modeled as (vec: Vec<T>, pos: usize).
    /// next() advances pos and returns vec[pos] if in bounds (then increments pos).
    pub(in crate::codegen_ay::statement) fn codegen_iter_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{
            ChainNext, FlattenNext, HashMapIterNext, IntoIterNext, IterCollect, IterFlatten,
            RangeSpecNext, TrustMcMapIterNext,
        };

        debug!(?stub_kind, %callee_path, "codegen_iter_stub");

        match stub_kind {
            IntoIterNext => {
                // VecIntoIter<T>::next(&mut self) -> Option<T>
                // if pos < vec.len: result = Some(vec[pos]), pos += 1
                // else: result = None
                if args.is_empty() {
                    warn!("VecIntoIter::next requires 1 arg (self)");
                    return target;
                }
                if let Some((base, iter)) = self.resolve_collection_base(&args[0]) {
                    // Guard against non-datatype iter (same as vec_field_select fix)
                    // Part of #1920: Explicit failure - record violation to fail verification
                    if !iter.sort().is_datatype() {
                        let count =
                            BMC_ITERATOR_UNSOUND_SKIP_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
                        error!(
                            "UNSOUND: VecIntoIter::next has non-datatype sort {:?} (hit #{}) - forcing verification failure",
                            iter.sort(),
                            count
                        );
                        // Record violation to fail verification explicitly
                        self.record_violation_guarded(
                            Expr::bool_const(true),
                            "iterator_sort_mismatch_unsound",
                        );
                        return target;
                    }
                    // Extract fields from VecIntoIter struct (renamed to avoid collision with array IntoIter).
                    // Clone Sort (O(1) Arc) so dt borrows from sort_ref, not iter.
                    let sort_ref = iter.sort().clone();
                    let (dt_name, ctor_name): (&str, &str) = sort_ref
                        .datatype_sort()
                        .and_then(|dt| {
                            let ctor = dt.constructors.first()?;
                            Some((&*dt.name, &*ctor.name))
                        })
                        .unwrap_or(("VecIntoIter", "VecIntoIter_mk"));

                    let vec_sort = self.infer_iter_vec_sort(&iter);
                    let iter_sort = iter.sort().clone();
                    let vec = iter.clone().field_select(dt_name, "fld_vec", vec_sort);
                    let pos = iter.field_select(dt_name, "fld_pos", ptr_sort());

                    // Get vec length
                    let len = self.vec_field_select_declared(&vec, "fld_len", ptr_sort());

                    // Check if pos < len
                    let in_bounds = pos.clone().bvult(len);

                    // Get element at current position from vec's data array
                    let data = self.extract_vec_data(&vec);
                    let elem = data.select(pos.clone());

                    // Increment position only when in_bounds
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_pos = Expr::ite(in_bounds.clone(), pos.clone().bvadd(one), pos);

                    // Update iterator state
                    let new_iter = Expr::datatype_constructor(
                        dt_name,
                        ctor_name,
                        vec![vec, new_pos],
                        iter_sort,
                    );
                    self.env_update(base, new_iter);

                    // #3133: Value-semantic encoding for ALL iter.next() results.
                    // Option<&T> encodes as Option<T> with the dereferenced value,
                    // not as Option<ptr64>. This aligns with CHC value semantics
                    // where references are transparent.
                    let dest_sort = self.infer_sort_from_place(destination);
                    let option_sort = self.option_sort_for_value(elem.sort(), dest_sort);
                    let some_elem = self.make_option_some(&option_sort, elem);
                    let none_val = self.make_option_none(&option_sort);
                    let result = Expr::ite(in_bounds, some_elem, none_val);
                    self.assign_value_to_place(destination, result);
                } else {
                    // Fallback: symbolic result
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            IterFlatten => {
                // Iterator::flatten(self) -> Flatten<Self>
                // For VecIntoIter<Vec<T>>, build a flattened Vec<T> and wrap in Flatten iterator.
                if args.is_empty() {
                    warn!("Iterator::flatten requires 1 arg (self)");
                    return target;
                }

                let iter_expr = self.codegen_operand(&args[0]);
                if let Some(iter_expr) = iter_expr {
                    if let Some(result) = self.codegen_iter_flatten_from_vec_iter(&iter_expr) {
                        self.assign_value_to_place(destination, result);
                    } else {
                        self.codegen_symbolic_result(destination);
                    }
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            IterCollect => {
                // Iterator::collect(self) -> B
                // For VecIntoIter<T> (and Flatten wrapping it), return the Vec.
                if args.is_empty() {
                    warn!("Iterator::collect requires 1 arg (self)");
                    return target;
                }

                // Part of #3189: Try MIR concrete filter_map replay first.
                // When the iterator chain includes filter_map(parse.ok()), this
                // extracts strings from MIR array aggregates and builds a concrete Vec.
                // Must run before codegen_iter_collect_vec, which always returns Some
                // (even with sort-mismatched symbolic fallback).
                if let Some(result) = self.try_concrete_filter_map_collect_from_mir(destination) {
                    debug!("IterCollect: MIR concrete filter_map replay succeeded (#3189)");
                    self.assign_value_to_place(destination, result);
                    return target;
                }

                let iter_expr = self.codegen_operand(&args[0]);
                if let Some(iter_expr) = iter_expr {
                    if let Some(result) = self.codegen_iter_collect_vec(&iter_expr) {
                        self.assign_value_to_place(destination, result);
                    } else {
                        self.codegen_symbolic_result(destination);
                    }
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            FlattenNext => {
                // Flatten<I>::next(&mut self) -> Option<I::Item>
                if args.is_empty() {
                    warn!("Flatten::next requires 1 arg (self)");
                    return target;
                }

                if let Some((base, flatten)) = self.resolve_collection_base(&args[0]) {
                    let flatten_sort = flatten.sort().clone();
                    if let Some((dt_name, ctor_name, iter_sort)) =
                        Self::datatype_field_info(&flatten_sort, "fld_iter")
                    {
                        // Move `flatten` into field_select — no clone needed
                        let iter_expr = flatten.field_select(dt_name, "fld_iter", iter_sort);
                        if let Some((new_iter, result)) = self.vec_iter_next_from_expr(
                            &iter_expr,
                            self.infer_sort_from_place(destination),
                        ) {
                            let new_flatten = Expr::datatype_constructor(
                                dt_name,
                                ctor_name,
                                vec![new_iter],
                                flatten_sort.clone(),
                            );
                            self.env_update(base, new_flatten);
                            self.assign_value_to_place(destination, result);
                        } else {
                            self.codegen_symbolic_result(destination);
                        }
                    } else {
                        self.codegen_symbolic_result(destination);
                    }
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            ChainNext => {
                // Chain<A, B>::next(&mut self) -> Option<A::Item>
                // Part of #4160: opaque — return symbolic over-approximation.
                self.codegen_symbolic_result(destination);
                target
            }

            RangeSpecNext => {
                // <Range<T> as RangeIteratorImpl>::spec_next(&mut self) -> Option<T>
                // Preserve range progression shape in BMC mode:
                // - has_remaining := start < end
                // - if has_remaining then start += 1
                // - return Some(old_start) / None
                if args.is_empty() {
                    warn!("RangeIteratorImpl::spec_next requires 1 arg (self)");
                    return target;
                }

                if let Some((base, range)) = self.resolve_collection_base(&args[0])
                    && let Some(dt) = range.sort().datatype_sort()
                    && let Some(ctor) = dt.constructors.first()
                    && let Some(start_field) = ctor.field("fld_start")
                    && let Some(end_field) = ctor.field("fld_end")
                {
                    let start = range.clone().field_select(
                        &*dt.name,
                        "fld_start",
                        start_field.sort.clone(),
                    );
                    let end =
                        range.clone().field_select(&*dt.name, "fld_end", end_field.sort.clone());

                    let start_sort = start.sort().clone();
                    let original_start = start.clone();
                    let advanced = if let (Some(start_width), Some(end_width)) =
                        (start_sort.bitvec_width(), end.sort().bitvec_width())
                    {
                        if start_width != end_width {
                            None
                        } else {
                            let has_remaining = start.clone().bvult(end);
                            let one = Expr::bitvec_const(1u64, start_width);
                            // Last use of `start` — move in else-branch, clone in then-branch
                            let next_start =
                                Expr::ite(has_remaining.clone(), start.clone().bvadd(one), start);
                            Some((has_remaining, next_start))
                        }
                    } else if start_sort.is_int() && end.sort().is_int() {
                        let has_remaining = start.clone().int_lt(end);
                        // Last use of `start` — move in else-branch, clone in then-branch
                        let next_start = Expr::ite(
                            has_remaining.clone(),
                            start.clone().int_add(Expr::int_const(1)),
                            start,
                        );
                        Some((has_remaining, next_start))
                    } else {
                        None
                    };

                    if let Some((has_remaining, next_start)) = advanced {
                        let mut ctor_args = Vec::with_capacity(ctor.fields.len());
                        for field in &ctor.fields {
                            if field.name == "fld_start" {
                                ctor_args.push(next_start.clone());
                            } else {
                                ctor_args.push(range.clone().field_select(
                                    &*dt.name,
                                    &*field.name,
                                    field.sort.clone(),
                                ));
                            }
                        }
                        let new_range = Expr::datatype_constructor(
                            &*dt.name,
                            &*ctor.name,
                            ctor_args,
                            range.sort().clone(),
                        );
                        self.env_update(base, new_range);

                        let option_sort = self.option_sort_for_value(
                            &start_sort,
                            self.infer_sort_from_place(destination),
                        );
                        let some_start = self.make_option_some(&option_sort, original_start);
                        let none_val = self.make_option_none(&option_sort);
                        self.assign_value_to_place(
                            destination,
                            Expr::ite(has_remaining, some_start, none_val),
                        );
                        return target;
                    }
                }

                self.codegen_symbolic_result(destination);
                target
            }

            // Collection-specific iterator next ops delegated to iter_collection_next.rs
            HashMapIterNext
            | TrustMcMapIterNext
            | StubKind::BTreeSetIterNext
            | StubKind::HashSetIterNext => {
                self.codegen_iter_collection_next_stub(stub_kind, args, destination, target)
            }

            // Iterator adapters delegated to iter_adapters.rs to keep this
            // file focused on concrete iterator state transitions.
            StubKind::IterMap => self.codegen_iter_map_stub(args, destination, target),
            StubKind::IterFilter => self.codegen_iter_filter_stub(args, destination, target),
            // Part of #3692: IterFilterMap reuses IterMap handler (sound over-approximation).
            StubKind::IterFilterMap => self.codegen_iter_map_stub(args, destination, target),
            StubKind::IterFold => self.codegen_iter_fold_stub(args, destination, target),
            StubKind::IterSum => self.codegen_iter_sum_stub(args, destination, target),
            StubKind::MapNext => self.codegen_map_next_stub(args, destination, target),
            StubKind::FilterNext => self.codegen_filter_next_stub(args, destination, target),
            // Part of #3692: FilterMapNext reuses MapNext handler (sound over-approximation).
            StubKind::FilterMapNext => self.codegen_map_next_stub(args, destination, target),
            // Part of #3381: Zip adapter creation and next().
            StubKind::IterZip => self.codegen_iter_zip_stub(args, destination, target),
            StubKind::ZipNext => self.codegen_zip_next_stub(args, destination, target),

            // Part of #3477: IterSizeHint returns (usize, Option<usize>).
            // Sound over-approximation: symbolic result. CHC encoding computes
            // precise (remaining, Some(remaining)) from iterator fields.
            StubKind::IterSizeHint => {
                debug!("codegen_iter_stub: IterSizeHint → symbolic result");
                self.codegen_symbolic_result(destination);
                target
            }

            // Part of #3477: Range::into_iter() is identity — the Range IS the
            // iterator. BMC parity with CHC encoding which copies src to dest.
            StubKind::RangeIntoIter => {
                debug!("codegen_iter_stub: RangeIntoIter → identity");
                if let Some(arg_expr) = args.first().and_then(|a| self.codegen_operand(a)) {
                    self.assign_value_to_place(destination, arg_expr);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            // partial dispatch: StubKind — parent dispatcher (stub_dispatch.rs) routes only
            // iterator variants here; reaching this arm is a programming error.
            _other => {
                warn!(
                    ?_other,
                    "codegen_iter_stub: unexpected stub — update stub_dispatch.rs routing"
                );
                None
            }
        }
    }
}
