// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Collection-specific iterator next operations for AY codegen.
//!
//! Extracted from `iter.rs`. Handles:
//! - HashMapIterNext / TrustMcMapIterNext
//! - BTreeSetIterNext / HashSetIterNext
//!
//! Part of #2246: Large file decomposition.

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use std::sync::atomic::Ordering;
use tracing::{error, warn};

use super::super::StatementCodegen;
use super::iter::BMC_ITERATOR_UNSOUND_SKIP_COUNT;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen collection-specific iterator next operations.
    ///
    /// Delegated from `codegen_iter_stub` for HashMap/Set iterator variants.
    pub(in super::super) fn codegen_iter_collection_next_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        match stub_kind {
            StubKind::HashMapIterNext | StubKind::TrustMcMapIterNext => {
                // HashMap/TrustMcMap IntoIter::next(&mut self) -> Option<(K, V)> (Part of #1751, #1812)
                // Iterator has (data, present, keys, pos, len) fields (#3057 DT-free layout)
                // If pos < len: return Some((keys[pos], unwrap(data[keys[pos]]))), pos += 1
                // Else: return None
                if args.is_empty() {
                    warn!("HashMapIntoIter::next requires 1 arg (self)");
                    return target;
                }

                if let Some((base, iter)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1920: Explicit failure - record violation to fail verification
                    if !iter.sort().is_datatype() {
                        let count =
                            BMC_ITERATOR_UNSOUND_SKIP_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
                        error!(
                            "UNSOUND: HashMapIterNext has non-datatype sort {:?} (hit #{}) - forcing verification failure",
                            iter.sort(),
                            count
                        );
                        // Record violation to fail verification explicitly
                        self.record_violation_guarded(
                            Expr::bool_const(true),
                            "iterator_sort_mismatch_unsound",
                        );
                        self.codegen_symbolic_result(destination);
                        return target;
                    }

                    // Extract iterator fields.
                    // Clone Sort (O(1) Arc) so dt borrows from sort_ref, not iter.
                    let sort_ref = iter.sort().clone();
                    let (dt_name, ctor_name): (&str, &str) = sort_ref
                        .datatype_sort()
                        .and_then(|dt| {
                            let ctor = dt.constructors.first()?;
                            Some((&*dt.name, &*ctor.name))
                        })
                        .unwrap_or(("HashMapIntoIter", "HashMapIntoIter_mk"));

                    // Extract fields from iterator
                    // Part of #3106: fld_data (not fld_map) per DT-free encoding (#3057).
                    let data = self.hashmap_iter_field_select(&iter, dt_name, "fld_data");
                    let present = self.hashmap_iter_field_select(&iter, dt_name, "fld_present");
                    let keys = self.hashmap_iter_field_select(&iter, dt_name, "fld_keys");
                    let pos = iter.clone().field_select(dt_name, "fld_pos", ptr_sort());
                    let len = iter.clone().field_select(dt_name, "fld_len", ptr_sort());

                    // Check if pos < len
                    let in_bounds = pos.clone().bvult(len.clone());

                    // Part of #1751: Guard against non-Array sorts before select.
                    // If into_iter was constructed with a wrong-sort expression,
                    // the extracted fields won't be arrays — fall back to symbolic.
                    if keys.sort().array_sort().is_none() || data.sort().array_sort().is_none() {
                        warn!(
                            "HashMapIterNext: keys or data has non-Array sort (keys={:?}, data={:?}), falling back to symbolic",
                            keys.sort(),
                            data.sort()
                        );
                        self.codegen_symbolic_result(destination);
                        return target;
                    }

                    // Get key at current position: key = keys[pos]
                    let key = keys.clone().select(pos.clone());

                    // Get value from data array: value = data[key] (returns Option<V> in BMC)
                    let option_val = data.clone().select(key.clone());

                    // SOUNDNESS FIX (Part of #1751): Assert membership invariant.
                    // Per designs/2026-02-02-symbolic-heap-collection-modeling.md:201-226,
                    // iterator keys must be constrained to exist in the underlying collection.
                    // Without this, symbolic keys could iterate over non-existent entries.
                    // Conditional on in_bounds: only assert when actually yielding an element.
                    let is_some_key = self.make_option_is_some(&option_val);
                    self.ctx.assert(Expr::ite(
                        in_bounds.clone(),
                        is_some_key,
                        Expr::bool_const(true),
                    ));

                    // Extract value from Option<V> - assertion above ensures it's Some
                    let value = self.extract_option_value(&option_val);

                    // Create tuple (key, value) for result
                    let tuple = self.make_tuple(key, value);

                    // Increment position
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_pos = Expr::ite(in_bounds.clone(), pos.clone().bvadd(one), pos);

                    // Update iterator state
                    // Part of #3106: include present field per DT-free layout (#3057).
                    let new_iter = Expr::datatype_constructor(
                        dt_name,
                        ctor_name,
                        vec![data, present, keys, new_pos, len],
                        iter.sort().clone(),
                    );
                    self.env_update(base, new_iter);

                    // Build Option<(K, V)> result
                    let tuple_sort = tuple.sort().clone();
                    let option_sort = self.option_sort_for_value(
                        &tuple_sort,
                        self.infer_sort_from_place(destination),
                    );
                    let some_tuple = self.make_option_some(&option_sort, tuple);
                    let none_val = self.make_option_none(&option_sort);

                    let result = Expr::ite(in_bounds, some_tuple, none_val);
                    self.assign_value_to_place(destination, result);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            StubKind::BTreeSetIterNext | StubKind::HashSetIterNext => {
                // SetIntoIter<K>::next(&mut self) -> Option<K> (Part of #1751)
                // Iterator has (set, keys, pos, len) fields
                // If pos < len: return Some(keys[pos]), pos += 1
                // Else: return None
                if args.is_empty() {
                    warn!("SetIntoIter::next requires 1 arg (self)");
                    return target;
                }

                if let Some((base, iter)) = self.resolve_collection_base(&args[0]) {
                    // Part of #1920: Explicit failure - record violation to fail verification
                    if !iter.sort().is_datatype() {
                        let count =
                            BMC_ITERATOR_UNSOUND_SKIP_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
                        error!(
                            "UNSOUND: SetIterNext has non-datatype sort {:?} (hit #{}) - forcing verification failure",
                            iter.sort(),
                            count
                        );
                        // Record violation to fail verification explicitly
                        self.record_violation_guarded(
                            Expr::bool_const(true),
                            "iterator_sort_mismatch_unsound",
                        );
                        self.codegen_symbolic_result(destination);
                        return target;
                    }

                    // Extract iterator fields.
                    // Clone Sort (O(1) Arc) so dt borrows from sort_ref, not iter.
                    let sort_ref = iter.sort().clone();
                    let (dt_name, ctor_name): (&str, &str) = sort_ref
                        .datatype_sort()
                        .and_then(|dt| {
                            let ctor = dt.constructors.first()?;
                            Some((&*dt.name, &*ctor.name))
                        })
                        .unwrap_or(("SetIntoIter", "SetIntoIter_mk"));

                    // Extract set and keys (for iterator invariant, not used in result)
                    let set = self.set_iter_field_select(&iter, dt_name, "fld_set");
                    let keys = self.set_iter_field_select(&iter, dt_name, "fld_keys");
                    let pos = iter.clone().field_select(dt_name, "fld_pos", ptr_sort());
                    let len = iter.clone().field_select(dt_name, "fld_len", ptr_sort());

                    // Check if pos < len
                    let in_bounds = pos.clone().bvult(len.clone());

                    // Part of #1751: Guard against non-Array sorts before select.
                    if keys.sort().array_sort().is_none() || set.sort().array_sort().is_none() {
                        warn!(
                            "SetIterNext: keys or set has non-Array sort (keys={:?}, set={:?}), falling back to symbolic",
                            keys.sort(),
                            set.sort()
                        );
                        self.codegen_symbolic_result(destination);
                        return target;
                    }

                    // Get key at current position: key = keys[pos]
                    let key = keys.clone().select(pos.clone());

                    // SOUNDNESS FIX (Part of #1751): Assert membership invariant.
                    // Per designs/2026-02-02-symbolic-heap-collection-modeling.md:201-226,
                    // iterator keys must be constrained to exist in the underlying collection.
                    // For sets modeled as Array<K, Bool>, set[key] = true means membership.
                    // Conditional on in_bounds: only assert when actually yielding an element.
                    let is_member = self.make_set_contains(&set, &key);
                    self.ctx.assert(Expr::ite(
                        in_bounds.clone(),
                        is_member,
                        Expr::bool_const(true),
                    ));

                    // Increment position only when in bounds
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_pos = Expr::ite(in_bounds.clone(), pos.clone().bvadd(one), pos);

                    // Update iterator state
                    let new_iter = Expr::datatype_constructor(
                        dt_name,
                        ctor_name,
                        vec![set, keys, new_pos, len],
                        iter.sort().clone(),
                    );
                    self.env_update(base, new_iter);

                    // Build Option<K> result
                    let key_sort = key.sort().clone();
                    let option_sort = self
                        .option_sort_for_value(&key_sort, self.infer_sort_from_place(destination));
                    let some_key = self.make_option_some(&option_sort, key);
                    let none_val = self.make_option_none(&option_sort);

                    let result = Expr::ite(in_bounds, some_key, none_val);
                    self.assign_value_to_place(destination, result);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            // partial dispatch: StubKind — parent codegen_iter_stub routes only
            // collection iterator next variants here; reaching this arm is a programming error.
            _other => {
                warn!(
                    ?_other,
                    "codegen_iter_collection_next_stub: unexpected stub — update iter.rs routing"
                );
                None
            }
        }
    }
}
