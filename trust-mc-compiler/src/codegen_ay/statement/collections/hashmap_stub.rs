// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// HashMap stub dispatch body extracted from hashmap.rs for structural decomposition.
// Converted from include!() to module for #2306.

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort, ptr_sort};
use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::super::super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen for HashMap/TrustMcMap stub operations.
    ///
    /// Part of #1275: BMC collection stubs implementation.
    pub(in crate::codegen_ay::statement) fn codegen_hashmap_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{
            BTreeMapClear, BTreeMapClone, BTreeMapContainsKey, BTreeMapGet, BTreeMapGetMut,
            BTreeMapInsert, BTreeMapIsEmpty, BTreeMapLen, BTreeMapNew, BTreeMapRemove,
            HashMapClear, HashMapClone, HashMapContainsKey, HashMapDrop, HashMapGet, HashMapGetMut,
            HashMapInsert, HashMapIntoIter, HashMapIsEmpty, HashMapIter, HashMapKeys, HashMapLen,
            HashMapNew, HashMapRemove, HashMapValues, TrustMcMapClear, TrustMcMapClone,
            TrustMcMapContainsKey, TrustMcMapGet, TrustMcMapInsert, TrustMcMapIntoIter,
            TrustMcMapIsEmpty, TrustMcMapLen, TrustMcMapNew, TrustMcMapRemove,
        };

        debug!(?stub_kind, %callee_path, "codegen_hashmap_stub");

        match stub_kind {
            // new/default: create empty map (const_array with None)
            // Part of #1744: Initialize len to 0 for soundness
            // Part of #1752: BTreeMap uses same model (ordering not modeled)
            HashMapNew | TrustMcMapNew | BTreeMapNew => {
                // Infer key/value sorts from destination type
                let (key_sort, option_sort) =
                    self.infer_hashmap_sorts(destination).unwrap_or_else(|| {
                        warn!("HashMap::new: cannot infer key/value sorts, using defaults");
                        (ptr_sort(), self.make_option_sort(ptr_sort()))
                    });

                // Create None value for const_array
                let none = self.make_option_none(&option_sort);
                let empty_map = Expr::const_array(key_sort, none);

                self.assign_value_to_place(destination, empty_map);

                // Part of #1744: Initialize len to 0 for the new map
                let dest_base = self.ssa_base_name(destination);
                let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                self.hashmap_len_symbols.insert(dest_base.into(), zero);

                target
            }

            // insert: store value, return previous Option
            // Part of #1744: Update len when inserting new key
            // Part of #1752: BTreeMap uses same model
            HashMapInsert | TrustMcMapInsert | BTreeMapInsert => {
                if args.len() < 3 {
                    warn!(
                        "HashMap::insert requires 3 args (self, key, value) — fail-closed (#2497)"
                    );
                    return None;
                }

                // Get map base name through ref_pointees
                let resolved = self.resolve_collection_base(&args[0]);
                let key = self.codegen_operand(&args[1]);
                let value = self.codegen_operand(&args[2]);

                if let (Some((base, map)), Some(k), Some(v)) = (resolved, key, value) {
                    if !map.sort().is_array() {
                        debug!("HashMap::insert: map sort is not Array; symbolic fallback");
                        self.codegen_symbolic_result(destination);
                        return target;
                    }
                    // Get previous value: prev = select(map, key)
                    let prev = map.clone().select(k.clone());

                    // Create new map with updated entry: map' = store(map, key, Some(value))
                    let option_sort = prev.sort();
                    let some_val = self.make_option_some(&option_sort, v);
                    let new_map = map.store(k, some_val);

                    // Update map in environment
                    self.env_update(std::sync::Arc::clone(&base), new_map);

                    // Part of #1744: Update len - increment if key was absent
                    // new_len = ite(was_absent, old_len + 1, old_len)
                    let old_len = self.get_or_create_hashmap_len(&base);
                    let was_absent = self.option_is_some(&prev).not();
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_len = Expr::ite(was_absent, old_len.clone().bvadd(one), old_len);
                    self.hashmap_len_symbols.insert(base, new_len);

                    // Return previous value
                    self.assign_value_to_place(destination, prev);
                } else {
                    // Fallback: symbolic result
                    debug!("HashMap::insert: fallback to symbolic result");
                    self.codegen_symbolic_result(destination);
                }

                target
            }

            // get/get_mut: select from map (returns Option)
            // Part of #1752: BTreeMap uses same model
            HashMapGet | HashMapGetMut | TrustMcMapGet | BTreeMapGet | BTreeMapGetMut => {
                if args.len() < 2 {
                    warn!("HashMap::get requires 2 args (self, key) — fail-closed (#2497)");
                    return None;
                }

                // Get map expression
                let resolved = self.resolve_collection_base(&args[0]);
                // Part of #1659: HashMap::get takes &Q, so args[1] is a reference.
                // Dereference to get actual key value.
                let key = self.get_value_through_ref(&args[1]);

                if let (Some((_base, map)), Some(k)) = (resolved, key) {
                    if !map.sort().is_array() {
                        debug!("HashMap::get: map sort is not Array; symbolic fallback");
                        self.codegen_symbolic_result(destination);
                        return target;
                    }
                    // result = select(map, key)
                    let result = map.select(k);
                    self.assign_value_to_place(destination, result);
                } else {
                    // Fallback: symbolic result
                    debug!("HashMap::get: fallback to symbolic result");
                    self.codegen_symbolic_result(destination);
                }

                target
            }

            // contains_key: check if key exists (is_some)
            // Part of #1752: BTreeMap uses same model
            HashMapContainsKey | TrustMcMapContainsKey | BTreeMapContainsKey => {
                if args.len() < 2 {
                    warn!(
                        "HashMap::contains_key requires 2 args (self, key) — fail-closed (#2497)"
                    );
                    return None;
                }

                // Get map expression
                let resolved = self.resolve_collection_base(&args[0]);
                // Part of #1659: HashMap::contains_key takes &Q, so args[1] is a reference.
                // Dereference to get actual key value.
                let key = self.get_value_through_ref(&args[1]);

                if let (Some((_base, map)), Some(k)) = (resolved, key) {
                    if !map.sort().is_array() {
                        debug!("HashMap::contains_key: map sort is not Array; symbolic fallback");
                        let name = self.ctx.fresh_name("contains_key");
                        let result = self.ctx.declare_var(&name, bool_sort());
                        self.assign_value_to_place(destination, result);
                        return target;
                    }
                    // result = is_some(select(map, key))
                    let option_val = map.select(k);
                    let is_some = self.option_is_some(&option_val);
                    self.assign_value_to_place(destination, is_some);
                } else {
                    // Fallback: symbolic boolean
                    let name = self.ctx.fresh_name("contains_key");
                    let result = self.ctx.declare_var(&name, bool_sort());
                    self.assign_value_to_place(destination, result);
                }

                target
            }

            // remove: remove key, return previous value
            // Part of #1744: Update len when removing key
            // Part of #1752: BTreeMap uses same model
            HashMapRemove | TrustMcMapRemove | BTreeMapRemove => {
                if args.len() < 2 {
                    warn!("HashMap::remove requires 2 args (self, key) — fail-closed (#2497)");
                    return None;
                }

                // Get map base name through ref_pointees
                let resolved = self.resolve_collection_base(&args[0]);
                // Part of #1659: HashMap::remove takes &Q, so args[1] is a reference.
                // Dereference to get actual key value.
                let key = self.get_value_through_ref(&args[1]);

                if let (Some((base, map)), Some(k)) = (resolved, key) {
                    if !map.sort().is_array() {
                        debug!("HashMap::remove: map sort is not Array; symbolic fallback");
                        self.codegen_symbolic_result(destination);
                        return target;
                    }
                    // Get previous value: prev = select(map, key)
                    let prev = map.clone().select(k.clone());
                    let option_sort = prev.sort();

                    // Create new map with entry removed: map' = store(map, key, None)
                    let none = self.make_option_none(&option_sort);
                    let new_map = map.store(k, none);

                    // Update map in environment
                    self.env_update(std::sync::Arc::clone(&base), new_map);

                    // Part of #1744: Update len - decrement if key was present
                    // new_len = ite(was_present, old_len - 1, old_len)
                    let old_len = self.get_or_create_hashmap_len(&base);
                    let was_present = self.option_is_some(&prev);
                    let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                    let new_len = Expr::ite(was_present, old_len.clone().bvsub(one), old_len);
                    self.hashmap_len_symbols.insert(base, new_len);

                    // Return previous value
                    self.assign_value_to_place(destination, prev);
                } else {
                    // Fallback: symbolic result
                    debug!("HashMap::remove: fallback to symbolic result");
                    self.codegen_symbolic_result(destination);
                }

                target
            }

            // len/is_empty: Track per-instance and maintain invariant (#1315)
            // len == 0 <=> is_empty ensures consistent HashMap state.
            // Part of #1752: BTreeMap uses same model
            HashMapLen | TrustMcMapLen | BTreeMapLen => {
                // Get map base for per-instance tracking
                let map_base =
                    if !args.is_empty() { self.get_map_base_from_ref(&args[0]) } else { None };

                let len = if let Some(ref base) = map_base {
                    self.get_or_create_hashmap_len(base)
                } else {
                    // Fallback: fresh symbol (can't track without base)
                    let name = self.ctx.fresh_name("hashmap_len");
                    self.ctx.declare_var(&name, ptr_sort())
                };

                self.assign_value_to_place(destination, len);
                target
            }

            // Part of #1752: BTreeMap uses same model
            HashMapIsEmpty | TrustMcMapIsEmpty | BTreeMapIsEmpty => {
                // Get map base for per-instance tracking
                let map_base =
                    if !args.is_empty() { self.get_map_base_from_ref(&args[0]) } else { None };

                // Create is_empty symbol
                let is_empty_name = self.ctx.fresh_name("hashmap_is_empty");
                let is_empty = self.ctx.declare_var(&is_empty_name, bool_sort());

                // Get or create len symbol and assert invariant
                if let Some(ref base) = map_base {
                    let len = self.get_or_create_hashmap_len(base);

                    // Assert invariant: is_empty <=> len == 0 (#1315)
                    // Express A <=> B as (A implies B) and (B implies A)
                    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                    let len_is_zero = len.eq(zero);
                    let fwd = is_empty.clone().implies(len_is_zero.clone()); // is_empty => len == 0
                    let bwd = len_is_zero.implies(is_empty.clone()); // len == 0 => is_empty
                    self.ctx.assert(fwd.and(bwd));
                }

                self.assign_value_to_place(destination, is_empty);
                target
            }

            // clear: reset map to empty
            // Part of #1744: Reset len to 0 for soundness
            // Part of #1752: BTreeMap uses same model
            HashMapClear | TrustMcMapClear | BTreeMapClear => {
                if args.is_empty() {
                    warn!("HashMap::clear requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                // Get map base name through ref_pointees
                if let Some((base, map)) = self.resolve_collection_base(&args[0]) {
                    // Get array sort info
                    if let Some(arr) = map.sort().array_sort() {
                        let key_sort = arr.index_sort.clone();
                        let option_sort = arr.element_sort.clone();
                        let none = self.make_option_none(&option_sort);
                        let empty_map = Expr::const_array(key_sort, none);
                        self.env_update(std::sync::Arc::clone(&base), empty_map);
                    }
                    // Part of #1744: Reset len to 0 (not remove - clear gives definite state)
                    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                    self.hashmap_len_symbols.insert(base, zero);
                }

                target
            }

            // clone: return same map (arrays are immutable)
            // Part of #1744: Copy length tracking to cloned map (like BTreeSet::clone)
            // Part of #1752: BTreeMap uses same model
            HashMapClone | TrustMcMapClone | BTreeMapClone => {
                if args.is_empty() {
                    warn!("HashMap::clone requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                // Get map expression and assign to destination
                if let Some((base, map)) = self.resolve_collection_base(&args[0]) {
                    self.assign_value_to_place(destination, map);

                    // Part of #1744: Copy length tracking to cloned map
                    if let Some(src_len) = self.hashmap_len_symbols.get(base.as_ref()).cloned() {
                        let dest_base = self.ssa_base_name(destination);
                        self.hashmap_len_symbols.insert(dest_base.into(), src_len);
                    }
                } else {
                    self.codegen_symbolic_result(destination);
                }

                target
            }

            HashMapDrop => target,

            // HashMap/TrustMcMap::into_iter(self) -> IntoIter<K, V> (Part of #1751, #1812)
            // Create iterator struct with (map, keys_array, pos, len) fields
            // keys_array is symbolic - we don't know actual keys, but we track them
            HashMapIntoIter | TrustMcMapIntoIter => {
                if args.is_empty() {
                    warn!("HashMap::into_iter requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                // Part of #1751: Use env_lookup to get the Array-sorted map expression,
                // matching how iter()/keys()/values() resolve. codegen_operand returns
                // a reference/pointer expression that lacks Array sort, causing panics.
                if let Some((base, map)) = self.resolve_collection_base(&args[0]) {
                    let iter = self.make_hashmap_into_iter(map, Some(&base));
                    self.assign_value_to_place(destination, iter);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            // HashMap::iter(&self) -> Iter<K, V> (Part of #1751)
            // Similar to into_iter but borrows instead of consuming
            HashMapIter => {
                if args.is_empty() {
                    warn!("HashMap::iter requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((base, map)) = self.resolve_collection_base(&args[0]) {
                    let iter = self.make_hashmap_into_iter(map, Some(&base));
                    self.assign_value_to_place(destination, iter);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            // HashMap::keys(&self) -> Keys<K, V> (Part of #1751)
            // Returns iterator over keys - modeled same as iter()
            HashMapKeys | HashMapValues => {
                if args.is_empty() {
                    warn!("HashMap::keys/values requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((base, map)) = self.resolve_collection_base(&args[0]) {
                    let iter = self.make_hashmap_into_iter(map, Some(&base));
                    self.assign_value_to_place(destination, iter);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            // partial dispatch: StubKind — parent dispatcher (stub_dispatch.rs) routes only
            // HashMap*/TrustMcMap*/BTreeMap* variants here; reaching this arm is a programming error.
            _other => {
                warn!(
                    ?_other,
                    "codegen_hashmap_stub: unexpected stub — update stub_dispatch.rs routing"
                );
                None
            }
        }
    }
}
