// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// HashMap iterator modeling helpers extracted from hashmap.rs for structural decomposition.
// Converted from include!() to module for #2306.

use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort, ptr_sort};
use ay_bindings::{Expr, Sort};
use tracing::trace;

use super::super::super::StatementCodegen;
use crate::codegen_ay::names::struct_sort;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Create a HashMapIntoIter struct for iterating over HashMap entries.
    /// (Part of #1751)
    ///
    /// Structure: (map: Array<K, Option<V>>, keys: Array<usize, K>, pos: usize, len: usize)
    /// - map: the original HashMap array
    /// - keys: symbolic array mapping indices to keys (we don't know actual keys)
    /// - pos: current position (starts at 0)
    /// - len: total number of entries (tracked length if available, otherwise symbolic >= 0)
    ///
    /// # Soundness: Membership Constraint (Part of #1751, Per Audit Report)
    ///
    /// We assert that all keys returned by the iterator map to Some values:
    /// `(forall i. i < len => is_some(select(map, select(keys, i))))`
    ///
    /// This ensures iterator soundness - every key yielded by iteration has
    /// a corresponding value in the underlying map.
    #[must_use]
    pub(super) fn make_hashmap_into_iter(&mut self, map: Expr, map_base: Option<&str>) -> Expr {
        // Get key and value sorts from the map's array sort
        let (key_sort, value_sort) = if let Some(arr) = map.sort().array_sort() {
            let key_sort = arr.index_sort.clone();
            // Value is Option<V>, extract V from it
            let value_sort = if let Some(dt) = arr.element_sort.datatype_sort() {
                dt.constructors
                    .iter()
                    .find(|c| crate::codegen_ay::names::is_some_constructor(&c.name))
                    .and_then(|c| c.fields.first())
                    .map_or_else(ptr_sort, |f| f.sort.clone())
            } else {
                ptr_sort()
            };
            (key_sort, value_sort)
        } else {
            (ptr_sort(), ptr_sort())
        };

        // Create symbolic keys array: Array<usize, K>
        let keys_name = self.ctx.fresh_name("hashmap_iter_keys");
        let keys_sort = Sort::array(ptr_sort(), key_sort.clone());
        let keys = self.ctx.declare_var(&keys_name, keys_sort.clone());

        // Part of #1744: Use tracked length if available, otherwise create symbolic >= 0
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let len = if let Some(base) = map_base {
            if let Some(tracked_len) = self.hashmap_len_symbols.get(base).cloned() {
                tracked_len
            } else {
                let len_name = self.ctx.fresh_name("hashmap_iter_len");
                let len = self.ctx.declare_var(&len_name, ptr_sort());
                self.ctx.assert(len.clone().bvuge(zero.clone()));
                len
            }
        } else {
            let len_name = self.ctx.fresh_name("hashmap_iter_len");
            let len = self.ctx.declare_var(&len_name, ptr_sort());
            self.ctx.assert(len.clone().bvuge(zero.clone()));
            len
        };

        // Part of #1751: Assert membership constraint for iterator soundness.
        // (forall i. i < len => is_some(select(map, select(keys, i))))
        // This ensures all keys yielded by the iterator have values in the map.
        let idx_name = self.ctx.fresh_name("hashmap_iter_idx");
        let idx = Expr::var(idx_name.clone(), ptr_sort());
        let in_bounds = idx.clone().bvult(len.clone());
        let key_at_i = keys.clone().select(idx);
        let value_at_key = map.clone().select(key_at_i);
        let is_some = self.option_is_some(&value_at_key);
        let body = in_bounds.implies(is_some);
        let membership_constraint = Expr::forall(vec![(idx_name, ptr_sort())], body);
        self.ctx.assert(membership_constraint);
        trace!("make_hashmap_into_iter: asserted forall membership constraint");

        // Position starts at 0
        let pos = zero;

        // Build iterator sort name based on key/value sorts
        let iter_sort_name = {
            let ks = crate::codegen_ay::names::sort_short_name(&key_sort);
            let vs = crate::codegen_ay::names::sort_short_name(&value_sort);
            let mut s = String::with_capacity(19 + ks.len() + vs.len());
            s.push_str("HashMapIntoIter_");
            s.push_str(&ks);
            s.push('_');
            s.push_str(&vs);
            s
        };

        // BMC path: construct a trivial presence array `Array(K, Bool)` where all
        // keys are present (true). The DT-based Option encoding tracks membership
        // via is_some/is_none, so the presence array is not semantically used here
        // but is required by the shared iterator field layout (Part of #3057).
        let present_sort = Sort::array(key_sort, bool_sort());
        let present = Expr::const_array(bool_sort(), Expr::bool_const(true));

        // Create iterator struct sort
        let iter_sort = struct_sort(
            iter_sort_name.clone(),
            crate::codegen_ay::names::hashmap_iter_fields(
                map.sort().clone(),
                present_sort,
                keys_sort,
            ),
        );

        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&iter_sort, &iter_sort_name);

        Expr::datatype_constructor(
            iter_sort_name,
            ctor_name,
            vec![map, present, keys, pos, len],
            iter_sort,
        )
    }
}
