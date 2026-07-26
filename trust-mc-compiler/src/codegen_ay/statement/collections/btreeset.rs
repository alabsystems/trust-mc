// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BTreeSet semantic model for AY codegen.
//!
//! BTreeSet is modeled as `Array<Key, Bool>` - an element presence map.
//! This captures set membership semantics without tracking ordering.
//!
//! # Semantics
//!
//! - `new`: `const_array(KeySort, false)`, len = 0
//! - `insert`: `was_absent = !select(set, key); set' = store(set, key, true);`
//!   `len' = ite(was_absent, len + 1, len);` return `was_absent`
//! - `contains`: `select(set, key)`
//! - `remove`: `was_present = select(set, key); set' = store(set, key, false);`
//!   `len' = ite(was_present, len - 1, len);` return `was_present`
//! - `len`: return tracked len (or symbolic if not tracked)
//! - `is_empty`: `len == 0` (or symbolic if not tracked)
//! - `clear`: `set' = const_array(KeySort, false), len' = 0`
//! - `clone`: return same set and copy len (arrays are immutable in the model)
//!
//! # Limitations (Part of #1750)
//!
//! **Ordering is not modeled.** BTreeSet guarantees sorted iteration order
//! (elements are visited in ascending order), but our Array model has no
//! ordering semantics. This is a precision gap, not a soundness bug:
//!
//! - Membership queries (`contains`, `insert`, `remove`) work correctly
//! - Set cardinality (`len`, `is_empty`) works correctly
//! - Iteration order cannot be verified (iterators return elements in unknown order)
//! - Properties like "first element is minimum" cannot be verified
//! - Range queries (`range`, `first`, `last`) would need ordering theory
//!
//! For most verification use cases, membership semantics are sufficient.
//! If ordering verification is needed, consider using BTreeMap/BTreeSet
//! with explicit ordering assertions in the test code, or file an issue
//! to add ordered sequence theory support.
//!
//! Part of #1312: Collection stubs implementation.
//! Part of #1354: Statement module refactoring.

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};
use ay_bindings::Sort;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, trace, warn};

use super::super::StatementCodegen;
use crate::codegen_ay::names::struct_sort;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen BTreeSet operations (Part of #1312).
    ///
    /// BTreeSet is modeled as Array<Key, Bool> - element presence map.
    /// Operations delegate to shared set helpers in `set_common.rs` (Part of #2308).
    pub(in crate::codegen_ay::statement) fn codegen_btreeset_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        debug!(?stub_kind, %callee_path, "codegen_btreeset_stub");

        match stub_kind {
            StubKind::BTreeSetNew => {
                let key_sort =
                    self.infer_set_key_sort(destination, "BTreeSet").unwrap_or(ptr_sort());
                self.set_op_new("BTreeSet", key_sort, destination, target)
            }
            StubKind::BTreeSetInsert => self.set_op_insert("BTreeSet", args, destination, target),
            StubKind::BTreeSetContains => {
                self.set_op_contains("BTreeSet", args, destination, target)
            }
            StubKind::BTreeSetRemove => self.set_op_remove("BTreeSet", args, destination, target),
            StubKind::BTreeSetLen => self.set_op_len("BTreeSet", args, destination, target),
            StubKind::BTreeSetIsEmpty => {
                self.set_op_is_empty("BTreeSet", args, destination, target)
            }
            StubKind::BTreeSetClear => self.set_op_clear("BTreeSet", args, target),
            StubKind::BTreeSetClone => self.set_op_clone("BTreeSet", args, destination, target),
            StubKind::BTreeSetIntoIter => {
                self.set_op_iter("BTreeSet", "into_iter", args, destination, target)
            }
            StubKind::BTreeSetIter => {
                self.set_op_iter("BTreeSet", "iter", args, destination, target)
            }
            // partial dispatch: StubKind — parent dispatcher (stub_dispatch.rs) routes only
            // BTreeSet* variants here; reaching this arm is a programming error.
            _other => {
                warn!(
                    ?_other,
                    "codegen_btreeset_stub: unexpected stub — update stub_dispatch.rs routing"
                );
                None
            }
        }
    }

    /// Create a SetIntoIter struct for iterating over set elements (Part of #1751).
    ///
    /// Structure: (set: Array<K, Bool>, keys: Array<usize, K>, pos: usize, len: usize)
    /// - set: the original set array (presence map)
    /// - keys: symbolic array mapping indices to keys (we don't know actual keys)
    /// - pos: current position (starts at 0)
    /// - len: total number of elements (tracked length if available, otherwise symbolic >= 0)
    ///
    /// # Soundness: Membership Constraint (Part of #1751, Per Audit Report)
    ///
    /// We assert that all keys returned by the iterator are members of the set:
    /// `(forall i. i < len => select(set, select(keys, i)))`
    ///
    /// This ensures iterator soundness - every key yielded by iteration is
    /// actually present in the underlying set.
    #[must_use]
    pub(in super::super) fn make_set_into_iter(
        &mut self,
        set: ay_bindings::Expr,
        set_base: Option<&str>,
    ) -> ay_bindings::Expr {
        use ay_bindings::Expr;

        // Get key sort from the set's array sort (Array<K, Bool>)
        let key_sort = if let Some(arr) = set.sort().array_sort() {
            arr.index_sort.clone()
        } else {
            ptr_sort()
        };

        // Create symbolic keys array: Array<usize, K>
        let keys_name = self.ctx.fresh_name("set_iter_keys");
        let keys_sort = Sort::array(ptr_sort(), key_sort.clone());
        let keys = self.ctx.declare_var(&keys_name, keys_sort.clone());

        // Use tracked length if available, otherwise create symbolic >= 0
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let len = if let Some(base) = set_base {
            let len_name = crate::codegen_ay::names::len_name(&base);
            if let Some(tracked_len) = self.env_lookup(&len_name).cloned() {
                tracked_len
            } else {
                let len_name = self.ctx.fresh_name("set_iter_len");
                let len = self.ctx.declare_var(&len_name, ptr_sort());
                self.ctx.assert(len.clone().bvuge(zero.clone()));
                len
            }
        } else {
            let len_name = self.ctx.fresh_name("set_iter_len");
            let len = self.ctx.declare_var(&len_name, ptr_sort());
            self.ctx.assert(len.clone().bvuge(zero.clone()));
            len
        };

        // Part of #1751: Assert membership constraint for iterator soundness.
        // (forall i. i < len => select(set, select(keys, i)))
        // This ensures all keys yielded by the iterator are actually in the set.
        let idx_name = self.ctx.fresh_name("set_iter_idx");
        let idx = Expr::var(idx_name.clone(), ptr_sort());
        let in_bounds = idx.clone().bvult(len.clone());
        let key_at_i = keys.clone().select(idx);
        let key_in_set = set.clone().select(key_at_i);
        let body = in_bounds.implies(key_in_set);
        let membership_constraint = Expr::forall(vec![(idx_name, ptr_sort())], body);
        self.ctx.assert(membership_constraint);
        trace!("make_set_into_iter: asserted forall membership constraint");

        // Position starts at 0
        let pos = zero;

        // Build iterator sort name based on key sort
        let iter_sort_name = {
            let ks = crate::codegen_ay::names::sort_short_name(&key_sort);
            let mut s = String::with_capacity(13 + ks.len());
            s.push_str("SetIntoIter_");
            s.push_str(&ks);
            s
        };

        // Create iterator struct sort
        let iter_sort = struct_sort(
            iter_sort_name.clone(),
            crate::codegen_ay::names::hashset_iter_fields(set.sort().clone(), keys_sort),
        );

        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&iter_sort, &iter_sort_name);

        Expr::datatype_constructor(iter_sort_name, ctor_name, vec![set, keys, pos, len], iter_sort)
    }
}
