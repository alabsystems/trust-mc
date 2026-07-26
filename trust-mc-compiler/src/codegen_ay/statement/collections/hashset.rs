// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! HashSet semantic model for AY codegen.
//!
//! HashSet is modeled as Array<Key, Bool> - an element presence map.
//! This captures set membership semantics without tracking hash behavior.
//!
//! Semantics:
//! - new: const_array(KeySort, false), len = 0
//! - insert: was_absent = !select(set, key); set' = store(set, key, true);
//!   len' = ite(was_absent, len + 1, len); return was_absent
//! - contains: select(set, key)
//! - remove: was_present = select(set, key); set' = store(set, key, false);
//!   len' = ite(was_present, len - 1, len); return was_present
//! - len: return tracked len (or symbolic if not tracked)
//! - is_empty: len == 0 (or symbolic if not tracked)
//! - clear: set' = const_array(KeySort, false), len' = 0
//! - clone: return same set and copy len (arrays are immutable in the model)
//!
//! Part of #1613: HashSet BMC stubs for perf suite.
//! Part of #1679: Length tracking for deduplication semantics.

use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::ptr_sort;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen HashSet operations (Part of #1613).
    ///
    /// HashSet is modeled as Array<Key, Bool> - element presence map.
    /// Operations delegate to shared set helpers in `set_common.rs` (Part of #2308).
    pub(in crate::codegen_ay::statement) fn codegen_hashset_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        debug!(?stub_kind, %callee_path, "codegen_hashset_stub");

        match stub_kind {
            StubKind::HashSetNew => {
                let key_sort =
                    self.infer_set_key_sort(destination, "HashSet").unwrap_or(ptr_sort());
                self.set_op_new("HashSet", key_sort, destination, target)
            }
            StubKind::HashSetInsert => self.set_op_insert("HashSet", args, destination, target),
            StubKind::HashSetContains => self.set_op_contains("HashSet", args, destination, target),
            StubKind::HashSetRemove => self.set_op_remove("HashSet", args, destination, target),
            StubKind::HashSetLen => self.set_op_len("HashSet", args, destination, target),
            StubKind::HashSetIsEmpty => self.set_op_is_empty("HashSet", args, destination, target),
            StubKind::HashSetClear => self.set_op_clear("HashSet", args, target),
            StubKind::HashSetClone => self.set_op_clone("HashSet", args, destination, target),
            StubKind::HashSetIntoIter => {
                self.set_op_iter("HashSet", "into_iter", args, destination, target)
            }
            StubKind::HashSetIter => self.set_op_iter("HashSet", "iter", args, destination, target),
            // partial dispatch: StubKind — parent dispatcher (stub_dispatch.rs) routes only
            // HashSet* variants here; reaching this arm is a programming error.
            _other => {
                warn!(
                    ?_other,
                    "codegen_hashset_stub: unexpected stub — update stub_dispatch.rs routing"
                );
                None
            }
        }
    }
}
