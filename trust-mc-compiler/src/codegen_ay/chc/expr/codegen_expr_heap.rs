// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Heap pointer operations and memory safety checks for CHC codegen.
//!
//! Extracted from codegen_expr.rs per #2129 decomposition.
//! Handles: heap metadata arrays, bitvector utilities for allocation checks,
//! pointer splitting, heap access validity checks, and error rule emission.
//!
//! Migrated from include!() to proper module.
//! Part of #2306: include!() to proper module migration.

use ay_bindings::{Expr, ExprValue, Sort};
use std::collections::HashSet;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use tracing::{debug, warn};
use trust_mc_core::chc::{RelationApp, Rule, RuleBody};
use trust_mc_core::violation::PropertyKind;

use crate::codegen_ay::chc::stmt::codegen_stmt_store::model_object_literal_lane;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, bool_sort, coerce_bitvec_width_safe};

use super::ChcCtx;
use super::codegen_ctx::diagnostics::{CellCounter, GLOBAL_COUNTERS};
use super::memory_model::MemPtr;

/// FailClose: a bounds check through a symbolic object lane was encoded before
/// an allocation that may run first (`record_symbolic_lane_bound_completeness`).
pub(in crate::codegen_ay::chc) const SYMBOLIC_LANE_BOUND_INCOMPLETE: &str =
    "symbolic_lane_bound_incomplete";

/// SoundHavoc, recorded unaccounted: an integer-to-pointer lane
/// (`CastKind::PointerWithExposedProvenance`, the `without_provenance` stubs)
/// invalidated `obj_valid` of the object its result names, and that object is
/// not the null object. See [`ChcCtx::invalidate_int_to_ptr_object`].
pub(in crate::codegen_ay::chc) const INT_TO_PTR_OBJ_INVALIDATED: &str =
    "int_to_ptr_obj_invalidated";

/// FailClose: an object an integer-to-pointer result named by a constant object
/// lane is accessed, and its validity is not the invalidation's to decide: the
/// model treats its accesses as always valid (a stack slot, a provably-valid
/// collection backing), or it was allocated after the cast. Recorded at such an
/// access, or at the cast when such an access was encoded before it. See
/// [`ChcCtx::invalidate_int_to_ptr_object`].
pub(in crate::codegen_ay::chc) const INT_TO_PTR_NAMES_ALWAYS_VALID_OBJECT: &str =
    "int_to_ptr_names_always_valid_object";

/// Get the current number of untranslatable heap safety check conservative error rules.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_heap_check_untranslatable_count() -> usize {
    GLOBAL_COUNTERS.heap_check_untranslatable.load(Ordering::Relaxed)
}

/// Get the current number of conservative heap checks due to unknown type layout.
/// Delegates to GLOBAL_COUNTERS (Part of #2906).
pub(in crate::codegen_ay) fn get_chc_heap_check_unknown_layout_count() -> usize {
    GLOBAL_COUNTERS.heap_check_unknown_layout.load(Ordering::Relaxed)
}

// =========================================================================
// Heap metadata array sort and variable constructors.
//
// The split-pointer heap model uses two metadata arrays:
//   obj_valid: Array(BV32, Bool)  — tracks which allocations are alive
//   obj_size:  Array(BV32, BV32)  — tracks allocation sizes
//
// CHC rules thread these through SSA-style in/out pairs. These helpers
// centralise the sort and variable construction that was previously
// repeated 20+ times across stubs_alloc, codegen_stmt_rvalue,
// codegen_rules_entry, codegen_rules_helpers, and codegen_decl_state_vars.
// Part of #2267: allocation debt reduction.
// =========================================================================

/// Sort for the obj_valid metadata array: `(Array (_ BitVec 32) Bool)`.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_valid_sort() -> Sort {
    Sort::array(Sort::bitvec(32), bool_sort())
}

/// Sort for the obj_size metadata array: `(Array (_ BitVec 32) (_ BitVec 32))`.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_size_sort() -> Sort {
    Sort::array(Sort::bitvec(32), Sort::bitvec(32))
}

/// Input `obj_valid` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_valid_in() -> Expr {
    Expr::var("obj_valid", obj_valid_sort())
}

/// Output `obj_valid__out` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_valid_out() -> Expr {
    Expr::var("obj_valid__out", obj_valid_sort())
}

/// Input `obj_size` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_size_in() -> Expr {
    Expr::var("obj_size", obj_size_sort())
}

/// Output `obj_size__out` variable for the current CHC rule.
#[must_use]
pub(in crate::codegen_ay::chc) fn obj_size_out() -> Expr {
    Expr::var("obj_size__out", obj_size_sort())
}

/// Whether `expr` mentions the variable `name`.
fn expr_mentions_var(expr: &Expr, name: &str) -> bool {
    let mut stack = vec![expr.clone()];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name: var } = node.value()
            && var == name
        {
            return true;
        }
        stack.extend(node.children().cloned());
    }
    false
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Returns the current obj_valid array expression (uses __out when this
    /// block has written `obj_valid`).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn current_obj_valid_array(&self) -> Expr {
        if self.heap_state.is_obj_valid_modified() { obj_valid_out() } else { obj_valid_in() }
    }

    /// Returns the current obj_size array expression (uses __out when this
    /// block has written `obj_size`). Per lane: a block that only invalidated
    /// a pointer's `obj_valid` leaves `obj_size` at its input variable.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn current_obj_size_array(&self) -> Expr {
        if self.heap_state.is_obj_size_modified() { obj_size_out() } else { obj_size_in() }
    }

    /// Invalidate `obj_id` in `obj_valid` through `heap_state.pending_updates`
    /// and mark only that lane modified.
    ///
    /// Chains on this rule's earlier pending definition of `obj_valid__out`
    /// when there is one (another invalidation, a `Box` allocation): that
    /// definition is replaced by `obj_valid__out = store(E, obj_id, false)`.
    /// Pushing a second equation built on `current_obj_valid_array()` instead
    /// gave `obj_valid__out = store(obj_valid__out, obj_id, false)` beside
    /// `obj_valid__out = store(obj_valid, a, false)`, which forces the INPUT
    /// `obj_valid[obj_id]` to false: with two integer-to-pointer casts into
    /// different objects in one block, that made the rule infeasible and the
    /// harness VACUOUS (`heap_metadata_lane_dual.rs::bug_two_int2ptr_casts_then_box`).
    pub(in crate::codegen_ay::chc) fn push_pending_obj_valid_invalidation(&mut self, obj_id: Expr) {
        let out = obj_valid_out();
        let prior = self.pending_obj_valid_definition();
        let base = self.pending_obj_valid_chain();
        let def = out.eq(base.store(obj_id, Expr::bool_const(false)));
        match prior {
            Some(i) => self.heap_state.pending_updates[i] = def,
            None => self.heap_state.pending_updates.push(def),
        }
        self.mark_obj_valid_modified();
    }

    /// Invalidate the object an integer-to-pointer result names (#3350, #3361).
    ///
    /// `obj_valid` starts all-true, so a pointer made from an integer would
    /// otherwise pass the validity check of a never-allocated object. The
    /// model has no set of exposed allocations, so the lane cannot tell an
    /// address that names a live object (`with_exposed_provenance(p.addr() +
    /// 2)`, `(p as usize) as *const T`, an address joined from two `u32`
    /// halves) from one that names nothing: it invalidates whatever object the
    /// result's object lane names. For a live object that is fail-closed, not
    /// exact: the object's every later access fails memory safety, where Kani
    /// (whose integer casts keep the pointer's bits) proves the program.
    ///
    /// The null object (a constant lane whose object field is 0: `0x1000 as
    /// *const u8`, `0x2_0000_0000 as *const u8`, `ptr::null()`, `dangling()`)
    /// holds no allocation, so invalidating it is exact and records nothing. Any other lane records
    /// [`INT_TO_PTR_OBJ_INVALIDATED`], unaccounted: the invalidation only adds
    /// violations, so a proof stands (SoundHavoc), but no counterexample in the
    /// harness is certified Genuine on its strength. The BMC lane records the
    /// same (`pointer_with_exposed_provenance`, codegen_assign_ref.rs). Main
    /// recorded nothing here; a harness whose only other reason was a dropped
    /// store (fixed on fix/chc-lost-writes) had its memory-safety failure
    /// certified Genuine (review round 3, finding 1).
    ///
    /// Why not exact: the model cannot tell an integer derived from a live
    /// object's address from one that merely equals it. Without the
    /// invalidation a nondeterministic or computed integer whose high word
    /// happens to be a live object's number would read that object, where Kani
    /// reports an invalid pointer. An access through a symbolic object lane is
    /// bounded by the object's size (`heap_access_checks`, review of
    /// fix/chc-lost-writes lostwrite round 1, finding 4), which catches an
    /// out-of-bounds round trip on its own, but not a pointer naming the wrong
    /// object in bounds.
    ///
    /// `source`: the integer operand. A LITERAL address whose high word names
    /// a model object (`0x1_0000_1000 as *const u8`) carries no provenance
    /// and names no object in Kani, so invalidating the model's object of
    /// that number is wrong both ways: a later access of that real object
    /// fails, and the invalidation does not reach a stack local (always
    /// valid), so a read through the literal pointer succeeded on main. Such a
    /// pointer invalidates nothing and records nothing here; the untyped-view
    /// net 3 fails it closed wherever it may be read
    /// (`const_pointer_names_model_object`), so only a harness that never
    /// reads through it keeps its proof or its certificate.
    ///
    /// A COMPUTED integer whose value is a constant naming a stack slot or a
    /// provably-valid collection backing (`(5usize << 32) as *const u32`,
    /// `transmute::<usize, *const u32>(k << 32)`, a `const fn` result) is no
    /// literal for net 3, and the invalidation does not reach such an object:
    /// `heap_access_checks` takes its validity to be `true` without reading
    /// `obj_valid`. The read or write through the pointer verified SUCCESSFUL
    /// clean, where Kani reports "invalid integer address" (review of
    /// fix/chc-lost-writes, lostwrite track round 1, findings 1 and 9; on main
    /// in a body that exposes no address, and on the branch in one that does,
    /// once `int_to_ptr_value_of_operand` kept the constant lane). The model
    /// cannot tell such a constant from the identity term of a slot whose
    /// address a walked callee exposed with no tracked base
    /// (`ptr_to_int_value`), so every access to that object encoded after the
    /// cast reads `obj_valid` after all (`int_to_ptr_named_lanes`) and fails
    /// closed: [`INT_TO_PTR_NAMES_ALWAYS_VALID_OBJECT`]. An access encoded
    /// BEFORE the cast took the slot's validity as given, and a loop may run it
    /// after the cast, so such an access makes the cast itself fail closed.
    /// The rule was harness-wide at the cast in round 1, which failed a
    /// program that only compares the pointer closed (review of
    /// fix/chc-lost-writes, lostwrite track round 2, finding 3).
    ///
    /// A constant lane that names NO object yet (an id the harness allocates
    /// after the cast) is invalidated before the object exists, and the
    /// allocation re-validates it (round 2, finding 5). An access through such
    /// a lane after the object is allocated fails closed the same way, and an
    /// access encoded before the cast does at the cast. (The review's
    /// `bug_int_ptr_lane1_then_vec`, which verified SUCCESSFUL on main and round
    /// 1 where Kani reports an invalid integer address, names a stack slot: its
    /// invalidation was lost to the allocating call of the same block, which
    /// `compose_heap_metadata_definitions` now keeps.)
    pub(in crate::codegen_ay::chc) fn invalidate_int_to_ptr_object(
        &mut self,
        obj_id: Expr,
        source: Option<&rustc_public::mir::Operand>,
    ) {
        // A computed constant (`hi << 32`) folds only through the full
        // evaluator, not `const_obj_id_u32`'s.
        let lane = Self::const_obj_id_u32(&obj_id).or_else(|| {
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&obj_id)
                .and_then(|folded| Self::const_obj_id_u32(&folded))
        });
        if let Some(high) = source.and_then(model_object_literal_lane)
            && lane == Some(high)
        {
            debug!(lane = high, "CHC: a literal address naming a model object invalidates nothing");
            return;
        }
        // The null object is the lane's object FIELD 0 (heap/stack_address.rs:
        // the lane is the 48-bit offset's high 16 bits over the 16-bit object
        // field, and an integer becomes the identity whose address it is,
        // `int_to_ptr_value`). A literal like `0x2_0000_0000`, or `(6usize <<
        // 32) as *const u32`, is object 0 at a 48-bit offset, an address no
        // object owns, as in Kani: invalidating it is exact and records nothing.
        // An access through it fails either way, by the constant lane's own
        // check or, once the lane is carried into another block, by this
        // invalidation. A lane at or past OBJECT_ID_LIMIT whose object field is
        // not 0 names an object in the far model: a far pointer of it (the
        // FAR_BIT), or a pointer at least 2^32 bytes past its start, which a
        // wrapping step can bring back into the object. Its invalidation
        // records the reason (fail closed).
        let no_object = lane.is_some_and(|id| id & 0xFFFF == 0);
        self.push_pending_obj_valid_invalidation(obj_id);
        if !no_object {
            self.record_sound_fallback_reason(INT_TO_PTR_OBJ_INVALIDATED);
        }
        if let Some(id) = lane
            && !no_object
        {
            let allocated = self.heap_state.alloc_block.contains_key(&id)
                || self.heap_state.local_idx_for_obj_id(id).is_some()
                || self.heap_state.is_provably_valid_backing(id)
                || self.heap_state.heap_alloc_size(id).is_some();
            let named = self.heap_state.int_to_ptr_named_lanes.entry(id).or_insert(allocated);
            *named &= allocated;
            let accessed_before = if allocated {
                self.heap_state.assumed_valid_lanes.borrow().contains(&id)
            } else {
                self.heap_state.accessed_const_lanes.borrow().contains(&id)
            };
            if accessed_before {
                debug!(
                    lane = id,
                    allocated,
                    "CHC: an integer-to-pointer result names an object an earlier-encoded access \
                     took as valid; fail closed"
                );
                self.record_sound_fallback_reason(INT_TO_PTR_NAMES_ALWAYS_VALID_OBJECT);
            }
        }
    }

    /// Index of this rule's pending definition `obj_valid__out = E` (E not
    /// reading `obj_valid__out`), the one [`Self::push_pending_obj_valid_invalidation`]
    /// chains on.
    fn pending_obj_valid_definition(&self) -> Option<usize> {
        let out = obj_valid_out();
        self.heap_state.pending_updates.iter().rposition(|c| {
            matches!(c.value(), ExprValue::Eq(lhs, rhs)
                if *lhs == out && !expr_mentions_var(rhs, "obj_valid__out"))
        })
    }

    /// The running `obj_valid` of this rule: the right side of its pending
    /// definition when there is one (an earlier free or allocation in the
    /// same rule), else [`Self::current_obj_valid_array`]. A check of an
    /// object's validity made after such an update must read this, or it
    /// misses the update (a second free of one object in one walk).
    pub(in crate::codegen_ay::chc) fn pending_obj_valid_chain(&self) -> Expr {
        match self
            .pending_obj_valid_definition()
            .map(|i| self.heap_state.pending_updates[i].value())
        {
            Some(ExprValue::Eq(_, rhs)) => rhs.clone(),
            _ => self.current_obj_valid_array(),
        }
    }

    /// Coerces a bitvec expression to 32-bit for the split-pointer heap model.
    ///
    /// The heap metadata arrays (`obj_size`, `obj_valid`) use BV32 indices and values
    /// because the split-pointer model represents object IDs and sizes as 32-bit.
    /// This function is intentionally lossy for widths > 32 (truncates high bits).
    /// Returns `None` if the expression is not a bitvec sort.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn coerce_to_heap_bv32(&self, expr: Expr) -> Option<Expr> {
        let expr = coerce_bitvec_width_safe(expr, 32, SignExtension::ZeroExtend);
        expr.sort().bitvec_width().map(|_| expr)
    }

    /// Builds a check that the upper bits of a bitvector are zero when width > 32.
    ///
    /// Used alongside [`coerce_to_heap_bv32`] in the split-pointer heap model:
    /// the coercion truncates, and this function produces the safety assertion
    /// that the truncation was lossless (high bits were zero).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn fits_in_bv32_check(&self, expr: &Expr) -> Option<Expr> {
        let width = expr.sort().bitvec_width()?;
        if width <= 32 {
            return None;
        }
        let high = expr.clone().extract(width - 1, 32);
        let zero = Expr::bitvec_const(0, width - 32);
        Some(high.eq(zero))
    }

    /// Builds a non-zero check for a bitvector expression.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn nonzero_bv_check(
        &self,
        expr: Expr,
        width: u32,
    ) -> Option<Expr> {
        let expr = coerce_bitvec_width_safe(expr, width, SignExtension::ZeroExtend);
        expr.sort().bitvec_width()?;
        let zero = Expr::bitvec_const(0, width);
        Some(expr.eq(zero).not())
    }

    /// Builds a power-of-two check for a bitvector expression.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn power_of_two_bv_check(
        &self,
        expr: Expr,
        width: u32,
    ) -> Option<Expr> {
        let expr = coerce_bitvec_width_safe(expr, width, SignExtension::ZeroExtend);
        expr.sort().bitvec_width()?;
        let one = Expr::bitvec_const(1, width);
        let minus_one = expr.clone().bvsub(one);
        let and_mask = expr.bvand(minus_one);
        let zero = Expr::bitvec_const(0, width);
        Some(and_mask.eq(zero))
    }

    /// Splits a pointer into (obj_id, offset) using the split-pointer model.
    ///
    /// The split-pointer model is designed for 64-bit pointers:
    /// - Upper 32 bits: object ID
    /// - Lower 32 bits: offset within object
    ///
    /// Non-64-bit pointers return None. 32-bit pointers cannot be sensibly
    /// split (zero-extending would make all obj_ids = 0, which is unsound).
    /// See #1205.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn split_pointer(&self, addr: &Expr) -> Option<(Expr, Expr)> {
        let width = addr.sort().bitvec_width()?;
        if width != 64 {
            return None;
        }
        Some((addr.clone().extract(63, 32), addr.clone().extract(31, 0)))
    }

    pub(in crate::codegen_ay::chc) fn const_obj_id_u32(obj_id: &Expr) -> Option<u32> {
        super::codegen_expr_heap_bv_eval::const_obj_id_u32(obj_id)
    }

    /// The size of the object a NON-CONSTANT object lane names, for the
    /// bounds check of an access through it.
    ///
    /// Such a lane comes from a pointer the encoder cannot resolve to one
    /// object: a step of the wrapping family (`p.wrapping_add(2)` is an exact
    /// full-width step, so the lane stops folding), `with_addr` / `map_addr`,
    /// a slice made by `slice::from_raw_parts` with a length the allocation
    /// may not hold, an integer turned into a pointer by a transmute or a
    /// union, a pointer loaded from memory. The check used to skip the bounds
    /// for every such lane ("unconstrained obj_id"), so a read or write past
    /// the end of a `Box`, a static or a `Vec` buffer through one of them
    /// verified clean where Kani reports "pointer outside object bounds"
    /// (review of fix/chc-lost-writes, lostwrite round 1, findings 2 and 4).
    ///
    /// The lane is the object's number, so the size is a choice over the
    /// objects that number can be: each stack slot whose address the body
    /// takes, each heap allocation of a known size, each heap allocation of a
    /// symbolic size (whose size is `obj_size` at that allocation's constant
    /// id, where the allocator stores it), each static, and each global object
    /// of a known length (a constant's referent: `static S: [&[u8]; 2] =
    /// [b"abcdefghij", ..]` stepped by `wrapping_add(10)` past its slice read
    /// clean, lostwrite track round 1, finding 9). Any other lane gets size 0,
    /// which the caller's zero-size exemption leaves unbounded, as before:
    /// null, a number no object has, and an object the encoder records no size
    /// for (a static without a layout, an address a model makes up for a
    /// value, a walked callee's local). Reading the size from `obj_size[lane]`
    /// instead made the metadata array a state variable of every relation,
    /// and trivial programs timed out (kani/Transparent/transparent1.rs: 0.3 s
    /// to 36 s); falling back to `obj_size[lane]` whenever an object without a
    /// recorded size existed put a symbolic-index select in every such check,
    /// and a walked `Box<dyn Send>` drop that ay answered in 3.6 s timed out
    /// (`test_nested_box_dyn_drop_solver_produces_unsat`). An allocation made
    /// later in encoding order, in a block that may run before the access, is
    /// not in the choice: `record_symbolic_lane_bound_completeness` fails such
    /// a harness closed once every block is encoded.
    ///
    /// The bound is certifiable. Every size in the choice is the record a
    /// constant-lane access to the same object is bounded by: a stack slot's
    /// layout, the size a heap allocator stored, a global object's allocation
    /// length (each object minted once, from the one id counter, so no two
    /// kinds share a number). A first cut certified only the stack half and
    /// wrapped the rest as `bound ∨ t` for a freed `t`, after the 737-unit run
    /// found two wrong records (an `Rc` inner sized without its header, a
    /// static's `&str` referent sized one byte); both records are fixed (the
    /// inner size here, the referent by main's const-pointer rule, D3). The
    /// wrapper cost true out-of-bounds reads their certificates and slowed the
    /// solver (`bug_dyn_from_call_oob`, `splice_value_pass`,
    /// `test_nested_box_dyn_drop_solver_produces_unsat`, lostwrite track round
    /// 1, findings 4 to 6), and its freed variable made every counterexample
    /// through such an access uncertified.
    pub(in crate::codegen_ay::chc) fn symbolic_lane_bounds(
        &self,
        obj_id: &Expr,
        end_offset: &Expr,
    ) -> Vec<Expr> {
        let size = self.symbolic_lane_size(obj_id);
        if matches!(size.value(), ExprValue::BitVecConst { .. }) {
            return Vec::new();
        }
        let zero = Expr::bitvec_const(0u64, 32);
        vec![Expr::or(size.clone().eq(zero), end_offset.clone().bvule(size))]
    }

    /// The size a bounds check takes for heap object `id` of recorded size
    /// `bytes`: the constant, or `ite(t, 0, bytes)` under the freed `t` of a
    /// `Vec::with_capacity` buffer whose `Vec` may grow
    /// (`taint_vec_capacity_size`).
    fn recorded_heap_size_expr(&self, id: u32, bytes: u32) -> Expr {
        let size = Expr::bitvec_const(i128::from(bytes), 32);
        match self.heap_state.vec_capacity_size_taints.get(&id) {
            Some(taint) => Expr::ite(taint.clone(), Expr::bitvec_const(0u64, 32), size),
            None => size,
        }
    }

    /// Whether an object lane is built from a fresh value the walker made up
    /// for a read it failed closed on (`havoc_for_place`). The harness then
    /// carries a FailClose reason, so no proof is claimed and no failure is
    /// certified, and bounding the made-up pointer only adds violations of a
    /// value the program never holds: the walked drop of a nested
    /// `Box<dyn Send>` read its inner box through one, its bound was violated
    /// at a made-up lane, and ay withheld the model it could not validate
    /// (`test_nested_box_dyn_drop_solver_produces_unsat`, lostwrite track
    /// round 1, finding 6).
    pub(in crate::codegen_ay::chc) fn lane_is_fail_closed_havoc(&self, obj_id: &Expr) -> bool {
        let havocs = &self.heap_state.fail_closed_havocs;
        if havocs.is_empty() {
            return false;
        }
        let mut stack = vec![obj_id];
        while let Some(node) = stack.pop() {
            if let ExprValue::Var { name } = node.value()
                && havocs.contains(&**name)
            {
                return true;
            }
            stack.extend(node.children());
        }
        false
    }

    /// The size choice of [`Self::symbolic_lane_bounds`]: the size of the
    /// object the lane names, 0 for a lane naming no object of a recorded
    /// size.
    fn symbolic_lane_size(&self, obj_id: &Expr) -> Expr {
        let next_id = self.heap_state.next_alloc_id;
        self.heap_state.symbolic_lane_checks.borrow_mut().push((self.current_encode_bb, next_id));
        let address_taken = self.heap_state.address_taken_locals.get_or_init(|| {
            use rustc_public::mir::{ProjectionElem, Rvalue, StatementKind};
            self.body
                .blocks
                .iter()
                .flat_map(|b| b.statements.iter())
                .filter_map(|st| match &st.kind {
                    StatementKind::Assign(
                        _,
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place),
                    ) if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) => {
                        Some(place.local)
                    }
                    _ => None,
                })
                .collect()
        });
        let mut sizes: Vec<(u32, Expr)> = Vec::new();
        // Global objects (constants' referents, statics) of a known length,
        // numbered before translation, that the harness reads: the targets of
        // its constant pointers (`object_read_types`). A global no constant
        // pointer of the harness reaches (a thread-local the runtime keeps,
        // a panic message) is no lane's object, and its arm only cost the
        // solver: `bug_dyn_from_call_oob` went from certified in 3 s to
        // Unknown at 30 s with one such arm (lostwrite track round 1).
        let read_globals: HashSet<u32> = self
            .ref_resolution
            .object_read_types
            .iter()
            .filter(|(_, tys)| !tys.is_empty())
            .filter_map(|(key, _)| self.ref_resolution.global_objects.get(key))
            .map(|object| object.obj_id)
            .collect();
        let mut global_sizes: std::collections::BTreeMap<u32, u32> = self
            .ref_resolution
            .global_objects
            .values()
            .filter(|object| read_globals.contains(&object.obj_id))
            .filter_map(|object| Some((object.obj_id, u32::try_from(object.size?).ok()?)))
            .filter(|(id, _)| *id != 0)
            .collect();
        let size_const = |bytes: u32| Expr::bitvec_const(i128::from(bytes), 32);
        for id in 1..next_id {
            let global_size = global_sizes.remove(&id);
            if let Some(local) = self.heap_state.local_idx_for_obj_id(id) {
                if address_taken.contains(&local)
                    && let Some(size) = self.heap_state.heap_alloc_size(id)
                {
                    sizes.push((id, size_const(size)));
                }
                continue;
            }
            if let Some(&(_, size, _)) =
                self.ref_resolution.static_alloc_sizes.iter().find(|(sid, _, _)| *sid == id)
            {
                sizes.push((id, size_const(size)));
            } else if self.is_heap_object_id(id) {
                if let Some(size) = self.heap_state.heap_alloc_size(id) {
                    sizes.push((id, self.recorded_heap_size_expr(id, size)));
                } else if self.heap_state.symbolic_size_heap_ids.contains(&id) {
                    let id_expr = size_const(id);
                    sizes.push((id, self.current_obj_size_array().select(id_expr)));
                }
            } else if let Some(size) = self.heap_state.heap_alloc_size(id).or(global_size) {
                sizes.push((id, size_const(size)));
            }
        }
        sizes.extend(global_sizes.into_iter().map(|(id, size)| (id, size_const(size))));
        debug!(
            %obj_id,
            objects = sizes.len(),
            "CHC: symbolic object lane bounded by a size choice"
        );
        let mut size = size_const(0);
        for (id, bytes) in sizes.into_iter().rev() {
            let is_id = obj_id.clone().eq(size_const(id));
            size = Expr::ite(is_id, bytes, size);
        }
        size
    }

    /// Fail the harness closed when a heap allocation made later in encoding
    /// order than a symbolic-lane bounds check (`symbolic_lane_bounds`),
    /// in a block that may run before the check's block, was left out of the
    /// check's choice of sizes: an access through such a lane into that object
    /// is not bounded.
    pub(in crate::codegen_ay::chc) fn record_symbolic_lane_bound_completeness(&mut self) {
        let checks = self.heap_state.symbolic_lane_checks.borrow().clone();
        if checks.is_empty() {
            return;
        }
        let late: Vec<(u32, usize)> =
            self.heap_state.alloc_block.iter().map(|(&id, &bb)| (id, bb)).collect();
        let mut reach: std::collections::HashMap<usize, Vec<bool>> = Default::default();
        for (check_bb, next_id) in checks {
            for &(id, alloc_bb) in &late {
                // Only an object the choice would have bounded: one of a
                // known or a symbolic size.
                let sized = self.heap_state.heap_alloc_size(id).is_some()
                    || self.heap_state.symbolic_size_heap_ids.contains(&id);
                if id < next_id || !sized || !self.is_heap_object_id(id) {
                    continue;
                }
                let row = reach
                    .entry(alloc_bb)
                    .or_insert_with(|| self.blocks_reached_after_an_edge(alloc_bb));
                if alloc_bb == check_bb || row.get(check_bb).copied().unwrap_or(true) {
                    debug!(
                        id,
                        alloc_bb,
                        check_bb,
                        "CHC: a symbolic-lane bound left out a later allocation"
                    );
                    self.record_sound_fallback_reason(SYMBOLIC_LANE_BOUND_INCOMPLETE);
                    return;
                }
            }
        }
    }

    /// Generates heap validity/bounds checks for a memory access.
    ///
    /// Part of #1860: When wide memory model is enabled, also generates
    /// WideMemManager bounds checks using `is_dereferenceable`.
    pub(in crate::codegen_ay::chc) fn heap_access_checks(
        &self,
        addr: Expr,
        pointee_ty: rustc_public::ty::Ty,
    ) -> Vec<Expr> {
        let Some((obj_id, offset)) = self.split_pointer(&addr) else {
            // Part of #2965: Fail-closed when pointer cannot be split (non-64-bit).
            // Emit `false` so the solver produces CTREX rather than an unconstrained
            // proof. Consistent with the unknown-alignment fail-closed pattern below.
            let count = self.diagnostics.heap_check_untranslatable.inc_get();
            warn!(
                count,
                addr_sort = ?addr.sort(),
                "heap_access_checks: cannot split non-64-bit pointer, emitting fail-closed check"
            );
            return vec![Expr::bool_const(false)];
        };

        let mut checks = Vec::new();
        // Stack locals are allocated at function entry and tracked in local_addresses.
        // For those IDs, derive bounds directly from local layout and avoid dependency
        // on metadata array propagation through unrelated calls.
        let const_obj_id = Self::const_obj_id_u32(&obj_id);
        let stack_obj_size = const_obj_id
            .and_then(|id| self.heap_state.local_idx_for_obj_id(id))
            .and_then(|local_idx| self.body.locals().get(local_idx))
            .and_then(|local_decl| self.get_type_size(local_decl.ty))
            .and_then(|size| u32::try_from(size).ok());

        // Stack locals are valid for the whole function and are not represented
        // by heap dealloc state. If this remains as obj_valid[obj_id], later
        // scalarization rewrites non-tracked constant IDs to an unconstrained
        // select_any value, which creates spurious UAF counterexamples.
        //
        // The same spurious-UAF hazard applies to the fresh backing buffer of a
        // provably-valid over-approximated collection constructor (into_vec /
        // bounded_any …): its `obj_valid[id]` select rides a free
        // `obj_valid__out` in the check rule. These allocations are known-live
        // under safe-Rust preconditions, so treat them as trivially valid.
        // SOUNDNESS: `Vec::from_raw_parts` pointers are never registered as
        // provably-valid backings, so a genuinely-dangling Vec still fails.
        let is_provably_valid_backing =
            const_obj_id.is_some_and(|id| self.heap_state.is_provably_valid_backing(id));
        // The allocation a symbolic lane's object bits name (see the bound
        // below); a stack local is valid for the whole function.
        let lane_object = if const_obj_id.is_none() && addr.sort().bitvec_width() == Some(64) {
            let object = addr.clone().extract(46, 32);
            let object =
                trust_mc_core::chc_const_prop::eval::try_eval_to_const(&object).unwrap_or(object);
            Self::const_obj_id_u32(&object)
                .filter(|&id| id != 0 && id < self.heap_state.next_alloc_id)
        } else {
            None
        };
        let lane_object_on_stack =
            lane_object.is_some_and(|id| self.heap_state.local_idx_for_obj_id(id).is_some());
        // An integer-to-pointer result named this object by a constant lane
        // and invalidated it (`invalidate_int_to_ptr_object`): read `obj_valid`,
        // and fail closed where the invalidation does not decide the object's
        // validity (an always-valid object, or one allocated after the cast).
        // The object a symbolic lane's object bits name is that object here
        // too: an access to it took its validity as given just the same.
        let always_valid = stack_obj_size.is_some() || is_provably_valid_backing || lane_object_on_stack;
        let named_id = const_obj_id.or(lane_object);
        let named_by_int_to_ptr =
            named_id.and_then(|id| self.heap_state.int_to_ptr_named_lanes.get(&id).copied());
        if let Some(id) = named_id {
            self.heap_state.accessed_const_lanes.borrow_mut().insert(id);
        }
        if always_valid && named_by_int_to_ptr.is_none() {
            if let Some(id) = named_id {
                self.heap_state.assumed_valid_lanes.borrow_mut().insert(id);
            }
            checks.push(Expr::bool_const(true));
        } else {
            if let Some(allocated_at_cast) = named_by_int_to_ptr
                && (always_valid || !allocated_at_cast)
            {
                debug!(
                    obj_id = ?const_obj_id,
                    always_valid,
                    allocated_at_cast,
                    "CHC: access to an object an integer-to-pointer result named; fail closed"
                );
                self.record_sound_fallback_reason(INT_TO_PTR_NAMES_ALWAYS_VALID_OBJECT);
            }
            let obj_valid = self.current_obj_valid_array();
            checks.push(obj_valid.select(obj_id.clone()));
        }

        // Part of #3159: Detect dyn Trait pointee types. Dyn trait types are
        // unsized — their layout is resolved at runtime via the vtable, not at
        // compile time. The allocation side already records obj_size = 0 for
        // these (with zero-size exemptions). The access side must skip the
        // fail-closed checks to avoid unconditional Genuine CTREX.
        let is_dyn_trait_pointee = matches!(
            pointee_ty.kind(),
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Dynamic(..))
        );

        // Part of #3495: Detect Slice(T) pointee types. Slices are unsized —
        // get_type_size/get_type_align return None for [T]. But element accesses
        // have known size/alignment from the element type T. Extract T and use
        // its layout instead of emitting fail-closed false.
        // Part of #3655: str is layout-identical to [u8] — treat it as
        // Slice(u8) for heap access checks (element size=1, alignment=1).
        // Without this, heap_access_checks emits fail-closed false for str,
        // causing unconditional Genuine CTREX on Box<str> drop.
        let slice_elem_ty = match pointee_ty.kind() {
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Slice(elem_ty)) => {
                Some(elem_ty)
            }
            rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Str) => {
                // str is [u8] under the hood — use u8 as the element type.
                Some(rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8))
            }
            _ => None,
        };

        // Resolve effective alignment: use element type for slices.
        let effective_align = self
            .get_type_align(pointee_ty)
            .or_else(|| slice_elem_ty.and_then(|ety| self.get_type_align(ety)));

        match effective_align {
            Some(align) if align > 1 => {
                let align_expr = Expr::bitvec_const(align as i128, 32);
                let rem = offset.clone().bvurem(align_expr);
                let zero = Expr::bitvec_const(0, 32);
                checks.push(rem.eq(zero));
            }
            Some(_) => {} // align <= 1: no alignment check needed
            None if is_dyn_trait_pointee => {
                // Part of #3159: dyn Trait alignment is unknown at compile time
                // but guaranteed correct by the vtable-resolved concrete type.
                // Skip instead of emitting fail-closed `false`.
                debug!("heap alignment check: dyn Trait pointee — skipping (vtable-resolved)");
            }
            None => {
                // #2501: Unknown alignment — emit conservative `false` (fail-closed).
                // Prevents false proofs for unknown-layout types.
                let count = self.diagnostics.heap_check_unknown_layout.inc_get();
                warn!(
                    count,
                    "heap alignment check: unknown type alignment, emitting fail-closed check"
                );
                checks.push(Expr::bool_const(false));
            }
        }

        // Resolve effective size: use element type for slices. Part of #3495.
        let effective_size = self
            .get_type_size(pointee_ty)
            .or_else(|| slice_elem_ty.and_then(|ety| self.get_type_size(ety)));

        match effective_size {
            Some(access_size) if access_size > 0 && u32::try_from(access_size).is_ok() => {
                // A constant lane at or past OBJECT_ID_LIMIT is no allocation's:
                // high offset bits set (at least 2^32 bytes past an object's
                // start, where a wrapping step carried) or an object field no
                // id reaches. An unallocated lane's metadata is permissive
                // (`obj_valid` true, `obj_size` 0 exempt), so the access checked
                // clean: `*a.as_ptr().wrapping_byte_add(1 << 32)` read a
                // havocked value where Kani reports a pointer outside object
                // bounds (fourth review of fix/chc-false-certificates:
                // `bs_wrapping_2p32_bug`).
                // A far pointer's lane carries the FAR_BIT (stack_address.rs),
                // so it is at or past OBJECT_ID_LIMIT too.
                if const_obj_id.is_some_and(|id| {
                    id >= crate::codegen_ay::chc::heap::stack_address::OBJECT_ID_LIMIT
                }) {
                    checks.push(Expr::bool_const(false));
                }
                let size_expr = Expr::bitvec_const(access_size as i128, 32);
                let end_offset = offset.clone().bvadd(size_expr);
                let no_wrap = end_offset.clone().bvuge(offset.clone());
                checks.push(no_wrap);

                // Part of #3159: Exempt zero-size allocations from bounds
                // checks. Dyn trait allocations record obj_size = 0 because
                // the size is resolved at runtime via the vtable. The check
                // becomes: obj_size[id] == 0 || end_offset <= obj_size[id].
                // A symbolic lane whose object (its low 15 bits, the part a
                // wrapping step keeps) folds to an allocated id names that
                // allocation: the access is in bounds only when the whole lane is
                // that id — no offset bit at or past 2^32 and no FAR_BIT
                // (stack_address.rs) — and the offset is within its size. Kani
                // checks the same object and offset. Skipping the bound here let
                // `*b.as_ptr().wrapping_add(k)` on a `Box<[u8; 4]>` with `k` in
                // `[4, 1000)` read clean (first review of the sixth round:
                // `g_heap_sym_small_oob`, `b12_bug_heap_small_oob`). Any other
                // symbolic lane takes `symbolic_lane_bounds` below.
                if let Some(id) = lane_object {
                    checks.push(obj_id.clone().eq(Expr::bitvec_const(id as i128, 32)));
                }
                let known_id = const_obj_id.or(lane_object);
                let lane_stack_size = lane_object
                    .and_then(|id| self.heap_state.local_idx_for_obj_id(id))
                    .and_then(|local_idx| self.body.locals().get(local_idx))
                    .and_then(|local_decl| self.get_type_size(local_decl.ty))
                    .and_then(|size| u32::try_from(size).ok());
                let alloc_size = if let Some(size) = stack_obj_size.or(lane_stack_size) {
                    Some(Expr::bitvec_const(size as i128, 32))
                } else if let Some((id, size)) =
                    known_id.and_then(|id| Some((id, self.heap_state.heap_alloc_size(id)?)))
                {
                    Some(self.recorded_heap_size_expr(id, size))
                } else if let Some(id) = known_id {
                    let heap_obj_size = self.current_obj_size_array();
                    Some(heap_obj_size.select(Expr::bitvec_const(id as i128, 32)))
                } else {
                    // A symbolic object lane: bounded by the size of the object
                    // the lane names (`symbolic_lane_bounds`).
                    // Not for the walker's eager read of a receiver's fields
                    // (`preloading_self_fields`), nor for a pointer the walker
                    // made up for a read it failed closed on
                    // (`lane_is_fail_closed_havoc`).
                    if !self.heap_state.preloading_self_fields
                        && !self.lane_is_fail_closed_havoc(&obj_id)
                    {
                        // The constant lane's rule above, for a lane that does not
                        // fold: no allocation has a lane at or past
                        // OBJECT_ID_LIMIT (offset bits above 2^32, or an object
                        // field no id reaches), and such a lane's metadata is
                        // permissive (`obj_valid` true, no size). A pointer made
                        // from a number naming no object and carried into another
                        // block read clean: through a `Box` cell
                        // (`t5_int_ptr_carried.rs::bug_via_box_then_alloc_k1`, round
                        // 3 review probes), an aggregate transmute or a union field
                        // (`int_to_ptr_const_lane_dual.rs::
                        // bug_exposed_array1_transmute_hi6_read`,
                        // `bug_exposed_union_int_hi6_read`), on main f61920d1a and
                        // on the landing merge alike, where Kani reports an invalid
                        // integer address. It is one check with the lane's size
                        // bound, so an access carries one obligation, not two.
                        use crate::codegen_ay::chc::heap::stack_address::OBJECT_ID_LIMIT;
                        let names_an_object = obj_id
                            .clone()
                            .bvult(Expr::bitvec_const(i128::from(OBJECT_ID_LIMIT), 32));
                        checks.push(
                            match self.symbolic_lane_bounds(&obj_id, &end_offset).pop() {
                                Some(bound) => names_an_object.and(bound),
                                None => names_an_object,
                            },
                        );
                    }
                    None
                };
                if let Some(ref alloc_size) = alloc_size {
                    let zero = Expr::bitvec_const(0u64, 32);
                    let is_zero_size = alloc_size.clone().eq(zero);
                    let bounds_ok = end_offset.bvule(alloc_size.clone());
                    checks.push(Expr::or(is_zero_size, bounds_ok));
                }

                // Part of #1860: WideMemManager bounds check integration.
                // Part of #3159: Only when alloc_size is known.
                if let (Some(wide_mem), Some(alloc_size)) =
                    (self.wide_mem_manager.as_ref(), alloc_size)
                {
                    let remaining_size = {
                        let zero = Expr::bitvec_const(0u64, 32);
                        let underflow = offset.clone().bvugt(alloc_size.clone());
                        let diff = alloc_size.bvsub(offset);
                        Expr::ite(underflow, zero, diff)
                    };

                    let extend_bits = POINTER_WIDTH - 32;
                    let remaining_size_wide = remaining_size.zero_extend(extend_bits);
                    let wide_ptr = MemPtr::wide(remaining_size_wide);

                    let deref_check = wide_mem.is_dereferenceable(&wide_ptr, access_size);
                    checks.push(deref_check);

                    debug!(
                        access_size,
                        "CHC: heap_access_checks - WideMemManager bounds check added (#1860)"
                    );
                }
            }
            Some(_) => {
                // Fix #1206: access_size == 0 or > u32::MAX — skip bounds check
                // (zero-size is trivially safe; >4GB would wrap in bv32 arithmetic).
            }
            None if is_dyn_trait_pointee => {
                // Part of #3159: dyn Trait size is unknown at compile time.
                // The allocation side already uses obj_size = 0 with a zero-size
                // exemption (line 298: is_zero_size || bounds_ok). Emitting
                // fail-closed `false` here would unconditionally trigger CTREX
                // on every dyn trait dereference. Skip the bounds check — the
                // concrete type's size is correct by construction via vtable dispatch.
                debug!("heap bounds check: dyn Trait pointee — skipping (vtable-resolved)");
            }
            None => {
                // #2501: Unknown size — emit conservative `false` (fail-closed).
                // Prevents false proofs for unknown-layout types.
                let count = self.diagnostics.heap_check_unknown_layout.inc_get();
                warn!(count, "heap bounds check: unknown type size, emitting fail-closed check");
                checks.push(Expr::bool_const(false));
            }
        }

        checks
    }

    /// Emits an error rule for a condition that must hold.
    ///
    /// A check `cond` generates: `from_rel(state) ∧ stmt_constraints ∧ !cond → error()`.
    ///
    /// If `cond` cannot be converted to a boolean expression (unsupported sort),
    /// emits a conservative unconditional error rule instead of silently dropping
    /// the check. This is sound: it may produce false counterexamples but never
    /// false proofs. See #2314.
    pub(in crate::codegen_ay::chc) fn emit_error_rule_for_condition(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        stmt_constraints: &[Expr],
        bb_idx: usize,
    ) {
        self.emit_error_rule_for_condition_with_kind(
            from_app,
            cond,
            stmt_constraints,
            bb_idx,
            PropertyKind::MemorySafety,
            None,
        );
    }

    /// Emit a memory-safety error rule for a copy / copy_nonoverlapping /
    /// write_bytes SPAN-access UB obligation, TAGGING the per-property relation
    /// so `translate()` can later detect whether the check const-folded to a
    /// definite (unconditional) violation once scalarization resolves a
    /// fully-concrete access. These span checks (alignment / count-overflow /
    /// allocation-bound) are PRECISE and PROVENANCE-INDEPENDENT, so a folded
    /// violation is a genuine bug — see
    /// `ChcDiagnostics::intrinsic_span_property_ids`.
    ///
    /// The tag is the property id `register_error_head` will assign, which is
    /// `self.vc.properties.len()` at registration; a per-property head is
    /// registered iff the check is non-trivial (not skipped as trivially true)
    /// and the per-harness property budget is not exhausted, so we record the
    /// id only when the property count actually advanced.
    pub(in crate::codegen_ay::chc) fn emit_intrinsic_span_ub_check(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        stmt_constraints: &[Expr],
        bb_idx: usize,
    ) {
        let id_before = self.vc.properties.len();
        self.emit_error_rule_for_condition(from_app, cond, stmt_constraints, bb_idx);
        if self.vc.properties.len() == id_before + 1 {
            self.diagnostics.intrinsic_span_property_ids.push(id_before as u32);
        }
    }

    /// Like [`Self::emit_error_rule_for_condition`], but with an explicit
    /// property kind and optional Kani-parity description for the per-property
    /// report line (e.g. `DivisionByZero` / "attempt to compute simd_div which
    /// would overflow"). The default `MemorySafety`+`None` wrapper above keeps
    /// the 70-odd existing heap-check call sites unchanged.
    pub(in crate::codegen_ay::chc) fn emit_error_rule_for_condition_with_kind(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        stmt_constraints: &[Expr],
        bb_idx: usize,
        kind: PropertyKind,
        message: Option<String>,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        let Some(bool_cond) = self.to_bool_expr(cond, bb_idx) else {
            // #2314: Emit conservative error rule instead of silently dropping.
            // Same pattern as emit_untranslatable_assert_rule in codegen_expr_assert.rs.
            let count = self.diagnostics.heap_check_untranslatable.inc_get();
            warn!(
                ?bb_idx,
                count,
                "cannot convert heap safety condition to bool; \
                 emitting conservative error rule"
            );
            // BSEM-18: per-property head (fail-closed conservative check).
            let error_app = self.register_error_head(kind, bb_idx, message);
            // Part of #2486: avoid stmt_constraints.to_vec() via from_base_and_extra.
            let body = RuleBody::from_base_and_extra(Some(from_app), stmt_constraints, []);
            let rule = Rule::new(body, error_app);
            self.vc.add_rule(rule);
            return;
        };

        if matches!(bool_cond.value(), ExprValue::BoolConst(true))
            || guard_disjunct_holds_under(&bool_cond, stmt_constraints)
        {
            debug!(?bb_idx, "skipping trivially true memory safety error rule");
            return;
        }

        let violation = bool_cond.not();
        // BSEM-18: per-property error head bridged into the aggregate `error`.
        let error_app = self.register_error_head(kind, bb_idx, message);

        // Part of #2486: avoid stmt_constraints.to_vec() + push via from_base_and_extra.
        let error_body =
            RuleBody::from_base_and_extra(Some(from_app), stmt_constraints, [violation]);

        let error_rule = Rule::new(error_body, error_app);
        self.vc.add_rule(error_rule);
        debug!(?bb_idx, "emitted memory safety error rule");
    }

    /// Shared-constraint variant of [`Self::emit_error_rule_for_condition`].
    ///
    /// Uses `RuleBody::from_shared_base` so repeated safety checks emitted from
    /// one block reuse the same `Arc<[Expr]>` base instead of cloning the full
    /// constraint vector per rule. Part of #2507.
    pub(in crate::codegen_ay::chc) fn emit_error_rule_for_condition_shared(
        &mut self,
        from_app: &RelationApp,
        cond: Expr,
        shared_constraints: &Arc<[Expr]>,
        bb_idx: usize,
    ) {
        let from_app = self.refresh_block_relation_app(from_app);
        let Some(bool_cond) = self.to_bool_expr(cond, bb_idx) else {
            let count = self.diagnostics.heap_check_untranslatable.inc_get();
            warn!(
                ?bb_idx,
                count,
                "cannot convert heap safety condition to bool; \
                 emitting conservative error rule"
            );
            // BSEM-18: per-property head (fail-closed conservative check).
            let error_app = self.register_error_head(PropertyKind::MemorySafety, bb_idx, None);
            let body =
                RuleBody::from_shared_base(Some(from_app), Arc::clone(shared_constraints), []);
            self.vc.add_rule(Rule::new(body, error_app));
            return;
        };

        if matches!(bool_cond.value(), ExprValue::BoolConst(true))
            || guard_disjunct_holds_under(&bool_cond, shared_constraints)
        {
            debug!(?bb_idx, "skipping trivially true memory safety error rule");
            return;
        }

        let violation = bool_cond.not();
        // BSEM-18: per-property error head bridged into the aggregate `error`.
        let error_app = self.register_error_head(PropertyKind::MemorySafety, bb_idx, None);
        let error_body =
            RuleBody::from_shared_base(Some(from_app), Arc::clone(shared_constraints), [violation]);

        let error_rule = Rule::new(error_body, error_app);
        self.vc.add_rule(error_rule);
        debug!(?bb_idx, "emitted shared memory safety error rule");
    }
}

/// Whether `cond` holds in every state the rule body `base` admits because
/// one of its top-level disjuncts is a dispatch-arm guard `¬(d = c)`
/// (`guard_dispatch_arm_pending_checks`) and `base` binds `d` to another
/// constant: the check belongs to an arm the body's own discriminant rules
/// out, and its error rule is dead. Such dead rules are not only waste: one
/// per walked arm's bound check made ay withhold the model of a nested
/// `Box<dyn Send>` drop it could not validate
/// (`test_nested_box_dyn_drop_solver_produces_unsat`, lostwrite track round 1,
/// finding 6).
fn guard_disjunct_holds_under(cond: &Expr, base: &[Expr]) -> bool {
    let ExprValue::Or(disjuncts) = cond.value() else { return false };
    let var_const = |e: &Expr| -> Option<(String, Expr)> {
        let ExprValue::Eq(a, b) = e.value() else { return None };
        match (a.value(), b.value()) {
            (ExprValue::Var { name }, ExprValue::BitVecConst { .. }) => {
                Some((name.clone(), b.clone()))
            }
            (ExprValue::BitVecConst { .. }, ExprValue::Var { name }) => {
                Some((name.clone(), a.clone()))
            }
            _ => None,
        }
    };
    let guards: Vec<(String, Expr)> = disjuncts
        .iter()
        .filter_map(|d| match d.value() {
            ExprValue::Not(inner) => var_const(inner),
            _ => None,
        })
        .collect();
    if guards.is_empty() {
        return false;
    }
    let mut stack: Vec<&Expr> = base.iter().collect();
    while let Some(e) = stack.pop() {
        match e.value() {
            ExprValue::And(parts) => stack.extend(parts.iter()),
            _ => {
                if let Some((name, value)) = var_const(e)
                    && guards.iter().any(|(g, c)| *g == name && *c != value)
                {
                    return true;
                }
            }
        }
    }
    false
}

#[cfg(test)]
mod guard_disjunct_tests {
    use super::guard_disjunct_holds_under;
    use ay_bindings::{Expr, Sort};

    #[test]
    fn a_dispatch_guard_the_body_refutes_makes_the_check_hold() {
        let disc = Expr::var("disc__out", Sort::bitvec(64));
        let check = Expr::var("bound_ok", Sort::bool());
        let one = Expr::bitvec_const(1u64, 64);
        let zero = Expr::bitvec_const(0u64, 64);
        let guarded = disc.clone().eq(one.clone()).not().or(check.clone());
        // The body binds the discriminant to another arm's id.
        let body = [Expr::bool_const(true).and(disc.clone().eq(zero))];
        assert!(guard_disjunct_holds_under(&guarded, &body));
        // ... or to this arm's id, or not at all: the check stands.
        assert!(!guard_disjunct_holds_under(&guarded, &[disc.clone().eq(one)]));
        assert!(!guard_disjunct_holds_under(&guarded, &[]));
        assert!(!guard_disjunct_holds_under(&check, &[disc.eq(Expr::bitvec_const(0u64, 64))]));
    }
}
