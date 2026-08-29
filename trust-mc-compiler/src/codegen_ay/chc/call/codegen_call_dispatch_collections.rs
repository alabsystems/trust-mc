// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Numeric + collection-family call dispatch helpers for CHC call terminators.
//!
//! Dispatches BigInt, BigRational, HashMap, BTreeSet, HashSet, heap alloc,
//! slice, iterator, Vec, and String stubs to their dedicated handlers.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

use crate::codegen_ay::stubs::StubKind;

use super::ChcCtx;
use super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::codegen_call_alloc::CallAlloc;
use super::codegen_call_collections::CallCollections;
use super::codegen_call_hashmap_iter::CallHashmapIter;
use super::codegen_call_iterator_adapter::CallIteratorAdapter;
use super::codegen_call_numeric::CallNumeric;
use super::codegen_call_option_result::CallOptionResult;
use super::codegen_call_slice::CallSlice;
use super::codegen_call_string::CallString;
use super::codegen_call_vec::CallVec;
use super::codegen_call_vec_ops_mutate::slice_permutation_stub_for_path;
/// Extension trait for numeric + collection-family dispatch in call-terminator codegen.
pub(in crate::codegen_ay::chc) trait CallDispatchCollections {
    fn try_dispatch_call_numeric_collections(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchCollections for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_numeric_collections(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let (bb_idx, func, args, destination, target, from_app, stmt_constraints, modified_locals) = (
            dcx.bb_idx,
            dcx.func,
            dcx.args,
            dcx.destination,
            dcx.target,
            dcx.from_app,
            dcx.stmt_constraints,
            dcx.modified_locals,
        );
        // === Pre-routes: type-based or custom detectors that bypass the stub registry ===
        // Design rule (Part of #2408 T5): these use type-based detection (BigInt,
        // BigRational, HashMap) or custom path patterns (alloc, iterators) that
        // cannot be reduced to a single StubKind registry lookup yet.

        // `<[T]>::reverse` / `<[T]>::sort*` reached through `Vec: DerefMut`.
        //
        // These never carry a `Vec<`/`Vec::` path segment, so the stub registry
        // returns None for them and `fn_inline` claimed the call and emitted
        // nothing for the `&mut [T]` receiver — encoding the mutation as the
        // IDENTITY. That fabricated proofs: `v.reverse(); assert!(v == old_v)`
        // verified, and `Vectors/any/sorting.rs` (`if v[0] > v[1] { v.reverse() }
        // assert!(v[0] <= v[1])`) reported a counterexample on the branch where
        // the reversal was dropped.
        //
        // Routing is guarded on the receiver actually resolving to a Vec
        // representation: a `[T; N]` array reaches the same paths, and handing
        // one to the Vec handlers would drop ITS mutation instead (the earlier
        // attempt at this fix made `[1,2,3].reverse(); assert!(a[0] == 1)`
        // verify). An unresolvable receiver declines here and keeps whatever
        // the existing chain did.
        if let Some(stub) =
            self.resolve_callee_path(func).as_deref().and_then(slice_permutation_stub_for_path)
            && self
                .resolve_collection_local(args)
                .and_then(|recv| self.resolve_reversible_vec_local(recv))
                .is_some()
        {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_vec_core(&cx);
                return true;
            }
            self.record_diverging_call_drop(
                func,
                Some(bb_idx),
                "collections::slice_permutation",
                Some(stub),
            );
            return true;
        }

        // `num_bigint::Sign::mul` stays a real library call after BigInt aggregate
        // scalarization. Handle it before generic BigInt stub detection so CHC
        // does not emit an inferable summary relation for this enum helper.
        if self.is_bigint_sign_mul_call(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub: StubKind::BigIntMul,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_bigint_sign_mul(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::bigint_sign_mul",
                    None,
                );
            }
            return true;
        }

        // Part of #3687: `BigInt::from_biguint(Sign, BigUint)` is a real library call
        // that constructs a signed BigInt from a sign enum and unsigned magnitude.
        // Handle it before generic detection so it doesn't become uninterpreted.
        if self.is_bigint_from_biguint_call(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub: StubKind::BigIntFrom,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_bigint_from_biguint(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::bigint_from_biguint",
                    None,
                );
            }
            return true;
        }

        // Part of #3687: `BigUint::set_zero(&mut self)` is an internal mutation
        // that writes 0 to the receiver. Handle as compound assign to args[0].
        if self.is_bigint_set_zero_call(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub: StubKind::BigIntZero,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_bigint_set_zero(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::bigint_set_zero",
                    None,
                );
            }
            return true;
        }

        // BigInt stubs (type-based detection)
        if let Some(stub) = self.detect_bigint_stub(func, args) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_bigint(func, &cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::bigint",
                    Some(stub),
                );
            }
            return true;
        }

        // BigRational stubs (type-based detection)
        if let Some(stub) = self.detect_bigrational_stub(func, args) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_bigrational(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::bigrational",
                    Some(stub),
                );
            }
            return true;
        }

        // HashMap stubs (type-based detection)
        // Part of #3057: detect_hashmap_stub catches iterator stubs via Phase 1
        // (to_hashmap_equivalent) and Phase 1.5 (hashbrown internal detection).
        // Route those to the iterator handler.
        if let Some(stub) = self.detect_hashmap_stub(func, args) {
            let is_iter_stub = matches!(
                stub,
                StubKind::HashMapIntoIter
                    | StubKind::HashMapIter
                    | StubKind::HashMapKeys
                    | StubKind::HashMapValues
                    | StubKind::HashMapIterNext
            );
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                if is_iter_stub {
                    self.codegen_call_hashmap_iter(&cx);
                } else {
                    self.codegen_call_hashmap(&cx);
                }
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    if is_iter_stub { "collections::hashmap_iter" } else { "collections::hashmap" },
                    Some(stub),
                );
            }
            return true;
        }

        // Heap allocation stubs (custom path detection)
        if let Some(stub) = self.detect_alloc_stub(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_alloc(bb_idx, &cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::alloc_detect",
                    Some(stub),
                );
            }
            return true;
        }

        // Iterator intrinsic stubs (custom detection)
        if let Some(stub) = self.detect_iterator_intrinsic_stub(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_iterator_intrinsic(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::iterator_intrinsic",
                    Some(stub),
                );
            }
            return true;
        }

        // Array inner iterator next: PolymorphicIter::next only (NOT IndexRange::next).
        // Part of #3984: These are called on inner fields of ArrayIntoIter locals
        // where the receiver is a BV64 heap pointer (no ref_target mapping).
        // Route through the parent IntoIter local from projection_locals.
        // IndexRange::next returns Option<usize> (index), not Option<T> (element),
        // so it must NOT be intercepted here — let fn_inline handle it.
        if self.detect_array_inner_iter_next(func) {
            if target.is_none() {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::array_inner_iter_next",
                    None,
                );
                return true;
            }
            self.codegen_call_array_inner_iter_next(dcx);
            return true;
        }

        // Array inner iterator IndexRange::next: returns Option<usize> (index).
        // Part of #3984: When MIR uses IndexRange::next + Option::map instead of
        // PolymorphicIter::next, we handle IndexRange::next here to return the
        // correct Option<usize> index, which Option::map then maps to the element.
        if self.detect_array_index_range_next(func) {
            if target.is_none() {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::array_index_range_next",
                    None,
                );
                return true;
            }
            self.codegen_call_array_index_range_next(dcx);
            return true;
        }

        // Vec iterator stubs (custom detection)
        if let Some(stub) = self.detect_vec_iter_stub(func) {
            if target.is_none() {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::vec_iter",
                    Some(stub),
                );
                return true;
            }
            self.codegen_call_vec_iter(stub, dcx);
            return true;
        }

        // HashMap iterator stubs (custom detection)
        if let Some(stub) = self.detect_hashmap_iter_stub(func) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_hashmap_iter(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::hashmap_iter",
                    Some(stub),
                );
            }
            return true;
        }

        // Iterator adapter next() by receiver type (Part of #4112).
        // Instance::resolve strips the Self type from trait method calls like
        // <FlatMap<I,U,F> as Iterator>::next, producing a generic "Iterator::next"
        // path that the stub registry cannot match. This type-based pre-route
        // checks the receiver arg's ADT name for known adapter types.
        if let Some(stub) = self.detect_adapter_next_by_receiver_type(func, args) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_iterator_adapter(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::adapter_next_type",
                    Some(stub),
                );
            }
            return true;
        }

        // === Single-detect route: one callee-path resolve for all stub-registry routes ===
        // Part of #2408 T5: ordered route table replaces 6 separate if-chains.
        type Predicate = fn(StubKind) -> bool;
        type Handler<'ctx, 'mir> = fn(&mut ChcCtx<'ctx, 'mir>, &ChcCallContext<'_>);

        let stub = match self.detect_stub(func) {
            Some(s) => s,
            None => return false,
        };

        // The registry deliberately recognizes suffix-compatible Index paths,
        // including downstream lookalikes. That is useful for routing but is
        // not proof authority: slice index stubs derive bounds, contents, and
        // subslice lengths. Require the exact core trait method DefId whenever
        // the registry selects an authority-bearing Index stub; otherwise
        // leave the real call to the ordinary inline/fallback chain.
        if matches!(stub, StubKind::IndexIndex | StubKind::SliceIndexIndex | StubKind::IndexMut)
            && self.authenticated_core_slice_index_args(func, args).is_none()
        {
            return false;
        }

        // SliceIntoVec — vec![...] macro expansion (#2967)
        // Custom handler because we need `func` operand for generic type extraction.
        if matches!(stub, StubKind::SliceIntoVec) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_slice_into_vec(func, &cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::slice_into_vec",
                    Some(stub),
                );
            }
            return true;
        }

        // HashSet iterator stubs — route through projection-aware handler (Part of #3057).
        // Without this, HashSetIntoIter/Iter/IterNext fall through to codegen_call_hashset
        // via is_hashset predicate, which uses apply_collection_result — that handler lacks
        // projection-aware decomposition and incorrectly treats iterator structs as Options,
        // causing sort mismatches that produce UNKNOWN verdicts.
        if matches!(
            stub,
            StubKind::HashSetIntoIter | StubKind::HashSetIter | StubKind::HashSetIterNext
        ) {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_hashset_iter(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::hashset_iter",
                    Some(stub),
                );
            }
            return true;
        }

        // Part of #4112: Iterator adapter stubs (FlattenNext, MapNext, etc.) must
        // be routed here in collections dispatch rather than waiting for misc dispatch.
        // Without this, fn_inline (position 277) can claim FlatMap::next() calls
        // before the adapter handler sees them, producing unconstrained results
        // instead of the precise ITE-chain encoding. This caused flat_map harnesses
        // to get CTREX because only the first next() call reached the adapter.
        if stub.is_iterator_adapter() {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                self.codegen_call_iterator_adapter(&cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::iterator_adapter",
                    Some(stub),
                );
            }
            return true;
        }

        // Ordered route table; preserves original dispatch priority.
        let routes: [(Predicate, Handler<'tcx, 'body>); 6] = [
            (StubKind::is_btreeset, Self::codegen_call_btreeset),
            (StubKind::is_hashset, Self::codegen_call_hashset),
            (StubKind::is_slice_stub, Self::codegen_call_slice_stub_parity),
            (StubKind::is_vec_core, Self::codegen_call_vec_core),
            (StubKind::is_string_core, Self::codegen_call_string_core),
            (StubKind::is_collection_predicate, Self::codegen_call_collection_predicate),
        ];
        let handler =
            routes.into_iter().find_map(|(predicate, handler)| predicate(stub).then_some(handler));

        if let Some(handler) = handler {
            if let Some(target) = target {
                let cx = ChcCallContext {
                    stub,
                    args,
                    destination,
                    target: *target,
                    from_app,
                    stmt_constraints,
                    modified_locals,
                };
                handler(self, &cx);
            } else {
                self.record_diverging_call_drop(
                    func,
                    Some(bb_idx),
                    "collections::route_table",
                    Some(stub),
                );
            }
            return true;
        }

        false
    }
}
