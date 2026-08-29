// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec residual mutation operation leaf handlers.
//!
//! Covers operations that previously fell through to the `other` arm in
//! `codegen_call_vec_core` with a warning + identity fallback. Each handler
//! provides a sound CHC abstraction of the operation's effect on Vec state
//! (length, capacity, data).
//!
//! Semantics summary:
//! - **VecSort/VecReverse/VecSwap**: permutation — preserves len, data unconstrained.
//! - **VecAppend**: `self.len += src.len`, `src.len = 0`.
//! - **VecTruncate**: `len = min(len, new_len)`.
//! - **VecInsert**: `len += 1`.
//! - **VecRemove**: `len -= 1`, returns removed element (unconstrained).
//! - **VecRetain/VecDedup**: `len' <= len` (some elements removed).
//! - **VecDrain**: `len -= drained_count` (range removed).
//! - **VecSplitOff**: `self.len = at`, new vec has `old_len - at`.
//! - **VecSplice**: range replaced; len changes by `(replacement_count - range_len)`.
//! - **VecLast**: returns Option of last element (query, no mutation).
//!
//! Part of #4135: Vec residual extend/sort/append leaf handlers.

use std::collections::HashSet;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::POINTER_WIDTH;
use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::debug;

use super::ChcCtx;
use super::codegen_call_vec::ChcVecFields;
use super::codegen_ctx::types::CollectionProjectionKind;
use super::{chc_fresh_name, declare_pending_var};
use crate::codegen_ay::stubs::StubKind;

/// Maximum number of moved source elements unrolled into `store` constraints by
/// `vec_op_append` when the source length is a concrete constant. Beyond this,
/// the data array is left as the sound unconstrained over-approximation. Part
/// of Fix 4.
const MAX_APPEND_MOVE_ELEMS: usize = 16;

/// Largest receiver length for which `vec_op_reverse` emits the EXACT reversal
/// fact `new[i] == old[len-1-i]`.
///
/// The post-state array is FRESH, so a longer receiver is left entirely
/// unconstrained rather than guessed — see `build_reversed_data`. Cost is
/// quadratic (one element equality per (length, slot) pair), and measured on
/// `Vectors/any/sorting.rs`: 8 -> 27s, 16 -> 41s.
const MAX_REVERSE_UNROLL: u64 = 8;

/// Largest receiver length for which [`ChcCtx::build_permuted_data`] pins the
/// post-permutation array to the input's element MULTISET.
///
/// Cost is quadratic (`k` disjuncts per slot, in each of two directions, per
/// covered length), so this is deliberately smaller than
/// [`MAX_REVERSE_UNROLL`]: the reversal is one equality per slot, a permutation
/// is `k`. A longer receiver leaves the post-state array entirely
/// unconstrained — a havoc, which can only ever refute.
const MAX_PERMUTE_UNROLL: u64 = 4;

/// Recognize the in-place slice PERMUTATION methods that a `Vec` receiver
/// reaches through `DerefMut`.
///
/// `v.reverse()` / `v.sort_by_key(..)` on a `Vec<T>` do NOT monomorphize to a
/// `Vec::<T>::…` path — `def_path_str` renders them as
/// `core::slice::<impl [T]>::reverse`, so the `Vec<`/`Vec::` guard on the stub
/// registry's Vec category never matches and the whole family fell through to
/// `fn_inline`, which claimed the call and emitted NOTHING for the `&mut [T]`
/// receiver. That silent identity is what let `v.reverse()` prove
/// `v == old_v`.
///
/// Matching here, on the shape that actually occurs, is only half the fix: the
/// caller must additionally confirm the receiver resolves to a Vec
/// representation before routing, because a `[T; N]` array receiver reaches the
/// same paths and the Vec handlers cannot address its storage.
pub(in crate::codegen_ay::chc) fn slice_permutation_stub_for_path(path: &str) -> Option<StubKind> {
    if !path.contains("slice::<impl [") {
        return None;
    }
    // `<impl [T]>::sort_by::<closure>` keeps trailing generics; take the segment
    // after the impl header, then drop any `::<…>` suffix.
    let after_impl = path.rsplit_once(">::")?.1;
    let method = after_impl.split("::").next()?;
    match method {
        "reverse" => Some(StubKind::VecReverse),
        "sort"
        | "sort_unstable"
        | "sort_by"
        | "sort_unstable_by"
        | "sort_by_key"
        | "sort_unstable_by_key" => Some(StubKind::VecSort),
        _ => None,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// VecSort / VecSwap: in-place PERMUTATION operations.
    ///
    /// The post-state is NOT the pre-state. Leaving the receiver's data array
    /// untouched (what this handler used to do, under the misnomer "data
    /// unconstrained") makes the operation an IDENTITY in the encoding, which
    /// PROVES false post-conditions — `v.sort(); assert!(v[0] == old_v0)` and
    /// `v.reverse(); assert!(v == old_v)` both verified. A permutation stub that
    /// does not constrain its result is a fabricated proof.
    ///
    /// The model here replaces the data array with a FRESH one and pins it only
    /// to facts every real permutation satisfies (see
    /// [`Self::build_permuted_data`]): each post-state slot holds some pre-state
    /// element and each pre-state element survives somewhere. That is a strict
    /// over-approximation of `multiset(out) == multiset(in)` — it can refute,
    /// never fabricate — and at `len == 1` it degenerates to the exact
    /// `new[0] == old[0]` that a 1-element sort must preserve.
    ///
    /// Sortedness is deliberately NOT assumed: `sort_by`/`sort_by_key` carry an
    /// arbitrary user comparator, so `is_sorted(out)` is not a fact this handler
    /// can establish.
    ///
    /// Returns `true` when the model was emitted. `false` means the receiver's
    /// Vec representation could not be resolved — the caller MUST fail closed
    /// rather than let the mutation vanish.
    pub(in crate::codegen_ay::chc) fn vec_op_permutation(
        &mut self,
        collection_local: Option<usize>,
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
        label: &str,
    ) -> bool {
        let emitted = self.vec_op_rewrite_data(
            collection_local,
            modified_locals,
            acc,
            Self::build_permuted_data,
        );
        debug!(
            fn_name = %self.fn_name,
            ?collection_local,
            label,
            emitted,
            "Vec permutation op: len/cap preserved, data re-bound to a permutation of the input"
        );
        emitted
    }

    /// `<[T]>::reverse` / `Vec::reverse` — in-place element reversal.
    ///
    /// Unlike the generic [`Self::vec_op_permutation`] family (sort/swap), the
    /// element mapping of a reversal is *known exactly*: the post-state array
    /// satisfies `new[i] == old[len-1-i]` for every `i < len`. Modeling it as an
    /// unconstrained permutation (or, as before this handler existed, dropping
    /// the mutation entirely and leaving the receiver untouched) makes
    /// post-conditions such as `v[0] <= v[1]` after a conditional
    /// `v.reverse()` unprovable.
    ///
    /// Returns `true` when the exact model was emitted; `false` leaves the
    /// caller's existing permutation fallback in place.
    pub(in crate::codegen_ay::chc) fn vec_op_reverse(
        &mut self,
        collection_local: Option<usize>,
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
    ) -> bool {
        self.vec_op_rewrite_data(collection_local, modified_locals, acc, Self::build_reversed_data)
    }

    /// Shared spine for the in-place whole-array rewrites (`reverse`, the
    /// permutation family): resolve the receiver to the local that carries the
    /// Vec representation, hand `(old_data, len)` to `build_data`, and write the
    /// resulting array back through whichever representation that local uses
    /// (flattened scalar fields or a single datatype state var).
    ///
    /// `ptr`, `cap` and `len` are carried through unchanged — none of these
    /// operations reallocates or resizes.
    ///
    /// Returns `false` without emitting anything when the receiver, its fields
    /// or the new array cannot be built. Every caller must treat that as
    /// fail-closed: the mutation was NOT modeled.
    fn vec_op_rewrite_data(
        &mut self,
        collection_local: Option<usize>,
        modified_locals: &HashSet<usize>,
        acc: &mut CallAccumulator<'_>,
        build_data: fn(&Expr, &Expr, &mut Vec<Expr>) -> Option<Expr>,
    ) -> bool {
        let Some(recv_local) = collection_local else {
            return false;
        };
        let Some(coll_local) = self.resolve_reversible_vec_local(recv_local) else {
            return false;
        };

        // Path 1: projected (flattened scalar fields) representation.
        if self.collections.projection_locals.get(&coll_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let ptr =
                self.flattened_local_field_expr(coll_local, vec_layout::IDX_PTR, modified_locals);
            let len =
                self.flattened_local_field_expr(coll_local, vec_layout::IDX_LEN, modified_locals);
            let cap =
                self.flattened_local_field_expr(coll_local, vec_layout::IDX_CAP, modified_locals);
            let data =
                self.flattened_local_field_expr(coll_local, vec_layout::IDX_DATA, modified_locals);
            let (Some(ptr), Some(len), Some(cap), Some(data)) = (ptr, len, cap, data) else {
                return false;
            };
            let Some(new_data) = build_data(&data, &len, acc.constraints) else {
                return false;
            };
            let emitted = self.constrain_flattened_fields_for_call(
                coll_local,
                &[Some(ptr), Some(len), Some(cap), Some(new_data)],
                acc.constraints,
            );
            if emitted {
                acc.dests.push(coll_local);
            }
            debug!(fn_name = %self.fn_name, coll_local, emitted, "VecRewriteData: projected model");
            return emitted;
        }

        // Path 2: datatype (Vec as a single aggregate state var).
        let Some(vec_idx) = self
            .ref_resolution
            .ref_arg_pointee_idx
            .get(&coll_local)
            .copied()
            .or_else(|| self.state_var_mgr.local_to_state_idx.get(&coll_local).copied())
        else {
            return false;
        };
        let Some(vec_in) = self
            .state_var_mgr
            .state_vars
            .get(vec_idx)
            .map(|(name, sort)| Expr::var(&**name, sort.clone()))
        else {
            return false;
        };
        let Some(fields) = ChcVecFields::extract(vec_in) else {
            return false;
        };
        let ChcVecFields { vec_sort, ptr, len, cap, data } = fields;
        let Some(new_data) = build_data(&data, &len, acc.constraints) else {
            return false;
        };
        let Some((out_name, out_sort)) = self.state_var_mgr.output_state_vars.get(vec_idx).cloned()
        else {
            return false;
        };
        let dt_name = vec_sort.datatype_name().expect("ChcVecFields ensures datatype sort");
        acc.constraints.push(Self::build_vec_datatype_eq(
            &dt_name,
            vec![ptr, len, cap, new_data],
            &out_name,
            &out_sort,
        ));
        acc.dests.push(coll_local);
        debug!(fn_name = %self.fn_name, coll_local, "VecRewriteData: datatype model");
        true
    }

    /// Resolve a `reverse` receiver local to the local that actually carries the
    /// Vec representation (flattened fields or datatype state var).
    ///
    /// `<[T]>::reverse` is reached through `Vec::deref_mut`, so `args[0]` is the
    /// `&mut [T]` fat pointer, not the Vec. `VecAsSlice` records that view in
    /// `slice_to_vec_local`; follow it (also through `ref_targets`) to get back
    /// to the owner.
    ///
    /// Returns `None` when the Vec sits behind field projections
    /// (`slice_to_vec_field_projections`) — the flattened field indices used
    /// below address a bare Vec local, so a struct-embedded receiver must fall
    /// back rather than write the wrong slots.
    pub(in crate::codegen_ay::chc) fn resolve_reversible_vec_local(
        &self,
        recv_local: usize,
    ) -> Option<usize> {
        let has_vec_repr = |ctx: &Self, local: usize| {
            ctx.collections.projection_locals.get(&local).copied()
                == Some(CollectionProjectionKind::Vec)
                || ctx
                    .state_var_mgr
                    .local_to_state_idx
                    .get(&local)
                    .and_then(|i| ctx.state_var_mgr.state_vars.get(*i))
                    .is_some_and(|(_, sort)| sort.datatype_sort().is_some())
        };

        if has_vec_repr(self, recv_local) {
            return Some(recv_local);
        }

        let resolved =
            self.ref_resolution.ref_targets.get(&recv_local).map_or(recv_local, |rt| rt.local);
        for candidate in [recv_local, resolved] {
            if self
                .ref_resolution
                .slice_to_vec_field_projections
                .get(&candidate)
                .is_some_and(|p| !p.is_empty())
            {
                return None;
            }
            if let Some(&vec_local) = self.ref_resolution.slice_to_vec_local.get(&candidate)
                && has_vec_repr(self, vec_local)
            {
                return Some(vec_local);
            }
        }
        if resolved != recv_local && has_vec_repr(self, resolved) {
            return Some(resolved);
        }
        None
    }

    /// Build the post-reversal data array for `old_data` of logical length `len`.
    ///
    /// The result is a FRESH, otherwise-unconstrained array pinned to the exact
    /// reversal by one implication per covered length:
    ///
    /// ```text
    /// len == k  ==>  new[0] == old[k-1] && … && new[k-1] == old[0]
    ///                                   for each k <= MAX_REVERSE_UNROLL
    /// ```
    ///
    /// The case split is what makes this tractable: every index above is a
    /// CONSTANT. The equivalent one-liner `i < len ==> new[i] == old[len-1-i]`
    /// selects at the symbolic index `len-1-i`, and ay could not certify the
    /// resulting array reasoning within budget on `Vectors/any/sorting.rs` (it
    /// computed the UNSAT, then rejected its own proof and returned `unknown`).
    ///
    /// A `len` past the covered range leaves `new_data` entirely
    /// unconstrained. That is the fail-closed direction: carrying the pre-call
    /// elements forward instead would be a guess that could let a stale value
    /// satisfy a post-condition the real reversal refutes, whereas an
    /// unconstrained array can only ever refute.
    ///
    /// Returns `None` when `old_data` is not an Array sort or its index width
    /// cannot be determined — the caller then keeps its own fallback.
    fn build_reversed_data(
        old_data: &Expr,
        len: &Expr,
        constraints: &mut Vec<Expr>,
    ) -> Option<Expr> {
        let data_sort = old_data.sort().clone();
        let idx_width = data_sort.array_sort()?.index_sort.bitvec_width()?;
        let len_width = len.sort().bitvec_width()?;

        // Index arithmetic happens in the array's own index width.
        let len_idx = if len_width == idx_width {
            len.clone()
        } else if len_width < idx_width {
            len.clone().zero_extend(idx_width - len_width)
        } else {
            len.clone().extract(idx_width - 1, 0)
        };

        let new_data = declare_pending_var(chc_fresh_name("vec_reverse"), data_sort);

        // Case-split on the concrete lengths the unroll covers so that every
        // element equality uses CONSTANT indices on both sides; a symbolic
        // `len - 1 - i` index would push the whole reversal into hard array
        // reasoning. `len` outside the covered range leaves `new_data`
        // completely unconstrained — nothing is guessed about it.
        for k in 0..=MAX_REVERSE_UNROLL {
            let len_is_k = len_idx.clone().eq(Expr::bitvec_const(k, idx_width));
            let Some(body) = (0..k)
                .map(|i| {
                    let dst = Expr::bitvec_const(i, idx_width);
                    let src = Expr::bitvec_const(k - 1 - i, idx_width);
                    new_data.clone().select(dst).eq(old_data.clone().select(src))
                })
                .reduce(Expr::and)
            else {
                continue;
            };
            constraints.push(len_is_k.implies(body));
        }

        Some(new_data)
    }

    /// Build the post-permutation data array for `old_data` of logical length
    /// `len` — the model for the `sort*` / `swap` family.
    ///
    /// The result is a FRESH array pinned, per covered concrete length `k`, to
    /// the two facts that every permutation of a `k`-element sequence satisfies:
    ///
    /// ```text
    /// len == k  ==>  (for each i < k)  new[i] == old[0] || … || new[i] == old[k-1]
    ///           &&   (for each j < k)  old[j] == new[0] || … || old[j] == new[k-1]
    /// ```
    ///
    /// Both directions are needed: the first alone permits `new = [old[0]; k]`
    /// (dropping elements), the second alone permits duplicating them. Together
    /// they are a strict OVER-approximation of `multiset(out) == multiset(in)` —
    /// they admit every real permutation plus some non-permutations that repeat
    /// a value, so the model can refute a false post-condition but can never
    /// prove one the real operation refutes. Genuine multiset equality would
    /// need the `k!` explicit orderings; this is the `k²` relaxation of it.
    ///
    /// At `k == 1` it collapses to the exact `new[0] == old[0]`, which is what a
    /// single-element `sort_by_key` must preserve.
    ///
    /// Sortedness is NOT asserted. `sort_by`/`sort_by_key` take an arbitrary
    /// user comparator, so `is_sorted(out)` is not a fact available here, and
    /// assuming it for `sort`/`sort_unstable` alone would be an assumption about
    /// a post-state this handler never computes.
    ///
    /// A `len` past `MAX_PERMUTE_UNROLL` leaves the array wholly unconstrained
    /// (havoc) rather than carrying the pre-call elements forward — the
    /// fail-closed direction, per the same reasoning as
    /// [`Self::build_reversed_data`].
    ///
    /// Returns `None` when `old_data` is not an Array sort or its index width
    /// cannot be determined — the caller then fails closed.
    fn build_permuted_data(
        old_data: &Expr,
        len: &Expr,
        constraints: &mut Vec<Expr>,
    ) -> Option<Expr> {
        let data_sort = old_data.sort().clone();
        let idx_width = data_sort.array_sort()?.index_sort.bitvec_width()?;
        let len_width = len.sort().bitvec_width()?;

        let len_idx = if len_width == idx_width {
            len.clone()
        } else if len_width < idx_width {
            len.clone().zero_extend(idx_width - len_width)
        } else {
            len.clone().extract(idx_width - 1, 0)
        };

        let fresh = declare_pending_var(chc_fresh_name("vec_permute"), data_sort);

        for k in 2..=MAX_PERMUTE_UNROLL {
            let slots: Vec<Expr> = (0..k).map(|i| Expr::bitvec_const(i, idx_width)).collect();

            // Every post-state slot holds SOME pre-state element.
            let forward = slots.iter().filter_map(|dst| {
                slots
                    .iter()
                    .map(|src| {
                        fresh.clone().select(dst.clone()).eq(old_data.clone().select(src.clone()))
                    })
                    .reduce(Expr::or)
            });
            // Every pre-state element survives in SOME post-state slot.
            let backward = slots.iter().filter_map(|src| {
                slots
                    .iter()
                    .map(|dst| {
                        old_data.clone().select(src.clone()).eq(fresh.clone().select(dst.clone()))
                    })
                    .reduce(Expr::or)
            });

            let Some(body) = forward.chain(backward).reduce(Expr::and) else {
                continue;
            };
            let len_is_k = len_idx.clone().eq(Expr::bitvec_const(k, idx_width));
            constraints.push(len_is_k.implies(body));
        }

        // A sequence of 0 or 1 elements has exactly ONE permutation: itself.
        // Stating that as array IDENTITY rather than as a fresh array pinned by
        // `new[0] == old[0]` is not just tighter, it is what keeps the query
        // tractable — the fresh-array form made a one-element `sort_by_key`
        // harness go from 2.4s to 68s and ay rejected its own proof
        // (`FalseProofRejected`), while the identity collapses the call away.
        let short = len_idx.bvule(Expr::bitvec_const(1u64, idx_width));
        Some(Expr::ite(short, old_data.clone(), fresh))
    }

    /// VecAppend: `self.append(&mut other)`.
    ///
    /// Moves all elements from `other` into `self`. After the call:
    /// - `self.len = self.len + other.len`
    /// - `other.len = 0`
    /// - `self.cap >= self.len` (may grow)
    /// - Data contents unconstrained (sound over-approximation).
    pub(in crate::codegen_ay::chc) fn vec_op_append(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        // Fix 4: the source Vec's concrete literal element values, captured from
        // `adapter_source_data` BEFORE the append call invalidates it (see
        // `codegen_call_vec.rs`). `Some` only when the source was built from a
        // compile-time-known literal (e.g. `vec![3]`); `None` otherwise.
        src_concrete_elems: Option<&[Expr]>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(self_local) = collection_local else {
            self.record_sound_fallback_reason("vec_append_no_self_local");
            return;
        };
        let Some(self_len_var) = self.collections.len_state.get_len_var(self_local).cloned() else {
            self.record_sound_fallback_reason("vec_append_no_self_len");
            return;
        };
        let self_old_len = self.collection_current_len(&self_len_var);

        // Resolve other's collection local from args[1].
        let other_local = args.get(1).and_then(|op| match op {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        });

        // Try to resolve other's ref target for length lookup.
        let other_resolved = other_local
            .and_then(|l| self.ref_resolution.ref_targets.get(&l).map(|rt| rt.local).or(Some(l)));

        let other_len_var =
            other_resolved.and_then(|l| self.collections.len_state.get_len_var(l).cloned());

        let other_len = other_len_var.as_ref().map(|v| self.collection_current_len(v));

        if let Some(ref src_len) = other_len {
            // self.len = self.len + other.len
            let new_self_len = self_old_len.clone().bvadd(src_len.clone());
            // Guard against unsigned overflow
            acc.constraints.push(new_self_len.clone().bvuge(self_old_len.clone()));
            self.collection_len_set(&self_len_var, new_self_len.clone(), acc);

            // Capacity growth: cap = max(cap, new_len).
            if let Some(cap_var) = self.collections.len_state.get_cap_var(self_local).cloned() {
                let old_cap = self.collection_current_cap(&cap_var);
                let grow_needed = old_cap.clone().bvult(new_self_len.clone());
                let new_cap = Expr::ite(grow_needed, new_self_len.clone(), old_cap);
                self.collection_cap_set(&cap_var, new_cap.clone(), acc);
                Self::emit_cap_ge_len(new_cap, new_self_len, acc.constraints);
            }

            // other.len = 0
            if let Some(ref other_lv) = other_len_var {
                self.collection_len_set(other_lv, Expr::bitvec_const(0u64, POINTER_WIDTH), acc);
            }

            // Fix 4: when the source was built from a compile-time-known literal
            // (its concrete element values were captured before this call
            // invalidated the adapter source data), store the MOVED element
            // VALUES into self's data array so reads of the appended slots
            // (`self[self_old_len + i]`) return the real moved values instead of
            // the construction fill. `append` moves ALL of other's elements, and
            // `src_concrete_elems` are exactly those values in order. This adds
            // only genuine facts, tightening the sound over-approximation.
            // Anything without a concrete literal source keeps the unconstrained
            // data model (do not store) — sound.
            if let Some(elems) = src_concrete_elems
                && (1..=MAX_APPEND_MOVE_ELEMS).contains(&elems.len())
            {
                self.vec_store_appended_elements(
                    self_local,
                    &self_old_len,
                    elems,
                    modified_locals,
                    acc,
                );
            }

            debug!(
                fn_name = %self.fn_name,
                self_local,
                ?other_resolved,
                "VecAppend: self.len += other.len, other.len = 0"
            );
        } else {
            // Cannot resolve other's length — leave self.len unconstrained
            // (sound over-approximation).
            debug!(
                fn_name = %self.fn_name,
                self_local,
                ?other_local,
                "VecAppend: other length unresolved — fallback"
            );
            self.record_sound_fallback_reason("vec_append_other_len_unresolved");
        }
    }

    /// VecTruncate: `self.truncate(new_len)`.
    ///
    /// If `new_len < self.len`, length is set to `new_len`. Otherwise no-op.
    /// Data contents beyond `new_len` are logically dropped (unconstrained in model).
    pub(in crate::codegen_ay::chc) fn vec_op_truncate(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_truncate_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_truncate_no_len");
            return;
        };

        let new_len_arg =
            args.get(1).and_then(|a| self.translate_operand_with_modified(a, modified_locals));

        let Some(new_len_arg) = new_len_arg else {
            debug!(
                fn_name = %self.fn_name,
                "VecTruncate: could not translate new_len argument"
            );
            self.record_sound_fallback_reason("vec_truncate_no_new_len");
            return;
        };

        let old_len = self.collection_current_len(&len_var);
        // new_len = min(old_len, new_len_arg)
        // = ite(old_len < new_len_arg, old_len, new_len_arg)
        let truncated = old_len.clone().bvult(new_len_arg.clone());
        let effective_len = Expr::ite(truncated, old_len, new_len_arg);
        self.collection_len_set(&len_var, effective_len, acc);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            "VecTruncate: len = min(old_len, arg)"
        );
    }

    /// VecInsert: `self.insert(index, element)`.
    ///
    /// Inserts an element at position `index`, shifting all elements after it
    /// to the right. `len += 1`.
    pub(in crate::codegen_ay::chc) fn vec_op_insert(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_insert_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_insert_no_len");
            return;
        };

        let old_len = self.collection_current_len(&len_var);
        let new_len = old_len.clone().bvadd(Expr::bitvec_const(1u64, POINTER_WIDTH));
        self.collection_len_set(&len_var, new_len.clone(), acc);

        // Capacity growth: cap = max(cap, new_len).
        if let Some(cap_var) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let old_cap = self.collection_current_cap(&cap_var);
            let grow_needed = old_cap.clone().bvult(new_len.clone());
            let new_cap = Expr::ite(grow_needed, new_len.clone(), old_cap);
            self.collection_cap_set(&cap_var, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, new_len, acc.constraints);
        }

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            "VecInsert: len += 1"
        );
    }

    /// VecRemove: `self.remove(index) -> T`.
    ///
    /// Removes and returns the element at position `index`, shifting all
    /// elements after it to the left. `len -= 1`. Return value is
    /// unconstrained (sound over-approximation).
    pub(in crate::codegen_ay::chc) fn vec_op_remove(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_remove_no_local");
            acc.dests.push(dest_local);
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_remove_no_len");
            acc.dests.push(dest_local);
            return;
        };

        let old_len = self.collection_current_len(&len_var);
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        // Guard: only decrement if len > 0 (prevents underflow)
        let can_dec = old_len.clone().bvugt(zero.clone());
        let new_len = Expr::ite(can_dec, old_len.bvsub(one), zero);
        self.collection_len_set(&len_var, new_len, acc);

        // Return value (T) is unconstrained — push dest for identity.
        acc.dests.push(dest_local);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            dest_local,
            "VecRemove: len -= 1, return unconstrained"
        );
    }

    /// VecRetain/VecDedup: filtering operations.
    ///
    /// After the call, `len' <= old_len`. The exact new length depends on
    /// the predicate/equality — modeled as unconstrained with the bound
    /// `0 <= new_len <= old_len` (sound over-approximation).
    pub(in crate::codegen_ay::chc) fn vec_op_filter_inplace(
        &mut self,
        collection_local: Option<usize>,
        label: &str,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_filter_inplace_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_filter_inplace_no_len");
            return;
        };

        let old_len = self.collection_current_len(&len_var);

        // new_len is fresh symbolic, constrained to [0, old_len]
        let fresh_len = super::declare_pending_var(
            super::chc_fresh_name("__vec_filter_len"),
            ay_bindings::Sort::bitvec(POINTER_WIDTH),
        );
        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        acc.constraints.push(fresh_len.clone().bvuge(zero));
        acc.constraints.push(fresh_len.clone().bvule(old_len));
        self.collection_len_set(&len_var, fresh_len, acc);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            label,
            "Vec filter-in-place: 0 <= new_len <= old_len"
        );
    }

    /// VecDrain: `self.drain(range)`.
    ///
    /// Removes elements in `range` from the Vec. The returned iterator
    /// yields the removed elements. `len -= range.len()`.
    /// Sound over-approximation: new_len is fresh with `0 <= new_len <= old_len`.
    pub(in crate::codegen_ay::chc) fn vec_op_drain(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        // Drain removes a range — model as filter_inplace since we don't
        // easily resolve the range bounds.
        self.vec_op_filter_inplace(collection_local, "drain", acc);
    }

    /// VecSplice: `self.splice(range, replace_with)`.
    ///
    /// Removes `range` from the Vec and replaces with elements from the
    /// iterator. Length change is `replacement_count - range_len`.
    /// Sound over-approximation: new_len is unconstrained (fresh symbolic >= 0).
    pub(in crate::codegen_ay::chc) fn vec_op_splice(
        &mut self,
        collection_local: Option<usize>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_splice_no_local");
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_splice_no_len");
            return;
        };

        // Splice can grow or shrink — new_len is fully unconstrained.
        // The only sound constraint is new_len >= 0 (unsigned).
        let fresh_len = super::declare_pending_var(
            super::chc_fresh_name("__vec_splice_len"),
            ay_bindings::Sort::bitvec(POINTER_WIDTH),
        );
        self.collection_len_set(&len_var, fresh_len.clone(), acc);

        // Cap must be >= len
        if let Some(cap_var) = self.collections.len_state.get_cap_var(coll_local).cloned() {
            let old_cap = self.collection_current_cap(&cap_var);
            let grow_needed = old_cap.clone().bvult(fresh_len.clone());
            let new_cap = Expr::ite(grow_needed, fresh_len.clone(), old_cap);
            self.collection_cap_set(&cap_var, new_cap.clone(), acc);
            Self::emit_cap_ge_len(new_cap, fresh_len, acc.constraints);
        }

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            "VecSplice: len unconstrained (splice can grow or shrink)"
        );
    }

    /// VecSplitOff: `self.split_off(at) -> Vec<T>`.
    ///
    /// Returns a new Vec containing elements from `at` to end.
    /// `self.len = at`, new vec `len = old_len - at`.
    /// Sound over-approximation: dest is unconstrained, self.len bounded.
    pub(in crate::codegen_ay::chc) fn vec_op_split_off(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        let Some(coll_local) = collection_local else {
            self.record_sound_fallback_reason("vec_split_off_no_local");
            acc.dests.push(dest_local);
            return;
        };
        let Some(len_var) = self.collections.len_state.get_len_var(coll_local).cloned() else {
            self.record_sound_fallback_reason("vec_split_off_no_len");
            acc.dests.push(dest_local);
            return;
        };

        let at_arg =
            args.get(1).and_then(|a| self.translate_operand_with_modified(a, modified_locals));

        if let Some(at) = at_arg {
            let old_len = self.collection_current_len(&len_var);
            // self.len = at (elements 0..at remain in self)
            // Ensure at <= old_len (Rust panics otherwise, but we model soundly)
            acc.constraints.push(at.clone().bvule(old_len.clone()));
            self.collection_len_set(&len_var, at.clone(), acc);

            // New Vec's length = old_len - at
            if let Some(dest_len_var) = self.collections.len_state.get_len_var(dest_local).cloned()
            {
                let new_vec_len = old_len.bvsub(at);
                self.collection_len_set(&dest_len_var, new_vec_len, acc);
            }
        } else {
            self.record_sound_fallback_reason("vec_split_off_no_at");
        }

        // Dest Vec data is unconstrained.
        acc.dests.push(dest_local);

        debug!(
            fn_name = %self.fn_name,
            coll_local,
            dest_local,
            "VecSplitOff: self.len = at, new vec unconstrained"
        );
    }

    /// VecLast: `self.last() -> Option<&T>`.
    ///
    /// Query operation — no mutation. Returns `Some(&last)` if non-empty,
    /// `None` if empty. Modeled as unconstrained Option return.
    pub(in crate::codegen_ay::chc) fn vec_op_last(
        &mut self,
        collection_local: Option<usize>,
        dest_local: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        // No mutation — Vec state is preserved.
        // Return value (Option<&T>) is unconstrained (sound over-approximation).
        acc.dests.push(dest_local);

        debug!(
            fn_name = %self.fn_name,
            ?collection_local,
            dest_local,
            "VecLast: query op, return unconstrained"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::{MAX_PERMUTE_UNROLL, MAX_REVERSE_UNROLL, slice_permutation_stub_for_path};
    use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
    use crate::codegen_ay::stubs::StubKind;

    /// The paths that ACTUALLY occur. `v.reverse()` / `v.sort_by_key(..)` on a
    /// `Vec<T>` go through `Vec: DerefMut`, and `def_path_str` renders the
    /// callee as `core::slice::<impl [T]>::reverse` — never
    /// `alloc::vec::Vec::<T>::reverse`. Matching the `Vec::` spelling is what
    /// left the whole family to `fn_inline`, which dropped the mutation.
    #[test]
    fn slice_permutation_paths_that_actually_occur_are_matched() {
        for path in [
            "core::slice::<impl [T]>::reverse",
            "core::slice::<impl [u32]>::reverse",
            "std::slice::<impl [u32]>::reverse",
        ] {
            assert_eq!(
                slice_permutation_stub_for_path(path),
                Some(StubKind::VecReverse),
                "{path} must route to the exact reversal model"
            );
        }
        for path in [
            "core::slice::<impl [T]>::sort",
            "core::slice::<impl [T]>::sort_unstable",
            "core::slice::<impl [T]>::sort_by",
            "core::slice::<impl [T]>::sort_unstable_by",
            "alloc::slice::<impl [GuestRegionMmap]>::sort_by_key::<GuestAddress, {closure@a.rs:1:1}>",
            "core::slice::<impl [T]>::sort_unstable_by_key",
        ] {
            assert_eq!(
                slice_permutation_stub_for_path(path),
                Some(StubKind::VecSort),
                "{path} must route to the permutation model"
            );
        }
    }

    /// The pre-route must not swallow unrelated slice methods, and must not fire
    /// on paths that have no `slice::<impl [` header at all.
    #[test]
    fn slice_permutation_declines_unrelated_paths() {
        for path in [
            "core::slice::<impl [T]>::first",
            "core::slice::<impl [T]>::iter",
            "core::slice::<impl [T]>::sort_floats",
            "alloc::vec::Vec::<u32>::push",
            "my_crate::Thing::reverse",
        ] {
            assert_eq!(slice_permutation_stub_for_path(path), None, "{path} must not be claimed");
        }
    }

    /// A receiver this handler could not model leaves the mutation UNMODELED —
    /// the identity, which is exactly the shape that proved
    /// `v.reverse(); assert!(v == old_v)`. The reason must therefore stay
    /// fail-closed; blessing it would let that same silent drop report a clean
    /// PROOF again.
    #[test]
    fn unresolved_permutation_receiver_is_fail_closed() {
        assert_eq!(
            fallback_soundness("vec_permutation_receiver_unresolved"),
            FallbackSoundness::FailClose,
            "a dropped permutation must never be blessed as a clean havoc"
        );
    }

    /// The permutation unroll is quadratic per covered length while the
    /// reversal unroll is linear, so the permutation bound must stay the
    /// smaller of the two.
    #[test]
    fn permute_unroll_is_bounded_below_reverse_unroll() {
        assert!(MAX_PERMUTE_UNROLL <= MAX_REVERSE_UNROLL);
        assert!(MAX_PERMUTE_UNROLL >= 2, "below 2 the model degenerates to the identity ITE alone");
    }
}
