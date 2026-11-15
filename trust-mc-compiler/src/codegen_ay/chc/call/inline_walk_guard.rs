// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Phase 0 of the dyn-walker write/read design
//! (`docs/chc-hole-fix-designs-2026-09-24.md`, section 2, with the critique's
//! widening): fail-closed rules for inline walks.
//!
//! The walker keeps three stores for one pointee cell and updates none of the
//! others: a write through a deref goes to the host memory model (W1) or
//! rebinds the pointer local to the updated pointee (W2); a read is served
//! from the self-field snapshot taken at walk entry, from the local's term
//! (`Deref` is the identity), or from memory. So a read after a write can see
//! the value from before it, and an address-bound reference is read as its
//! own bits. Phase 1 (an overlay that answers such reads exactly) is not
//! built. Phase 0 makes every such read, and every write the walk loses,
//! record a reason that is NOT on the blessed list (`fallback_soundness`), so a
//! proof resting on it is demoted and a counterexample through it is never
//! certified Genuine. The rules add records and havocs, and remove no error
//! clause. Two lanes change a concrete value, each to the value the program
//! holds there:
//!
//! * `GuardedRead::ThroughTerm`: a read through a stale self-field snapshot
//!   is served from the local's current term instead, only when F1 passed
//!   (no write since the outermost mark but W2 rebinds of this very local),
//!   the local is not address-bound, and its term has the pointee's datatype
//!   sort with no declared address field (the pointee VALUE, never an
//!   address). Otherwise it fails closed with [`WALKER_SELF_FIELD_MAP_STALE`].
//! * The referent write (`codegen_call_virtual_inline/referent_write.rs`,
//!   review finding M1): a W2 write through a non-argument pointer local whose
//!   term is its referent's value is applied to the referent the walked body
//!   names as well, or recorded as [`WALKER_DEREF_WRITE_REBIND_LOST`].
//!
//! * F1, [`WALKER_DEREF_READ_AFTER_WRITE`]: a read through a deref (any
//!   resolver) or any heap read, after ANY write since the outermost walk
//!   mark. The mark is taken once at the outermost walk entry or host front
//!   door that walks several bodies (the dyn candidate loop, the Fn-trait
//!   guarded dispatch, the dyn drop candidates), never per walk, so a later
//!   candidate that reads what an earlier one wrote is caught. No exemption.
//! * [`WALKER_SELF_FIELD_MAP_STALE`]: a read of the self-field snapshot after
//!   its local was rebound (plain reassignment included, which writes
//!   nothing: `walker_referent_read_dual.rs::bug_maybe_moved_guard`).
//! * F2, [`WALKER_DEREF_READ_ADDRESS_AS_VALUE`]: a transparent `Deref` of a
//!   reference local whose term is an address, tracked from binder tags (the
//!   dyn door, nested walks, fn_inline unreported bindings) and propagated
//!   through copies, casts, reborrows that take the address lane, references
//!   read through a pointer, and nested returns. Its residual: a reference
//!   copied out of a field or variant payload of a by-value argument (the walk
//!   never saw how the caller bound it), or of a local the walk marked as
//!   address-carrying (built from such a reference or argument, or copied
//!   through a pointer), is address-bound whatever its term's shape
//!   (`statement_exec.rs::rvalue_reads_field_address`).
//! * [`WALKER_SELF_FIELD_UNLOADED`]: a self-field entry the map builder could
//!   not load, which used to be the field's ADDRESS served as its value.
//! * F3, [`WALKER_DEREF_WRITEBACK_MEMORY_ONLY`]: a memory store through a
//!   pointer ARGUMENT (and the caller gets a havoc alias update for it), and,
//!   widened by review finding M2, EVERY store the walker's store lanes make
//!   unless it reached an object allocated during the walk, a static no state
//!   variable holds, or a `static mut` whose state variable the mirror updated
//!   (`ChcCtx::classify_inline_walk_lane_store`): a store through a raw copy
//!   of an argument, or through a reference held in an aggregate, reaches the
//!   heap arrays only, and a caller's state variable keeps the old value.

use crate::codegen_ay::chc::codegen_ctx::Havoc;
use ay_bindings::Expr;
use rustc_public::mir::{Body, LocalDecl, Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::{HashMap, HashSet};
use tracing::debug;

use super::ChcCtx;
use super::codegen_types::CodegenTypes;
use super::inline_field_map::{
    DIRECT_DEREF_FIELD, SELF_FIELD_MAP_ROOT_TERM, is_unloaded_self_field_entry,
};
use super::inline_shared::PlaceResolver;
use crate::codegen_ay::chc::chc_fresh_name;

/// F1: a read through a deref, or a heap read, inside an inline walk after a
/// write since the outermost walk mark.
pub(in crate::codegen_ay::chc) const WALKER_DEREF_READ_AFTER_WRITE: &str =
    "walker_deref_read_after_write";
/// A self-field snapshot entry read after its local was rebound.
pub(in crate::codegen_ay::chc) const WALKER_SELF_FIELD_MAP_STALE: &str =
    "walker_self_field_map_stale";
/// F2: a transparent `Deref` of an address-bound reference.
pub(in crate::codegen_ay::chc) const WALKER_DEREF_READ_ADDRESS_AS_VALUE: &str =
    "walker_deref_read_address_as_value";
/// A self-field entry the map builder could not load.
pub(in crate::codegen_ay::chc) const WALKER_SELF_FIELD_UNLOADED: &str =
    "walker_self_field_unloaded";
/// F3: a memory store through a reference or pointer argument, which reaches
/// no alias update (the caller's state variable keeps the old value).
pub(in crate::codegen_ay::chc) const WALKER_DEREF_WRITEBACK_MEMORY_ONLY: &str =
    "walker_deref_writeback_memory_only";
/// F5: a dispatch or SwitchInt alias update whose arms disagree in sort.
pub(in crate::codegen_ay::chc) const DYN_DISPATCH_ALIAS_UPDATE_SORT_MISMATCH: &str =
    "dyn_dispatch_alias_update_sort_mismatch";
/// F6: a projected write the walker skipped.
pub(in crate::codegen_ay::chc) const WALKER_DEREF_WRITE_DROPPED: &str =
    "walker_deref_write_dropped";
/// F6: a `SetDiscriminant` the walker skipped.
pub(in crate::codegen_ay::chc) const WALKER_SET_DISCRIMINANT_DROPPED: &str =
    "walker_set_discriminant_dropped";
/// A W2 rebind of a non-argument pointer local whose term was a memory
/// address: the write updates neither memory nor any alias.
pub(in crate::codegen_ay::chc) const WALKER_DEREF_WRITE_REBIND_LOST: &str =
    "walker_deref_write_rebind_lost";
/// A memory effect made inside a multi-target SwitchInt arm or a
/// multi-candidate dispatch arm: the host applies it unguarded.
pub(in crate::codegen_ay::chc) const WALKER_STORE_IN_BRANCH_ARM: &str =
    "walker_store_in_branch_arm";
/// A nested call's alias update the walker could not write back.
pub(in crate::codegen_ay::chc) const WALKER_NESTED_ALIAS_WRITEBACK_DROPPED: &str =
    "walker_nested_alias_writeback_dropped";
/// Rule D (design trust-mc-reds-final §4.1): a translation that removes a
/// check, a write or a deallocation the program can reach books FailClose. A
/// sound havoc may replace a VALUE only. Each effect a site drops is one of
/// these; [`record_lost_obligation`] books it, and a unit test holds every
/// reason off the audited SoundHavoc list (`fallback_soundness`), so a later
/// edit to that list cannot bless one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum LostEffect {
    /// A SwitchInt arm the walker could not finish, whose region can check or
    /// write (`codegen_call_virtual_inline/switchint.rs`; mechanism C).
    BailedArm,
    /// A nested call the walker havocked whose body can check or write, or
    /// has no body (`codegen_call_virtual_inline/terminator_exec.rs`;
    /// mechanism B).
    NestedCallFallback,
    /// An `Assert` whose condition did not translate: were the walk to
    /// continue past it with nothing recorded, its check would be gone
    /// (`terminator_exec.rs`; mechanism E). The walker records no such loss:
    /// it states the Assert as a check that fails wherever it is reached,
    /// never certified (`codegen_call_virtual_inline/uncertified_check.rs`),
    /// which keeps the obligation, so nothing books this effect today. Kept
    /// in [`LostEffect::ALL`] so a site that drops such an Assert has its
    /// reason, off the SoundHavoc list.
    UntranslatableAssert,
    /// An `Rc`/`Arc` drop skipped as a clone alias, its deallocation with it
    /// (`transition_drop/arc_drop.rs`; C8b).
    RcDeallocSkippedCloneAlias,
    /// An `Rc`/`Arc` drop skipped because the handle's pointer is unknown
    /// (`transition_drop/arc_drop.rs`; C8b).
    RcDeallocSkippedPointerUnknown,
    /// A dyn drop dispatch arm the walker could not inline: that type's drop
    /// glue (its checks, writes and deallocation) is not encoded on its arm
    /// (`codegen_call_virtual_inline/drop_placeholder_dispatch.rs`; Rule E's
    /// classification of the dispatch default, decision REDS-REST).
    DropDispatchArmNotWalked,
}

impl LostEffect {
    /// Every lost effect, for the table test.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(in crate::codegen_ay::chc) const ALL: [LostEffect; 6] = [
        LostEffect::BailedArm,
        LostEffect::NestedCallFallback,
        LostEffect::UntranslatableAssert,
        LostEffect::RcDeallocSkippedCloneAlias,
        LostEffect::RcDeallocSkippedPointerUnknown,
        LostEffect::DropDispatchArmNotWalked,
    ];

    /// The fail-closed reason the effect records.
    pub(in crate::codegen_ay::chc) const fn reason(self) -> &'static str {
        match self {
            LostEffect::BailedArm => "walker_bailed_arm_lost_effect",
            LostEffect::NestedCallFallback => "walker_nested_call_lost_effect",
            LostEffect::UntranslatableAssert => "walker_untranslatable_assert_lost",
            LostEffect::RcDeallocSkippedCloneAlias => "rc_dealloc_skipped_clone_alias",
            LostEffect::RcDeallocSkippedPointerUnknown => "rc_dealloc_skipped_pointer_unknown",
            LostEffect::DropDispatchArmNotWalked => "drop_dispatch_arm_not_walked",
        }
    }
}

/// Book a lost effect (Rule D): one recorder for every site.
pub(in crate::codegen_ay::chc) fn record_lost_obligation(
    ctx: &ChcCtx<'_, '_>,
    effect: LostEffect,
) -> crate::codegen_ay::chc::codegen_ctx::Booked {
    debug!(?effect, reason = effect.reason(), "Rule D: lost effect booked fail-closed");
    ctx.record_sound_fallback_reason(effect.reason())
}
/// A walked closure behind a fn pointer wrote an argument the caller does not
/// write back.
pub(in crate::codegen_ay::chc) const WALKER_FN_PTR_CLOSURE_ALIAS_DROPPED: &str =
    "walker_fn_ptr_closure_alias_dropped";

/// One active inline walk: its body's address-bound reference locals (F2), its
/// locals whose value may hold an address inside a field (F2 residual), and
/// the writes it made through a deref with the W2 rebinding lane, per root
/// local (the F1 exemption). All only grow; SwitchInt arms share the frame.
#[derive(Default)]
pub(in crate::codegen_ay::chc) struct InlineWalkFrame {
    pub(super) native_drop_addresses:
        HashMap<usize, Option<super::native_drop_memory::NativeDropAddress>>,
    address_bound: HashSet<usize>,
    referent_bound: HashSet<usize>,
    pub(super) referent_unknown: HashSet<usize>,
    address_carrying: HashSet<usize>,
    rebind_writes: HashMap<usize, u64>,
    pub(super) native_dyn_origins:
        HashMap<usize, Option<super::native_dyn_origin::NativeDynOrigin>>,
    pub(super) mut_ref_owners:
        HashMap<usize, Option<super::inline_mut_ref_owner::InlineMutRefOwner>>,
    pub(super) rustcall_mut_ref_args:
        HashMap<usize, Option<Vec<Option<super::inline_mut_ref_owner::InlineMutRefArg>>>>,
    pub(super) readonly_ref_values:
        HashMap<usize, Option<super::inline_readonly_ref::ReadonlyRefValue>>,
}

/// Every reason this module (and F4 in `heap/memory_impl_region.rs`) records.
#[cfg_attr(not(test), allow(dead_code))]
pub(in crate::codegen_ay::chc) const PHASE0_REASONS: [&str; 14] = [
    WALKER_DEREF_READ_AFTER_WRITE,
    WALKER_SELF_FIELD_MAP_STALE,
    WALKER_DEREF_READ_ADDRESS_AS_VALUE,
    WALKER_SELF_FIELD_UNLOADED,
    WALKER_DEREF_WRITEBACK_MEMORY_ONLY,
    DYN_DISPATCH_ALIAS_UPDATE_SORT_MISMATCH,
    WALKER_DEREF_WRITE_DROPPED,
    WALKER_SET_DISCRIMINANT_DROPPED,
    WALKER_DEREF_WRITE_REBIND_LOST,
    WALKER_STORE_IN_BRANCH_ARM,
    WALKER_NESTED_ALIAS_WRITEBACK_DROPPED,
    LostEffect::BailedArm.reason(),
    WALKER_FN_PTR_CLOSURE_ALIAS_DROPPED,
    // F4, recorded by heap/memory_impl_region.rs (a private module).
    "heap_region_stale_after_subsort_store",
];

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Run `f` under the outermost inline-walk write mark, taking it now when
    /// no enclosing walk or front door holds one.
    pub(in crate::codegen_ay::chc) fn with_inline_walk_write_mark<T>(
        &mut self,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        if self.inline_walk_write_mark.is_some() {
            return f(self);
        }
        self.inline_walk_write_mark = Some(self.heap_state.write_mark());
        // Objects allocated from here on are the walk's own (F3, M2).
        let saved_alloc_ids = self.heap_state.inline_walk_alloc_ids.replace(HashSet::new());
        let result = f(self);
        self.heap_state.inline_walk_alloc_ids = saved_alloc_ids;
        self.inline_walk_write_mark = None;
        result
    }

    /// Whether a write was recorded since the outermost walk mark.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn inline_walk_written_since_mark(&self) -> bool {
        self.inline_walk_write_mark.is_some_and(|mark| self.heap_state.written_since(mark))
    }

    /// Heap-read hook (F1): every memory read entry calls this. Outside a walk,
    /// or before the walk wrote, it records nothing.
    pub(in crate::codegen_ay::chc) fn note_inline_walk_memory_read(&self) {
        if self.native_drop_memory.is_some() {
            self.refuse_native_drop_memory("native_drop_memory_read_without_ssa");
            return;
        }
        if self.inline_walk_written_since_mark() {
            debug!(fn_name = %self.fn_name, "inline walk: heap read after a write — fail closed");
            self.record_sound_fallback_reason(WALKER_DEREF_READ_AFTER_WRITE);
        }
    }

    /// Run a walk of `body` in its own frame of address-bound locals, seeded
    /// from [`Self::inline_walk_param_address_seeds`] (taken here).
    pub(in crate::codegen_ay::chc) fn with_inline_walk_frame<T>(
        &mut self,
        body: &Body,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let seeds = self.inline_walk_param_address_seeds.take().unwrap_or_default();
        let locals = body.locals();
        let address_bound: HashSet<usize> = seeds
            .into_iter()
            .filter(|&local| local_is_pointer_or_reference(self, locals, local))
            .collect();
        let mut referent_bound: HashSet<usize> = self
            .inline_walk_param_referent_seeds
            .take()
            .unwrap_or_default()
            .into_iter()
            .filter(|&local| local_is_reference(self, locals, local))
            .collect();
        // Legacy logical-value tags carry no read epoch. Only a fresh
        // binder/borrow or an existing current certificate grants the
        // stronger pointer-width RustCall authority.
        let mut readonly_ref_values = HashMap::new();
        for (local, value) in self.inline_walk_param_readonly_ref_seeds.take().unwrap_or_default() {
            if (1..=body.arg_locals().len()).contains(&local)
                && locals.get(local).is_some_and(|decl| self.resolve_body_ty(decl.ty) == value.ty)
                && value.mark == self.heap_state.write_mark()
            {
                if local_is_reference(self, locals, local) {
                    referent_bound.insert(local);
                }
                readonly_ref_values.insert(local, Some(value));
            }
        }
        let mut_ref_owners = self.inline_walk_param_mut_owner_seeds.take().unwrap_or_default()
            .into_iter().filter(|(local, owner)| {
                (1..=body.arg_locals().len()).contains(local)
                    && locals.get(*local).is_some_and(|decl| {
                        matches!(self.resolve_body_ty(decl.ty).kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, rustc_public::mir::Mutability::Mut))
                            if self.resolve_body_ty(pointee) == owner.pointee)
                    })
            }).map(|(local, owner)| (local, Some(owner))).collect();
        let rustcall_mut_ref_args = self.inline_walk_param_rustcall_mut_owner_seeds.take().unwrap_or_default()
            .into_iter().filter(|(local, args)| {
                if !(1..=body.arg_locals().len()).contains(local) { return false; }
                let Some(decl) = locals.get(*local) else { return false; };
                let TyKind::RigidTy(RigidTy::Tuple(fields)) = self.resolve_body_ty(decl.ty).kind() else { return false; };
                fields.len() == args.len() && fields.iter().zip(args).all(|(ty, arg)| {
                    arg.as_ref().is_none_or(|arg| matches!(self.resolve_body_ty(*ty).kind(), TyKind::RigidTy(RigidTy::Ref(_, pointee, rustc_public::mir::Mutability::Mut)) if self.resolve_body_ty(pointee) == arg.owner.pointee))
                })
            }).map(|(local, args)| (local, Some(args))).collect();
        let native_dyn_origins = self
            .inline_walk_param_native_dyn_seeds
            .take()
            .unwrap_or_default()
            .into_iter()
            .filter(|(local, origin)| {
                (1..=body.arg_locals().len()).contains(local)
                    && locals
                        .get(*local)
                        .is_some_and(|decl| self.native_dyn_origin_matches(origin, decl.ty))
            })
            .map(|(local, origin)| (local, Some(origin)))
            .collect();
        if !address_bound.is_empty() {
            debug!(?address_bound, "inline walk: address-bound reference parameters");
        }
        let native_drop_addresses = self
            .inline_walk_param_native_drop_seeds
            .take()
            .unwrap_or_default()
            .into_iter()
            .filter(|(local, address)| {
                self.native_drop_address_matches(address, locals.get(*local).map(|decl| decl.ty))
                    && !super::native_drop_memory::carrier_exposed(body, *local)
            })
            .map(|(local, address)| (local, Some(address)))
            .collect();
        self.inline_walk_frames.push(InlineWalkFrame {
            native_drop_addresses,
            address_bound,
            referent_bound,
            mut_ref_owners,
            rustcall_mut_ref_args,
            readonly_ref_values,
            native_dyn_origins,
            ..Default::default()
        });
        let result = f(self);
        if let Some(frame) = self.inline_walk_frames.pop() {
            self.inline_walk_returned_native_dyn =
                frame.native_dyn_origins.get(&0).cloned().flatten();
            if frame.address_bound.contains(&0) {
                self.inline_walk_returned_address = true;
            }
            if frame.address_carrying.contains(&0) {
                self.inline_walk_returned_carrying = true;
            }
        }
        result
    }

    /// Record a write through a deref of `local` of the innermost walked body
    /// that took the W2 rebinding lane (the pointer local was rebound to the
    /// updated pointee; no memory was written).
    pub(in crate::codegen_ay::chc) fn note_inline_walk_rebind_write(&mut self, local: usize) {
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            *frame.rebind_writes.entry(local).or_default() += 1;
        }
    }

    /// The F1 exemption. A read through `*local` is exact when EVERY write
    /// since the outermost mark was a W2 rebind of that same `local` in this
    /// same body: the local holds the pointee value the last such write
    /// produced (or, on a sibling arm that did not write, its entry value),
    /// and `Deref` reads it as the identity. Any other write — a memory store,
    /// a skipped write, a write to another root (an alias of the same cell), a
    /// write in another body — makes the counts differ. Decided on write
    /// records only, never on a sort or a width; the remaining reads of such a
    /// local (a stale self-field entry, an address-bound term) still fail
    /// closed on their own rules.
    pub(super) fn inline_walk_read_exempt_after_rebinds(&self, local: usize) -> bool {
        let (Some(mark), Some(frame)) =
            (self.inline_walk_write_mark, self.inline_walk_frames.last())
        else {
            return false;
        };
        let writes = self.heap_state.writes_since(mark);
        writes > 0 && frame.rebind_writes.get(&local) == Some(&writes)
    }

    /// The branch-arm rule: a memory effect made while walking one arm of a
    /// multi-target SwitchInt or one candidate of a multi-candidate dispatch
    /// (since `effects_before`, a [`super::heap_state::ChcHeapState::effect_mark`])
    /// is kept in the rule's heap state and applied by the host UNGUARDED, on
    /// every path, and the later arms are walked against it.
    pub(in crate::codegen_ay::chc) fn note_inline_branch_arm_effects(&self, effects_before: u64) {
        if self.heap_state.effect_mark() > effects_before {
            debug!(fn_name = %self.fn_name, "inline walk: memory effect inside a branch arm — fail closed");
            self.record_sound_fallback_reason(WALKER_STORE_IN_BRANCH_ARM);
        }
    }

    /// Whether `local` of the innermost walked body is address-bound.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn inline_walk_local_is_address(&self, local: usize) -> bool {
        self.inline_walk_frames.last().is_some_and(|frame| frame.address_bound.contains(&local))
    }

    /// Mark `local` of the innermost walked body address-bound.
    pub(in crate::codegen_ay::chc) fn tag_inline_walk_address_local(&mut self, local: usize) {
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            frame.address_bound.insert(local);
        }
    }

    /// Whether `local` of the innermost walked body may hold an address in a
    /// field (an aggregate built from, or copied out of, a value whose
    /// reference fields the walk cannot establish as referent values).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn inline_walk_local_carries_address(
        &self,
        local: usize,
    ) -> bool {
        self.inline_walk_frames.last().is_some_and(|frame| frame.address_carrying.contains(&local))
    }

    /// Mark `local` of the innermost walked body as possibly holding an
    /// address in a field.
    pub(in crate::codegen_ay::chc) fn mark_inline_walk_address_carrying(&mut self, local: usize) {
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            frame.address_carrying.insert(local);
        }
    }

    /// Whether `operand` copies an address-bound local of the innermost walk.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn inline_walk_operand_is_address(
        &self,
        operand: &Operand,
    ) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                place.projection.is_empty() && self.inline_walk_local_is_address(place.local)
            }
            _ => false,
        }
    }

    /// Positive value authority from a reference binder or a transparent
    /// borrow. An address or an uncertain reassignment dominates it across
    /// shared SwitchInt frames; an absent address mark is not value authority.
    pub(in crate::codegen_ay::chc) fn inline_walk_operand_is_referent(
        &self,
        operand: &Operand,
    ) -> bool {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else { return false };
        place.projection.is_empty()
            && self.inline_walk_frames.last().is_some_and(|frame| {
                frame.referent_bound.contains(&place.local)
                    && !frame.address_bound.contains(&place.local)
                    && !frame.referent_unknown.contains(&place.local)
            })
    }

    pub(in crate::codegen_ay::chc) fn tag_inline_walk_referent_local(&mut self, local: usize) {
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            frame.referent_bound.insert(local);
        }
    }

    pub(in crate::codegen_ay::chc) fn forget_inline_walk_referent_local(&mut self, local: usize) {
        if let Some(frame) = self.inline_walk_frames.last_mut() {
            frame.referent_unknown.insert(local);
        }
    }
}

/// What the walker's static mirror (`mirror_static_state_var_update`) did with
/// a store.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) enum StaticMirror {
    /// The store's address is the base of a harness `static mut`, whose state
    /// variable took the value.
    Mirrored,
    /// The store reached an object the harness keeps a static state variable
    /// for, which the mirror could not update (a field at a nonzero offset,
    /// another sort, an interior-mutable immutable static): that state
    /// variable keeps the old value.
    StateVarStale,
    /// No harness static state variable holds the stored object.
    NoStateVar,
}

/// The obj_id of an address whose object half is a constant, whatever its
/// offset half (`obj_id ++ offset`, the split-pointer encoding).
fn constant_obj_id(addr: &Expr) -> Option<u32> {
    if let Some(obj_id) = ChcCtx::try_extract_obj_id(addr) {
        return Some(obj_id);
    }
    let ay_bindings::ExprValue::BvConcat(high, _) = addr.value() else {
        return None;
    };
    let ay_bindings::ExprValue::BitVecConst { value, width: 32 } = high.value() else {
        return None;
    };
    let (_, digits) = value.to_u32_digits();
    match digits.as_slice() {
        [] => Some(0),
        [obj_id] => Some(*obj_id),
        _ => None,
    }
}

/// Re-key a walked closure's alias updates to its CALLER's argument
/// numbering. A closure body uses the RustCall local layout (local 1 is the
/// environment, argument `i` is local `i + 2`), and a caller's write-back reads
/// key `k` as argument `k - 1`, so each key shifts down by one. A write to the
/// environment has no argument to reach: it records
/// [`WALKER_FN_PTR_CLOSURE_ALIAS_DROPPED`]. Used by both fn-pointer routes
/// that walk a closure body (the host's `inline_fn_ptr_body` and the nested
/// `walk_nested_fn_ptr_target`, review finding M3).
pub(in crate::codegen_ay::chc) fn rekey_closure_alias_updates_for_caller(
    ctx: &ChcCtx<'_, '_>,
    alias_updates: std::collections::BTreeMap<usize, Expr>,
) -> std::collections::BTreeMap<usize, Expr> {
    let mut rekeyed = std::collections::BTreeMap::new();
    for (local, update) in alias_updates {
        if local >= 2 {
            rekeyed.insert(local - 1, update);
        } else {
            debug!(local, "walked closure behind a fn pointer wrote its environment — fail closed");
            ctx.record_sound_fallback_reason(WALKER_FN_PTR_CLOSURE_ALIAS_DROPPED);
        }
    }
    rekeyed
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// F3 widened (review finding M2): classify a store one of the walker's
    /// store lanes made at `addr` (`try_inline_memory_store` and the mid-chain
    /// `Deref` of `update_inline_value_expr`), after the static mirror did
    /// `mirror`.
    ///
    /// The host reads its locals and statics from state variables and its
    /// arguments' pointees back from alias updates; a store reaches the heap
    /// arrays only. The store is exact for the host only when it reached
    /// * a `static mut` whose state variable the mirror updated;
    /// * an object allocated during the current walk, which no state
    ///   variable of the host holds (see `inline_walk_alloc_ids`);
    /// * a static discovered in a callee, which has an address and no state
    ///   variable, so memory is the only copy of it.
    ///
    /// Every other store records [`WALKER_DEREF_WRITEBACK_MEMORY_ONLY`]: a
    /// store through a raw-pointer copy of an argument, through a reference
    /// held in a by-value aggregate, or through any pointer whose object is
    /// not a constant, may reach a host local's cell, whose state variable
    /// keeps the old value (`walker_referent_write_dual.rs`).
    pub(in crate::codegen_ay::chc) fn classify_inline_walk_lane_store(
        &self,
        addr: &Expr,
        mirror: StaticMirror,
    ) {
        let exact = match mirror {
            StaticMirror::Mirrored => true,
            StaticMirror::StateVarStale => false,
            StaticMirror::NoStateVar => constant_obj_id(addr).is_some_and(|obj_id| {
                self.heap_state.inline_walk_allocated(obj_id)
                    || self.is_stateless_static_obj(obj_id)
            }),
        };
        if !exact {
            debug!(
                fn_name = %self.fn_name,
                ?mirror,
                "inline walk: a store no host state variable sees — fail closed (F3, M2)"
            );
            self.record_sound_fallback_reason(WALKER_DEREF_WRITEBACK_MEMORY_ONLY);
        }
    }

    /// Whether `obj_id` is a static's object that no harness state variable
    /// holds (a static discovered only in a callee body).
    fn is_stateless_static_obj(&self, obj_id: u32) -> bool {
        !self.ref_resolution.static_state_idx_by_obj.contains_key(&obj_id)
            && self
                .ref_resolution
                .global_objects
                .iter()
                .any(|(key, object)| key.static_def().is_some() && object.obj_id == obj_id)
    }
}

/// Address seeds for a dyn-door walk: every reference-typed parameter whose
/// term has a pointer's shape. The dyn door binds raw operand terms
/// (`translate_operand_with_modified`), which report nothing about what they
/// returned, so a pointer-shaped term cannot be established as the referent
/// value; a term of another shape (a narrower bitvector, a datatype without a
/// declared address) cannot be an address.
pub(in crate::codegen_ay::chc) fn dyn_door_address_seeds(
    ctx: &ChcCtx<'_, '_>,
    body: &Body,
    params: &[Expr],
) -> Vec<usize> {
    let locals = body.locals();
    params
        .iter()
        .enumerate()
        .take(body.arg_locals().len())
        .filter(|(i, param)| {
            local_is_reference(ctx, locals, i + 1)
                && crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(param).is_some()
        })
        .map(|(i, _)| i + 1)
        .collect()
}

/// Whether `local` is declared `&T` / `&mut T` in `locals`.
pub(in crate::codegen_ay::chc) fn local_is_reference(
    ctx: &ChcCtx<'_, '_>,
    locals: &[LocalDecl],
    local: usize,
) -> bool {
    locals.get(local).is_some_and(|decl| {
        matches!(ctx.resolve_body_ty(decl.ty).kind(), TyKind::RigidTy(RigidTy::Ref(..)))
    })
}

/// The type permits an explicitly produced address fact. This does not
/// establish that fact: callers must supply a real address producer/seed.
pub(in crate::codegen_ay::chc) fn local_is_pointer_or_reference(
    ctx: &ChcCtx<'_, '_>,
    locals: &[LocalDecl],
    local: usize,
) -> bool {
    locals.get(local).is_some_and(|decl| {
        matches!(
            ctx.resolve_body_ty(decl.ty).kind(),
            TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..))
        )
    })
}

/// Whether `a` is the very term `b` (same sort, same shared node). A rebind to
/// a structurally equal but freshly built term counts as a rebind, which only
/// fails closed more often.
fn same_term(a: Option<&Expr>, b: &Expr) -> bool {
    a.is_some_and(|a| a.sort() == b.sort() && std::ptr::eq(a.value(), b.value()))
}

/// The self-field entry `resolve_projected_place` serves for `place`, if any:
/// the first `Field` after the leading `Deref` (with no second `Deref` before
/// it), or the whole-object entry for a bare `*local`.
fn served_self_field_entry<'m>(
    map: &'m HashMap<(usize, usize), Expr>,
    place: &Place,
) -> Option<&'m Expr> {
    for proj in &place.projection[1..] {
        match proj {
            ProjectionElem::Field(idx, _) => return map.get(&(place.local, *idx)),
            ProjectionElem::Downcast(_) | ProjectionElem::OpaqueCast(_) => {}
            _ => return None,
        }
    }
    map.get(&(place.local, DIRECT_DEREF_FIELD))
}

/// Why a projected read inside an inline walk must fail closed, if it must.
/// What the guard does with a projected read.
enum GuardedRead {
    /// Fail closed with this reason.
    FailClosed(&'static str),
    /// The self-field snapshot is stale, but the local's term is the pointee
    /// value: resolve through the term, without the snapshot.
    ThroughTerm,
}

/// Whether `local`'s current term can answer a read through `*local` in place
/// of a stale self-field snapshot: an untagged `&T` whose term has the
/// pointee's datatype sort and declares no address field, so it is the pointee
/// VALUE in the walker's reference convention (the updated value a W2 rebind
/// produced, or a value-convention reference it was reassigned from), never an
/// address. Decided with F1 already passed: no write since the outermost mark
/// other than W2 rebinds of this very local.
fn term_answers_for_stale_map(
    ctx: &ChcCtx<'_, '_>,
    local_exprs: &HashMap<usize, Expr>,
    locals: &[LocalDecl],
    local: usize,
) -> bool {
    if ctx.inline_walk_local_is_address(local) {
        return false;
    }
    let (Some(term), Some(decl)) = (local_exprs.get(&local), locals.get(local)) else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) = ctx.resolve_body_ty(decl.ty).kind() else {
        return false;
    };
    let Some(pointee_sort) = ChcCtx::translate_ty(ctx.resolve_body_ty(pointee)) else {
        return false;
    };
    pointee_sort.is_datatype()
        && *term.sort() == pointee_sort
        && crate::codegen_ay::chc::dyn_coercion::extract_pointer_expr(term).is_none()
}

fn projected_read_fail_closed_reason(
    ctx: &ChcCtx<'_, '_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<GuardedRead> {
    let leading_deref = matches!(place.projection.first(), Some(ProjectionElem::Deref));
    if ctx.inline_walk_written_since_mark()
        && !(leading_deref && ctx.inline_walk_read_exempt_after_rebinds(place.local))
    {
        return Some(GuardedRead::FailClosed(WALKER_DEREF_READ_AFTER_WRITE));
    }
    if !leading_deref {
        return None;
    }
    let map = match resolver {
        PlaceResolver::FieldMap(map) => Some(*map),
        PlaceResolver::Captures(_) => None,
    };
    if let Some(map) = map
        && let Some(root) = map.get(&(place.local, SELF_FIELD_MAP_ROOT_TERM))
        && !same_term(local_exprs.get(&place.local), root)
    {
        // Invalidated: the snapshot no longer answers for this local.
        return Some(if term_answers_for_stale_map(ctx, local_exprs, locals, place.local) {
            GuardedRead::ThroughTerm
        } else {
            GuardedRead::FailClosed(WALKER_SELF_FIELD_MAP_STALE)
        });
    }
    if let Some(entry) = map.and_then(|map| served_self_field_entry(map, place)) {
        return is_unloaded_self_field_entry(entry)
            .then_some(GuardedRead::FailClosed(WALKER_SELF_FIELD_UNLOADED));
    }
    (ctx.inline_walk_local_is_address(place.local) && local_is_reference(ctx, locals, place.local))
        .then_some(GuardedRead::FailClosed(WALKER_DEREF_READ_ADDRESS_AS_VALUE))
}

/// Fail-closed guard for a projected read inside an inline walk, called by
/// `resolve_place` before either resolver runs. `Some(havoc)` when the read
/// must not be trusted: the reason is recorded and a fresh value of the
/// place's sort flows instead (never `None`, which can reach the Assert arm's
/// assume-pass). When the place's sort is unknown the reason is still recorded
/// and the ordinary resolution runs.
pub(in crate::codegen_ay::chc) fn guard_inline_projected_read(
    ctx: &mut ChcCtx<'_, '_>,
    local_exprs: &HashMap<usize, Expr>,
    place: &Place,
    resolver: &PlaceResolver<'_>,
    locals: &[LocalDecl],
) -> Option<Expr> {
    if ctx.native_drop_memory.is_some()
        && place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
    {
        if let Some(value) = ctx.read_native_drop_place(local_exprs, place, locals) {
            return Some(value);
        }
        ctx.refuse_native_drop_memory("native_drop_projected_read_unmodeled");
    }
    if ctx.inline_walk_frames.is_empty() && ctx.inline_walk_write_mark.is_none() {
        return None;
    }
    if !place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Deref)) {
        return None;
    }
    let reason = projected_read_fail_closed_reason(ctx, local_exprs, place, resolver, locals);
    let reason = if !matches!(&reason, Some(GuardedRead::FailClosed(_)))
        && !super::inline_shared::projected_scalar_ref::has_value_view(
            ctx,
            local_exprs,
            place,
            resolver,
            locals,
        ) {
        Some(GuardedRead::FailClosed("walker_projected_scalar_ref_value_unproven"))
    } else {
        reason
    };
    let reason = match reason? {
        GuardedRead::FailClosed(reason) => reason,
        GuardedRead::ThroughTerm => {
            let no_snapshot = HashMap::new();
            if let Some(value) = super::inline_shared::field_map_projection::resolve_projected_place(
                ctx,
                local_exprs,
                place,
                &no_snapshot,
                locals,
            ) {
                debug!(
                    local = place.local,
                    projection = ?place.projection,
                    "inline walk: rebound local read through its term, not the stale snapshot"
                );
                return Some(value);
            }
            WALKER_SELF_FIELD_MAP_STALE
        }
    };
    debug!(
        fn_name = %ctx.fn_name,
        local = place.local,
        projection = ?place.projection,
        reason,
        "inline walk: projected read fails closed"
    );
    let booked = ctx.record_sound_fallback_reason(reason);
    havoc_for_place(ctx, booked, place, locals)
}

/// A fresh value of `place`'s sort, standing on the caller's booking.
pub(in crate::codegen_ay::chc) fn havoc_for_place(
    ctx: &mut ChcCtx<'_, '_>,
    booked: crate::codegen_ay::chc::codegen_ctx::Booked,
    place: &Place,
    locals: &[LocalDecl],
) -> Option<Expr> {
    let ty = ctx.resolve_body_ty(place.ty(locals).ok()?);
    let sort = match ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty() => {
            Expr::bool_const(true).sort().clone()
        }
        _ => ChcCtx::translate_ty(ty)?,
    };
    ctx.declare_datatype_sort_if_needed(&sort);
    let name = chc_fresh_name("__walker_fail_closed_read");
    ctx.heap_state.fail_closed_havocs.insert(name.clone());
    Some(Havoc::booked(booked, name, sort))
}

/// Whether a block is dead by rustc's own proof: no statements and an
/// `Unreachable` terminator (#3889), or a single `Goto` onto one (#4050).
/// Such an arm carries no obligation.
pub(in crate::codegen_ay::chc) fn block_is_proven_dead(body: &Body, bb: usize) -> bool {
    use rustc_public::mir::TerminatorKind;
    let blocks = &body.blocks;
    let Some(block) = blocks.get(bb) else {
        return false;
    };
    // Inert statements (storage markers and the like) do not make the block
    // live (fix/chc-walker-fail-closed): rustc proved it unreachable all the same.
    use crate::codegen_ay::obligation_free_walk::statement_is_inert;
    match &block.terminator.kind {
        TerminatorKind::Unreachable => block.statements.iter().all(statement_is_inert),
        TerminatorKind::Goto { target } => {
            block.statements.iter().all(statement_is_inert)
                && blocks.get(*target).is_some_and(|next| {
                    matches!(next.terminator.kind, TerminatorKind::Unreachable)
                        && next.statements.iter().all(statement_is_inert)
                })
        }
        _ => false,
    }
}

/// Rule D's one predicate: whether the region of `body` reachable from
/// `start` along normal-path successors, up to `Return`, can CHECK or WRITE.
/// A translation that replaces such a region by nothing (a bailed SwitchInt
/// arm, a havocked callee) loses an obligation and books a [`LostEffect`].
///
/// It CHECKS unless the obligation-free walk certifies the region
/// (`obligation_free_walk::region_verdict` is `Free`): every statement and
/// terminator by the walk's rules, which mirror the encoder's check emitters
/// (an `Assert`, a UB-carrying `BinOp` such as `AddUnchecked`, a raw-pointer
/// deref, `Offset`, an `Unreachable` rustc did not prove dead, inline asm,
/// and every callee walked through unless it is an obligation-free intrinsic).
/// "Could not tell" counts as a check.
///
/// It WRITES when it assigns or sets a discriminant through a deref, runs a
/// `CopyNonOverlapping` or a `Drop`, or calls with a writable pointer (a raw
/// pointer, a `&mut`, or a `&T` to interior-mutable data) or a deref
/// destination. The scope is the whole continuation, not a merge block: the
/// fallback's `InlineReturn` replaces the arm through its `Return`.
pub(in crate::codegen_ay::chc) fn region_may_check_or_write(
    ctx: &ChcCtx<'_, '_>,
    body: &Body,
    start: usize,
) -> bool {
    region_may_check_or_write_discharging(ctx, body, start, None)
}

/// [`region_may_check_or_write`], not counting the region body's own sites
/// that `discharge` proves hold on every path (the bailed-arm site's interval
/// facts, `codegen_call_virtual_inline/region_intervals.rs`): dropping a check
/// that cannot fail drops no obligation. Writes count as before.
pub(in crate::codegen_ay::chc) fn region_may_check_or_write_discharging(
    ctx: &ChcCtx<'_, '_>,
    body: &Body,
    start: usize,
    discharge: Option<&crate::codegen_ay::obligation_free_walk::RegionDischarge<'_>>,
) -> bool {
    region_may_write(ctx, body, start)
        || crate::codegen_ay::obligation_free_walk::region_verdict_discharging(
            ctx.tcx,
            body,
            start,
            |bb| block_is_proven_dead(body, bb),
            discharge,
        ) != crate::codegen_ay::obligation_free_walk::Verdict::Free
}

/// The WRITE half of [`region_may_check_or_write`].
pub(in crate::codegen_ay::chc) fn region_may_write(
    ctx: &ChcCtx<'_, '_>,
    body: &Body,
    start: usize,
) -> bool {
    use rustc_public::mir::{NonDivergingIntrinsic, StatementKind, TerminatorKind};
    let locals = body.locals();
    let writes_through_deref =
        |place: &Place| place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
    let mut seen = HashSet::new();
    let mut stack = vec![start];
    while let Some(bb) = stack.pop() {
        if !seen.insert(bb) {
            continue;
        }
        let Some(block) = body.blocks.get(bb) else {
            continue;
        };
        for stmt in &block.statements {
            let writes = match &stmt.kind {
                StatementKind::Assign(place, _) => writes_through_deref(place),
                StatementKind::SetDiscriminant { place, .. } => writes_through_deref(place),
                StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping(_)) => true,
                _ => false,
            };
            if writes {
                return true;
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Drop { .. } => return true,
            TerminatorKind::Call { args, destination, .. } => {
                if writes_through_deref(destination)
                    || args.iter().any(|arg| {
                        arg.ty(locals).is_ok_and(|ty| {
                            crate::codegen_ay::foreign_defs::arg_is_writable_pointer(ctx.tcx, ty)
                        })
                    })
                {
                    return true;
                }
            }
            _ => {}
        }
        // Normal-path successors only: the walker never walks an unwind
        // cleanup block (a panic is an error, not a path Kani continues).
        match &block.terminator.kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Drop { target, .. }
            | TerminatorKind::Assert { target, .. }
            | TerminatorKind::Call { target: Some(target), .. } => stack.push(*target),
            TerminatorKind::SwitchInt { targets, .. } => {
                stack.extend(targets.branches().map(|(_, bb)| bb));
                stack.push(targets.otherwise());
            }
            TerminatorKind::InlineAsm { destination: Some(target), .. } => stack.push(*target),
            _ => {}
        }
    }
    false
}
