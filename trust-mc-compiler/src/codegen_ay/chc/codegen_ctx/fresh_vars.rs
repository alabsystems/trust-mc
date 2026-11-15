// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Rule E (design trust-mc-reds-final §4.4): a fresh symbolic value says what
//! it is.
//!
//! A `declare-var` the encoder mints is universally quantified over its rule.
//! What that means for a verdict depends on WHY the value is fresh, and a
//! verdict can only account for an approximation it is told about: a fresh
//! value that stood for something the encoding does not compute, booked
//! nowhere, let a counterexample through it be certified Genuine
//! (`zst_enum_variant_index_dual.rs::safe_iflet_b_direct`). So code outside
//! `codegen_ctx` cannot declare one directly (`globals::declare_pending_var`
//! is private to it, and `test_fresh_var_single_rule` holds the spelling): it
//! asks for one of these constructors, and each states the reason.
//!
//! - [`ExactVar::defined`]: pinned by a defining equation the caller emits in
//!   the same rule (`v == e`, a quantified relation, a renaming, an ITE whose
//!   cases the emitted constraints make exhaustive).
//! - [`ExactVar::nondet`]: the program's own semantics leave the value
//!   unspecified, so every value is an execution: `kani::any`, padding bytes,
//!   uninitialized memory, an indeterminate C local, the address identity of
//!   two zero-sized allocations, Kani's own nondeterministic model choices.
//! - [`ExactVar::unobserved`]: no execution reads the value as data: a cell
//!   past a sequence's length, a payload slot of a constructor that has no
//!   field there, the value on a path an emitted check refutes, a placeholder
//!   whose every read fails closed.
//! - [`Havoc::mint`]: a VALUE the encoding does not compute, replaced by a
//!   fresh one under an audited [`SoundHavocReason`]. The havoc only adds
//!   behaviours, so a proof stands; the value is booked with its identity, so a
//!   counterexample that reads it is OverApproximation unless
//!   `recertify_overapprox_ctrex` certifies it.
//! - [`Havoc::booked`]: a fresh value standing on a booking this translation
//!   already made, proved by its [`Booked`] token: a sound-fallback reason
//!   (audited or fail-closed), a demoting fallback, a lost obligation, or a
//!   counter a verdict reads.
//!
//! Evidence rung: a type plus a review. The constructors force a choice at
//! every site; whether a `defined` value really has its equation, or a
//! [`SoundHavocReason`] is truly value-only, is audited by people (design §10,
//! residual 2). Each site's choice is its constructor and reason in the code;
//! the classes, the rules for choosing among them and their counts are in
//! `docs/DECISION_QUEUE.md` (REDS-REST).

use ay_bindings::{Expr, Sort};

use super::ChcCtx;
use super::globals::declare_pending_var;

/// Proof that this translation booked an approximation a verdict reads. Only
/// the recorders in `codegen_ctx` (and the verdict-read counters of
/// `ChcDiagnostics`) make one.
#[derive(Clone, Copy, Debug)]
pub(in crate::codegen_ay::chc) struct Booked {
    _recorded: (),
}

impl Booked {
    pub(in crate::codegen_ay::chc::codegen_ctx) const fn recorded() -> Self {
        Booked { _recorded: () }
    }

    /// A token for a unit test of a builder, which has no translation to book
    /// into.
    #[cfg(test)]
    pub(in crate::codegen_ay::chc) const fn for_test() -> Self {
        Booked { _recorded: () }
    }
}

/// A sound-havoc reason whose audit line is in `codegen_ctx::fallback_soundness`.
/// Only the consts of [`sound_havoc`] build one, and a unit test holds every one
/// of them to `fallback_soundness(..) == SoundHavoc`, so a new reason needs its
/// audit line before a site can mint under it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::codegen_ay::chc) struct SoundHavocReason(&'static str);

impl SoundHavocReason {
    #[must_use]
    pub(in crate::codegen_ay::chc) const fn as_str(self) -> &'static str {
        self.0
    }
}

/// The audited sound-havoc reasons the Rule E constructors mint under. Each is
/// listed, with its audit, in `codegen_ctx::fallback_soundness`.
pub(in crate::codegen_ay::chc) mod sound_havoc {
    use super::SoundHavocReason;

    /// A collection model's length, data, keys, iterator state or predicate
    /// result the stub does not compute.
    pub(in crate::codegen_ay::chc) const UNTRACKED_COLLECTION_STATE: SoundHavocReason =
        SoundHavocReason("untracked_collection_state");
    /// An address the model does not pin (a buffer's base, a drop's `self`, an
    /// allocator result, a reference payload).
    pub(in crate::codegen_ay::chc) const UNTRACKED_POINTER_VALUE: SoundHavocReason =
        SoundHavocReason("untracked_pointer_value");
    /// Vtable metadata, a type id or a vtable discriminant for a vtable id no
    /// registered type has.
    pub(in crate::codegen_ay::chc) const UNTRACKED_VTABLE_METADATA: SoundHavocReason =
        SoundHavocReason("untracked_vtable_metadata");
    /// The state, payload, field or discriminant of a coroutine the walk does
    /// not resume.
    pub(in crate::codegen_ay::chc) const UNTRACKED_COROUTINE_STATE: SoundHavocReason =
        SoundHavocReason("untracked_coroutine_state");
    /// A value replaced because its sort and the slot's disagree.
    pub(in crate::codegen_ay::chc) const UNTRACKED_SORT_MISMATCH_VALUE: SoundHavocReason =
        SoundHavocReason("untracked_sort_mismatch_value");
    /// A discriminant the encoding does not read, ranging over the variants'
    /// discriminant values (or wider).
    pub(in crate::codegen_ay::chc) const UNTRACKED_DISCRIMINANT: SoundHavocReason =
        SoundHavocReason("untracked_discriminant");
    /// An intrinsic's or library call's result the model does not compute.
    pub(in crate::codegen_ay::chc) const UNTRACKED_CALL_RESULT: SoundHavocReason =
        SoundHavocReason("untracked_call_result");
    /// Bytes or metadata of a constant the encoding does not read out.
    pub(in crate::codegen_ay::chc) const UNTRACKED_CONSTANT_BYTES: SoundHavocReason =
        SoundHavocReason("untracked_constant_bytes");
    /// A value the inline walker hands back without computing it.
    pub(in crate::codegen_ay::chc) const UNTRACKED_WALKER_VALUE: SoundHavocReason =
        SoundHavocReason("untracked_walker_value");
    /// A big-number value the LIA model does not compute.
    pub(in crate::codegen_ay::chc) const UNTRACKED_BIGNUM_VALUE: SoundHavocReason =
        SoundHavocReason("untracked_bignum_value");
    /// A memory cell read under a type key no store wrote it under (Rule C's
    /// backstop, `heap/memory_cell_backstop.rs`). Booked with the cell, not
    /// minted: the read itself is the unconstrained value.
    pub(in crate::codegen_ay::chc) const MEMORY_CELL_UNWRITTEN_UNDER_KEY: SoundHavocReason =
        SoundHavocReason("memory_cell_unwritten_under_key");
    /// An iterator adapter's value the model has no exact term for (a `fold` /
    /// `sum` result, a `next` payload, a filter's keep bit:
    /// `fresh_adapter_symbol`). Main's reason, kept by name when the
    /// reds-rest/residuals merge routed the site through Rule E.
    pub(in crate::codegen_ay::chc) const ITER_ADAPTER_SYMBOL_OVERAPPROX: SoundHavocReason =
        SoundHavocReason("iter_adapter_symbol_overapprox");
    /// `Vec::extend`'s new length when the source length does not resolve: a
    /// fresh value no smaller than the old (`vec_op_extend_from_slice`).
    pub(in crate::codegen_ay::chc) const VEC_EXTEND_SOURCE_LEN_UNRESOLVED: SoundHavocReason =
        SoundHavocReason("vec_extend_source_len_unresolved");
    /// The free "far again, or back in range" bit of a wrapping pointer step
    /// from a far pointer whose full 64-bit offset is unknown
    /// (`heap/stack_address.rs`, `far_step_unknown`). It replaced the landed
    /// model's `wrapping_step_landed_unknown` (fix/chc-false-certificates,
    /// the sixth round's far pointers).
    pub(in crate::codegen_ay::chc) const WRAPPING_STEP_FAR_UNKNOWN: SoundHavocReason =
        SoundHavocReason("wrapping_step_far_unknown");
    /// The free guard bit of a fail-closed far pointer observation's error
    /// copy (`heap/stack_address.rs`, `apply_far_observation_cuts`): the copy's
    /// property reads it, so it is never certified, while the cut rule reads
    /// nothing of it.
    pub(in crate::codegen_ay::chc) const FAR_POINTER_OBSERVATION: SoundHavocReason =
        SoundHavocReason("far_pointer_observation");
    /// An `Iterator::sum` value the sum stub does not compute (a float sum,
    /// elements past the replay, a sequence it cannot address): `reduce.rs`
    /// `reduce_havoc`.
    pub(in crate::codegen_ay::chc) const ITER_SUM_VALUE_OVERAPPROX: SoundHavocReason =
        SoundHavocReason("iter_sum_value_overapprox");
    /// The free flag of the sum stub's conservative overflow rule for the
    /// elements its replay did not check (`reduce.rs` `iter_conservative_flag`).
    pub(in crate::codegen_ay::chc) const ITER_SUM_OVERFLOW_UNCHECKED: SoundHavocReason =
        SoundHavocReason("iter_sum_overflow_unchecked");
    /// The free flag of the rule for a `Sum` impl the sum stub does not model.
    pub(in crate::codegen_ay::chc) const ITER_SUM_IMPL_UNMODELED: SoundHavocReason =
        SoundHavocReason("iter_sum_impl_unmodeled");
    /// The free flag of the rule for a closure an iterator stub runs and does
    /// not encode (`codegen_call_iterator_adapter/mod.rs`).
    pub(in crate::codegen_ay::chc) const ITER_ADAPTER_CLOSURE_UNMODELED: SoundHavocReason =
        SoundHavocReason("iter_adapter_closure_unmodeled");
    /// The free flag of the rule for a float sum's "NaN on addition" under
    /// `--nan-check`.
    pub(in crate::codegen_ay::chc) const ITER_SUM_NAN_UNCHECKED: SoundHavocReason =
        SoundHavocReason("iter_sum_nan_unchecked");
    /// The free bit `t` of a `Vec::with_capacity` buffer's bound `ite(t, 0,
    /// bytes)` when the `Vec` may grow past the recorded capacity
    /// (`call/codegen_call_vec_ops/constructors.rs`, `taint_vec_capacity_size`).
    pub(in crate::codegen_ay::chc) const VEC_CAPACITY_SIZE_UNCERTIFIED: SoundHavocReason =
        SoundHavocReason("vec_capacity_size_uncertified");
    /// The bytes of a flattened enum's untagged variant whose payload has no
    /// exact byte image (`call/codegen_call_result_mem.rs`,
    /// `flattened_enum_tag_image`).
    pub(in crate::codegen_ay::chc) const ENUM_TAG_IMAGE_PAYLOAD_UNKNOWN: SoundHavocReason =
        SoundHavocReason("enum_tag_image_payload_unknown");
    /// The values `Vec::extend` appends from a range whose count is symbolic
    /// or past the store bound (`codegen_call_vec_ops_extend_range.rs`,
    /// `appended_data`). The Vec's `len` and `cap` fields are written exactly.
    pub(in crate::codegen_ay::chc) const VEC_EXTEND_RANGE_ELEMENTS_UNMODELLED: SoundHavocReason =
        SoundHavocReason("vec_extend_range_elements_unmodelled");
    /// The values `Vec::extend_from_slice` / `extend` appends from a slice
    /// whose length is known and whose values are not
    /// (`codegen_call_vec_ops_len.rs`).
    pub(in crate::codegen_ay::chc) const VEC_EXTEND_SLICE_ELEMENTS_UNMODELLED: SoundHavocReason =
        SoundHavocReason("vec_extend_slice_elements_unmodelled");
    /// A Vec's grown capacity where the model does not know `RawVec`'s growth:
    /// a fresh value of at least the required capacity
    /// (`codegen_call_vec_ops/shared.rs`, `vec_fresh_grown_cap`).
    pub(in crate::codegen_ay::chc) const VEC_GROWN_CAPACITY_UNMODELLED: SoundHavocReason =
        SoundHavocReason("vec_grown_capacity_unmodelled");
    /// A collected Vec's capacity where the collect may reuse its source
    /// Vec's buffer: a fresh value of at least the length
    /// (`codegen_call_iterator_adapter/collect.rs`, `collected_vec_cap`).
    pub(in crate::codegen_ay::chc) const VEC_COLLECTED_CAPACITY_UNMODELLED: SoundHavocReason =
        SoundHavocReason("vec_collected_capacity_unmodelled");
    /// The elements of the Vec `split_off` returns
    /// (`codegen_call_vec_ops_mutate.rs`, `vec_op_split_off`); its length and
    /// capacity are written exactly.
    pub(in crate::codegen_ay::chc) const VEC_SPLIT_OFF_ELEMENTS_UNMODELLED: SoundHavocReason =
        SoundHavocReason("vec_split_off_elements_unmodelled");
    /// The `Option<char>` `chars().nth(..)` returns where the string's bytes
    /// may hold a multi-byte char (`codegen_call_string_nth.rs`).
    pub(in crate::codegen_ay::chc) const STR_CHARS_NTH_MULTIBYTE_OVERAPPROX: SoundHavocReason =
        SoundHavocReason("str_chars_nth_multibyte_overapprox");

    /// Every reason above, for the table test.
    #[cfg(test)]
    pub(in crate::codegen_ay::chc) const ALL: &[SoundHavocReason] = &[
        UNTRACKED_COLLECTION_STATE,
        UNTRACKED_POINTER_VALUE,
        UNTRACKED_VTABLE_METADATA,
        UNTRACKED_COROUTINE_STATE,
        UNTRACKED_SORT_MISMATCH_VALUE,
        UNTRACKED_DISCRIMINANT,
        UNTRACKED_CALL_RESULT,
        UNTRACKED_CONSTANT_BYTES,
        UNTRACKED_WALKER_VALUE,
        UNTRACKED_BIGNUM_VALUE,
        MEMORY_CELL_UNWRITTEN_UNDER_KEY,
        ITER_ADAPTER_SYMBOL_OVERAPPROX,
        VEC_EXTEND_SOURCE_LEN_UNRESOLVED,
        WRAPPING_STEP_FAR_UNKNOWN,
        FAR_POINTER_OBSERVATION,
        ITER_SUM_VALUE_OVERAPPROX,
        ITER_SUM_OVERFLOW_UNCHECKED,
        ITER_SUM_IMPL_UNMODELED,
        ITER_ADAPTER_CLOSURE_UNMODELED,
        ITER_SUM_NAN_UNCHECKED,
        VEC_CAPACITY_SIZE_UNCERTIFIED,
        ENUM_TAG_IMAGE_PAYLOAD_UNKNOWN,
        VEC_EXTEND_RANGE_ELEMENTS_UNMODELLED,
        VEC_EXTEND_SLICE_ELEMENTS_UNMODELLED,
        VEC_GROWN_CAPACITY_UNMODELLED,
        VEC_COLLECTED_CAPACITY_UNMODELLED,
        VEC_SPLIT_OFF_ELEMENTS_UNMODELLED,
        STR_CHARS_NTH_MULTIBYTE_OVERAPPROX,
    ];
}

/// A fresh variable that is not an approximation (see the module docs).
pub(in crate::codegen_ay::chc) struct ExactVar;

impl ExactVar {
    /// Pinned by a defining equation the caller emits in the same rule.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn defined(name: String, sort: Sort) -> Expr {
        declare_pending_var(name, sort)
    }

    /// Every value is an execution of the program: its semantics leave the
    /// value unspecified.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn nondet(name: String, sort: Sort) -> Expr {
        declare_pending_var(name, sort)
    }

    /// No execution reads the value as data.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn unobserved(name: String, sort: Sort) -> Expr {
        declare_pending_var(name, sort)
    }
}

/// A fresh value standing for one the encoding does not compute (see the
/// module docs).
pub(in crate::codegen_ay::chc) struct Havoc;

impl Havoc {
    /// Book `reason` with the fresh value's identity, then mint it.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn mint(
        ctx: &mut ChcCtx<'_, '_>,
        reason: SoundHavocReason,
        name: String,
        sort: Sort,
    ) -> Expr {
        ctx.record_sound_fallback_reason_identified(reason.as_str(), Some(&name));
        declare_pending_var(name, sort)
    }

    /// [`Self::mint`] for a site that holds the context shared: the identity
    /// is queued and accounted when the translation is finalized.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn mint_deferred(
        ctx: &ChcCtx<'_, '_>,
        reason: SoundHavocReason,
        name: String,
        sort: Sort,
    ) -> Expr {
        ctx.record_sound_fallback_reason_identified_deferred(reason.as_str(), name.clone());
        declare_pending_var(name, sort)
    }

    /// Book `reason` WITHOUT the value's identity: the harness's approximations
    /// are then incomplete, so no counterexample in it is certified Genuine.
    /// For a value whose dependents the identity would not cover (a path the
    /// value stands on, not only the value).
    #[must_use]
    pub(in crate::codegen_ay::chc) fn mint_unattributed(
        ctx: &ChcCtx<'_, '_>,
        reason: SoundHavocReason,
        name: String,
        sort: Sort,
    ) -> Expr {
        let _: Booked = ctx.record_sound_fallback_reason(reason.as_str());
        declare_pending_var(name, sort)
    }

    /// A fresh value standing on a booking this translation already made.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn booked(_booking: Booked, name: String, sort: Sort) -> Expr {
        declare_pending_var(name, sort)
    }
}
