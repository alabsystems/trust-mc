// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Unsoundness counter collector functions for fallback, fail-closed,
//! and statement-level counters.
//!
//! Extracted from `unsoundness_fields.rs` — Part of #4206.

use tracing::warn;
use trust_mc_metadata::{
    AbstractedFallbackInfo, AssertUntranslatableInfo, ChcFallbackInfo, ChcTranslationDropInfo,
    ConstantZeroFallbackInfo, ErrorBlockedFmtInfo, HeapCheckUnknownLayoutInfo,
    HeapCheckUntranslatableInfo, InternalWorkaroundInfo, IntoOptionDropInfo,
    KnownStdlibUnconstrainedInfo, PointeeSynthesisFallbackInfo, SignednessFallbackInfo,
    TypeSortFallbackInfo, UnconstrainedAssignmentInfo, UnhandledCallInfo,
    UnsupportedConstructFallbackInfo, VecFieldFallbackInfo,
};

use super::{
    get_chc_assert_untranslatable_count, get_chc_heap_check_unknown_layout_count,
    get_chc_heap_check_untranslatable_count, take_abstracted_fallback_count,
    take_chc_fallback_counts, take_chc_unhandled_call_count, take_constant_translation_drop_count,
    take_constant_zero_fallback_count, take_drop_fallback_reasons_by_fn,
    take_error_blocked_fmt_count, take_internal_workaround_count, take_into_option_dropped_count,
    take_known_stdlib_unconstrained_count, take_place_translation_drop_count,
    take_pointee_synthesis_fallback_count, take_signedness_fallback_by_fn,
    take_signedness_fallback_count, take_sound_havoc_drop_by_fn, take_translation_drop_by_fn,
    take_translation_drop_site_reasons_by_fn, take_type_sort_fallback_by_fn,
    take_type_sort_fallback_count, take_unconstrained_assignment_count, take_unhandled_call_by_fn,
    take_unsupported_construct_fallback_count, take_unsupported_field_projection_count,
    take_vec_field_fallback_counter,
};

/// Collect fallback and dispatch counters.
#[allow(clippy::type_complexity)]
pub(super) fn collect_fallback_fields() -> (
    Option<ChcFallbackInfo>,
    Option<ChcTranslationDropInfo>,
    Option<UnhandledCallInfo>,
    Option<ErrorBlockedFmtInfo>,
    Option<KnownStdlibUnconstrainedInfo>,
    Option<ConstantZeroFallbackInfo>,
    Option<TypeSortFallbackInfo>,
    Option<SignednessFallbackInfo>,
) {
    let per_harness = take_chc_fallback_counts();
    let chc_fallbacks = if per_harness.is_empty() {
        None
    } else {
        let total_count = per_harness.values().copied().sum::<usize>();
        warn!(
            total_count,
            harness_count = per_harness.len(),
            "CHC used type/size fallback defaults"
        );
        Some(ChcFallbackInfo { total_count, per_harness })
    };

    let place_drop_count = take_place_translation_drop_count();
    let constant_drop_count = take_constant_translation_drop_count();
    let field_projection_drop_count = take_unsupported_field_projection_count();
    let translation_drop_per_harness = take_translation_drop_by_fn();
    let drop_fallback_reasons = take_drop_fallback_reasons_by_fn();
    let translation_drop_site_reasons = take_translation_drop_site_reasons_by_fn();
    // Recognized-clean SoundHavoc drops, split out of place_translation_drop
    // (Part of #unsound-havoc-split). Crate total is the sum of the per-fn map.
    let sound_havoc_per_harness = take_sound_havoc_drop_by_fn();
    let sound_havoc_count = sound_havoc_per_harness.values().copied().sum::<usize>();
    let chc_translation_drops = if place_drop_count > 0
        || constant_drop_count > 0
        || field_projection_drop_count > 0
        || sound_havoc_count > 0
        || !translation_drop_per_harness.is_empty()
        || !sound_havoc_per_harness.is_empty()
        || !drop_fallback_reasons.is_empty()
        || !translation_drop_site_reasons.is_empty()
    {
        warn!(
            place_drop_count,
            sound_havoc_count,
            constant_drop_count,
            field_projection_drop_count,
            harness_count = translation_drop_per_harness.len(),
            drop_fallback_reason_count = drop_fallback_reasons.len(),
            translation_drop_site_count = translation_drop_site_reasons.len(),
            "CHC translation dropped unsupported immutable/static expression paths"
        );
        Some(ChcTranslationDropInfo {
            place_count: place_drop_count,
            constant_count: constant_drop_count,
            field_projection_count: field_projection_drop_count,
            per_harness: translation_drop_per_harness,
            per_harness_reasons: drop_fallback_reasons,
            per_harness_translation_sites: translation_drop_site_reasons,
            sound_havoc_count,
            sound_havoc_per_harness,
        })
    } else {
        None
    };

    let unhandled_count = take_chc_unhandled_call_count();
    let unhandled_call_per_harness = take_unhandled_call_by_fn();
    let unhandled_calls = if unhandled_count > 0 || !unhandled_call_per_harness.is_empty() {
        warn!(
            unhandled_count,
            harness_count = unhandled_call_per_harness.len(),
            "CHC call dispatch: function calls left destination unconstrained"
        );
        Some(UnhandledCallInfo { count: unhandled_count, per_harness: unhandled_call_per_harness })
    } else {
        None
    };

    // Part of #3379: sub-classified dispatch counters.
    let error_blocked_fmt_count = take_error_blocked_fmt_count();
    let error_blocked_fmt = (error_blocked_fmt_count > 0)
        .then_some(ErrorBlockedFmtInfo { count: error_blocked_fmt_count });
    let known_stdlib_count = take_known_stdlib_unconstrained_count();
    let known_stdlib_unconstrained = (known_stdlib_count > 0)
        .then_some(KnownStdlibUnconstrainedInfo { count: known_stdlib_count });

    let zero_count = take_constant_zero_fallback_count();
    let constant_zero_fallbacks = if zero_count > 0 {
        warn!(zero_count, "Statement codegen used zero-value fallback for unextracted constants");
        Some(ConstantZeroFallbackInfo { count: zero_count, ..Default::default() })
    } else {
        None
    };

    let type_sort_count = take_type_sort_fallback_count();
    let type_sort_per_harness = take_type_sort_fallback_by_fn();
    let type_sort_fallbacks = if type_sort_count > 0 || !type_sort_per_harness.is_empty() {
        let effective_count =
            type_sort_count.max(type_sort_per_harness.values().copied().sum::<usize>());
        warn!(
            effective_count,
            harness_count = type_sort_per_harness.len(),
            "CHC type-sort resolution fell back to hardcoded sorts (potentially narrower than actual types)"
        );
        Some(TypeSortFallbackInfo { count: effective_count, per_harness: type_sort_per_harness })
    } else {
        None
    };

    let signedness_count = take_signedness_fallback_count();
    let signedness_per_harness = take_signedness_fallback_by_fn();
    let signedness_fallbacks = if signedness_count > 0 || !signedness_per_harness.is_empty() {
        let effective_count =
            signedness_count.max(signedness_per_harness.values().copied().sum::<usize>());
        warn!(
            effective_count,
            harness_count = signedness_per_harness.len(),
            "Signedness could not be determined from MIR types; used operation-specific defaults (#2749)"
        );
        Some(SignednessFallbackInfo { count: effective_count, per_harness: signedness_per_harness })
    } else {
        None
    };

    (
        chc_fallbacks,
        chc_translation_drops,
        unhandled_calls,
        error_blocked_fmt,
        known_stdlib_unconstrained,
        constant_zero_fallbacks,
        type_sort_fallbacks,
        signedness_fallbacks,
    )
}

/// Collect and report fail-closed counter fields.
pub(super) fn collect_fail_closed_fields() -> (
    Option<AssertUntranslatableInfo>,
    Option<HeapCheckUntranslatableInfo>,
    Option<HeapCheckUnknownLayoutInfo>,
) {
    let assert_count = get_chc_assert_untranslatable_count();
    let assert_untranslatable = if assert_count > 0 {
        warn!(assert_count, "CHC conservative error rules for untranslatable assertions");
        Some(AssertUntranslatableInfo { count: assert_count })
    } else {
        None
    };
    let heap_untranslatable = get_chc_heap_check_untranslatable_count();
    let heap_check_untranslatable = if heap_untranslatable > 0 {
        warn!(heap_untranslatable, "CHC conservative error rules for untranslatable heap safety");
        Some(HeapCheckUntranslatableInfo { count: heap_untranslatable })
    } else {
        None
    };
    let heap_unknown = get_chc_heap_check_unknown_layout_count();
    let heap_check_unknown_layout = if heap_unknown > 0 {
        warn!(heap_unknown, "CHC fail-closed heap checks for unknown-layout types (#2501)");
        Some(HeapCheckUnknownLayoutInfo { count: heap_unknown })
    } else {
        None
    };

    (assert_untranslatable, heap_check_untranslatable, heap_check_unknown_layout)
}

/// Collect statement-level unsoundness counters.
#[allow(clippy::type_complexity)]
pub(super) fn collect_statement_counter_fields() -> (
    Option<IntoOptionDropInfo>,
    Option<InternalWorkaroundInfo>,
    Option<AbstractedFallbackInfo>,
    Option<VecFieldFallbackInfo>,
    Option<PointeeSynthesisFallbackInfo>,
    Option<UnsupportedConstructFallbackInfo>,
    Option<UnconstrainedAssignmentInfo>,
) {
    let into_option_count = take_into_option_dropped_count();
    let into_option_drops = if into_option_count > 0 {
        warn!(
            into_option_count,
            "Statement codegen dropped Result::Err in IntoOption and skipped constraints"
        );
        Some(IntoOptionDropInfo { count: into_option_count, ..Default::default() })
    } else {
        None
    };
    let workaround_count = take_internal_workaround_count();
    let internal_workarounds = if workaround_count > 0 {
        warn!(
            workaround_count,
            "Statement codegen used symbolic workarounds for pre-inlined collection internals"
        );
        Some(InternalWorkaroundInfo { count: workaround_count, ..Default::default() })
    } else {
        None
    };
    let fallback_count = take_abstracted_fallback_count();
    let abstracted_fallbacks = if fallback_count > 0 {
        warn!(
            fallback_count,
            "Statement codegen used abstracted fallbacks for pre-inlined stdlib internals"
        );
        Some(AbstractedFallbackInfo { count: fallback_count, ..Default::default() })
    } else {
        None
    };
    let vec_field_count = take_vec_field_fallback_counter() as usize;
    let vec_field_fallbacks = if vec_field_count > 0 {
        warn!(
            vec_field_count,
            "Vec field select returned symbolic fallback for non-datatype Vec expressions"
        );
        Some(VecFieldFallbackInfo { count: vec_field_count, ..Default::default() })
    } else {
        None
    };
    let pointee_synth_count = take_pointee_synthesis_fallback_count();
    let pointee_synthesis_fallbacks = if pointee_synth_count > 0 {
        warn!(
            pointee_synth_count,
            "Statement codegen synthesized unconstrained symbolic pointees for untracked dereferences (#3013)"
        );
        Some(PointeeSynthesisFallbackInfo { count: pointee_synth_count, ..Default::default() })
    } else {
        None
    };
    let unsupported_construct_count = take_unsupported_construct_fallback_count();
    let unsupported_construct_fallbacks = if unsupported_construct_count > 0 {
        warn!(
            unsupported_construct_count,
            "Codegen proceeded with fallback data after unsupported construct (#3017)"
        );
        Some(UnsupportedConstructFallbackInfo {
            count: unsupported_construct_count,
            ..Default::default()
        })
    } else {
        None
    };
    let unconstrained_count = take_unconstrained_assignment_count();
    let unconstrained_assignments = if unconstrained_count > 0 {
        warn!(
            unconstrained_count,
            "BMC codegen_assign: rvalue returned None, LHS SSA variables unconstrained (#3192)"
        );
        Some(UnconstrainedAssignmentInfo { count: unconstrained_count, ..Default::default() })
    } else {
        None
    };
    (
        into_option_drops,
        internal_workarounds,
        abstracted_fallbacks,
        vec_field_fallbacks,
        pointee_synthesis_fallbacks,
        unsupported_construct_fallbacks,
        unconstrained_assignments,
    )
}
