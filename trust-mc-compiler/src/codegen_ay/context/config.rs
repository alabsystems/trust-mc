// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY backend configuration.

use crate::args::{ChcStepMode, ChcTrackLevel};

/// Configuration for the AY backend.
///
/// # Fields
/// - `unwind_depth`: Maximum loop unrolling depth for bounded verification (default: 1)
/// - `unwinding_assertions`: Emit a failure when unwinding may be insufficient (default: true)
/// - `use_chc`: Enable CHC/Horn clause mode for unbounded verification
/// - `produce_models`: Request counterexample models on SAT results
/// - `logic`: SMT-LIB logic string (default: "QF_AUFBV" for quantifier-free arrays+bitvectors)
/// - `logic_override`: When true, `logic` was explicitly set by user and overrides automatic selection
#[derive(Debug, Clone)]
pub(in crate::codegen_ay) struct AYConfig {
    /// Maximum loop unrolling depth for bounded verification.
    pub(in crate::codegen_ay) unwind_depth: u32,
    /// Whether to generate an unwinding-assertion failure when a loop could continue.
    pub(in crate::codegen_ay) unwinding_assertions: bool,
    /// Enable CHC/Horn clause mode for unbounded verification.
    pub(in crate::codegen_ay) use_chc: bool,
    /// Request counterexample models when verification fails (SAT).
    pub(in crate::codegen_ay) produce_models: bool,
    /// SMT-LIB logic string (e.g., "QF_AUFBV", "HORN").
    pub(in crate::codegen_ay) logic: String,
    /// When true, `logic` was explicitly set by user via --ay-logic.
    /// User override takes precedence over automatic logic selection (#621).
    pub(in crate::codegen_ay) logic_override: bool,
    /// Enable function inlining to eliminate Call terminators.
    pub(in crate::codegen_ay) function_inlining: bool,
    /// Maximum function inlining depth (to prevent infinite expansion).
    pub(in crate::codegen_ay) inline_depth: usize,
    /// Use the abstract IR emission path (emit_bmc) instead of direct program construction.
    ///
    /// When true, the finalization path uses `emit_bmc(bmc_vc)` to generate the
    /// AY program from the abstract BMC verification condition. This is the target
    /// architecture for #206.
    ///
    /// When false (default), uses the legacy direct-construction path which
    /// builds the AYProgram incrementally during MIR traversal.
    pub(in crate::codegen_ay) use_emit_bmc: bool,
    /// CHC memory tracking precision level.
    ///
    /// Controls how memory operations are modeled in CHC encoding:
    /// - `Reg`: Register-only, loads havoc, stores no-op (default)
    /// - `Ptr`: Pointer validity, loads havoc but emits r_ok checks
    /// - `Mem`: Full memory, uses select/store for complete modeling
    pub(in crate::codegen_ay) chc_track_level: ChcTrackLevel,
    /// CHC encoding step granularity (#112).
    ///
    /// `Small`: one predicate per basic block.
    /// `Large`: one predicate per cut point (loop headers + entry/exit).
    /// `Auto` (default): `Large` for functions with loops, `Small` for acyclic.
    pub(in crate::codegen_ay) chc_step_mode: ChcStepMode,
    /// Lift bitvector sorts to integer for loop-header CHC predicates.
    ///
    /// Part of #112: designs/2026-03-03-loop-invariant-synthesis.md Direction 2.
    pub(in crate::codegen_ay) chc_int_lift: bool,
    /// Enable wide memory model with bounds checking.
    ///
    /// When true, uses WideMemManager which tracks allocation sizes with pointers.
    /// When false (default), skips bounds checking.
    /// Part of #1678, #1860: WideMemManager integration.
    pub(in crate::codegen_ay) ay_wide_mem: bool,
    /// Enable extra pointer checks (offset overflow). Part of #3176.
    pub(in crate::codegen_ay) extra_pointer_checks: bool,
    /// Prove safety only: suppress user assertion/panic violations, keep safety checks.
    /// Part of #4217: --prove-safety-only flag implementation.
    pub(in crate::codegen_ay) prove_safety_only: bool,
    /// Emit memory-safety checks such as bounds, null, alignment, and pointer-validity checks.
    pub(in crate::codegen_ay) memory_safety_checks: bool,
    /// Emit arithmetic overflow checks.
    pub(in crate::codegen_ay) overflow_checks: bool,
    /// Emit NaN-generation obligations for float binops (`--nan-check`).
    ///
    /// OFF by default, matching Kani: producing a NaN is DEFINED behaviour in
    /// Rust, not UB, so this is an opt-in lint and not a safety property.
    /// Emitting it unconditionally made every harness containing symbolic
    /// float arithmetic report a false FAILURE.
    pub(in crate::codegen_ay) nan_checks: bool,
    /// Emit failures for reachable undefined foreign function calls.
    pub(in crate::codegen_ay) undefined_function_checks: bool,
    /// Apply bounded loop unrolling before CHC encoding.
    ///
    /// When true, loops with `#[kani::unwind(N)]` are unrolled into acyclic code
    /// before CHC translation, avoiding the need for loop invariant synthesis.
    pub(in crate::codegen_ay) chc_bounded_unroll: bool,
    /// Whether the unwind depth was explicitly set (CLI `--unwind`, `#[kani::unwind(N)]`,
    /// or `--default-unwind`). When false, `unwind_depth` is the default (1) and should
    /// NOT override CHC recursive inline depth. Part of #3929.
    pub(in crate::codegen_ay) has_explicit_unwind: bool,
    /// `-Z uninit-checks` is active: the `check_uninit` instrumentation ran, so
    /// the backends must thread the scalar shadow-memory state and give the
    /// `Is*/Set*PtrInitialized` model calls real verdicts (MEMUB-24/25/27).
    pub(in crate::codegen_ay) uninit_checks: bool,
    /// This harness is a `#[kani::proof_for_contract]`. SOUNDNESS: constant
    /// propagation can weaken a genuinely-violated postcondition-assertion error
    /// edge into an unreachable form that the downstream discharge / PDR then
    /// proves SAFE (e.g. `expected/function-contract/as-assertions/
    /// assert-postconditions`). For an *acyclic* contract harness the reduction
    /// buys nothing (no loop invariant to help PDR converge), so const-prop is
    /// skipped to keep the postcondition obligation intact. Cyclic contract
    /// harnesses keep const-prop (they rely on it for invariant synthesis).
    pub(in crate::codegen_ay) is_contract_proof: bool,
    /// Emit the per-assertion reachability flag (`ay_reach_kani_assert_<n>`)
    /// that lets the driver report an assertion as UNREACHABLE.
    ///
    /// Mirrors Kani's `--assertion-reach-checks` (the driver passes it unless
    /// the user asked for `--no-assertion-reach-checks`). Kani generates the
    /// companion reachability check ONLY for assertions, and with the checks
    /// turned off an assertion in dead code reports the solver's own verdict —
    /// SUCCESS — instead of UNREACHABLE. Two corpus files pin exactly that
    /// (`expected/reach/turned-off`, `expected/assert-location/debug-assert`).
    ///
    /// SOUNDNESS: the flag governs only the SUCCESS -> UNREACHABLE *annotation*
    /// of an already-discharged check. It never removes an obligation (the
    /// `ay_violation_*` predicate is emitted either way), and it cannot mask a
    /// FAILURE (only non-failing checks are ever annotated). Whole-harness
    /// vacuity is adjudicated by `probe_harness_reachable`, which does not read
    /// these per-check flags, so the V4 gate is unaffected.
    pub(in crate::codegen_ay) assertion_reach_checks: bool,
}

impl Default for AYConfig {
    fn default() -> Self {
        Self {
            unwind_depth: 1,
            unwinding_assertions: true,
            use_chc: false,
            produce_models: true,
            logic: "QF_AUFBV".to_owned(),
            logic_override: false,
            function_inlining: true,
            inline_depth: 10,
            use_emit_bmc: false, // Legacy path by default during migration
            chc_track_level: ChcTrackLevel::Mem,
            chc_step_mode: ChcStepMode::Auto,
            chc_int_lift: false,
            ay_wide_mem: false, // Raw memory model by default
            extra_pointer_checks: false,
            prove_safety_only: false,
            memory_safety_checks: true,
            overflow_checks: true,
            nan_checks: false,
            undefined_function_checks: true,
            chc_bounded_unroll: false,
            has_explicit_unwind: false,
            uninit_checks: false,
            is_contract_proof: false,
            // Default ON so a compiler invoked without the driver keeps the
            // richer UNREACHABLE annotation; the driver sets it from the user's
            // `--assertion-reach-checks` / `--no-assertion-reach-checks` choice.
            assertion_reach_checks: true,
        }
    }
}

impl AYConfig {
    /// Select the appropriate SMT-LIB logic based on verification mode and features.
    ///
    /// # Logic Selection Policy
    ///
    /// Logic selection policy:
    ///
    /// ## User Override (`logic_override = true`)
    /// - Returns `self.logic` directly, bypassing automatic selection.
    /// - Allows experimentation with non-default logics via `--ay-logic`.
    ///
    /// ## CHC mode (`use_chc = true`)
    /// - Returns `"HORN"` for fixedpoint/CHC solving.
    /// - HORN logic is not upgraded even when datatypes are present.
    ///
    /// ## BMC (non-CHC) mode (`use_chc = false`)
    /// - Returns `"QF_AUFBV"` when no datatypes are present.
    /// - Returns `"ALL"` when datatypes are present (most solvers support this).
    ///
    /// # Arguments
    /// * `has_datatypes` - Whether algebraic datatypes are declared in the program.
    ///
    /// # Returns
    /// The SMT-LIB logic string to emit in `(set-logic ...)`.
    #[must_use]
    pub(in crate::codegen_ay) fn select_logic(&self, has_datatypes: bool) -> &str {
        // User override takes precedence over all automatic selection (#621)
        if self.logic_override {
            return &self.logic;
        }

        if self.use_chc {
            // CHC mode: always use HORN logic for PDR-based CHC solving
            "HORN"
        } else if has_datatypes {
            // BMC mode with datatypes: use ALL (widely supported)
            // Note: QF_DT and combined *_DT logics exist but solver support varies
            "ALL"
        } else {
            // BMC mode without datatypes: use configured logic (default QF_AUFBV)
            &self.logic
        }
    }
}
