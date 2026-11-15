// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The caller-owned memory envelope one harness's CHC solves run in (AY ask
//! R2, `trust_mc_ay_asks_design_resources.md`).
//!
//! # What AY offers, at the pinned revision
//!
//! Three public setters exist at ay `22db3bcc1`, and the native CHC lanes used
//! none of them:
//!
//! * `ay_encode::invoke::EncodeConfig::with_memory_budget` — the per-property
//!   row route. Lowered to `AdaptiveConfig::memory_budget`, which a concrete
//!   portfolio DIVIDES across the workers that may be live at once
//!   (`portfolio/types.rs::per_engine_term_budget`), so a row's simultaneous
//!   engines share the allowance instead of each claiming all of it.
//! * `ay_chc::AdaptiveConfig::with_memory_budget` — the same, for the
//!   forced-engine one-shot's portfolio.
//! * `ay_chc::BmcConfig::with_memory_budget` — the acyclic-BMC shortcut, the
//!   forced BMC lane and the BMC cross-check. Its documented meaning is PER
//!   CONTEXT: each BMC and checked-replay SMT context may hold this many term
//!   bytes (`bmc/mod.rs`, `bmc/memory.rs`). That meaning is preserved here,
//!   not reinterpreted as an aggregate.
//!
//! The external `ay` proof fallback is a separate process; it gets the same
//! allowance as its `--memory` ceiling ([`external_ay_memory_mb`]), instead of
//! the CLI's default of 85% of the host's RAM.
//!
//! `PdrConfig` has no memory setter, so the forced PDR lane and the external
//! invariant-model validator run under AY's own defaults; the thread-scoped
//! budget that would reach them is crate-private to AY. Unset, every setter
//! falls back to AY's global term limit, whose default is UNLIMITED
//! (`ay-core` `DEFAULT_TERM_MEMORY_LIMIT = usize::MAX`) — so before this
//! module one engine of a twelve-engine portfolio could take the whole
//! process cap.
//!
//! # The envelope
//!
//! One value per harness, computed once, before any lane of that harness
//! starts, from quantities the driver already owns or measures — no invented
//! constant:
//!
//! ```text
//! allowance = (process_cap - measured_driver_footprint) / harness_workers
//! ```
//!
//! * `process_cap` is the in-process cap `main()` armed as AY's process-wide
//!   RSS guard (`memory_limit`: `TRUST_MC_AY_MEMORY_LIMIT_MB`, else
//!   `phys / (2 * TRUST_MC_JOBS)`, else AY's `phys / 2`, clamped to
//!   `[2 GB, 64 GB]`). A qualification run that wants AY's 4-GiB test
//!   envelope sets `TRUST_MC_AY_MEMORY_LIMIT_MB=4096`; there is no built-in
//!   4-GiB default. Unarmed (`0`): no envelope, AY's defaults stand.
//! * `measured_driver_footprint` is the driver's resident footprint when the
//!   envelope is built — the fixed driver/runtime headroom (parsed problem,
//!   compiler artifacts, allocator retention from earlier harnesses) that the
//!   solves cannot use.
//! * `harness_workers` is how many harnesses this process solves at once (the
//!   `--jobs` rayon pool, 1 by default). Concurrent harnesses' in-process
//!   solves share the cap instead of each being granted all of it; with fewer
//!   harnesses than pool threads the division is conservative, never generous.
//!   The division is `memory_limit::harness_share_bytes`, the same one the
//!   loop-contract retry's child driver is carved from (below).
//!
//! The lanes of one harness run one at a time (every lane is joined before the
//! next starts — see `owned_lane`), so each lane may use the whole allowance;
//! the portfolio inside a lane divides it across its live engines. The
//! loop-contract retry runs a child driver after this harness's own solve has
//! returned, and its cap is this harness's share, not the process cap
//! (`memory_limit::retry_child_cap_mb`). The child solves its one harness on a
//! one-thread pool (the retry drops `--jobs` from its argv), so its own
//! envelope is that share again, not a fraction of it.
//!
//! History. Before review round 2 the retry's two concurrent children each got
//! half of the WHOLE process cap and its deepening children were handed nothing
//! (each re-derived the full cap), so under `--jobs 2` four children claimed
//! twice the cap (measured: 4 x 31152 MiB against 62304 MiB). Round 2 carved
//! them from the harness share, but each child still inherited the parent's
//! `--jobs N` and divided its cap by N a second time (review round 3: 7770 MiB
//! of a 15567 MiB cap at `--jobs 2`, 101 MiB at `--jobs 20`). Round 3 removed
//! the second division and, with the properties lane, the concurrent pair.
//!
//! # What it is not
//!
//! AY's setters account TERM memory only. Source expressions, SMT text, SAT
//! clauses, proof payloads and reconstruction are outside them, so this is a
//! working-set budget, NOT a process-RSS cap. The armed RSS guard stays the
//! process backstop and the wall-clock watchdog the outer containment. A
//! solve that reaches the allowance ends as AY's typed memory refusal
//! (Unknown), never as a verdict.

/// The memory envelope for one harness. See the module docs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct HarnessMemoryEnvelope {
    /// The process-wide cap `main()` armed, in bytes.
    pub(super) process_cap: usize,
    /// Driver footprint measured when the envelope was built, in bytes.
    pub(super) measured_headroom: usize,
    /// Harnesses sharing the cap in this process.
    pub(super) harness_workers: usize,
    /// Term-memory bytes each solve context of this harness may hold.
    pub(super) allowance: usize,
}

impl HarnessMemoryEnvelope {
    /// Pure policy, so it is testable with fixed inputs. `None` when no cap is
    /// armed (`process_cap == 0`): AY's own defaults then stand, unchanged.
    pub(super) fn compute(
        process_cap: usize,
        measured_headroom: usize,
        harness_workers: usize,
    ) -> Option<Self> {
        let allowance = crate::memory_limit::harness_share_bytes(
            process_cap,
            measured_headroom,
            harness_workers,
        )?;
        Some(Self {
            process_cap,
            measured_headroom,
            harness_workers: harness_workers.max(1),
            allowance,
        })
    }

    /// The envelope for the harness about to be solved on this thread, or
    /// `None` when the driver armed no cap.
    pub(super) fn for_current_harness() -> Option<Self> {
        let (cap, footprint) = crate::memory_limit::armed_cap_and_footprint();
        // Inside the harness runner's rayon pool, that pool's size (1 unless
        // `--jobs`); outside any pool, 1.
        Self::compute(cap, footprint, crate::memory_limit::harness_workers_here())
    }

    /// One stable line per harness for the run log. A `[AY-chc]` diagnostic
    /// line, not an `[AY:...]` marker: it appears on every harness, and the
    /// scorers' marker lists (the dual gate keeps the first twelve) should
    /// keep their room for the markers that classify a row.
    pub(super) fn marker_line(&self) -> String {
        const MIB: usize = 1024 * 1024;
        format!(
            "[AY-chc] resource-envelope term_memory_allowance_mib={} process_cap_mib={} \
             measured_headroom_mib={} harness_workers={} scope=per-lane-term-memory \
             (portfolio engines share it; not an RSS cap)",
            self.allowance / MIB,
            self.process_cap / MIB,
            self.measured_headroom / MIB,
            self.harness_workers,
        )
    }
}

/// The process-wide cap `main()` armed as AY's RSS guard, in bytes (0 when
/// none is armed). The row export records it with the execution environment.
pub(super) fn armed_process_cap_bytes() -> usize {
    crate::memory_limit::armed_cap_and_footprint().0
}

/// Apply the envelope to a BMC config (per-context term memory; see the
/// module docs). No envelope leaves the config untouched.
pub(super) fn bmc_with_envelope(
    config: ay::chc::BmcConfig,
    envelope: Option<HarnessMemoryEnvelope>,
) -> ay::chc::BmcConfig {
    match envelope {
        Some(envelope) => config.with_memory_budget(envelope.allowance),
        None => config,
    }
}

/// The `--memory <MiB>` ceiling for an external `ay` process run as a lane of
/// this harness (the CHC proof fallback), or `None` without an envelope.
///
/// Unlike AY's in-process setters this is the child's own PROCESS ceiling
/// (AY's RSS guard in that process), which is what the envelope's allowance
/// is: the armed cap less what the driver holds. Never `0`, which the CLI
/// reads as "unlimited": a zero allowance becomes 1 MiB, a refusal.
pub(super) fn external_ay_memory_mb(envelope: Option<HarnessMemoryEnvelope>) -> Option<u64> {
    let envelope = envelope?;
    let mb = u64::try_from(envelope.allowance / (1024 * 1024)).unwrap_or(u64::MAX);
    Some(mb.max(1))
}

#[cfg(test)]
mod tests {
    use super::*;

    const MIB: usize = 1024 * 1024;
    const GIB: usize = 1024 * MIB;

    #[test]
    fn no_armed_cap_means_no_envelope() {
        assert_eq!(HarnessMemoryEnvelope::compute(0, 300 * MIB, 1), None);
        assert_eq!(HarnessMemoryEnvelope::compute(0, 0, 8), None);
    }

    /// AY's 4-GiB test envelope, as a runner asks for it
    /// (`TRUST_MC_AY_MEMORY_LIMIT_MB=4096`): the allowance is what the driver
    /// does not already hold.
    #[test]
    fn the_allowance_is_the_cap_less_the_measured_driver_footprint() {
        let e = HarnessMemoryEnvelope::compute(4 * GIB, 312 * MIB, 1).unwrap();
        assert_eq!(e.allowance, 4 * GIB - 312 * MIB);
        assert_eq!(e.harness_workers, 1);
        assert!(e.marker_line().contains("term_memory_allowance_mib=3784"));
        assert!(e.marker_line().contains("process_cap_mib=4096"));
        assert!(e.marker_line().contains("measured_headroom_mib=312"));
    }

    /// Concurrent harnesses share the cap: two harnesses never hold more than
    /// one cap between them.
    #[test]
    fn concurrent_harnesses_share_the_cap_instead_of_each_claiming_it() {
        let e = HarnessMemoryEnvelope::compute(20 * GIB, 0, 4).unwrap();
        assert_eq!(e.allowance, 5 * GIB);
        assert!(e.allowance * e.harness_workers <= e.process_cap);
        // Zero workers reads as one: never a division by zero, never a larger share.
        let zero = HarnessMemoryEnvelope::compute(GIB, 0, 0).unwrap();
        assert_eq!((zero.allowance, zero.harness_workers), (GIB, 1));
    }

    /// The in-process envelope and the loop-contract retry's child driver are
    /// cut from the SAME per-harness share (`memory_limit::harness_share_bytes`),
    /// so at `--jobs 2` a harness's child never gets more than that harness's
    /// allowance.
    #[test]
    fn the_retry_child_is_carved_from_this_harness_allowance() {
        let e = HarnessMemoryEnvelope::compute(62304 * MIB, 300 * MIB, 2).unwrap();
        let child = crate::memory_limit::retry_child_cap_mb(Some(e.allowance)).unwrap();
        assert!(child as usize * MIB <= e.allowance, "{child} {e:?}");
        assert_eq!(child as usize, e.allowance / MIB);
        assert_eq!(
            crate::memory_limit::harness_share_bytes(62304 * MIB, 300 * MIB, 2),
            Some(e.allowance)
        );
    }

    /// A driver already at its cap gets a ZERO allowance: AY refuses the work
    /// (a typed Unknown), which is what its RSS guard would do anyway.
    #[test]
    fn a_driver_at_its_cap_gets_a_zero_allowance_not_an_underflow() {
        let e = HarnessMemoryEnvelope::compute(2 * GIB, 3 * GIB, 1).unwrap();
        assert_eq!(e.allowance, 0);
    }

    /// The external fallback's ceiling is the allowance in MiB, and never the
    /// CLI's "unlimited" `0`.
    #[test]
    fn the_external_ay_ceiling_is_the_allowance_and_never_unlimited() {
        assert_eq!(external_ay_memory_mb(None), None);
        let e = HarnessMemoryEnvelope::compute(4 * GIB, 312 * MIB, 1);
        assert_eq!(external_ay_memory_mb(e), Some(4096 - 312));
        let zero = HarnessMemoryEnvelope::compute(GIB, 2 * GIB, 1);
        assert_eq!(external_ay_memory_mb(zero), Some(1));
        let sub_mib = HarnessMemoryEnvelope::compute(MIB / 2, 0, 1);
        assert_eq!(external_ay_memory_mb(sub_mib), Some(1));
    }

    /// `(x = 0) -> Inv x; Inv x & x < 3 -> Inv (x + 1); Inv x & x = 2 -> error`:
    /// reachable in two steps.
    const UNSAFE_COUNTER: &str = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-rel error ())
(declare-var x Int)
(declare-var x1 Int)
(rule (=> (= x 0) (Inv x)))
(rule (=> (and (Inv x) (< x 3) (= x1 (+ x 1))) (Inv x1)))
(rule (=> (and (Inv x) (= x 2)) error))
(query error)
"#;

    /// The BMC setter is live on the route the driver uses: a generous
    /// envelope finds the counterexample, a zero envelope makes AY refuse the
    /// work — an Unknown, never a verdict.
    #[test]
    fn the_bmc_envelope_is_enforced_by_ay_and_a_zero_envelope_refuses_work() {
        let base = ay::chc::BmcConfig::default()
            .with_max_depth(8)
            .with_time_budget(std::time::Duration::from_secs(20));
        let parse = || ay::chc::ChcParser::parse(UNSAFE_COUNTER).expect("fixture parses");
        let generous = HarnessMemoryEnvelope::compute(GIB, 0, 1);
        let found =
            ay::chc::engines::solve_bmc_only(parse(), bmc_with_envelope(base.clone(), generous));
        assert!(found.is_unsafe(), "a 1 GiB envelope must not hide a 2-step counterexample");
        let zero = HarnessMemoryEnvelope::compute(GIB, 2 * GIB, 1);
        assert_eq!(zero.map(|e| e.allowance), Some(0));
        let refused = ay::chc::engines::solve_bmc_only(parse(), bmc_with_envelope(base, zero));
        assert!(
            !refused.is_unsafe() && !refused.is_safe(),
            "a zero envelope must refuse the work, not decide it"
        );
    }

    #[test]
    fn the_bmc_setter_is_applied_only_with_an_envelope() {
        let config = ay::chc::BmcConfig::default();
        let untouched = bmc_with_envelope(config.clone(), None);
        assert_eq!(format!("{untouched:?}"), format!("{config:?}"));
        let e = HarnessMemoryEnvelope::compute(4 * GIB, 0, 1);
        let budgeted = bmc_with_envelope(config.clone(), e);
        assert_ne!(format!("{budgeted:?}"), format!("{config:?}"));
        assert!(format!("{budgeted:?}").contains(&format!("memory_budget: Some({})", 4 * GIB)));
    }
}
