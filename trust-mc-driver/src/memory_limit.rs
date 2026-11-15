// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The in-process AY memory cap, and how many drivers share the host.
//!
//! `main()` arms ay's process-wide RSS guard (`ay_sys::set_process_memory_limit`)
//! so the linked CHC portfolio — up to a dozen engines in this process — cannot
//! take the host down. ay's own default is `phys / 2` clamped to
//! `[2 GB, 64 GB]`, which is right for ONE driver and 3x oversubscribed for the
//! six a corpus runner starts on a 121 GB host: every driver claims 60 GB, and a
//! run was killed for low memory on 2026-09-12. Two knobs fix that, both listed
//! in `trust-mc explain env`:
//!
//! * `TRUST_MC_AY_MEMORY_LIMIT_MB=<n>` — an explicit cap in MiB. It never
//!   RAISES the cap above ay's default; the `[2 GB, 64 GB]` clamp still applies
//!   (below 2 GB the guard trips before anything useful is solved, so a smaller
//!   value reads as 2 GB — or as the host's whole RAM inside a smaller cgroup).
//! * `TRUST_MC_JOBS=<n>` — how many drivers the caller runs concurrently. The
//!   cap becomes `phys / (2 * max(1, n))`, clamped the same way, so the drivers
//!   share `phys / 2` between them instead of each claiming it. A runner that
//!   exports it (`tools/kani-domination` with `--jobs N`) gets the sharing
//!   without any per-driver flag.
//!
//! A driver that runs a child driver for one harness (the loop-contract
//! retry) hands it a cap as `TRUST_MC_AY_MEMORY_LIMIT_MB`
//! ([`retry_child_cap_mb`]). The cap is carved from what THAT HARNESS owns
//! ([`harness_share_bytes`]: the armed cap less the driver's footprint, divided
//! by the harnesses solved at once under `--jobs`), not from the whole process
//! cap. The retry runs one child per harness, and the child solves its one
//! harness on a one-thread pool (the retry drops `--jobs` from its argv), so
//! the child's own envelope is that share, not a fraction of it. So under
//! `--jobs N` the children of N concurrent harnesses hold one cap between them,
//! not N.
//!
//! Overcommit at the floor: a child's own [`resolve`] clamps an explicit cap to
//! at least 2 GB (AY's usable minimum). When a harness's share is below that,
//! each child claims 2 GB anyway, and the children together can exceed the
//! parent's cap. On this 121 GB host (cap 62304 MiB) that starts at `--jobs 31`
//! (62304 / 31 is about 2010 MiB). Until review round 3 the retry ran two
//! children at once per harness, each carved half the share, and the floor bound
//! from `--jobs 16` on (62304 / 16 / 2 is about 1947 MiB). The caps are the
//! advisory RSS guard, not a kill: a child that reaches its cap ends its solve
//! as a typed `Memout` UNKNOWN.
//!
//! Precedence: the explicit MiB value, then the jobs derivation, then ay's
//! default. Every derived value is a CAP on the advisory guard — a driver that
//! reaches it ends its solve as a typed `Memout` UNKNOWN, never a kill.

/// The clamp ay's default uses: never below 2 GB (or the host's whole RAM when
/// that is smaller), never above 64 GB.
pub(crate) const MIN_LIMIT_BYTES: usize = 2 * 1024 * 1024 * 1024;
pub(crate) const MAX_LIMIT_BYTES: usize = 64 * 1024 * 1024 * 1024;

/// Where the resolved cap came from, for the one-line stderr note.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Source {
    /// `TRUST_MC_AY_MEMORY_LIMIT_MB`.
    ExplicitMb,
    /// `TRUST_MC_JOBS=<n>`: `phys / (2 * n)`.
    Jobs(usize),
    /// ay's own default (`phys / 2`, clamped).
    Default,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Resolved {
    /// Bytes to hand `ay_sys::set_process_memory_limit`; 0 means "leave ay's
    /// guard unarmed" (only when ay itself could not size a default).
    pub(crate) bytes: usize,
    pub(crate) source: Source,
}

impl Resolved {
    /// One stderr line when the cap is NOT ay's default, so a corpus log shows
    /// what each driver was allowed. Silent for the default: it is the
    /// unchanged behaviour and would add a line to every run.
    pub(crate) fn stderr_note(&self) -> Option<String> {
        let mib = self.bytes / (1024 * 1024);
        match self.source {
            Source::ExplicitMb => Some(format!(
                "[AY] in-process ay memory cap: {mib} MiB (TRUST_MC_AY_MEMORY_LIMIT_MB)"
            )),
            Source::Jobs(jobs) => Some(format!(
                "[AY] in-process ay memory cap: {mib} MiB (phys / (2 * TRUST_MC_JOBS={jobs}))"
            )),
            Source::Default => None,
        }
    }
}

/// Clamp a derived cap into `[min(2 GB, phys), 64 GB]` and under ay's default
/// (when ay could size one): the knobs only ever LOWER the cap.
fn bound(bytes: usize, phys_bytes: usize, ay_default: usize) -> usize {
    let floor = if phys_bytes == 0 { MIN_LIMIT_BYTES } else { MIN_LIMIT_BYTES.min(phys_bytes) };
    let clamped = bytes.clamp(floor, MAX_LIMIT_BYTES);
    if ay_default > 0 { clamped.min(ay_default) } else { clamped }
}

/// Pure resolution, so the policy is testable with fixed inputs.
///
/// `explicit_mb` and `jobs` are the raw environment values (unset, empty,
/// unparsable and zero all mean "not set"); `phys_bytes` is the host's
/// physical memory as ay sizes it (0 = unknown); `ay_default` is
/// `ay_sys::default_memory_limit()` (0 = ay could not size one).
pub(crate) fn resolve(
    explicit_mb: Option<&str>,
    jobs: Option<&str>,
    phys_bytes: usize,
    ay_default: usize,
) -> Resolved {
    let parse = |raw: Option<&str>| raw?.trim().parse::<u64>().ok().filter(|n| *n > 0);
    if let Some(mb) = parse(explicit_mb) {
        let bytes = usize::try_from(mb.saturating_mul(1024 * 1024)).unwrap_or(usize::MAX);
        return Resolved {
            bytes: bound(bytes, phys_bytes, ay_default),
            source: Source::ExplicitMb,
        };
    }
    if let Some(jobs) = parse(jobs).and_then(|n| usize::try_from(n).ok())
        && phys_bytes > 0
    {
        let share = phys_bytes / (2 * jobs.max(1));
        return Resolved {
            bytes: bound(share, phys_bytes, ay_default),
            source: Source::Jobs(jobs),
        };
    }
    Resolved { bytes: ay_default, source: Source::Default }
}

/// [`resolve`] from the process environment and ay's own sizing.
#[cfg(all(feature = "ay-chc-native", feature = "ay-memory-limit"))]
pub(crate) fn resolve_from_env() -> Resolved {
    let explicit = std::env::var("TRUST_MC_AY_MEMORY_LIMIT_MB").ok();
    let jobs = std::env::var("TRUST_MC_JOBS").ok();
    resolve(
        explicit.as_deref(),
        jobs.as_deref(),
        ay_sys::physical_memory_bytes(),
        ay_sys::default_memory_limit(),
    )
}

/// What one harness owns of the driver's armed cap, in bytes:
/// `(process_cap - footprint) / harness_workers`, or `None` when no cap is
/// armed (`process_cap == 0`).
///
/// `footprint` is the driver's resident footprint (the fixed headroom no solve
/// can use) and `harness_workers` how many harnesses this process solves at
/// once (the `--jobs` rayon pool; 1 by default). This is the ONE division both
/// consumers use: the in-process envelope
/// (`call_ay::chc::resource_envelope::HarnessMemoryEnvelope`) and the child
/// driver of the loop-contract retry ([`retry_child_cap_mb`]), so N concurrent
/// harnesses and everything they start hold the cap between them.
pub(crate) fn harness_share_bytes(
    process_cap: usize,
    footprint: usize,
    harness_workers: usize,
) -> Option<usize> {
    if process_cap == 0 {
        return None;
    }
    Some(process_cap.saturating_sub(footprint) / harness_workers.max(1))
}

/// The explicit cap (`TRUST_MC_AY_MEMORY_LIMIT_MB`) to hand each of
/// `children` driver processes that run AT THE SAME TIME out of an owner's
/// `owner_bytes` (AY ask R2: "account simultaneous portfolio children against
/// a shared owner rather than granting each the entire allowance").
///
/// `None` when there is no owner budget (`owner_bytes == 0`, no cap armed):
/// the children keep deriving their own, as before. The child's own
/// [`resolve`] still applies its `[min(2 GB, phys), 64 GB]` clamp, so below
/// twice the floor the share reads as the floor there — AY's usable minimum
/// wins over an exact split.
pub(crate) fn concurrent_child_share_mb(owner_bytes: usize, children: usize) -> Option<u64> {
    if owner_bytes == 0 {
        return None;
    }
    let share = owner_bytes / children.max(1);
    Some(u64::try_from(share / (1024 * 1024)).unwrap_or(u64::MAX).max(1))
}

/// The cap the loop-contract retry hands its child driver
/// (`TRUST_MC_AY_MEMORY_LIMIT_MB`): the whole of the harness's share
/// ([`harness_share_bytes`]). The child is the only process the retry runs for
/// the harness, and it solves one harness on one thread. `None` (no cap armed)
/// leaves the child to derive its own cap, as before.
pub(crate) fn retry_child_cap_mb(harness_share: Option<usize>) -> Option<u64> {
    concurrent_child_share_mb(harness_share.unwrap_or(0), 1)
}

/// The armed process cap and the driver's current resident footprint, in
/// bytes (`(0, 0)` without `ay-memory-limit`, where no cap is armed).
#[cfg(feature = "ay-memory-limit")]
pub(crate) fn armed_cap_and_footprint() -> (usize, usize) {
    let cap = ay_sys::get_process_memory_limit();
    // Current resident footprint (Linux: resident pages; macOS: the jetsam
    // `phys_footprint`). `current_rss_bytes` is a PEAK, so it is only the
    // fallback when no footprint API answers.
    let footprint = match ay_sys::current_footprint_bytes() {
        0 => ay_sys::current_rss_bytes(),
        bytes => bytes,
    };
    (cap, footprint)
}

/// Without `ay-memory-limit` the driver arms no cap.
#[cfg(not(feature = "ay-memory-limit"))]
pub(crate) fn armed_cap_and_footprint() -> (usize, usize) {
    (0, 0)
}

/// How many harnesses this process solves at once, seen from the calling
/// thread: inside the harness runner's rayon pool that pool's size (1 unless
/// `--jobs`), outside any pool 1.
pub(crate) fn harness_workers_here() -> usize {
    if rayon::current_thread_index().is_some() { rayon::current_num_threads() } else { 1 }
}

/// [`harness_share_bytes`] for the harness running on the calling thread.
pub(crate) fn current_harness_share_bytes() -> Option<usize> {
    let (cap, footprint) = armed_cap_and_footprint();
    harness_share_bytes(cap, footprint, harness_workers_here())
}

#[cfg(test)]
mod tests {
    use super::*;

    const GB: usize = 1024 * 1024 * 1024;
    /// A 121 GB host, as measured: ay's default is phys / 2 = 60.5 GB.
    const PHYS: usize = 121 * GB;
    const AY_DEFAULT: usize = PHYS / 2;

    #[test]
    fn unset_keeps_ays_default() {
        for (mb, jobs) in
            [(None, None), (Some(""), Some("")), (Some("x"), Some("0")), (Some("0"), None)]
        {
            let r = resolve(mb, jobs, PHYS, AY_DEFAULT);
            assert_eq!(
                r,
                Resolved { bytes: AY_DEFAULT, source: Source::Default },
                "{mb:?} {jobs:?}"
            );
            assert_eq!(r.stderr_note(), None);
        }
    }

    /// Six concurrent drivers on the 121 GB host share phys / 2: ~10 GB each
    /// instead of 60 GB each (3x oversubscribed).
    #[test]
    fn jobs_share_half_the_host() {
        let r = resolve(None, Some("6"), PHYS, AY_DEFAULT);
        assert_eq!(r.source, Source::Jobs(6));
        assert_eq!(r.bytes, PHYS / 12);
        assert!(r.bytes * 6 <= AY_DEFAULT);
        assert!(r.stderr_note().unwrap().contains("TRUST_MC_JOBS=6"));
        // One job is exactly ay's default.
        assert_eq!(resolve(None, Some("1"), PHYS, AY_DEFAULT).bytes, AY_DEFAULT);
    }

    /// The [2 GB, 64 GB] clamp stays: many jobs floor at 2 GB, a huge host
    /// caps at 64 GB.
    #[test]
    fn clamp_bounds_are_kept() {
        assert_eq!(resolve(None, Some("64"), PHYS, AY_DEFAULT).bytes, 2 * GB);
        let huge = 1024 * GB;
        assert_eq!(resolve(None, Some("2"), huge, 64 * GB).bytes, 64 * GB);
        assert_eq!(resolve(Some("999999"), None, huge, 64 * GB).bytes, 64 * GB);
        // Inside a small cgroup the floor is the whole budget, not 2 GB.
        let small = GB;
        assert_eq!(resolve(Some("100"), None, small, small / 2).bytes, small / 2);
    }

    /// The explicit value lowers the cap and never raises it above ay's
    /// default: "below phys / 2" is the contract.
    #[test]
    fn explicit_mb_only_lowers() {
        let r = resolve(Some("8192"), Some("6"), PHYS, AY_DEFAULT);
        assert_eq!(r, Resolved { bytes: 8 * GB, source: Source::ExplicitMb });
        assert!(r.stderr_note().unwrap().contains("8192 MiB"));
        assert_eq!(resolve(Some("200000"), None, PHYS, AY_DEFAULT).bytes, AY_DEFAULT);
        assert_eq!(resolve(Some("1"), None, PHYS, AY_DEFAULT).bytes, 2 * GB);
    }

    /// Two simultaneous children of a 20 GB driver get 10 GB each, and a
    /// child resolving that share never exceeds it: together they hold the
    /// parent's cap, not twice it.
    #[test]
    fn simultaneous_children_share_the_parent_cap() {
        assert_eq!(concurrent_child_share_mb(0, 2), None);
        let parent = 20 * GB;
        let mb = concurrent_child_share_mb(parent, 2).unwrap();
        assert_eq!(mb, 10 * 1024);
        let child = resolve(Some(&mb.to_string()), Some("3"), PHYS, AY_DEFAULT);
        assert_eq!(child.source, Source::ExplicitMb);
        assert!(child.bytes * 2 <= parent);
        // Zero children reads as one: the whole cap, never a division by zero.
        assert_eq!(concurrent_child_share_mb(4 * GB, 0), Some(4 * 1024));
        // At the floor the child's clamp wins (documented): a 3 GB parent's
        // 1.5 GB share resolves to 2 GB in each child.
        let floor_mb = concurrent_child_share_mb(3 * GB, 2).unwrap();
        assert_eq!(resolve(Some(&floor_mb.to_string()), None, PHYS, AY_DEFAULT).bytes, 2 * GB);
    }

    /// Review round 2 of fix/ay-consumer-alignment, measured at `--jobs 2`: the
    /// parent armed 62304 MiB, and every two-lane child carried 31152 MiB
    /// (half the WHOLE cap), with 4 children alive at once — 124608 MiB, twice
    /// the cap. The child's cap now comes out of the harness's share (review
    /// round 3: one child per harness, which gets the whole share), so two
    /// workers' children hold the cap between them.
    #[test]
    fn the_children_of_concurrent_harnesses_share_one_cap() {
        const MIB: usize = 1024 * 1024;
        let cap = 62304 * MIB;
        let workers = 2;
        let share = harness_share_bytes(cap, 0, workers);
        assert_eq!(share, Some(cap / 2));
        let child = retry_child_cap_mb(share).unwrap();
        assert_eq!(child, 62304 / 2);
        // One child per worker alive at once fits in the cap together.
        assert!(child as usize * MIB * workers <= cap);
        // The driver's own footprint is not handed out twice.
        let with_footprint = harness_share_bytes(cap, 1024 * MIB, workers).unwrap();
        assert_eq!(with_footprint, (cap - 1024 * MIB) / 2);
        // One worker: the child gets the whole (cap - footprint).
        assert_eq!(retry_child_cap_mb(harness_share_bytes(cap, 0, 1)), Some(62304));
        // No cap armed: the child derives its own, as before.
        assert_eq!(harness_share_bytes(0, 0, 2), None);
        assert_eq!(retry_child_cap_mb(None), None);
        // Zero workers reads as one.
        assert_eq!(harness_share_bytes(cap, 0, 0), Some(cap));
    }

    /// The documented floor overcommit: below 2 GB of share the child's own
    /// clamp raises its cap to 2 GB. On a 62304 MiB cap that begins at 31
    /// workers, and not at 30.
    #[test]
    fn the_child_floor_overcommits_only_below_two_gib_of_share() {
        const MIB: usize = 1024 * 1024;
        let cap = 62304 * MIB;
        let resolved = |workers: usize| {
            let mb = retry_child_cap_mb(harness_share_bytes(cap, 0, workers)).unwrap();
            resolve(Some(&mb.to_string()), None, PHYS, AY_DEFAULT).bytes
        };
        assert!(resolved(30) * 30 <= cap, "30 workers fit");
        assert!(resolved(31) * 31 > cap, "31 workers overcommit at the 2 GB floor");
        assert_eq!(resolved(31), MIN_LIMIT_BYTES);
    }

    /// The share is read from the calling thread's rayon pool: inside a
    /// 2-thread pool (the harness runner under `--jobs 2`) it halves.
    #[test]
    fn the_harness_share_divides_by_the_pool_it_is_read_from() {
        assert_eq!(harness_workers_here(), 1);
        let pool = rayon::ThreadPoolBuilder::new().num_threads(2).build().unwrap();
        assert_eq!(pool.install(harness_workers_here), 2);
    }

    /// No host sizing at all: the explicit value still applies (clamped);
    /// jobs cannot derive anything and fall through to ay's (absent) default.
    #[test]
    fn unknown_phys_falls_through() {
        assert_eq!(resolve(None, Some("4"), 0, 0), Resolved { bytes: 0, source: Source::Default });
        assert_eq!(resolve(Some("4096"), None, 0, 0).bytes, 4 * GB);
    }
}
