// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Design step 8c: one solve and one replay per normalized CHC input of a
//! native bundle; one seal per request.
//!
//! A native bundle asks one question per obligation, and every request on a
//! function carries the same whole-function CHC (5f805b339 translates it once
//! and shares it). Solving and replaying each request afresh therefore ran the
//! same engine pipeline on the same problem once per request, and on an
//! undecided function every request burned its own full watchdog.
//!
//! [`TypedChcSolveShare`] lives for one bundle call. It groups the PDR-route
//! requests by normalized CHC input and runs each engine call of the solve
//! pipeline, and each fresh invariant replay of the seal, once per group. What
//! is shared is ONLY the output of the engine ([`EngineSlots`]): the acyclic
//! direct-SMT decision, the IC3 loop lane's proof run, the strict PDR proof
//! run, the bounded-unroll witness search and the invariant model's clause
//! check. Every per-request step is unchanged and still runs per request: the
//! lowering and its binding checks, the demotion gates, the evidence packaging
//! (obligation id, kind, native metadata, cache key, artifacts), the fresh
//! re-lowering at seal time and every check of the seal verifier.
//!
//! # When two requests share
//!
//! A request joins a group only when all of these hold:
//!
//! 1. its normalized-input digest is the group's;
//! 2. its normalized input is BYTE-identical to the group's, so no digest
//!    collision can merge two problems;
//! 3. its lowering input is identical: the same `ChcVc` (`Arc::ptr_eq`, the
//!    case of every request on one translated function) or equal relations,
//!    rules and query target in the same order. Lowering reads nothing else,
//!    so the engine sees the identical problem, clause for clause. The
//!    normalized input is order-insensitive (ay sorts clauses), and positional
//!    evidence — a counterexample's derivation clause indices — is not, so
//!    condition 3 is what makes every shared row byte-identical to the row a
//!    per-request solve produces. A same-digest request whose lowering input
//!    differs gets its own group and its own solve;
//! 4. its effective solve timeout is the group's;
//! 5. its effective execution configuration, including frame cap, is the group's.
//!    Raw request ids are deliberately not group keys; each seal binds its own.
//!
//! Finding the group costs one hash lookup per request, never a scan of the
//! groups. They are indexed by (digest, timeout, execution configuration, an order-sensitive hash of the
//! lowering input), so a lookup meets one candidate unless two lowering inputs
//! collide in 64 bits, and the candidate is checked by all five conditions:
//! the index only decides where to look. A later request on a `ChcVc`
//! ALLOCATION that already joined a group goes straight to it and is checked by
//! conditions 1, 2, 4 and 5: the allocation's lowering input was compared with the
//! group's when it joined, and it cannot change while the share holds its
//! `Arc`.
//!
//! # What the seal is bound to
//!
//! The solve hands its request a [`SolvedInGroup`]: the group whose engine
//! results answered it. A seal is minted only when THAT group admits the
//! request's FRESH seal-time re-lowering by the same five conditions
//! ([`TypedChcSolveShare::group_for_seal`]), so the engine answer behind the
//! seal was computed on exactly the problem the request's own obligation lowers
//! to. A CHC-validity seal on the PDR route also requires that group's acyclic
//! decision to be `Safe` ([`ShareGroup::acyclic_decision_is_safe`]): that shared
//! decision is the whole derivation such a seal stands on, and nothing re-decides
//! it at seal time. A PDR-invariant seal takes its fresh clause check from the
//! same group ([`EngineSlots::invariant_replay`], keyed by the model bytes and
//! the replay timeout).
//!
//! The seal records [`super::PrivateSealRequestBinding`]: the digest of the
//! normalized input that group's solve and replay ran on — by condition 1 it
//! is also the request's own, so minting refuses any other — and a digest of
//! the request's own identity (obligation id, obligation kind, proof kind,
//! native request/proof/lineage ids, obligation-set hash and every evidence
//! row). The verifier recomputes both from the verification it is asked to
//! authorize. The pre-existing binding hash already covered the digest (in the
//! cache key) and the identity (in the candidate verdict); the request half is
//! defense in depth that names a moved seal's defect.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::time::Duration;

/// Deterministic counters of one native bundle call's solve and replay
/// sharing (design step 8c).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NativeBundleSolveWork {
    /// Requests handed to the solver (requests refused before solving, such as
    /// one carrying an obligation the safety CHC does not model, are not).
    pub requests: u64,
    /// Of those, requests on the PDR route — the only route with engine work.
    /// A trivially-safe request is decided structurally and shares nothing.
    pub pdr_route_requests: u64,
    /// Distinct normalized-input digests among the PDR-route requests.
    pub distinct_normalized_inputs: u64,
    /// Share groups. Equal to `distinct_normalized_inputs` unless two requests
    /// with the same digest had different lowering inputs (clause order), timeout or execution configuration.
    pub share_groups: u64,
    /// Engine pipelines run: the first engine call of a group's first request.
    pub solves_run: u64,
    /// PDR-route requests answered from their group's earlier pipeline.
    pub solves_shared: u64,
    /// Engine calls actually run, over every engine call site of the pipeline.
    pub engine_calls_run: u64,
    /// Engine calls answered from the group's earlier result.
    pub engine_calls_shared: u64,
    /// Fresh invariant-model clause checks actually run for PDR-invariant seals.
    pub replays_run: u64,
    /// PDR-invariant seals whose clause check came from the group's earlier replay.
    pub replays_shared: u64,
    /// Solve-time lowerings of a PDR-route `ChcVc` run: one per allocation.
    pub lowerings_run: u64,
    /// PDR-route requests whose solve reused their `ChcVc`'s earlier lowering.
    pub lowerings_shared: u64,
}

/// The share group whose engine results answered one request's solve.
///
/// Only [`TypedChcSolveShare::group`] makes one, and only that request's seal
/// takes it ([`TypedChcSolveShare::group_for_seal`]). It is neither `Clone` nor
/// `Copy`: one solve, one seal.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct SolvedInGroup(usize);

/// Where a group is filed: its digest, its timeout and an order-sensitive hash
/// of its lowering input. Equal keys are necessary, not sufficient, for
/// membership; [`ShareGroup::admits`] decides.
#[derive(Debug, PartialEq, Eq, Hash)]
struct GroupKey {
    digest: String,
    timeout: Duration,
    lowering: u64,
    execution: Option<trust_mc_core::NativeMcExecutionConfig>,
}

/// Per-bundle-call share of engine results.
#[derive(Default)]
pub(super) struct TypedChcSolveShare {
    /// Every group, in creation order. A [`SolvedInGroup`] indexes it.
    groups: Vec<ShareGroup>,
    /// The groups filed under each key; more than one only when two lowering
    /// inputs collide in the 64-bit hash or a digest collides.
    index: HashMap<GroupKey, Vec<usize>>,
    /// The group each `ChcVc` allocation joined under each timeout, keyed by
    /// the allocation's address.
    by_vc: HashMap<
        (usize, Duration, Option<trust_mc_core::NativeMcExecutionConfig>),
        JoinedAllocation,
    >,
    requests: u64,
    /// The solve-time lowering of each PDR-route `ChcVc` allocation, keyed by
    /// its address; the entry holds the `Arc`, so the address is not reused.
    #[cfg(feature = "ay-chc-native")]
    lowerings: HashMap<usize, SharedLowering>,
    lowerings_run: u64,
    lowerings_shared: u64,
    /// Candidates the membership check examined, for the lookup-cost tests.
    #[cfg(test)]
    admits_checked: u64,
    /// Test-only: file every group under this lowering hash, as if all
    /// lowering inputs collided, so the membership check alone separates them.
    #[cfg(test)]
    colliding_lowering_hash: Option<u64>,
}

impl TypedChcSolveShare {
    pub(super) fn new() -> Self {
        Self::default()
    }

    /// Count one request handed to the solver.
    pub(super) fn count_request(&mut self) {
        self.requests += 1;
    }

    /// [`super::prepare_validated_typed_chc_pdr_input`] for a request solved in
    /// this share. A PDR-route `ChcVc` allocation is lowered ONCE per bundle
    /// call, and every later request on it takes that lowering: the problem,
    /// its normalized input and digest, its accounting. The lowering reads only
    /// the relations, the rules and the query target, so it is the lowering the
    /// request would compute itself, and the shared-versus-per-request tests
    /// pin that every row is equal. The request's own identity (the
    /// obligation-set hash) is still computed for it alone, and the seal's
    /// fresh re-lowering is never taken from here.
    #[cfg(feature = "ay-chc-native")]
    pub(super) fn prepare(
        &mut self,
        obligation: &trust_mc_core::MirChcPdrObligation,
    ) -> super::NativeSolveResult<super::PreparedTypedChcPdrInput> {
        if super::typed_chc_pdr_route(obligation) != super::TypedChcPdrRoute::PdrProof {
            return super::prepare_validated_typed_chc_pdr_input(obligation);
        }
        let address = Arc::as_ptr(&obligation.vc) as usize;
        let shared = match self.lowerings.entry(address) {
            std::collections::hash_map::Entry::Occupied(entry)
                if Arc::ptr_eq(&entry.get().vc, &obligation.vc) =>
            {
                self.lowerings_shared += 1;
                entry.into_mut()
            }
            entry => {
                self.lowerings_run += 1;
                let lowered = SharedLowering {
                    vc: Arc::clone(&obligation.vc),
                    lowered: super::lower_typed_chc_for_pdr(obligation),
                };
                match entry {
                    std::collections::hash_map::Entry::Occupied(mut entry) => {
                        entry.insert(lowered);
                        entry.into_mut()
                    }
                    std::collections::hash_map::Entry::Vacant(entry) => entry.insert(lowered),
                }
            }
        };
        match &shared.lowered {
            Ok(lowered) => Ok(super::prepared_from_lowering(obligation, lowered)),
            Err(error) => Err(error.clone()),
        }
    }

    /// The group whose shared engine results answer a PDR-route solve of
    /// `obligation`, created on its first request, counting the request as a
    /// member. See the module docs for the four membership conditions.
    pub(super) fn group(
        &mut self,
        obligation: &trust_mc_core::MirChcPdrObligation,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
    ) -> (SolvedInGroup, &mut ShareGroup) {
        self.group_with_execution(obligation, normalized, timeout, None)
    }

    pub(super) fn group_with_execution(
        &mut self,
        obligation: &trust_mc_core::MirChcPdrObligation,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
        execution: Option<&trust_mc_core::NativeMcExecutionConfig>,
    ) -> (SolvedInGroup, &mut ShareGroup) {
        let index = self.locate_or_create(obligation, normalized, timeout, execution);
        let group = &mut self.groups[index];
        group.members += 1;
        (SolvedInGroup(index), group)
    }

    /// The group that answered a request's solve, handed back for that
    /// request's seal ONLY IF it admits the request's FRESH seal-time
    /// re-lowering (`normalized` is that re-lowering's, not the solve's) by
    /// every membership condition. `None` means the engine answer behind the
    /// request's verdict was not computed on the problem its own obligation
    /// lowers to, and no seal may be minted. Counts no member, creates no group.
    pub(super) fn group_for_seal(
        &mut self,
        solved_in: SolvedInGroup,
        obligation: &trust_mc_core::MirChcPdrObligation,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
    ) -> Option<&mut ShareGroup> {
        self.group_for_seal_with_execution(solved_in, obligation, normalized, timeout, None)
    }

    pub(super) fn group_for_seal_with_execution(
        &mut self,
        solved_in: SolvedInGroup,
        obligation: &trust_mc_core::MirChcPdrObligation,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
        execution: Option<&trust_mc_core::NativeMcExecutionConfig>,
    ) -> Option<&mut ShareGroup> {
        let group = self.groups.get_mut(solved_in.0)?;
        group.admits(obligation, normalized, timeout, execution).then_some(group)
    }

    fn locate_or_create(
        &mut self,
        obligation: &trust_mc_core::MirChcPdrObligation,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
        execution: Option<&trust_mc_core::NativeMcExecutionConfig>,
    ) -> usize {
        let address = Arc::as_ptr(&obligation.vc) as usize;
        // A request on an allocation the share has seen joins that allocation's
        // group after the normalized-input conditions alone: the allocation's
        // lowering input was compared with the group's when it first joined,
        // and a `ChcVc` behind an `Arc` the share holds cannot change (and its
        // address cannot be reused) while the share lives.
        if let Some(joined) = self.by_vc.get(&(address, timeout, execution.cloned()))
            && Arc::ptr_eq(&joined.vc, &obligation.vc)
        {
            #[cfg(test)]
            {
                self.admits_checked += 1;
            }
            if self.groups[joined.group].admits_normalized_input(normalized, timeout, execution) {
                return joined.group;
            }
        }
        let lowering = lowering_input_hash(&obligation.vc);
        #[cfg(test)]
        let lowering = self.colliding_lowering_hash.unwrap_or(lowering);
        let key = GroupKey {
            digest: normalized.normalized_input_hash.value.clone(),
            timeout,
            lowering,
            execution: execution.cloned(),
        };
        let candidates = self.index.entry(key).or_default();
        let mut found = None;
        for &index in candidates.iter() {
            #[cfg(test)]
            {
                self.admits_checked += 1;
            }
            if self.groups[index].admits(obligation, normalized, timeout, execution) {
                found = Some(index);
                break;
            }
        }
        let index = found.unwrap_or_else(|| {
            self.groups.push(ShareGroup::new(obligation, normalized, timeout, execution));
            let index = self.groups.len() - 1;
            candidates.push(index);
            index
        });
        self.by_vc.insert(
            (address, timeout, execution.cloned()),
            JoinedAllocation { vc: Arc::clone(&obligation.vc), group: index },
        );
        index
    }

    /// The counters, summed over every group.
    pub(super) fn work(&self) -> NativeBundleSolveWork {
        let digests = self
            .groups
            .iter()
            .map(|group| &group.normalized_input_hash.value)
            .collect::<std::collections::HashSet<_>>();
        let mut work = NativeBundleSolveWork {
            requests: self.requests,
            distinct_normalized_inputs: digests.len() as u64,
            lowerings_run: self.lowerings_run,
            lowerings_shared: self.lowerings_shared,
            ..NativeBundleSolveWork::default()
        };
        for group in &self.groups {
            let engine = group.engine_work();
            work.share_groups += 1;
            work.pdr_route_requests += group.members;
            work.solves_run += engine.solves_run;
            work.solves_shared += engine.solves_shared;
            work.engine_calls_run += engine.engine_calls_run;
            work.engine_calls_shared += engine.engine_calls_shared;
            work.replays_run += engine.replays_run;
            work.replays_shared += engine.replays_shared;
        }
        work
    }

    /// Every group's members and counters, for tests that pin "at most once
    /// per group".
    #[cfg(test)]
    pub(super) fn group_work(&self) -> Vec<(u64, EngineWork)> {
        self.groups.iter().map(|group| (group.members, group.engine_work())).collect()
    }

    /// The primary verdict that selected each group's later engine call sites.
    #[cfg(all(test, feature = "ay-chc-native"))]
    pub(super) fn group_pdr_results(&self) -> Vec<Option<&ay_chc::VerifiedChcResult>> {
        self.groups
            .iter()
            .map(|group| {
                group
                    .engine
                    .pdr
                    .as_ref()
                    .and_then(|slot| slot.as_ref())
                    .and_then(|run| run.as_ref().ok())
                    .map(|run| run.result())
            })
            .collect()
    }

    /// How many candidates the membership check has examined so far.
    #[cfg(test)]
    pub(super) fn admits_checked(&self) -> u64 {
        self.admits_checked
    }

    /// A share whose index files every group under ONE lowering hash, so the
    /// tests can show the membership check separates what the index does not.
    #[cfg(test)]
    pub(super) fn with_colliding_lowering_hash() -> Self {
        Self { colliding_lowering_hash: Some(0), ..Self::default() }
    }

    /// Test-only access to the group a solve was answered by, to simulate a
    /// grouping defect the seal must catch.
    #[cfg(test)]
    pub(super) fn group_mut_for_test(&mut self, solved_in: &SolvedInGroup) -> &mut ShareGroup {
        &mut self.groups[solved_in.0]
    }
}

/// One PDR-route `ChcVc` allocation's solve-time lowering (or its failure).
#[cfg(feature = "ay-chc-native")]
struct SharedLowering {
    vc: Arc<trust_mc_core::ChcVc>,
    lowered: super::NativeSolveResult<super::LoweredTypedChc>,
}

/// A `ChcVc` allocation whose lowering input was found identical to `group`'s.
/// Holding the `Arc` keeps the allocation, and so its address, alive.
struct JoinedAllocation {
    vc: Arc<trust_mc_core::ChcVc>,
    group: usize,
}

/// An order-sensitive hash of exactly what the lowering reads: the query
/// target, the relations in order (they fix the predicate ids) and the rules in
/// order (they fix the clause indices). An index key only; membership compares
/// the values themselves.
fn lowering_input_hash(vc: &trust_mc_core::ChcVc) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    vc.query.target.hash(&mut hasher);
    vc.relations.hash(&mut hasher);
    vc.rules.hash(&mut hasher);
    hasher.finish()
}

/// One group's engine counters. `solves_*` count the pipeline's first engine
/// call, `engine_calls_*` every engine call site, `replays_*` the seals' fresh
/// invariant clause checks.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct EngineWork {
    pub(super) solves_run: u64,
    pub(super) solves_shared: u64,
    pub(super) engine_calls_run: u64,
    pub(super) engine_calls_shared: u64,
    pub(super) replays_run: u64,
    pub(super) replays_shared: u64,
}

/// What a bounded-unroll witness search found: the unroll depth the unrolled
/// problem actually represents and the witness of its error derivation.
#[cfg(feature = "ay-chc-native")]
pub(super) type BoundedUnrollHit = (u32, crate::direct_smt_cex::AcyclicUnsafeWitness);

/// A shared strict proof run, or the failure text of the run.
#[cfg(feature = "ay-chc-native")]
pub(super) type SharedProofRun = Result<Arc<ay_encode::proof::ProofRun>, String>;

/// One normalized CHC input's group: the problem it answers and its engine
/// results.
pub(super) struct ShareGroup {
    normalized_input_hash: trust_mc_core::EvidenceHash,
    normalized_input: String,
    vc: Arc<trust_mc_core::ChcVc>,
    timeout: Duration,
    execution: Option<trust_mc_core::NativeMcExecutionConfig>,
    /// PDR-route solves the group answered.
    members: u64,
    #[cfg(feature = "ay-chc-native")]
    engine: EngineSlots,
}

impl ShareGroup {
    fn new(
        obligation: &trust_mc_core::MirChcPdrObligation,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
        execution: Option<&trust_mc_core::NativeMcExecutionConfig>,
    ) -> Self {
        Self {
            normalized_input_hash: normalized.normalized_input_hash.clone(),
            normalized_input: normalized.normalized_input.clone(),
            vc: Arc::clone(&obligation.vc),
            timeout,
            execution: execution.cloned(),
            members: 0,
            #[cfg(feature = "ay-chc-native")]
            engine: EngineSlots::default(),
        }
    }

    /// The four membership conditions of the module docs.
    fn admits(
        &self,
        obligation: &trust_mc_core::MirChcPdrObligation,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
        execution: Option<&trust_mc_core::NativeMcExecutionConfig>,
    ) -> bool {
        self.admits_normalized_input(normalized, timeout, execution)
            && same_lowering_input(&self.vc, &obligation.vc)
    }

    /// Conditions 1, 2 and 4: the PDR route, the digest, the bytes and the
    /// timeout.
    fn admits_normalized_input(
        &self,
        normalized: &super::NativeTypedChcPdrNormalizedInput,
        timeout: Duration,
        execution: Option<&trust_mc_core::NativeMcExecutionConfig>,
    ) -> bool {
        normalized.route == super::TypedChcPdrRoute::PdrProof
            && self.normalized_input_hash == normalized.normalized_input_hash
            && self.normalized_input == normalized.normalized_input
            && self.timeout == timeout
            && self.execution.as_ref() == execution
    }

    /// The digest of the normalized input this group's engine results answer.
    pub(super) fn normalized_input_hash(&self) -> &trust_mc_core::EvidenceHash {
        &self.normalized_input_hash
    }

    /// The group's engine results.
    #[cfg(feature = "ay-chc-native")]
    pub(super) fn engine(&mut self) -> &mut EngineSlots {
        &mut self.engine
    }

    /// True when the group's acyclic direct-SMT decision ran and found the
    /// problem `Safe`: the derivation a PDR-route CHC-validity seal stands on.
    #[cfg(feature = "ay-chc-native")]
    pub(super) fn acyclic_decision_is_safe(&self) -> bool {
        matches!(
            self.engine.acyclic.as_ref(),
            Some(Some(decision)) if matches!(**decision, crate::direct_smt_cex::AcyclicDecision::Safe)
        )
    }

    fn engine_work(&self) -> EngineWork {
        #[cfg(feature = "ay-chc-native")]
        {
            self.engine.work
        }
        #[cfg(not(feature = "ay-chc-native"))]
        {
            EngineWork::default()
        }
    }

    /// Test-only: overwrite the normalized input the group answers, as a
    /// grouping defect that filed a request under another problem would.
    #[cfg(test)]
    pub(super) fn corrupt_normalized_input_for_test(&mut self, normalized_input: String) {
        self.normalized_input = normalized_input;
    }

    /// Test-only: forget the group's acyclic decision, as if its pipeline had
    /// never decided the problem `Safe`.
    #[cfg(all(test, feature = "ay-chc-native"))]
    pub(super) fn forget_acyclic_decision_for_test(&mut self) {
        self.engine.acyclic = Some(None);
    }
}

/// The engine results of ONE problem under one timeout, each slot filled by
/// the first call that reaches its call site and read by every later one.
///
/// A share group owns one for its normalized input; a request solved without a
/// share owns a fresh one for its own pipeline, so the pipeline code is the
/// same either way and a call site the pipeline reaches twice on the same
/// input (the IC3 loop lane before PDR and again after a PDR `Unknown`) runs
/// once in both.
#[cfg(feature = "ay-chc-native")]
#[derive(Default)]
pub(super) struct EngineSlots {
    work: EngineWork,
    /// `acyclic_direct_smt_decision` under the watchdog (`None`: it expired).
    acyclic: Option<Option<Arc<crate::direct_smt_cex::AcyclicDecision>>>,
    /// The IC3 loop lane's proof run (outer `None`: watchdog). The lane is a
    /// function of the problem and the timeout, so its two call sites share it.
    ic3: Option<Option<Option<Arc<ay_encode::proof::ProofRun>>>>,
    /// The strict PDR proof run (outer `None`: watchdog).
    pdr: Option<Option<SharedProofRun>>,
    /// Bounded-unroll witness searches, one per ladder and ceiling.
    bounded_unroll: Vec<BoundedUnrollSearch>,
    /// Fresh invariant-model clause checks, one per distinct model and timeout.
    invariant_replays: Vec<InvariantReplay>,
}

/// One bounded-unroll witness search: its whole input besides the problem.
#[cfg(feature = "ay-chc-native")]
struct BoundedUnrollSearch {
    ladder: Vec<u32>,
    ceiling: Duration,
    hit: Option<BoundedUnrollHit>,
}

/// One fresh clause check of an invariant model against the group's problem.
#[cfg(feature = "ay-chc-native")]
struct InvariantReplay {
    model_bytes: Vec<u8>,
    timeout: Duration,
    validated: Option<Result<bool, String>>,
}

#[cfg(feature = "ay-chc-native")]
impl EngineSlots {
    /// The pipeline's first engine call. Its run/share split is the
    /// solves-run/solves-shared count.
    pub(super) fn acyclic_decision(
        &mut self,
        run: impl FnOnce() -> Option<crate::direct_smt_cex::AcyclicDecision>,
    ) -> Option<Arc<crate::direct_smt_cex::AcyclicDecision>> {
        if self.acyclic.is_some() {
            self.work.solves_shared += 1;
        } else {
            self.work.solves_run += 1;
        }
        get_or_run(&mut self.acyclic, &mut self.work, || run().map(Arc::new))
    }

    /// The IC3 loop lane's engine half, from either of its call sites.
    pub(super) fn ic3_loop_lane(
        &mut self,
        run: impl FnOnce() -> Option<Option<ay_encode::proof::ProofRun>>,
    ) -> Option<Option<Arc<ay_encode::proof::ProofRun>>> {
        get_or_run(&mut self.ic3, &mut self.work, || run().map(|lane| lane.map(Arc::new)))
    }

    pub(super) fn pdr(
        &mut self,
        run: impl FnOnce() -> Option<SharedProofRun>,
    ) -> Option<SharedProofRun> {
        get_or_run(&mut self.pdr, &mut self.work, run)
    }

    /// The bounded-unroll witness search over `ladder` within `ceiling`, run
    /// once per distinct ladder and ceiling: both are part of the search's
    /// input, so another ladder never reads this one's witness or depth.
    pub(super) fn bounded_unroll(
        &mut self,
        ladder: &[u32],
        ceiling: Duration,
        run: impl FnOnce() -> Option<BoundedUnrollHit>,
    ) -> Option<BoundedUnrollHit> {
        if let Some(search) = self
            .bounded_unroll
            .iter()
            .find(|search| search.ceiling == ceiling && search.ladder == ladder)
        {
            self.work.engine_calls_shared += 1;
            return search.hit.clone();
        }
        self.work.engine_calls_run += 1;
        let hit = run();
        self.bounded_unroll.push(BoundedUnrollSearch {
            ladder: ladder.to_vec(),
            ceiling,
            hit: hit.clone(),
        });
        hit
    }

    /// The fresh clause check of the invariant model `model_bytes` against
    /// this group's problem under `timeout`, run once per distinct model.
    ///
    /// The caller parsed `model_bytes` against ITS OWN freshly re-lowered
    /// problem, which this group admitted (byte-identical normalized input,
    /// identical lowering input), so the model and the problem the check
    /// answers are exactly the caller's.
    pub(super) fn invariant_replay(
        &mut self,
        model_bytes: &[u8],
        timeout: Duration,
        run: impl FnOnce() -> Option<Result<bool, String>>,
    ) -> Option<Result<bool, String>> {
        if let Some(replay) = self
            .invariant_replays
            .iter()
            .find(|replay| replay.timeout == timeout && replay.model_bytes == model_bytes)
        {
            self.work.replays_shared += 1;
            return replay.validated.clone();
        }
        self.work.replays_run += 1;
        let validated = run();
        self.invariant_replays.push(InvariantReplay {
            model_bytes: model_bytes.to_vec(),
            timeout,
            validated: validated.clone(),
        });
        validated
    }

    /// This pipeline's counters (a request solved without a share).
    #[cfg(test)]
    pub(super) fn work(&self) -> EngineWork {
        self.work
    }
}

/// Return the slot's result, running `run` only when no earlier call has.
#[cfg(feature = "ay-chc-native")]
fn get_or_run<T: Clone>(slot: &mut Option<T>, work: &mut EngineWork, run: impl FnOnce() -> T) -> T {
    if let Some(value) = slot {
        work.engine_calls_shared += 1;
        return value.clone();
    }
    work.engine_calls_run += 1;
    let value = run();
    *slot = Some(value.clone());
    value
}

/// True when lowering `a` and `b` yields the identical `ay_chc::ChcProblem`.
///
/// `typed_chc_ay::lower_obligation_with_accounting` reads exactly the
/// relations (in order: they fix the predicate ids), the rules (in order: they
/// fix the clause indices) and the query target. Pointer equality is the case
/// of every request on one translated function and costs nothing; the
/// structural comparison runs only for a request whose normalized input is
/// already byte-identical to the group's.
fn same_lowering_input(a: &Arc<trust_mc_core::ChcVc>, b: &Arc<trust_mc_core::ChcVc>) -> bool {
    Arc::ptr_eq(a, b)
        || (a.query.target == b.query.target && a.relations == b.relations && a.rules == b.rules)
}
