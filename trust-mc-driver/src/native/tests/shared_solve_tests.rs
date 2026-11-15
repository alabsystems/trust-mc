// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Design step 8c: one solve and one replay per normalized CHC input of a native
//! bundle, one seal per request.
//!
//! These tests pin, against the per-request solve as the oracle:
//!
//! * EQUALITY: every row the shared solve returns is equal — verification
//!   (outcome, verdict, cache key, artifact directory, route AND the private
//!   seal), transport, not-proved reason, refutation — to the row an unshared,
//!   per-request solve returns for the same request: on the driver's bundle
//!   corpus (CHC-validity AND PDR-invariant proofs through the production
//!   entry point), on a looping refutation, below the gate on the checked-in
//!   dumped modules, on rows whose per-request gates differ inside one group,
//!   and on randomly generated programs (the TMC-1 generator families);
//! * WORK: one engine pipeline per distinct normalized input, however many
//!   requests ask about it, each engine call site run at most once per input
//!   (the IC3 loop lane's two call sites share one run), and one fresh
//!   invariant replay per group and model, at the production entry point;
//! * BINDING: a seal is minted only from the share group that answered the
//!   request's solve, only when that group admits the request's fresh
//!   re-lowering, and — for a CHC-validity seal — only when that group decided
//!   the problem `Safe`; a seal moved to another request, even one answered by
//!   the same shared solve and even with its binding hash recomputed for the
//!   target, is refused;
//! * MEMBERSHIP: two requests share only with a byte-identical normalized input
//!   AND an identical lowering input AND one timeout, and a lookup examines one
//!   candidate group.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::*;

/// The solve options of every bundle solve below: the PDR engine with a short
/// budget, as the neighbouring bundle tests use.
fn runner() -> NativeTrustIrChcPdrRunner {
    NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default()
            .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
            .with_timeout(Duration::from_secs(8)),
    )
}

/// `bundle` with every CHC request asked `copies` more times: the same function
/// and obligations under fresh request ids — the compiler's shape, one request
/// per public obligation, all on one function.
fn with_request_copies(
    mut bundle: trust_ir::NativeVerificationBundle,
    copies: u32,
) -> trust_ir::NativeVerificationBundle {
    let originals = bundle
        .requests
        .iter()
        .filter_map(|request| match request {
            trust_ir::NativeVerificationRequest::TrustMc(request) => Some(request.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut next_id =
        bundle.requests.iter().map(|request| request.id().index()).max().unwrap_or(0) + 1;
    for _ in 0..copies {
        for original in &originals {
            let mut copy = original.clone();
            copy.id = trust_ir::NativeRequestId::new(next_id);
            next_id += 1;
            bundle.requests.push(trust_ir::NativeVerificationRequest::TrustMc(copy));
        }
    }
    bundle
}

fn fixture_bundle(json: &str) -> trust_ir::NativeVerificationBundle {
    let mut bundle: trust_ir::NativeVerificationBundle =
        serde_json::from_str(json).expect("the checked-in native bundle is valid JSON");
    // The captures stay immutable. This solver-sharing test selects the actual
    // supported execution profile explicitly, independent of historical defaults.
    for row in &mut bundle.requests {
        if let trust_ir::NativeVerificationRequest::TrustMc(request) = row {
            request.options.slicing = trust_ir::TrustMcSlicingMode::None;
            request.options.chc.engine = trust_ir::TrustMcChcEngine::NativePdr;
            request.options.chc.invariant_source = trust_ir::TrustMcInvariantSource::None;
            request.options.chc.pdr.enabled = true;
        }
    }
    bundle
}

/// A compiler-shaped bundle around a SAFE loop: the counter of
/// `loop_overflow_trust_ir_bundle` without its u8 accumulator, so the one check
/// is the counter's `i + 1` overflow, which holds on every iteration only by a
/// loop invariant (`i <= 64`) — a PDR-invariant proof whose seal runs the fresh
/// invariant replay, through the production bundle entry point.
fn counting_loop_bundle() -> trust_ir::NativeVerificationBundle {
    use trust_ir::inst::ICmpOp;
    use trust_ir::ty::Ty;
    use trust_ir::{
        NativeAdapterInput, NativeAssertionId, NativeBundleProducer, NativeCompilerFactRef,
        NativeCompilerFacts, NativeMonomorphizationFact, NativeMonomorphizationId,
        NativeObligationCause, NativeObligationSource, NativeReplayAtom, NativeReplayAtomId,
        NativeReplayContext, NativeRequestId, NativeRequestProvenance, NativeToolIdentity,
        NativeVerificationBundle, NativeVerificationRequest, ObligationKind, ProofDigest,
        ProofFormula, ProofId, ProofLineageId, ProofLineageManifest, ProofLineageNode,
        ProofObligation, ProofReplayIdentity, ProofStatus, ProofTransform, ProofTransformStage,
        TrustMcNativeRequest, TrustMcVerificationMode,
    };
    use trust_ir_build::ModuleBuilder;

    let source_digest = ProofDigest::sha256([0x81; 32]);
    let trust_ir_module_digest = ProofDigest::sha256([0x82; 32]);

    let mut mb = ModuleBuilder::new("native_trust_ir_counting_loop_bundle");
    let ft = mb.add_func_type(vec![Ty::U8], vec![Ty::U8]);
    {
        let mut fb = mb.function("counting_loop", ft);
        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();

        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let _x = fb.add_block_param(entry, Ty::U8);
        let zero_i = fb.iconst(Ty::U64, 0);
        let zero_t = fb.iconst(Ty::U8, 0);
        fb.br(header, vec![zero_i, zero_t]);

        let i = fb.add_block_param(header, Ty::U64);
        let t = fb.add_block_param(header, Ty::U8);
        fb.switch_to_block(header);
        let bound = fb.iconst(Ty::U64, 64);
        let in_loop = fb.icmp(ICmpOp::Ult, Ty::U64, i, bound);
        fb.condbr(in_loop, body, vec![i, t], exit, vec![t]);

        let i_body = fb.add_block_param(body, Ty::U64);
        let t_body = fb.add_block_param(body, Ty::U8);
        fb.switch_to_block(body);
        let one = fb.iconst(Ty::U64, 1);
        let i_next = fb.add(Ty::U64, i_body, one);
        fb.br(header, vec![i_next, t_body]);

        let t_exit = fb.add_block_param(exit, Ty::U8);
        fb.switch_to_block(exit);
        fb.ret(vec![t_exit]);
        fb.build();
    }

    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    let function = module
        .functions
        .iter()
        .find(|func| func.name == "counting_loop")
        .expect("fixture includes the requested function")
        .id;
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "the loop counter's increment does not overflow",
        )
        .with_formula(ProofFormula::smtlib2("counting_loop_safe", "Bool"))
        .with_function(function)
        .with_source(native_test_obligation_source(
            "rust:native_trust_ir_counting_loop_bundle::counting_loop",
            "vc:trust-mc-driver:counting-loop:0",
            b"counting_loop_safe",
        )),
    );
    let mut lineage_node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source_digest,
        trust_ir_module_digest,
    );
    lineage_node.obligations.push(ProofId::new(0));
    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![lineage_node],
        roots: vec![ProofLineageId::new(0)],
    };
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir { body_digest: source_digest },
        trust_ir_module_digest,
        module,
        lineage,
    );
    let span = trust_ir::SourceSpan { file: 0, line: 31, col: 9 };
    bundle.compiler_facts = NativeCompilerFacts {
        monomorphizations: vec![NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: "native_trust_ir_counting_loop_bundle::counting_loop".to_owned(),
            symbol: "_RNvNtC6native13counting_loop".to_owned(),
            generic_args: Vec::new(),
            function: Some(function),
            stable_digest: ProofDigest::sha256([0x83; 32]),
        }],
        obligation_sources: vec![NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: "vc:trust-mc-driver:counting-loop:0".to_string(),
            function: Some(function),
            span: Some(span),
            assertion_id: Some(NativeAssertionId::new(0)),
            cause: NativeObligationCause::OverflowCheck,
            monomorphization: Some(NativeMonomorphizationId::new(0)),
            facts: vec![NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0))],
        }],
        ..NativeCompilerFacts::default()
    };
    bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(9),
        mode: TrustMcVerificationMode::Chc,
        function,
        obligations: vec![ProofId::new(0)],
        lineage_roots: vec![ProofLineageId::new(0)],
        options: {
            let mut options = trust_ir::TrustMcRequestOptions::default();
            options.slicing = trust_ir::TrustMcSlicingMode::None;
            options.chc.engine = trust_ir::TrustMcChcEngine::NativePdr;
            options.chc.invariant_source = trust_ir::TrustMcInvariantSource::None;
            options.chc.pdr.enabled = true;
            options.chc.emit_horn_clauses = true;
            options
        },
        diagnostics: Default::default(),
        provenance: NativeRequestProvenance::trust_mc(
            NativeToolIdentity::new("trust-mc").with_version("chc-v1"),
        )
        .with_solver(NativeToolIdentity::new("ay-chc").with_version("native-v1"))
        .with_replay(
            ProofReplayIdentity::new("trust-mc", "trust_mc native typed CHC/PDR test replay")
                .with_transcript_digest(ProofDigest::sha256([0x84; 32])),
        )
        .with_replay_context(
            NativeReplayContext::default().with_atom(
                NativeReplayAtom::assertion(
                    NativeReplayAtomId::new(0),
                    ProofFormula::smtlib2("counting_loop_safe", "Bool"),
                )
                .with_obligation(ProofId::new(0))
                .with_assertion_id(NativeAssertionId::new(0))
                .with_span(span),
            ),
        ),
    }));
    refresh_native_test_bundle_module_identity(&mut bundle);
    bundle
}

/// How a corpus bundle enters the proof-grade lane.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Lane {
    /// `solve_bundle_native_proof_grade`: no source-generation authority.
    DefaultDeny,
    /// `..._with_source_authority`, with authority minted for the exact bundle
    /// (a saved compiler body carries none of its own).
    SourceAuthority,
}

/// The corpus: the driver's compiler-shaped bundles, each asked several times,
/// and the checked-in `-Ztrust-dump` bundles, which already ask one question per
/// obligation of one function. The proof-grade gate refuses all three dumps
/// before any solve (an unauthenticated `Assume`, an `Undef`, an unbound
/// `Alloca`; their saved schema is too old to mint authority for), so here they
/// pin only that sharing leaves the refusal unchanged;
/// `shared_solve_equals_per_request_solve_on_the_dumped_modules` solves their
/// functions below the gate. The looping refutation has its own test
/// (`shared_loop_refutation_equals_per_request_refutation`): its rows depend on
/// watchdog timing, and a flake there must name itself.
fn corpus() -> Vec<(&'static str, Lane, trust_ir::NativeVerificationBundle)> {
    use Lane::{DefaultDeny, SourceAuthority};
    vec![
        (
            "compiler_style_safe x4",
            DefaultDeny,
            with_request_copies(compiler_style_safe_trust_ir_bundle(), 3),
        ),
        (
            "mixed_outcome x3",
            DefaultDeny,
            with_request_copies(mixed_outcome_trust_ir_bundle(true), 2),
        ),
        ("panic_free x3", DefaultDeny, with_request_copies(panic_free_compiler_bundle(), 2)),
        (
            "u32_guarded x3",
            DefaultDeny,
            with_request_copies(u32_compiler_shaped_guarded_bundle(), 2),
        ),
        ("counting_loop x3", DefaultDeny, with_request_copies(counting_loop_bundle(), 2)),
        (
            "source_generated_unwrap_or x3",
            SourceAuthority,
            with_request_copies(source_generated_unwrap_or_bundle(), 2),
        ),
        (
            "recursive_requires",
            DefaultDeny,
            fixture_bundle(include_str!(
                "../../../../trust-mc-trust-bmc/tests/fixtures/recursive_requires_native_bundle.json"
            )),
        ),
        (
            "stale_struct",
            DefaultDeny,
            fixture_bundle(include_str!(
                "../../../../trust-mc-trust-bmc/tests/fixtures/stale_struct_native_bundle.json"
            )),
        ),
        (
            "format_args_insert_element",
            DefaultDeny,
            fixture_bundle(include_str!(
                "../../../../trust-mc-trust-bmc/tests/fixtures/format_args_insert_element_native_bundle.json"
            )),
        ),
    ]
}

/// The normalized-input digest of every PDR-route request the bundle solve
/// hands to the engine, computed independently of the share.
fn pdr_route_digests(
    runner: &NativeTrustIrChcPdrRunner,
    bundle: &trust_ir::NativeVerificationBundle,
) -> Vec<String> {
    let Ok(translated) = runner.translate_obligations(bundle) else {
        return Vec::new();
    };
    translated
        .iter()
        .filter(|row| row.unmodeled_obligations.is_empty() && row.obligation.validate().is_ok())
        .filter_map(|row| normalized_typed_chc_pdr_input(&row.obligation).ok())
        .filter(|normalized| normalized.route == TypedChcPdrRoute::PdrProof)
        .map(|normalized| normalized.normalized_input_hash.value)
        .collect()
}

fn request_key(translated: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation) -> (u32, String) {
    (translated.request_id.index(), translated.obligation.obligation_id.clone())
}

/// Assert the shared solve's evidence equals the per-request solve's, row by row.
fn assert_rows_equal(
    name: &str,
    shared: &NativeTrustIrChcPdrBundleEvidence,
    per_request: &NativeTrustIrChcPdrBundleEvidence,
) {
    assert_eq!(shared.obligations.len(), per_request.obligations.len(), "{name}: proved rows");
    for (shared, reference) in shared.obligations.iter().zip(&per_request.obligations) {
        let key = request_key(&shared.translated);
        assert_eq!(key, request_key(&reference.translated), "{name}: proved row order");
        // `TypedChcPdrFullVerification: PartialEq` compares the PRIVATE SEAL too:
        // the shared seal is the seal the request's own unshared solve mints.
        assert_eq!(shared.verification, reference.verification, "{name} {key:?}: verification");
        assert_eq!(shared.transport, reference.transport, "{name} {key:?}: transport");
        shared
            .verification
            .authorized_native_proof()
            .unwrap_or_else(|error| panic!("{name} {key:?}: shared row lost authority: {error}"));
    }
    assert_eq!(shared.not_proved.len(), per_request.not_proved.len(), "{name}: not-proved rows");
    for (shared, reference) in shared.not_proved.iter().zip(&per_request.not_proved) {
        let key = request_key(&shared.translated);
        assert_eq!(key, request_key(&reference.translated), "{name}: not-proved row order");
        assert_eq!(shared.reason, reference.reason, "{name} {key:?}: not-proved reason");
    }
    assert_eq!(shared.refuted.len(), per_request.refuted.len(), "{name}: refuted rows");
    for (shared, reference) in shared.refuted.iter().zip(&per_request.refuted) {
        let key = request_key(&shared.translated);
        assert_eq!(key, request_key(&reference.translated), "{name}: refuted row order");
        assert_eq!(shared.verification, reference.verification, "{name} {key:?}: refutation");
    }
}

fn proof_kind(verification: &TypedChcPdrFullVerification) -> trust_mc_core::ChcPdrProofKind {
    trust_mc_core::validated_native_typed_chc_pdr_candidate(&verification.verdict)
        .expect("a proved row carries a validated candidate")
        .proof_kind
}

/// Solve `bundle` per request and with a share, and return both.
fn solve_both_ways(
    runner: &NativeTrustIrChcPdrRunner,
    bundle: &trust_ir::NativeVerificationBundle,
    authority: Option<&trust_ir::SourceGenerationAuthority>,
) -> (
    NativeSolveResult<NativeTrustIrChcPdrBundleEvidence>,
    NativeSolveResult<NativeTrustIrChcPdrBundleEvidence>,
    TypedChcSolveShare,
) {
    let per_request = runner.solve_bundle_native_proof_grade_inner(bundle, authority, None, None);
    let mut share = TypedChcSolveShare::new();
    let shared =
        runner.solve_bundle_native_proof_grade_inner(bundle, authority, None, Some(&mut share));
    (shared, per_request, share)
}

#[test]
fn shared_rows_equal_per_request_rows_on_the_corpus() {
    let runner = runner();
    let mut proved = 0;
    let mut not_proved = 0;
    let mut refuted = 0;
    let mut replays_shared = 0;
    let mut kinds = BTreeSet::new();
    for (name, lane, mut bundle) in corpus() {
        let authority = (lane == Lane::SourceAuthority).then(|| {
            trust_ir::SourceGenerationAuthority::mint_from_live_lowering(&mut bundle)
                .expect("mint authority for the exact corpus bundle")
        });
        let (shared, per_request, share) = solve_both_ways(&runner, &bundle, authority.as_ref());
        let (shared, per_request) = match (shared, per_request) {
            (Ok(shared), Ok(per_request)) => (shared, per_request),
            (Err(shared), Err(per_request)) => {
                assert_eq!(shared, per_request, "{name}: the bundle error is the same");
                eprintln!("[8c corpus] {name}: bundle refused before solving: {shared}");
                continue;
            }
            (shared, per_request) => panic!(
                "{name}: one solve failed the bundle and the other did not: shared={:?} \
                 per_request={:?}",
                shared.err(),
                per_request.err()
            ),
        };
        assert_rows_equal(name, &shared, &per_request);

        let work = share.work();
        let digests = pdr_route_digests(&runner, &bundle);
        let distinct = digests.iter().collect::<BTreeSet<_>>().len() as u64;
        assert_eq!(work.pdr_route_requests, digests.len() as u64, "{name}: {work:?}");
        assert_eq!(work.distinct_normalized_inputs, distinct, "{name}: {work:?}");
        assert_eq!(work.share_groups, distinct, "{name}: no same-digest split: {work:?}");
        assert_eq!(work.solves_run, distinct, "{name}: one solve per digest: {work:?}");
        assert_eq!(
            work.solves_run + work.solves_shared,
            work.pdr_route_requests,
            "{name}: every PDR-route request entered the pipeline once: {work:?}"
        );
        for (members, group) in share.group_work() {
            assert_eq!(group.solves_run, 1, "{name}: {group:?}");
            // Four engine call sites (acyclic, IC3 lane, PDR, bounded unroll),
            // each run at most once per group.
            assert!(group.engine_calls_run <= 4, "{name}: {group:?}");
            assert!(group.replays_run <= 1, "{name}: one model per group: {group:?}");
            assert!(group.replays_run + group.replays_shared <= members, "{name}: {group:?}");
        }
        replays_shared += work.replays_shared;

        for row in &shared.obligations {
            kinds.insert(format!("{:?}", proof_kind(&row.verification)));
        }
        proved += shared.obligations.len();
        not_proved += shared.not_proved.len();
        refuted += shared.refuted.len();
        eprintln!(
            "[8c corpus] {name}: proved={} not_proved={} refuted={} {work:?}",
            shared.obligations.len(),
            shared.not_proved.len(),
            shared.refuted.len()
        );
    }
    eprintln!("[8c corpus] proof kinds: {kinds:?}");
    // Both proof kinds — so both shared authorities (the acyclic `Safe` decision
    // behind a CHC-validity seal, the invariant replay behind a PDR-invariant
    // seal) — are exercised, and the replay is shared at the bundle entry point.
    assert!(kinds.contains("ChcValidity") && kinds.contains("PdrInvariant"), "{kinds:?}");
    assert!(replays_shared > 0, "the corpus shares an invariant replay");
    // Proofs and not-proved rows happen, so the equality above is not vacuous;
    // the refuted channel is the looping refutation's test below.
    assert!(proved > 0 && not_proved > 0, "{proved}/{not_proved}/{refuted}");
}

/// The looping refutation keeps the independently replayable bounded-unroll
/// witness whether primary PDR ends `Unknown` or finds `Unsafe` first. The
/// latter skips the post-Unknown IC3 call site, so pin work to the actual
/// cached primary verdict without requiring a weaker solver outcome.
#[test]
fn shared_loop_refutation_equals_per_request_refutation() {
    let runner = runner();
    let bundle = with_request_copies(loop_overflow_trust_ir_bundle(), 1);
    let (shared, per_request, share) = solve_both_ways(&runner, &bundle, None);
    let shared = shared.expect("the bundle solves");
    let per_request = per_request.expect("the bundle solves");
    assert_rows_equal("loop_overflow x2", &shared, &per_request);
    assert_eq!(shared.refuted.len(), 2, "both requests are refuted with a witness");
    for row in &shared.refuted {
        assert!(
            matches!(
                &row.verification.outcome.status,
                trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) }
                    if matches!(
                        witness.verification,
                        trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { .. }
                    )
            ),
            "the refutation must retain its independently replayable bounded-unroll witness"
        );
    }

    let work = share.work();
    assert_eq!(work.solves_run, 1, "{work:?}");
    assert_eq!(work.solves_shared, 1, "{work:?}");
    let [(members, group)] = share.group_work()[..] else {
        panic!("one group: {work:?}");
    };
    assert_eq!(members, 2);
    // Acyclic, IC3, PDR and bounded unroll each run once. An Unknown primary
    // also reads the IC3 cache before unrolling (once per request); an Unsafe
    // primary goes directly to the same independently replayable unroll lane.
    assert_eq!(group.engine_calls_run, 4, "{group:?}");
    let primary_results = share.group_pdr_results();
    let [Some(primary)] = primary_results.as_slice() else {
        panic!("one completed primary PDR result: {primary_results:?}");
    };
    let expected_shared = match primary {
        ay_chc::VerifiedChcResult::Unsafe(_) => 4,
        ay_chc::VerifiedChcResult::Unknown(_) => 6,
        other => panic!("the unsafe loop must not receive a safety proof: {other:?}"),
    };
    assert_eq!(group.engine_calls_shared, expected_shared, "{group:?}; primary={primary:?}");
}

#[test]
fn one_solve_per_distinct_normalized_input_at_every_request_count() {
    let runner = runner();
    for requests in [1_u32, 4, 16] {
        let bundle = with_request_copies(compiler_style_safe_trust_ir_bundle(), requests - 1);
        let lowerings_before = typed_chc_ay::lowerings_on_this_thread();
        let (evidence, work) =
            runner.solve_bundle_native_proof_grade_with_work(&bundle).expect("bundle proves");
        let lowerings = typed_chc_ay::lowerings_on_this_thread() - lowerings_before;
        assert_eq!(evidence.obligations.len(), requests as usize, "every request proves");
        // The CHC is lowered once for the solve of every request on it; each
        // request's seal still re-lowers it freshly for itself.
        assert_eq!((work.lowerings_run, work.lowerings_shared), (1, u64::from(requests) - 1));
        assert_eq!(lowerings, 1 + u64::from(requests), "{work:?}");
        assert_eq!(work.requests, u64::from(requests), "{work:?}");
        assert_eq!(work.pdr_route_requests, u64::from(requests), "{work:?}");
        assert_eq!(work.distinct_normalized_inputs, 1, "{work:?}");
        assert_eq!(work.share_groups, 1, "{work:?}");
        assert_eq!(work.solves_run, 1, "ONE solve for {requests} requests: {work:?}");
        assert_eq!(work.solves_shared, u64::from(requests) - 1, "{work:?}");
        assert_eq!(
            work.engine_calls_shared,
            (u64::from(requests) - 1) * work.engine_calls_run,
            "every later request reads every engine call the first one ran: {work:?}"
        );
        for row in &evidence.obligations {
            row.verification.authorized_native_proof().expect("each request keeps its own seal");
        }
    }
}

/// The production entry point (`solve_bundle_native_proof_grade_with_work`) on a
/// function whose proof is a PDR invariant: N requests, ONE solve and ONE fresh
/// invariant replay, N seals that each authorize their own request.
#[test]
fn a_pdr_invariant_bundle_replays_once_at_the_production_entry_point() {
    let runner = runner();
    for requests in [1_u32, 4] {
        let bundle = with_request_copies(counting_loop_bundle(), requests - 1);
        let (evidence, work) =
            runner.solve_bundle_native_proof_grade_with_work(&bundle).expect("bundle solves");
        assert_eq!(
            evidence.obligations.len(),
            requests as usize,
            "every request proves: {:?}",
            evidence.not_proved.iter().map(|row| &row.reason).collect::<Vec<_>>()
        );
        for row in &evidence.obligations {
            assert_eq!(proof_kind(&row.verification), trust_mc_core::ChcPdrProofKind::PdrInvariant);
            row.verification.authorized_native_proof().expect("each request keeps its own seal");
        }
        assert_eq!(work.solves_run, 1, "{work:?}");
        assert_eq!(work.replays_run, 1, "ONE fresh replay for {requests} seals: {work:?}");
        assert_eq!(work.replays_shared, u64::from(requests) - 1, "{work:?}");
    }
}

/// `count` requests on one function whose CHC is replaced by a safe LOOP, so
/// the solve proves through a PDR invariant and the seal runs the fresh
/// invariant replay: the translated rows keep their own ids and metadata and
/// share one `Arc` of the loop CHC, exactly as rows of one function do.
fn pdr_invariant_rows(count: u32) -> Vec<trust_mc_trust_bmc::NativeTrustMcChcPdrObligation> {
    rows_on_one_vc(count, safe_cyclic_typed_chc_obligation("loop", 10).vc)
}

/// `count` translated compiler-shaped rows (their own ids and metadata), all
/// carrying `vc`.
fn rows_on_one_vc(
    count: u32,
    vc: Arc<trust_mc_core::ChcVc>,
) -> Vec<trust_mc_trust_bmc::NativeTrustMcChcPdrObligation> {
    let bundle = with_request_copies(compiler_style_safe_trust_ir_bundle(), count - 1);
    let mut rows = runner().translate_obligations(&bundle).expect("bundle translates");
    for row in &mut rows {
        row.obligation.vc = Arc::clone(&vc);
    }
    rows
}

/// Solve and seal one row as the bundle loop does, through `share` (or alone).
fn solve_and_seal_one(
    runner: &NativeTrustIrChcPdrRunner,
    row: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    share: Option<&mut TypedChcSolveShare>,
) -> TypedChcPdrFullVerification {
    let options = row.request_config.solve_options(runner.solve_options());
    let typed = NativeTypedChcPdrRunner::with_options(options.clone());
    match share {
        Some(share) => {
            let (verification, solved_in) = typed
                .solve_full_verification_in(row.obligation.clone(), Some(&mut *share))
                .expect("the row solves");
            verification.with_private_native_bundle_authority(
                row,
                &options,
                solved_in.map(|solved_in| (share, solved_in)),
            )
        }
        None => typed
            .solve_full_verification(row.obligation.clone())
            .expect("the row solves")
            .with_private_native_bundle_authority(
                row,
                &row.request_config.solve_options(runner.solve_options()),
                None,
            ),
    }
}

/// Solve and seal `rows` as the bundle loop does, through one share.
fn solve_and_seal(
    rows: &[trust_mc_trust_bmc::NativeTrustMcChcPdrObligation],
    share: &mut TypedChcSolveShare,
) -> Vec<TypedChcPdrFullVerification> {
    let runner = runner();
    rows.iter().map(|row| solve_and_seal_one(&runner, row, Some(&mut *share))).collect()
}

#[test]
fn pdr_invariant_rows_solve_and_replay_once_and_keep_their_own_seals() {
    let rows = pdr_invariant_rows(3);
    let mut share = TypedChcSolveShare::new();
    let shared = solve_and_seal(&rows, &mut share);
    let work = share.work();
    assert_eq!(work.distinct_normalized_inputs, 1, "{work:?}");
    assert_eq!(work.solves_run, 1, "{work:?}");
    assert_eq!(work.solves_shared, 2, "{work:?}");
    assert_eq!(work.replays_run, 1, "ONE fresh invariant replay for three seals: {work:?}");
    assert_eq!(work.replays_shared, 2, "{work:?}");

    let runner = runner();
    for (row, shared) in rows.iter().zip(&shared) {
        assert_eq!(proof_kind(shared), trust_mc_core::ChcPdrProofKind::PdrInvariant);
        shared.authorized_native_proof().expect("each request keeps its own seal");
        let per_request = solve_and_seal_one(&runner, row, None);
        assert_eq!(shared, &per_request, "{}: shared row equals per-request row", row.request_id);
    }
}

#[test]
fn a_shared_replay_never_answers_for_another_invariant_model() {
    let rows = pdr_invariant_rows(2);
    let runner = runner();
    let mut share = TypedChcSolveShare::new();
    let first = solve_and_seal(&rows[..1], &mut share).pop().expect("first request");
    first.authorized_native_proof().expect("the genuine model replays and authorizes");
    assert_eq!(share.work().replays_run, 1);

    // The second request of the group carries a canonical but NON-inductive
    // model: its clause check is another question, so the group's cached
    // answer for the genuine model must not be reused for it.
    let options = rows[1].request_config.solve_options(runner.solve_options());
    let (solved, solved_in) = NativeTypedChcPdrRunner::with_options(options.clone())
        .solve_full_verification_in(rows[1].obligation.clone(), Some(&mut share))
        .expect("the loop CHC solves");
    let invalid = rebuild_pdr_candidate_with_model(
        solved,
        &invalid_but_canonical_pdr_model_bytes(&rows[1].obligation),
    );
    let sealed = invalid.with_private_native_bundle_authority(
        &rows[1],
        &options,
        Some((&mut share, solved_in.expect("a PDR-route solve names its group"))),
    );
    assert!(sealed.authorized_native_proof().is_err(), "an invalid model never authorizes");
    let work = share.work();
    assert_eq!(work.replays_run, 2, "another model is replayed afresh: {work:?}");
    assert_eq!(work.replays_shared, 0, "{work:?}");
}

/// Re-seal `seal` for `target`: keep its request binding but recompute the
/// binding hash over `target`, as a minting bug that attached the wrong request
/// identity would. Only the request-binding check can refuse the result.
fn rebound_for(
    target: &TypedChcPdrFullVerification,
    seal: PrivateNativeProofSeal,
) -> PrivateNativeProofSeal {
    match seal {
        PrivateNativeProofSeal::ChcValidity(seal) => {
            let binding = private_chc_validity_binding(target, seal.derivation, &seal.request)
                .expect("the target is a CHC-validity candidate");
            PrivateNativeProofSeal::ChcValidity(Box::new(PrivateChcValiditySeal {
                binding,
                ..*seal
            }))
        }
        PrivateNativeProofSeal::PdrInvariant(seal) => {
            let seal = *seal;
            // The replay half that is per request (the obligation-set hash and the
            // typed-problem artifact, which names the obligation) is taken from the
            // target; the shared half (problem digest, invariant model) is equal.
            let candidate =
                trust_mc_core::validated_native_typed_chc_pdr_candidate(&target.verdict)
                    .expect("the target is a validated candidate");
            let typed_problem = candidate
                .proof
                .artifacts
                .iter()
                .find(|artifact| {
                    artifact.kind == trust_mc_core::FullVerificationArtifactKind::TypedChcProblem
                })
                .expect("the target carries its typed problem");
            let replay = PrivatePdrInvariantReplayBinding {
                exact_obligation_set_hash: target.cache_key.parts.obligation_set_hash.clone(),
                typed_problem_digest: typed_problem.digest.clone().expect("digest-backed"),
                ..seal.replay
            };
            let binding = private_pdr_invariant_binding(target, &replay, &seal.request)
                .expect("the target is a PDR-invariant candidate");
            PrivateNativeProofSeal::PdrInvariant(Box::new(PrivatePdrInvariantSeal {
                replay,
                request: seal.request,
                binding,
            }))
        }
    }
}

fn seal_request_mut(seal: &mut PrivateNativeProofSeal) -> &mut PrivateSealRequestBinding {
    match seal {
        PrivateNativeProofSeal::ChcValidity(seal) => &mut seal.request,
        PrivateNativeProofSeal::PdrInvariant(seal) => &mut seal.request,
    }
}

/// Re-hash `seal`'s binding over its own verification after its request half
/// was edited, so the edit is the only thing that is wrong with it.
fn rehash(
    verification: &TypedChcPdrFullVerification,
    seal: PrivateNativeProofSeal,
) -> PrivateNativeProofSeal {
    match seal {
        PrivateNativeProofSeal::ChcValidity(seal) => {
            let binding =
                private_chc_validity_binding(verification, seal.derivation, &seal.request)
                    .expect("candidate still validates");
            PrivateNativeProofSeal::ChcValidity(Box::new(PrivateChcValiditySeal {
                binding,
                ..*seal
            }))
        }
        PrivateNativeProofSeal::PdrInvariant(seal) => {
            let seal = *seal;
            let binding = private_pdr_invariant_binding(verification, &seal.replay, &seal.request)
                .expect("candidate still validates");
            PrivateNativeProofSeal::PdrInvariant(Box::new(PrivatePdrInvariantSeal {
                binding,
                ..seal
            }))
        }
    }
}

const ANOTHER_REQUEST: &str = "minted for another request or another normalized input";

fn assert_refused(verification: &TypedChcPdrFullVerification, what: &str) {
    match verification.authorized_native_proof() {
        Ok(_) => panic!("{what}: a misbound seal authorized"),
        Err(error) => assert!(error.to_string().contains(ANOTHER_REQUEST), "{what}: {error}"),
    }
}

/// Run the tampering checks on two requests answered by ONE shared solve.
fn assert_seals_do_not_transplant(
    mut a: TypedChcPdrFullVerification,
    mut b: TypedChcPdrFullVerification,
) {
    a.authorized_native_proof().expect("a's own seal authorizes a");
    b.authorized_native_proof().expect("b's own seal authorizes b");
    assert_eq!(
        a.cache_key.parts.normalized_input_hash, b.cache_key.parts.normalized_input_hash,
        "the two requests share one normalized input"
    );
    let seal_a = a.private_native_proof_seal.take().expect("a is sealed");
    let seal_b = b.private_native_proof_seal.take().expect("b is sealed");
    assert_ne!(seal_a, seal_b, "same digest, different requests: different seals");

    // 1. Swapped seals: each refused by name.
    a.private_native_proof_seal = Some(rebound_for(&a, clone_seal(&seal_b)));
    b.private_native_proof_seal = Some(clone_seal(&seal_a));
    assert_refused(&a, "b's seal re-hashed over a");
    assert_refused(&b, "a's seal moved verbatim to b");

    // 2. The shared digest of another normalized input, re-hashed so the digest
    //    is the only defect.
    let mut foreign_digest = clone_seal(&seal_a);
    seal_request_mut(&mut foreign_digest).shared_normalized_input_hash =
        trust_mc_core::EvidenceHash::sha256_bytes(b"another normalized CHC input");
    a.private_native_proof_seal = Some(rehash(&a, foreign_digest));
    assert_refused(&a, "a's seal bound to another digest");
    //    ... and minting refuses that digest outright.
    assert!(
        private_seal_request_binding(
            &a,
            trust_mc_core::EvidenceHash::sha256_bytes(b"another normalized CHC input"),
        )
        .is_none(),
        "a seal is never minted for a digest that is not the request's own"
    );

    // 3. Another request's identity under the right digest, re-hashed.
    let mut foreign_identity = clone_seal(&seal_a);
    seal_request_mut(&mut foreign_identity).request_identity_hash =
        clone_request(&seal_b).request_identity_hash;
    a.private_native_proof_seal = Some(rehash(&a, foreign_identity));
    assert_refused(&a, "a's seal carrying b's identity");

    // 4. The untouched seals still authorize their own requests.
    a.private_native_proof_seal = Some(seal_a);
    b.private_native_proof_seal = Some(seal_b);
    a.authorized_native_proof().expect("a's own seal still authorizes a");
    b.authorized_native_proof().expect("b's own seal still authorizes b");
}

/// Field-by-field copy of a seal. The seal types are deliberately not `Clone`
/// (authority is affine); only this test builds copies, to tamper with them.
fn clone_seal(seal: &PrivateNativeProofSeal) -> PrivateNativeProofSeal {
    match seal {
        PrivateNativeProofSeal::ChcValidity(seal) => {
            PrivateNativeProofSeal::ChcValidity(Box::new(PrivateChcValiditySeal {
                derivation: seal.derivation,
                request: clone_request_binding(&seal.request),
                binding: seal.binding.clone(),
            }))
        }
        PrivateNativeProofSeal::PdrInvariant(seal) => {
            PrivateNativeProofSeal::PdrInvariant(Box::new(PrivatePdrInvariantSeal {
                replay: PrivatePdrInvariantReplayBinding {
                    exact_obligation_set_hash: seal.replay.exact_obligation_set_hash.clone(),
                    fresh_problem_hash: seal.replay.fresh_problem_hash.clone(),
                    typed_problem_digest: seal.replay.typed_problem_digest.clone(),
                    invariant_model_digest: seal.replay.invariant_model_digest.clone(),
                    invariant_model_byte_len: seal.replay.invariant_model_byte_len,
                },
                request: clone_request_binding(&seal.request),
                binding: seal.binding.clone(),
            }))
        }
    }
}

fn clone_request(seal: &PrivateNativeProofSeal) -> PrivateSealRequestBinding {
    match seal {
        PrivateNativeProofSeal::ChcValidity(seal) => clone_request_binding(&seal.request),
        PrivateNativeProofSeal::PdrInvariant(seal) => clone_request_binding(&seal.request),
    }
}

fn clone_request_binding(request: &PrivateSealRequestBinding) -> PrivateSealRequestBinding {
    PrivateSealRequestBinding {
        shared_normalized_input_hash: request.shared_normalized_input_hash.clone(),
        request_identity_hash: request.request_identity_hash.clone(),
    }
}

#[test]
fn a_chc_validity_seal_never_transplants_between_requests_of_one_shared_solve() {
    let bundle = with_request_copies(compiler_style_safe_trust_ir_bundle(), 1);
    let (evidence, work) =
        runner().solve_bundle_native_proof_grade_with_work(&bundle).expect("bundle proves");
    assert_eq!(work.solves_run, 1, "both requests were answered by one solve: {work:?}");
    let mut rows = evidence.obligations.into_iter();
    let a = rows.next().expect("first proved request").verification;
    let b = rows.next().expect("second proved request").verification;
    assert_eq!(proof_kind(&a), trust_mc_core::ChcPdrProofKind::ChcValidity);
    assert_seals_do_not_transplant(a, b);
}

#[test]
fn a_pdr_invariant_seal_never_transplants_between_requests_of_one_shared_replay() {
    let rows = pdr_invariant_rows(2);
    let mut share = TypedChcSolveShare::new();
    let mut sealed = solve_and_seal(&rows, &mut share).into_iter();
    assert_eq!(share.work().replays_run, 1, "{:?}", share.work());
    let a = sealed.next().expect("first request");
    let b = sealed.next().expect("second request");
    assert_eq!(proof_kind(&a), trust_mc_core::ChcPdrProofKind::PdrInvariant);
    assert_seals_do_not_transplant(a, b);
}

/// One row of each of two DIFFERENT functions of `compiler_style_safe` x2 and
/// `counting_loop`, solved into one share: the CHC-validity row `a`, the
/// PDR-invariant row `b`, and `a`'s sibling on the same function.
struct TwoProblems {
    runner: NativeTrustIrChcPdrRunner,
    a: trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    a_sibling: trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
    b: trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
}

impl TwoProblems {
    fn new() -> Self {
        let runner = runner();
        let mut safe = runner
            .translate_obligations(&with_request_copies(compiler_style_safe_trust_ir_bundle(), 1))
            .expect("translates")
            .into_iter();
        let a = safe.next().expect("a");
        let a_sibling = safe.next().expect("a's sibling");
        let b = runner
            .translate_obligations(&counting_loop_bundle())
            .expect("translates")
            .into_iter()
            .next()
            .expect("b");
        Self { runner, a, a_sibling, b }
    }

    fn solve(
        &self,
        row: &trust_mc_trust_bmc::NativeTrustMcChcPdrObligation,
        share: &mut TypedChcSolveShare,
    ) -> (TypedChcPdrFullVerification, SolvedInGroup) {
        let (verification, solved_in) = NativeTypedChcPdrRunner::with_options(
            row.request_config.solve_options(self.runner.solve_options()),
        )
        .solve_full_verification_in(row.obligation.clone(), Some(share))
        .expect("solves");
        (verification, solved_in.expect("a PDR-route solve names its group"))
    }
}

/// The seal takes ONLY the group that answered the request's own solve: handed
/// another problem's group, it mints nothing, though that group holds a proof
/// of its own; handed its own group, it mints.
#[test]
fn a_seal_is_minted_only_from_the_group_that_answered_the_solve() {
    let fixture = TwoProblems::new();
    let mut share = TypedChcSolveShare::new();
    let (a, a_group) = fixture.solve(&fixture.a, &mut share);
    let (b, b_group) = fixture.solve(&fixture.b, &mut share);
    assert_ne!(a_group, b_group);

    // a's verification with b's group; b's verification with a's group.
    let a_wrong = a.clone().with_private_native_bundle_authority(
        &fixture.a,
        &fixture.a.request_config.solve_options(fixture.runner.solve_options()),
        Some((&mut share, b_group)),
    );
    assert!(a_wrong.authorized_native_proof().is_err(), "a sealed from b's group");
    let (_, a_group_again) = fixture.solve(&fixture.a, &mut share);
    let b_wrong = b.clone().with_private_native_bundle_authority(
        &fixture.b,
        &fixture.b.request_config.solve_options(fixture.runner.solve_options()),
        Some((&mut share, a_group_again)),
    );
    assert!(b_wrong.authorized_native_proof().is_err(), "b sealed from a's group");

    // Each with its own group: sealed.
    let a_sealed = a.with_private_native_bundle_authority(
        &fixture.a,
        &fixture.a.request_config.solve_options(fixture.runner.solve_options()),
        Some((&mut share, a_group)),
    );
    a_sealed.authorized_native_proof().expect("a sealed from its own group");
    let (b, b_group) = fixture.solve(&fixture.b, &mut share);
    let b_sealed = b.with_private_native_bundle_authority(
        &fixture.b,
        &fixture.b.request_config.solve_options(fixture.runner.solve_options()),
        Some((&mut share, b_group)),
    );
    b_sealed.authorized_native_proof().expect("b sealed from its own group");
}

/// A grouping defect — the group that answered the solve holds another
/// normalized input under the request's digest — leaves the request unsealed:
/// the seal-time membership check compares the BYTES of the fresh re-lowering.
#[test]
fn a_group_that_does_not_admit_the_fresh_relowering_mints_nothing() {
    let fixture = TwoProblems::new();
    for row in [&fixture.a, &fixture.b] {
        let mut share = TypedChcSolveShare::new();
        let (verification, solved_in) = fixture.solve(row, &mut share);
        let mut drifted = prepared_normalized(&row.obligation).normalized_input;
        drifted.push(' ');
        share.group_mut_for_test(&solved_in).corrupt_normalized_input_for_test(drifted);
        let sealed = verification.with_private_native_bundle_authority(
            row,
            &row.request_config.solve_options(fixture.runner.solve_options()),
            Some((&mut share, solved_in)),
        );
        assert!(
            sealed.private_native_proof_seal.is_none(),
            "{}: a group that does not admit the fresh re-lowering seals nothing",
            row.request_id
        );
        assert_eq!(share.work().replays_run, 0, "and runs no replay for it");
    }
}

/// A PDR-route CHC-validity seal stands on its group's acyclic `Safe` decision
/// and on nothing else; a group that holds no such decision seals nothing,
/// while the sibling solved and sealed from an intact group still is.
#[test]
fn a_chc_validity_seal_needs_its_groups_acyclic_safe_decision() {
    let fixture = TwoProblems::new();

    let mut share = TypedChcSolveShare::new();
    let (a, a_group) = fixture.solve(&fixture.a, &mut share);
    assert_eq!(proof_kind(&a), trust_mc_core::ChcPdrProofKind::ChcValidity);
    let (sibling, sibling_group) = fixture.solve(&fixture.a_sibling, &mut share);
    assert_eq!(a_group, sibling_group, "one group answers both");
    let sibling = sibling.with_private_native_bundle_authority(
        &fixture.a_sibling,
        &fixture.a_sibling.request_config.solve_options(fixture.runner.solve_options()),
        Some((&mut share, sibling_group)),
    );
    sibling.authorized_native_proof().expect("sealed from an intact group");

    share.group_mut_for_test(&a_group).forget_acyclic_decision_for_test();
    let a = a.with_private_native_bundle_authority(
        &fixture.a,
        &fixture.a.request_config.solve_options(fixture.runner.solve_options()),
        Some((&mut share, a_group)),
    );
    assert!(a.private_native_proof_seal.is_none(), "no Safe decision in the group, no seal");
}

/// A seal attempted under OTHER solve options than the solve's (another
/// timeout) borrows no replay and mints nothing: the group's timeout is part
/// of membership. (Adopted from the 8c review.)
#[test]
fn a_seal_under_other_options_never_borrows_a_replay() {
    let rows = pdr_invariant_rows(2);
    let runner = runner();
    let mut share = TypedChcSolveShare::new();
    let a = solve_and_seal_one(&runner, &rows[0], Some(&mut share));
    a.authorized_native_proof().expect("a authorizes");
    let options = rows[1].request_config.solve_options(runner.solve_options());
    let (b, solved_in) = NativeTypedChcPdrRunner::with_options(options.clone())
        .solve_full_verification_in(rows[1].obligation.clone(), Some(&mut share))
        .expect("b solves");
    let other = options.with_timeout(Duration::from_secs(9));
    let before = share.work();
    let b = b.with_private_native_bundle_authority(
        &rows[1],
        &other,
        Some((&mut share, solved_in.expect("a PDR-route solve names its group"))),
    );
    assert!(b.authorized_native_proof().is_err(), "other options never mint");
    assert_eq!(share.work(), before, "and touch no replay");
}

/// Per-request gates (the demotion counts this request's metadata carries)
/// still apply when the engine decision comes from an earlier member of the
/// group, in both member orders: a refuting function asked twice, one copy
/// carrying a fail-closed lowering site. (Adopted from the 8c review.)
#[test]
fn per_request_demotion_survives_a_shared_unsafe_decision() {
    let runner = runner();
    let bundle = with_request_copies(mixed_outcome_trust_ir_bundle(true), 1);
    let rows = runner.translate_obligations(&bundle).expect("translates");
    let mut by_vc: Vec<Vec<usize>> = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        match by_vc
            .iter_mut()
            .find(|group| Arc::ptr_eq(&rows[group[0]].obligation.vc, &row.obligation.vc))
        {
            Some(group) => group.push(index),
            None => by_vc.push(vec![index]),
        }
    }
    let mut refuted_then_demoted = 0;
    for demote_first in [true, false] {
        for group in by_vc.iter().filter(|group| group.len() >= 2) {
            let mut members = group.iter().map(|&index| rows[index].clone()).collect::<Vec<_>>();
            let target = if demote_first { 0 } else { members.len() - 1 };
            let Some(metadata) = members[target].obligation.native_metadata.as_mut() else {
                continue;
            };
            metadata.fail_closed_lowering_site_count = 1;
            let mut share = TypedChcSolveShare::new();
            let shared = members
                .iter()
                .map(|row| solve_and_seal_one(&runner, row, Some(&mut share)))
                .collect::<Vec<_>>();
            assert_eq!(share.work().solves_run, 1, "{:?}", share.work());
            let mut statuses = Vec::new();
            for (row, shared) in members.iter().zip(&shared) {
                let reference = solve_and_seal_one(&runner, row, None);
                assert_eq!(shared, &reference, "{}: shared equals per-request", row.request_id);
                statuses.push(std::mem::discriminant(&shared.outcome.status));
            }
            let refuted = shared.iter().any(|row| {
                matches!(row.outcome.status, trust_mc_core::ChcPdrSolveStatus::Refuted { .. })
            });
            if refuted && statuses.iter().collect::<std::collections::HashSet<_>>().len() == 2 {
                refuted_then_demoted += 1;
            }
        }
    }
    assert_eq!(refuted_then_demoted, 2, "the refuting function, demoted in both member orders");
}

/// Interleaved functions (A, B, A, B, ...) whose rows differ in metadata only
/// per-request gates read (inductive-hypothesis sites): every shared row equals
/// its per-request row. (Adopted from the 8c review.)
#[test]
fn interleaved_functions_with_differing_gates_equal_per_request() {
    let runner = runner();
    let bundle = with_request_copies(mixed_outcome_trust_ir_bundle(true), 3);
    let rows = runner.translate_obligations(&bundle).expect("translates");
    let mut share = TypedChcSolveShare::new();
    for (index, row) in rows.iter().enumerate() {
        let mut row = row.clone();
        if index % 3 == 1
            && let Some(metadata) = row.obligation.native_metadata.as_mut()
        {
            metadata.inductive_hypothesis_site_count = 2;
        }
        let shared = solve_and_seal_one(&runner, &row, Some(&mut share));
        let reference = solve_and_seal_one(&runner, &row, None);
        assert_eq!(shared, reference, "row {index}");
    }
    let work = share.work();
    assert_eq!(work.share_groups, 2, "{work:?}");
    assert_eq!(work.solves_shared, rows.len() as u64 - 2, "{work:?}");
}

/// A normalized input as the solver prepares it, for the membership tests.
fn prepared_normalized(
    obligation: &trust_mc_core::MirChcPdrObligation,
) -> NativeTypedChcPdrNormalizedInput {
    prepare_validated_typed_chc_pdr_input(obligation).expect("fixture prepares").normalized
}

fn join(
    share: &mut TypedChcSolveShare,
    obligation: &trust_mc_core::MirChcPdrObligation,
    normalized: &NativeTypedChcPdrNormalizedInput,
    timeout: Duration,
) -> SolvedInGroup {
    share.group(obligation, normalized, timeout).0
}

#[test]
fn requests_share_only_an_identical_problem() {
    let timeout = Duration::from_secs(8);
    let base = safe_cyclic_typed_chc_obligation("a", 10);
    let normalized = prepared_normalized(&base);
    assert_eq!(normalized.route, TypedChcPdrRoute::PdrProof);
    // Every lowering input is filed under ONE index key here, so each separation
    // below is the membership check's own, not the index's.
    for mut share in [TypedChcSolveShare::new(), TypedChcSolveShare::with_colliding_lowering_hash()]
    {
        let groups = |share: &TypedChcSolveShare| share.work().share_groups;
        let first = join(&mut share, &base, &normalized, timeout);
        assert_eq!(groups(&share), 1);

        // Another request on the SAME translated CHC (`Arc::ptr_eq`): shares.
        let mut sibling = base.clone();
        sibling.obligation_id = "b".to_owned();
        assert_eq!(join(&mut share, &sibling, &prepared_normalized(&sibling), timeout), first);

        // An equal CHC in another allocation (another function with the same
        // body): shares.
        let mut twin = base.clone();
        twin.vc = Arc::new((*base.vc).clone());
        assert!(!Arc::ptr_eq(&twin.vc, &base.vc));
        assert_eq!(join(&mut share, &twin, &prepared_normalized(&twin), timeout), first);
        assert_eq!(share.work().pdr_route_requests, 3);

        // The same clauses in another order: ay's normalized input sorts clauses,
        // so the digest and the bytes are equal, but positional evidence
        // (derivation clause indices) is not, so the request gets its own group.
        let mut reordered = base.clone();
        let mut vc = (*base.vc).clone();
        vc.rules.reverse();
        reordered.vc = Arc::new(vc);
        let reordered_normalized = prepared_normalized(&reordered);
        assert_eq!(reordered_normalized.normalized_input, normalized.normalized_input);
        join(&mut share, &reordered, &reordered_normalized, timeout);
        assert_eq!(share.work().distinct_normalized_inputs, 1);
        assert_eq!(groups(&share), 2, "same digest, split by clause order");

        // Another timeout: its own group.
        join(&mut share, &base, &normalized, timeout * 2);
        assert_eq!(groups(&share), 3, "another timeout is another engine question");

        // A forged digest collision — another problem's normalized input under
        // the group's digest — never joins: membership compares the bytes.
        let other = safe_cyclic_typed_chc_obligation("c", 11);
        let mut forged = prepared_normalized(&other);
        assert_ne!(forged.normalized_input, normalized.normalized_input);
        forged.normalized_input_hash = normalized.normalized_input_hash.clone();
        join(&mut share, &other, &forged, timeout);
        assert_eq!(share.work().distinct_normalized_inputs, 1);
        assert_eq!(groups(&share), 4, "a forged digest collision gets its own group");

        // Even on the SAME translated CHC, other normalized bytes under the
        // group's digest (a collision, or a lowering that did not reproduce its
        // own bytes) never join: the byte comparison stands on its own.
        let mut drifted = normalized.clone();
        drifted.normalized_input.push(' ');
        join(&mut share, &sibling, &drifted, timeout);
        assert_eq!(groups(&share), 5, "same CHC, other bytes under one digest: its own group");

        // The seal-time lookup takes the solve's group, counts no member,
        // creates no group — and refuses a fresh re-lowering the group does not
        // admit.
        let members = share.work().pdr_route_requests;
        let solved_in = join(&mut share, &sibling, &prepared_normalized(&sibling), timeout);
        let members = members + 1;
        assert!(
            share
                .group_for_seal(solved_in, &sibling, &prepared_normalized(&sibling), timeout)
                .is_some()
        );
        let solved_in = join(&mut share, &sibling, &prepared_normalized(&sibling), timeout);
        assert!(
            share.group_for_seal(solved_in, &reordered, &reordered_normalized, timeout).is_none()
        );
        let solved_in = join(&mut share, &sibling, &prepared_normalized(&sibling), timeout);
        assert!(share.group_for_seal(solved_in, &sibling, &drifted, timeout).is_none());
        assert_eq!(groups(&share), 5);
        assert_eq!(share.work().pdr_route_requests, members + 2);
    }
}

/// Finding a request's group examines ONE candidate however many groups share
/// its digest: the index separates clause orders by an order-sensitive hash of
/// the lowering input, and a later request on a known allocation goes straight
/// to its group.
#[test]
fn a_lookup_examines_one_candidate_group() {
    let timeout = Duration::from_secs(8);
    let base = safe_cyclic_typed_chc_obligation("a", 10);
    let normalized = prepared_normalized(&base);
    let rule_count = base.vc.rules.len();
    assert!(rule_count >= 3, "enough clauses for several orders");
    let mut share = TypedChcSolveShare::new();
    // One group per rotation of the clauses: same digest, other order.
    let rotations = (0..rule_count)
        .map(|shift| {
            let mut rotated = base.clone();
            let mut vc = (*base.vc).clone();
            vc.rules.rotate_left(shift);
            rotated.vc = Arc::new(vc);
            rotated
        })
        .collect::<Vec<_>>();
    for rotated in &rotations {
        join(&mut share, rotated, &prepared_normalized(rotated), timeout);
    }
    assert_eq!(share.work().share_groups, rule_count as u64);
    assert_eq!(share.work().distinct_normalized_inputs, 1);
    assert_eq!(normalized.normalized_input, prepared_normalized(&rotations[1]).normalized_input);

    // A request on a known allocation: one candidate.
    let before = share.admits_checked();
    join(&mut share, &rotations[rule_count - 1], &normalized, timeout);
    assert_eq!(share.admits_checked() - before, 1);

    // A twin of the last rotation in a new allocation: one candidate, though
    // every group shares its digest.
    let mut twin = rotations[rule_count - 1].clone();
    twin.vc = Arc::new((*twin.vc).clone());
    let before = share.admits_checked();
    join(&mut share, &twin, &normalized, timeout);
    assert_eq!(share.admits_checked() - before, 1);
    assert_eq!(share.work().share_groups, rule_count as u64, "the twin joined its group");
}

/// Both IC3 call sites in both requests reuse an absent candidate, whether the
/// first run expired or completed without a candidate. Primary PDR need not
/// return Unknown in the integration fixture to exercise this cache contract.
#[test]
fn absent_ic3_candidates_are_shared_between_call_sites_and_requests() {
    for expired in [false, true] {
        let mut engine = EngineSlots::default();
        let mut runs = 0;
        for _request in 0..2 {
            for _site in 0..2 {
                let candidate = engine.ic3_loop_lane(|| {
                    runs += 1;
                    if expired { None } else { Some(None) }
                });
                assert!(candidate.flatten().is_none());
            }
        }
        assert_eq!(runs, 1, "expired={expired}");
        let work = engine.work();
        assert_eq!(
            (work.engine_calls_run, work.engine_calls_shared),
            (1, 3),
            "expired={expired}: {work:?}"
        );
    }
}

/// The bounded-unroll witness search is keyed by its ladder and ceiling: a
/// search over another ladder never reads this one's depth or witness.
#[test]
fn the_bounded_unroll_search_is_keyed_by_its_ladder_and_ceiling() {
    let mut engine = EngineSlots::default();
    let ceiling = Duration::from_secs(1);
    let mut runs = 0;
    let mut search = |engine: &mut EngineSlots, ladder: &[u32], ceiling: Duration| {
        engine.bounded_unroll(ladder, ceiling, || {
            runs += 1;
            None
        })
    };
    assert!(search(&mut engine, &[1, 2], ceiling).is_none());
    assert!(search(&mut engine, &[1, 2], ceiling).is_none());
    assert!(search(&mut engine, &[1, 2, 4], ceiling).is_none());
    assert!(search(&mut engine, &[1, 2], ceiling * 2).is_none());
    assert_eq!(runs, 3, "one search per distinct ladder and ceiling");
    let work = engine.work();
    assert_eq!((work.engine_calls_run, work.engine_calls_shared), (3, 1), "{work:?}");
}

/// A row with nothing to seal (a refutation, an undecided row) never pays for
/// the seal's O(function) fresh re-lowering; a proved row pays for exactly one.
#[test]
fn only_a_candidate_row_pays_for_the_seal_time_relowering() {
    let runner = runner();
    let bundle = mixed_outcome_trust_ir_bundle(true);
    let rows = runner.translate_obligations(&bundle).expect("translates");
    let mut seen = BTreeSet::new();
    for row in &rows {
        let verification = NativeTypedChcPdrRunner::with_options(
            row.request_config.solve_options(runner.solve_options()),
        )
        .solve_full_verification(row.obligation.clone())
        .expect("solves");
        let candidate =
            trust_mc_core::validated_native_typed_chc_pdr_candidate(&verification.verdict).is_ok();
        let before = typed_chc_ay::lowerings_on_this_thread();
        let sealed = verification.with_private_native_bundle_authority(
            row,
            &row.request_config.solve_options(runner.solve_options()),
            None,
        );
        let lowerings = typed_chc_ay::lowerings_on_this_thread() - before;
        if candidate {
            assert_eq!(lowerings, 1, "{}: one fresh re-lowering", row.request_id);
            sealed.authorized_native_proof().expect("the candidate seals");
        } else {
            assert_eq!(lowerings, 0, "{}: nothing to seal, nothing lowered", row.request_id);
        }
        seen.insert(candidate);
    }
    assert_eq!(seen.len(), 2, "both kinds of row were exercised");
}

/// Below the gate: every function of the checked-in `-Ztrust-dump` modules,
/// asked three times (three obligations on one translated CHC, as a bundle asks),
/// solved with a share and without. The verifications must be equal and the
/// engine must run once per distinct normalized input.
#[test]
fn shared_solve_equals_per_request_solve_on_the_dumped_modules() {
    let options = trust_mc_core::ChcPdrSolveOptions::default()
        .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
        .with_timeout(Duration::from_secs(8));
    let modules = [
        fixture_bundle(include_str!(
            "../../../../trust-mc-trust-bmc/tests/fixtures/recursive_requires_native_bundle.json"
        ))
        .module,
        fixture_bundle(include_str!(
            "../../../../trust-mc-trust-bmc/tests/fixtures/stale_struct_native_bundle.json"
        ))
        .module,
        fixture_bundle(include_str!(
            "../../../../trust-mc-trust-bmc/tests/fixtures/format_args_insert_element_native_bundle.json"
        ))
        .module,
    ];
    let mut share = TypedChcSolveShare::new();
    let mut digests = BTreeSet::new();
    let mut solved = 0;
    for module in &modules {
        for function in &module.functions {
            if function.blocks.is_empty() {
                continue;
            }
            let Some(output) = trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output(
                module,
                function.id,
                &trust_mc_trust_bmc::TranslateOptions::default(),
            ) else {
                continue;
            };
            let vc = Arc::new(output.vc);
            let obligations = (0..3)
                .map(|row| {
                    trust_mc_core::MirChcPdrObligation::new(
                        format!("dumped-{}-{}-{row}", module.name, function.id.index()),
                        function.name.clone(),
                        trust_mc_core::MirObligationKind::Assertion,
                        Arc::clone(&vc),
                    )
                })
                .collect::<Vec<_>>();
            if obligations[0].validate().is_err() {
                continue;
            }
            if let Ok(normalized) = normalized_typed_chc_pdr_input(&obligations[0])
                && normalized.route == TypedChcPdrRoute::PdrProof
            {
                digests.insert(normalized.normalized_input_hash.value);
            }
            for obligation in obligations {
                let request = || {
                    trust_mc_core::ChcPdrSolveRequest::new(obligation.clone())
                        .with_options(options.clone())
                };
                let shared = solve_typed_chc_pdr_full_verification_in(request(), Some(&mut share))
                    .map(|(verification, _)| verification);
                let per_request = solve_typed_chc_pdr_full_verification(request());
                assert_eq!(shared, per_request, "{}::{}", module.name, function.name);
                solved += 1;
            }
        }
    }
    let work = share.work();
    eprintln!("[8c dumped modules] solved={solved} {work:?}");
    assert!(solved > 0);
    assert_eq!(work.distinct_normalized_inputs, digests.len() as u64, "{work:?}");
    assert_eq!(work.solves_run, digests.len() as u64, "one solve per digest: {work:?}");
    assert_eq!(work.solves_shared, 2 * digests.len() as u64, "{work:?}");
}

/// Whether a not-proved `reason` is a native watchdog's expiry
/// ([`WALL_CLOCK_CEILING`]) rather than a reason the solve reached.
fn ran_out_of_the_wall_clock(reason: &str) -> bool {
    reason.ends_with(WALL_CLOCK_CEILING)
}

/// One request's row in a bundle result, by channel.
#[derive(Debug)]
enum Row<'a> {
    Proved(&'a NativeTrustIrChcPdrEvidence),
    NotProved(&'a NativeTrustIrChcPdrNotProved),
    Refuted(&'a NativeTrustIrChcPdrRefuted),
}

fn rows_by_request(
    evidence: &NativeTrustIrChcPdrBundleEvidence,
) -> BTreeMap<(u32, String), Row<'_>> {
    let mut rows = BTreeMap::new();
    for row in &evidence.obligations {
        rows.insert(request_key(&row.translated), Row::Proved(row));
    }
    for row in &evidence.not_proved {
        rows.insert(request_key(&row.translated), Row::NotProved(row));
    }
    for row in &evidence.refuted {
        rows.insert(request_key(&row.translated), Row::Refuted(row));
    }
    rows
}

/// The differential over randomly generated programs: the TMC-1 generator
/// families (straight-line, nested, loops, cells, summarized callees, joins,
/// vectors, borrowed cells, tuples, bools, ...), each program wrapped in a
/// compiler-shaped bundle and asked three times, solved per request (the
/// oracle) and with a share.
///
/// A row decided in both runs must be EQUAL (a proved row's verification
/// including the private seal, its transport; a refutation; a not-proved
/// reason). The one difference tolerated is a watchdog firing on a loaded
/// machine, and it is counted, at most one row in ten: a row one run decided
/// and the other left `not_proved`, or two `not_proved` rows of which one
/// names the wall-clock ceiling it ran out of ([`WALL_CLOCK_CEILING`]). An
/// expiry is not a reason, so it is not a different one: the run it stopped
/// never reached the reason the other run gave. A row proved by one run and
/// refuted by the other fails, as do two different reasons neither run's clock
/// chose, and any authority the oracle did not also grant.
#[test]
fn shared_rows_equal_per_request_rows_on_random_programs() {
    let runner = NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default().with_timeout(Duration::from_secs(6)),
    );
    let mut compared = 0_u64;
    let mut proved = 0_u64;
    let mut refuted = 0_u64;
    let mut refused = 0_u64;
    let mut timing_flips = Vec::new();
    let mut failures = Vec::new();
    for (label, bundle) in crate::native::array_gate_differential::sample_program_bundles(4) {
        let bundle = with_request_copies(bundle, 2);
        let (shared, per_request, share) = solve_both_ways(&runner, &bundle, None);
        let (shared, per_request) = match (shared, per_request) {
            (Ok(shared), Ok(per_request)) => (shared, per_request),
            (Err(shared), Err(per_request)) => {
                if shared != per_request {
                    failures
                        .push(format!("{label}: bundle errors differ: {shared} / {per_request}"));
                }
                refused += 1;
                continue;
            }
            (shared, per_request) => {
                failures.push(format!(
                    "{label}: one run failed the bundle: shared={:?} per_request={:?}",
                    shared.err(),
                    per_request.err()
                ));
                continue;
            }
        };
        let work = share.work();
        if work.solves_run != work.distinct_normalized_inputs {
            failures.push(format!("{label}: not one solve per digest: {work:?}"));
        }
        let shared_rows = rows_by_request(&shared);
        let reference_rows = rows_by_request(&per_request);
        if shared_rows.keys().ne(reference_rows.keys()) {
            failures.push(format!("{label}: the two runs answer different requests"));
            continue;
        }
        for (key, shared_row) in &shared_rows {
            compared += 1;
            match (shared_row, &reference_rows[key]) {
                (Row::Proved(shared), Row::Proved(reference)) => {
                    proved += 1;
                    if shared.verification != reference.verification
                        || shared.transport != reference.transport
                    {
                        failures.push(format!("{label} {key:?}: proved rows differ"));
                    }
                    if shared.verification.authorized_native_proof().is_err() {
                        failures.push(format!("{label} {key:?}: shared proof lost authority"));
                    }
                }
                (Row::Refuted(shared), Row::Refuted(reference)) => {
                    refuted += 1;
                    if shared.verification != reference.verification {
                        failures.push(format!("{label} {key:?}: refutations differ"));
                    }
                }
                (Row::NotProved(shared), Row::NotProved(reference)) => {
                    if shared.reason != reference.reason {
                        if ran_out_of_the_wall_clock(&shared.reason)
                            || ran_out_of_the_wall_clock(&reference.reason)
                        {
                            timing_flips.push(format!(
                                "{label} {key:?}: not proved: {} / {}",
                                shared.reason, reference.reason
                            ));
                        } else {
                            failures.push(format!(
                                "{label} {key:?}: not-proved reasons differ: {} / {}",
                                shared.reason, reference.reason
                            ));
                        }
                    }
                }
                (Row::NotProved(_), decided) | (decided, Row::NotProved(_)) => {
                    timing_flips.push(format!("{label} {key:?}: {decided:?}"));
                }
                (shared, reference) => failures.push(format!(
                    "{label} {key:?}: DECIDED DIFFERENTLY: shared {shared:?} / per-request \
                     {reference:?}"
                )),
            }
        }
    }
    eprintln!(
        "[8c random] compared={compared} proved={proved} refuted={refuted} \
         bundles_refused_by_the_gate={refused} timing_flips={}",
        timing_flips.len()
    );
    for flip in &timing_flips {
        eprintln!("[8c random] timing flip (not a failure): {flip}");
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    // Not vacuous: proofs are compared, seal included, and most rows agree.
    assert!(proved >= 10, "proved={proved}");
    assert!(
        timing_flips.len() as u64 * 10 <= compared,
        "{} flips of {compared}",
        timing_flips.len()
    );
}

/// The ever-init cleanup-chain shape (`trust-mc-driver/tests/
/// chc_liveness_verdict_parity.rs`, after trust-mc-trust-bmc's liveness tests):
/// per local a drop flag set, cleared and re-tested by a cleanup chain that
/// every unwind choice can enter, and an overflow-checked running sum. Its CHC
/// grows as N^2 (every drop flag is live along the cleanup chain), and the
/// compiler asks 6N+2 questions of it.
fn ever_init(n: usize) -> (trust_ir::Module, trust_ir::value::FuncId) {
    use trust_ir::inst::{ICmpOp, OverflowOp};
    use trust_ir::ty::Ty;
    use trust_ir_build::ModuleBuilder;
    let mut mb = ModuleBuilder::new("ever_init");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("many_locals", ft);
    let entry = fb.create_block();
    let make: Vec<_> = (0..n).map(|_| fb.create_block()).collect();
    let add: Vec<_> = (0..n).map(|_| fb.create_block()).collect();
    let exit = fb.create_block();
    let cleanup: Vec<_> = (0..=n).map(|_| fb.create_block()).collect();
    let drop: Vec<_> = (0..=n).map(|_| fb.create_block()).collect();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let sum = fb.alloca(Ty::U64);
    let zero = fb.iconst(Ty::U64, 0);
    fb.store(Ty::U64, sum, zero);
    let mut flags = Vec::with_capacity(n);
    for _ in 0..n {
        let flag = fb.alloca(Ty::Bool);
        let no = fb.bool_const(false);
        fb.store(Ty::Bool, flag, no);
        flags.push(flag);
    }
    fb.br(make[0], vec![]);
    for i in 0..n {
        fb.switch_to_block(make[i]);
        let yes = fb.bool_const(true);
        fb.store(Ty::Bool, flags[i], yes);
        let unwinds = fb.undef(Ty::Bool);
        fb.condbr(unwinds, cleanup[i], vec![], add[i], vec![]);
        fb.switch_to_block(add[i]);
        let before = fb.load(Ty::U64, sum);
        let one = fb.iconst(Ty::U64, 1);
        let (total, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, before, one);
        let no = fb.bool_const(false);
        let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
        fb.assert(ok);
        fb.store(Ty::U64, sum, total);
        let no = fb.bool_const(false);
        fb.store(Ty::Bool, flags[i], no);
        let drop_unwinds = fb.undef(Ty::Bool);
        let next = if i + 1 < n { make[i + 1] } else { exit };
        fb.condbr(drop_unwinds, cleanup[i + 1], vec![], next, vec![]);
    }
    fb.switch_to_block(exit);
    let result = fb.load(Ty::U64, sum);
    fb.ret(vec![result]);
    fb.switch_to_block(cleanup[0]);
    let unwound = fb.undef(Ty::U64);
    fb.ret(vec![unwound]);
    for i in 1..=n {
        fb.switch_to_block(cleanup[i]);
        let live = fb.load(Ty::Bool, flags[i - 1]);
        let no = fb.bool_const(false);
        let dead = fb.icmp(ICmpOp::Eq, Ty::Bool, live, no);
        fb.condbr(dead, cleanup[i - 1], vec![], drop[i], vec![]);
        fb.switch_to_block(drop[i]);
        let dropped = fb.bool_const(true);
        fb.assert(dropped);
        fb.br(cleanup[i - 1], vec![]);
    }
    fb.switch_to_block(drop[0]);
    fb.unreachable();
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// Retained evidence bytes of one verification: every artifact's bytes and the
/// normalized input its candidate obligation carries.
fn retained_evidence_bytes(verification: &TypedChcPdrFullVerification) -> u64 {
    match trust_mc_core::validated_native_typed_chc_pdr_candidate(&verification.verdict) {
        Ok(candidate) => {
            candidate
                .proof
                .artifacts
                .iter()
                .map(|artifact| artifact.byte_len.unwrap_or(0))
                .sum::<u64>()
                + candidate.proof.obligation.normalized_input.len() as u64
        }
        Err(_) => 0,
    }
}

/// Measurement of record for the residual per-row cost (DECISION_QUEUE 8f;
/// ignored: a measurement, not a check). The ever-init function at N locals,
/// asked its 6N+2 questions as compiler-shaped rows sharing ONE `ChcVc`, solved
/// and sealed through one share, as the bundle loop does, with a 120 s budget so
/// every row proves and the seal path is measured too. Prints the engine time
/// (the first row's solve), the per-row time of every LATER row (solve, then
/// seal: all of it outside the engine), the O(function) parts a row pays timed
/// alone (one lowering, one obligation-set identity), and the evidence bytes the
/// rows retain. Set `TRUST_MC_8C_EVER_INIT_N` to measure one N alone (for
/// `/usr/bin/time -l`), and `TRUST_MC_8E_ENCODING=per_block` to measure the
/// per-block encoding instead of the large-block query the production
/// translation makes of this acyclic function (design step 8e).
///
/// ```text
/// targo --unverified test -p trust-mc-driver --lib -- --ignored --nocapture measure_8f
/// ```
#[test]
#[ignore = "measurement of record: the residual per-row O(function) cost"]
fn measure_8f_residual_per_row_cost_on_ever_init() {
    let only = std::env::var("TRUST_MC_8C_EVER_INIT_N").ok().and_then(|n| n.parse::<usize>().ok());
    let per_block = std::env::var("TRUST_MC_8E_ENCODING").is_ok_and(|value| value == "per_block");
    let runner = NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default()
            .with_engine(trust_mc_core::ChcPdrEngine::Pdr)
            .with_timeout(Duration::from_secs(120)),
    );
    for n in [1_usize, 2, 4, 8, 16] {
        if only.is_some_and(|only| only != n) {
            continue;
        }
        let (module, function) = ever_init(n);
        let options = trust_mc_trust_bmc::TranslateOptions::default();
        let output = if per_block {
            trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output_per_block(
                &module, function, &options,
            )
        } else {
            trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output(
                &module, function, &options,
            )
        }
        .expect("ever-init translates");
        let vc = Arc::new(output.vc);
        let row_count = 6 * n as u32 + 2;
        let rows = rows_on_one_vc(row_count, Arc::clone(&vc));
        let normalized = prepared_normalized(&rows[0].obligation);

        // The O(function)-per-row parts, timed alone on one row.
        let started = std::time::Instant::now();
        let _ = prepare_validated_typed_chc_pdr_input(&rows[0].obligation).expect("prepares");
        let lowering_us = started.elapsed().as_micros();
        let started = std::time::Instant::now();
        let identity = typed_obligation_set_bytes(&rows[0].obligation, TypedChcPdrRoute::PdrProof);
        let _ = trust_mc_core::EvidenceHash::sha256_bytes(&identity);
        let identity_us = started.elapsed().as_micros();

        let mut share = TypedChcSolveShare::new();
        let mut engine_us = 0;
        let mut later_solve_us = 0;
        let mut seal_us = 0;
        let mut retained = 0;
        let mut proved = 0;
        for (index, row) in rows.iter().enumerate() {
            let solve_started = std::time::Instant::now();
            let options = row.request_config.solve_options(runner.solve_options());
            let (verification, solved_in) = NativeTypedChcPdrRunner::with_options(options.clone())
                .solve_full_verification_in(row.obligation.clone(), Some(&mut share))
                .expect("solves");
            let solve = solve_started.elapsed().as_micros();
            if index == 0 {
                engine_us = solve;
            } else {
                later_solve_us += solve;
            }
            let seal_started = std::time::Instant::now();
            let sealed = verification.with_private_native_bundle_authority(
                row,
                &options,
                solved_in.map(|solved_in| (&mut share, solved_in)),
            );
            proved += u64::from(sealed.authorized_native_proof().is_ok());
            seal_us += seal_started.elapsed().as_micros();
            retained += retained_evidence_bytes(&sealed);
        }
        let later = u128::from(row_count - 1);
        eprintln!(
            "[8f measure] ever_init N={n} per_block={per_block} rows={row_count} normalized_input_bytes={} \
             obligation_set_bytes={} proved={proved} engine_ms={} \
             later_row_solve_us={} row_seal_us={} one_lowering_us={lowering_us} \
             one_identity_us={identity_us} retained_evidence_bytes={retained} \
             retained_per_row={} {:?}",
            normalized.normalized_input.len(),
            identity.len(),
            engine_us / 1000,
            later_solve_us / later.max(1),
            seal_us / u128::from(row_count),
            retained / u64::from(row_count),
            share.work()
        );
    }
}

/// Measurement of record for design step 8c (ignored: it runs the per-request
/// reference, whose cost is the point). For each bundle and request count it
/// solves the bundle with the share and, unless
/// `TRUST_MC_8C_MEASURE_MODE=shared`, without it (`=per_request` runs only the
/// reference), and prints the wall time and the engine counters, so each mode
/// can also run alone under `/usr/bin/time -l` for its peak RSS:
///
/// ```text
/// targo --unverified test -p trust-mc-driver --lib -- --ignored --nocapture measure_8c
/// ```
#[test]
#[ignore = "measurement of record: runs the per-request reference on purpose"]
fn measure_8c_solve_and_replay_cost() {
    let mode = std::env::var("TRUST_MC_8C_MEASURE_MODE").unwrap_or_default();
    let runner = runner();
    let cases: [(&str, fn() -> trust_ir::NativeVerificationBundle, &[u32]); 3] = [
        ("compiler_style_safe", compiler_style_safe_trust_ir_bundle, &[1, 16, 64, 256]),
        ("counting_loop", counting_loop_bundle, &[1, 16, 64]),
        ("loop_overflow", loop_overflow_trust_ir_bundle, &[1, 2, 4]),
    ];
    for (name, build, counts) in cases {
        for &requests in counts {
            let bundle = with_request_copies(build(), requests - 1);
            if mode != "per_request" {
                let started = std::time::Instant::now();
                let mut share = TypedChcSolveShare::new();
                let shared = runner
                    .solve_bundle_native_proof_grade_inner(&bundle, None, None, Some(&mut share))
                    .expect("bundle solves");
                eprintln!(
                    "[8c measure] {name} requests={requests} mode=shared ms={} proved={} \
                     refuted={} not_proved={} {:?}",
                    started.elapsed().as_millis(),
                    shared.obligations.len(),
                    shared.refuted.len(),
                    shared.not_proved.len(),
                    share.work()
                );
            }
            if mode != "shared" {
                let started = std::time::Instant::now();
                let per_request = runner
                    .solve_bundle_native_proof_grade_inner(&bundle, None, None, None)
                    .expect("bundle solves");
                eprintln!(
                    "[8c measure] {name} requests={requests} mode=per_request ms={} proved={} \
                     refuted={} not_proved={} engine_pipelines={requests}",
                    started.elapsed().as_millis(),
                    per_request.obligations.len(),
                    per_request.refuted.len(),
                    per_request.not_proved.len()
                );
            }
        }
    }
}
