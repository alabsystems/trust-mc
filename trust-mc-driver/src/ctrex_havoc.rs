// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The havoc-read gate on a `Genuine` CHC counterexample
//! (fix/chc-false-certificates).
//!
//! [`crate::ctrex_classify::classify_ctrex`] calls a counterexample `Genuine`
//! when the compiler booked no approximation for the harness. Two encoding
//! defects free a value without booking one — a clause reading a state
//! variable its body does not bind, and a read of memory no clause writes —
//! and each certified a counterexample on a program Kani proves
//! (`trust_mc_driver::certify_error_free_of_havoc` has the shapes). This gate
//! keeps `Genuine` only when some violated check is derivable without such a
//! read; otherwise the counterexample is an over-approximation, printed and
//! scored as one, never a certified bug.

use std::path::Path;

use crate::property_model::{CheckStatus, Property};

/// What the gate decided for one `Genuine` counterexample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum HavocGate {
    /// Not a CHC artifact (the BMC lane has its own certification).
    NotApplicable,
    /// Some violated check reads no undefined value; `Some` carries the replay
    /// summary when that took the cut system.
    Certified(Option<String>),
    /// Every violated check reads an undefined value: the refusal.
    Refused(String),
}

/// Name of the aggregate error relation every `error_pN` feeds.
const AGGREGATE_ERROR: &str = "error";

/// The error relations to certify: the `error_pN` of every violated check the
/// solver attributed, or the aggregate `error` when no violated check names
/// one — the unattributed `chc.0` report, or no VC artifact to map ids.
///
/// An unattributed failure carries property id 0, which is NOT the id of the
/// check that failed: looking it up named `error_p0`, usually an eliminated
/// memory-safety check, and refused real bugs over it ("error_p0: not
/// declared"), or certified `Clean` from a relation nothing showed violated
/// (fix/chc-false-certificates review, probes `g1`/`g2`/`g6`/`g7`). The
/// aggregate's backward cone holds every check, so a certificate for it is a
/// certificate for whichever check the solver's model violates.
fn violated_relations(smt_binary: &Path, results: &[Property]) -> Vec<String> {
    let vc_path = crate::ay_parse::vc_artifact::vc_artifact_path_for_smt(smt_binary);
    let mut relations: Vec<String> =
        match crate::ay_parse::vc_artifact::load_approximation_evidence(&vc_path) {
            Some(ev) => results
                .iter()
                .filter(|p| p.status == CheckStatus::Failure && !p.is_unattributed_chc_check())
                .filter_map(|p| ev.relation_by_id.get(&p.property_id.id).cloned())
                .collect(),
            None => Vec::new(),
        };
    if relations.is_empty() {
        relations.push(AGGREGATE_ERROR.to_string());
    }
    relations.sort();
    relations.dedup();
    relations
}

/// Decide the gate for a counterexample already classified `Genuine`, from the
/// harness's emitted system `smt_binary` and its per-check `results`. `strict`
/// for a `should_panic` harness, whose verdict the certificate decides.
pub(crate) fn havoc_gate(smt_binary: &Path, results: &[Property], strict: bool) -> HavocGate {
    let text = match std::fs::read_to_string(smt_binary) {
        Ok(text) => text,
        Err(error) => {
            return HavocGate::Refused(format!("cannot read {}: {error}", smt_binary.display()));
        }
    };
    if !text.contains("(set-logic HORN)") {
        return HavocGate::NotApplicable;
    }
    let relations = violated_relations(smt_binary, results);
    let targets: Vec<&str> = relations.iter().map(String::as_str).collect();
    match trust_mc_driver::certify_error_free_of_havoc(&text, &targets, strict) {
        Ok(trust_mc_driver::HavocCertificate::Clean) => HavocGate::Certified(None),
        Ok(
            trust_mc_driver::HavocCertificate::Independent(summary)
            | trust_mc_driver::HavocCertificate::Replayed(summary),
        ) => HavocGate::Certified(Some(summary)),
        Err(reason) => HavocGate::Refused(reason),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A fresh directory under the system temp dir for one test.
    fn scratch(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "trust-mc-ctrex-havoc-{tag}-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create scratch dir");
        dir
    }

    #[test]
    fn a_bmc_artifact_is_not_gated() {
        let dir = scratch("bmc");
        let smt = dir.join("h.symtab.smt2");
        std::fs::write(&smt, "(set-logic QF_BV)\n(assert false)\n(check-sat)\n").expect("write");
        assert_eq!(havoc_gate(&smt, &[], false), HavocGate::NotApplicable);
    }

    #[test]
    fn a_missing_artifact_is_refused() {
        let dir = scratch("absent");
        let smt = dir.join("absent.symtab.smt2");
        assert!(matches!(havoc_gate(&smt, &[], false), HavocGate::Refused(_)));
    }

    const UNATTRIBUTED_SMT: &str = r#"(set-logic HORN)
(declare-var x (_ BitVec 8))
(declare-var _h_mem_u8 (Array (_ BitVec 64) (_ BitVec 8)))
(declare-rel bb0 ((_ BitVec 8) (Array (_ BitVec 64) (_ BitVec 8))))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> (= x #x01) (bb0 x _h_mem_u8)))
(rule (=> error_p0 error))
(rule (=> (and (bb0 x _h_mem_u8) (= x #x05)) error_p0))
(rule (=> (and (bb0 x _h_mem_u8) (not (= (select _h_mem_u8 #x0000000000000000) #x01))) error))
(query error)
"#;

    const UNATTRIBUTED_VC: &str = r#"{
  "version": {"major": 0, "minor": 1, "patch": 0},
  "mode": "chc",
  "harness": {"mangled_name": "h", "pretty_name": "h"},
  "properties": [
    {"id": {"id": 0, "description": null}, "kind": "memory_safety", "smt_var": "error_p0"}
  ]
}"#;

    fn chc_failure(class: &'static str, id: u32, function: Option<&str>) -> Property {
        Property {
            description: "".into(),
            property_id: crate::property_model::PropertyId {
                fn_name: function.map(str::to_string),
                class: class.into(),
                id,
            },
            source_location: crate::property_model::RawSourceLocation {
                column: None,
                file: function.map(|_| "h.rs".to_string()),
                function: function.map(str::to_string),
                line: None,
            },
            status: CheckStatus::Failure,
            trace: None,
        }
    }

    /// An unattributed failure (`chc.0`) names no check: its id 0 is property
    /// 0's, whose `error_p0` here is clean-coned and never violated. The gate
    /// must certify the aggregate `error`, whose only derivation depends on
    /// the unwritten memory, and refuse. Looking up id 0 certified `Clean`.
    #[test]
    fn an_unattributed_counterexample_is_gated_on_the_aggregate() {
        let dir = scratch("unattributed");
        let smt = dir.join("h.symtab.smt2");
        std::fs::write(&smt, UNATTRIBUTED_SMT).expect("write smt");
        std::fs::write(dir.join("h.symtab.vc.json"), UNATTRIBUTED_VC).expect("write vc");
        let unattributed = chc_failure("chc", 0, None);
        assert!(unattributed.is_unattributed_chc_check());
        assert_eq!(violated_relations(&smt, &[unattributed.clone()]), vec!["error".to_string()]);
        match havoc_gate(&smt, &[unattributed], false) {
            HavocGate::Refused(reason) => assert!(reason.contains("error reads"), "{reason}"),
            other => panic!("expected a refusal, got {other:?}"),
        }
        // An ATTRIBUTED failure of property 0 is gated on its own relation.
        let attributed = chc_failure("assertion", 0, Some("h"));
        assert_eq!(violated_relations(&smt, &[attributed]), vec!["error_p0".to_string()]);
    }

    /// A HORN system that reads memory no clause writes, with no VC artifact:
    /// the aggregate `error` is the target, and its only derivation depends on
    /// the unwritten cell, so the gate refuses.
    #[test]
    fn an_unwritten_memory_read_is_refused() {
        let dir = scratch("unwritten");
        let smt = dir.join("h.symtab.smt2");
        std::fs::write(
            &smt,
            r#"(set-logic HORN)
(declare-var r (_ BitVec 64))
(declare-var _h_mem_u8 (Array (_ BitVec 64) (_ BitVec 8)))
(declare-rel bb0 ((_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
(declare-rel error ())
(declare-rel error_p0 ())
(rule (=> true (bb0 r _h_mem_u8)))
(rule (=> error_p0 error))
(rule (=> (and (bb0 r _h_mem_u8) (not (= (select _h_mem_u8 r) #x01))) error_p0))
(query error)
"#,
        )
        .expect("write");
        match havoc_gate(&smt, &[], false) {
            HavocGate::Refused(reason) => assert!(reason.contains("error reads"), "{reason}"),
            other => panic!("expected a refusal, got {other:?}"),
        }
    }
}
