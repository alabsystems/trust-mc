// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Engine verdicts over the bulk-memory model (`MemCopy`, `MemSet`) of stack
//! cells (`trust-mc-trust-bmc/src/translate_chc_bulk_memory.rs`).
//!
//! A whole-object copy or fill reaches the native typed CHC/PDR solver as an
//! SMT-array assignment or one `const_array` per leaf, and a symbolic byte count
//! as one comparison per object size — never a term per byte or per lane. These
//! tests ask the ENGINE for verdicts, at lengths from 4 to 4097, including an
//! array value carried across a block boundary in a relation column, and pin
//! that a lane run (which needs an array-range write the CHC path cannot
//! express) is never proved.

#![cfg(all(feature = "native-typed-chc-pdr", feature = "native-trust-ir-bundle"))]

use std::time::Duration;

use trust_ir::inst::ICmpOp;
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir::{Constant, Module};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::{
    ChcPdrSolveOptions, ChcPdrSolveRequest, FullVerificationVerdict, MirChcPdrObligation,
    MirObligationKind,
};
use trust_mc_trust_bmc::{
    TranslateOptions, TrustIrChcUnsupportedReason, trust_ir_function_to_chc_translation_output,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Refuted,
    Unknown,
}

/// The engine's own verdict, and the translator's fail-closed reasons.
fn solve(module: &Module) -> (Verdict, Vec<TrustIrChcUnsupportedReason>) {
    let output = trust_ir_function_to_chc_translation_output(
        module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("fixture function translates");
    let reasons = output.diagnostics.iter().map(|diagnostic| diagnostic.reason).collect();
    let obligation = MirChcPdrObligation::new(
        "bulk-memory".to_owned(),
        "f".to_owned(),
        MirObligationKind::Assertion,
        output.vc,
    );
    if obligation.validate().is_err() {
        return (Verdict::Unknown, reasons);
    }
    let request = ChcPdrSolveRequest::new(obligation)
        .with_options(ChcPdrSolveOptions::default().with_timeout(Duration::from_secs(20)));
    let verdict = match trust_mc_driver::solve_typed_chc_pdr_full_verification(request) {
        Ok(solved) => match solved.verdict {
            FullVerificationVerdict::Proved { .. } => Verdict::Proved,
            FullVerificationVerdict::Failed { .. } => Verdict::Refuted,
            _ => Verdict::Unknown,
        },
        Err(_) => Verdict::Unknown,
    };
    (verdict, reasons)
}

const LENGTHS: [u64; 4] = [4, 5, 257, 4097];

#[derive(Clone, Copy, Debug)]
enum Shape {
    /// `d = [7u8; n]; s = [9u8; n]; memcpy(d, s, n); assert(d[1] == want)`.
    WholeCopy,
    /// The same with the count a parameter `m` and `assume(m == n)`.
    SymbolicCopy,
    /// `d = [7u32; n]; memset(d, 0xAB, 4n); assert(d[2] == want)`.
    WholeFill,
    /// `WholeCopy`, then `v = *d; br next(v)`; `next(v): assert(v[n - 1] == want)`.
    AcrossABlock,
    /// `memcpy(d, s, 2)`: a two-lane run of `[u8; n]`.
    LaneRun,
}

fn module(shape: Shape, n: u64, want: i128) -> Module {
    let mut mb = ModuleBuilder::new("bulk_verdicts");
    let elem = match shape {
        Shape::WholeFill => Ty::U32,
        _ => Ty::U8,
    };
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, n);
    let params = match shape {
        Shape::SymbolicCopy => vec![Ty::U64],
        _ => vec![],
    };
    let ft = mb.add_func_type(params, vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let m = match shape {
        Shape::SymbolicCopy => Some(fb.add_block_param(entry, Ty::U64)),
        _ => None,
    };
    let d = fb.alloca(arr.clone());
    let sevens = fb.const_value(arr.clone(), Constant::splat(Constant::Int(7), n));
    fb.store(arr.clone(), d, sevens);
    let s = fb.alloca(arr.clone());
    let nines = fb.const_value(arr.clone(), Constant::splat(Constant::Int(9), n));
    fb.store(arr.clone(), s, nines);
    let lane = match shape {
        Shape::WholeFill => 2,
        Shape::AcrossABlock => n - 1,
        _ => 1,
    };
    match shape {
        Shape::WholeCopy | Shape::AcrossABlock => {
            let bytes = fb.const_value(Ty::U64, Constant::Int(i128::from(n)));
            fb.memcopy(d, s, bytes, false);
        }
        Shape::SymbolicCopy => {
            let m = m.expect("count parameter");
            let total = fb.iconst(Ty::U64, i128::from(n));
            let pinned = fb.icmp(ICmpOp::Eq, Ty::U64, m, total);
            fb.assume(pinned);
            fb.memcopy(d, s, m, false);
        }
        Shape::WholeFill => {
            let byte = fb.iconst(Ty::U8, 0xAB);
            let bytes = fb.const_value(Ty::U64, Constant::Int(i128::from(n * 4)));
            fb.memset(d, byte, bytes);
        }
        Shape::LaneRun => {
            let bytes = fb.const_value(Ty::U64, Constant::Int(2));
            fb.memcopy(d, s, bytes, false);
        }
    }
    let after = fb.load(arr.clone(), d);
    let block_value = match shape {
        Shape::AcrossABlock => {
            let next = fb.create_block();
            fb.br(next, vec![after]);
            fb.switch_to_block(next);
            fb.add_block_param(next, arr)
        }
        _ => after,
    };
    let index = fb.iconst(Ty::U64, i128::from(lane));
    let read = fb.extract_element(elem.clone(), block_value, index);
    let want = fb.const_value(elem.clone(), Constant::Int(want));
    let holds = fb.icmp(ICmpOp::Eq, elem, read, want);
    fb.assert(holds);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn whole_object_bulk_writes_are_decided_at_every_length() {
    for n in LENGTHS {
        for (shape, written, stale) in [
            (Shape::WholeCopy, 9, 7),
            (Shape::SymbolicCopy, 9, 7),
            (Shape::WholeFill, 0xABAB_ABAB, 7),
            (Shape::AcrossABlock, 9, 7),
        ] {
            let (proved, reasons) = solve(&module(shape, n, written));
            // A symbolic count keeps the lane-run rule, guarded by `m` naming no
            // whole object; the assumption `m == n` makes that guard unreachable.
            let guarded = match shape {
                Shape::SymbolicCopy => vec![TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange],
                _ => Vec::new(),
            };
            assert_eq!(reasons, guarded, "{shape:?} n={n}");
            assert_eq!(proved, Verdict::Proved, "{shape:?} n={n}: the written value");
            let (refuted, _) = solve(&module(shape, n, stale));
            assert_eq!(refuted, Verdict::Refuted, "{shape:?} n={n}: the pre-write value");
        }
    }
}

#[test]
fn a_lane_run_is_never_proved() {
    for n in LENGTHS {
        let (verdict, reasons) = solve(&module(Shape::LaneRun, n, 9));
        assert_eq!(reasons, vec![TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange], "n={n}");
        assert_ne!(verdict, Verdict::Proved, "n={n}: a lane run fails closed");
    }
}
