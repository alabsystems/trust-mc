// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `MemCopy` / `MemSet` in both lanes against trust-ir's byte-level reference
//! interpreter, over the shapes the grid in
//! `src/translate_chc_bulk_memory_tests.rs` does not reach: nested arrays, a
//! struct with an array field, a struct with padding, a newtype chain at offset
//! 0, a struct of structs (an object that starts BEFORE an interior pointer, the
//! one an off-by-one in the enclosing-object chain would wrongly write), an
//! array of structs, and cross-type copies of equal size. Every `GEP`-addressable
//! destination and source sub-object, `memcpy`/`memmove`/within-one-cell/`memset`,
//! every count from 0 to one past the cell, with memory checks on and off.
//! (First written by the wave-12 soundness review of the bulk arm.)
//!
//! Checked on EVERY case:
//!
//! * interpreter undefined behaviour => the CHC error is reachable (checks on);
//! * interpreter post-state `P` => for every leaf, `leaf == P[leaf] ^ 1` is
//!   REFUTED, never proved;
//! * and in the other direction `leaf == P[leaf]` is proved, or fails closed with
//!   a named diagnostic: a reachable error with no diagnostic on a defined
//!   program (checks on) is a false refutation.
//!
//! The BMC lane is checked on its whole-cell model: scalar cells against the
//! interpreter, and compound cells read lane by lane after a whole-cell write.

use std::collections::BTreeMap;

use ay_bindings::Expr;
use trust_ir::inst::ICmpOp;
use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::value::{FuncId, StructId, ValueId};
use trust_ir::{Constant, FieldDef, Module, StructDef, StructRepr, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};
use trust_mc_core::bmc::BmcVc;
use trust_mc_core::decl::Decl;
use trust_mc_core::violation::{PropertyKind, Violation};
use trust_mc_trust_bmc::{
    ChcTranslationOutput, TranslateOptions, TrustIrChcUnsupportedReason,
    trust_ir_function_to_chc_translation_output, trust_ir_to_bmc_vc,
};

// ---------------------------------------------------------------------------
// Solving
// ---------------------------------------------------------------------------

fn sat(logic: &str, decls: &[Decl], vars: &[(String, ay_bindings::Sort)], cs: &[Expr]) -> bool {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic(logic);
    let mut seen = std::collections::BTreeSet::new();
    for (name, sort) in vars {
        if seen.insert(name.clone()) {
            let _ = program.declare_const(name.clone(), sort.clone());
        }
    }
    for decl in decls {
        if let Decl::Const { name, sort } = decl {
            if seen.insert(name.to_string()) {
                let _ = program.declare_const(name.clone(), sort.clone());
            }
        }
    }
    for c in cs {
        program.assert(c.clone());
    }
    program.check_sat();
    match ay_bindings::execute_direct::execute(&program).expect("AY runs") {
        ay_bindings::execute_direct::ExecuteResult::Counterexample { .. } => true,
        ay_bindings::execute_direct::ExecuteResult::Verified => false,
        other => panic!("unexpected solver outcome: {other:?}"),
    }
}

fn chc_error_reachable(output: &ChcTranslationOutput) -> bool {
    let vars: Vec<(String, ay_bindings::Sort)> =
        output.vc.vars().iter().map(|v| (v.name.to_string(), v.sort.clone())).collect();
    output.vc.rules.iter().filter(|r| r.head.name == "error").any(|r| {
        let cs: Vec<Expr> = r.body.constraints.iter().cloned().collect();
        sat("QF_ABV", &output.vc.decls, &vars, &cs)
    })
}

fn bmc_reachable(vc: &BmcVc, v: &Violation) -> bool {
    let mut cs = vc.constraints.clone();
    cs.push(v.condition.clone());
    sat("QF_ABV", &vc.decls, &[], &cs)
}

// ---------------------------------------------------------------------------
// A small type language
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum T {
    U8,
    U16,
    U32,
    Arr(Box<T>, u64),
    /// Index into `struct_defs()`.
    S(usize),
}

/// (fields (type, offset), size, align)
fn struct_defs() -> Vec<(Vec<(T, u64)>, u64, u64)> {
    vec![
        // S0 { a: [u8; 2] @0, b: u16 @2 }  size 4
        (vec![(T::Arr(Box::new(T::U8), 2), 0), (T::U16, 2)], 4, 2),
        // S1 { a: u8 @0, b: u32 @4 }  size 8, padding [1, 4)
        (vec![(T::U8, 0), (T::U32, 4)], 8, 4),
        // S2 { a: u32 @0 }  newtype
        (vec![(T::U32, 0)], 4, 4),
        // S3 { a: S2 @0, b: u32 @4 }  newtype chain at offset 0
        (vec![(T::S(2), 0), (T::U32, 4)], 8, 4),
        // S4 { a: u32 @0, b: u32 @4 }
        (vec![(T::U32, 0), (T::U32, 4)], 8, 4),
        // S5 { p: S4 @0, q: S4 @8 }: `p` starts before a pointer to `p.b`, and an
        // 8-byte range from `p.b` (in bounds) is `p.b` and `q.a`, not `p`.
        (vec![(T::S(4), 0), (T::S(4), 8)], 16, 4),
    ]
}

fn size_of(t: &T) -> u64 {
    match t {
        T::U8 => 1,
        T::U16 => 2,
        T::U32 => 4,
        T::Arr(e, n) => size_of(e) * n,
        T::S(k) => struct_defs()[*k].1,
    }
}

fn has_padding(t: &T) -> bool {
    match t {
        T::S(1) => true,
        T::Arr(e, _) => has_padding(e),
        T::S(k) => struct_defs()[*k].0.iter().any(|(f, _)| has_padding(f)),
        _ => false,
    }
}

/// Every sub-object a constant GEP chain can name: (path, type, byte offset).
fn addressable(t: &T) -> Vec<(Vec<usize>, T, u64)> {
    let mut out = vec![(Vec::new(), t.clone(), 0)];
    match t {
        T::Arr(e, n) => {
            for i in 0..*n {
                for (p, ty, off) in addressable(e) {
                    let mut path = vec![i as usize];
                    path.extend(p);
                    out.push((path, ty, i * size_of(e) + off));
                }
            }
        }
        T::S(k) => {
            for (f, (fty, foff)) in struct_defs()[*k].0.iter().enumerate() {
                assert_eq!(f as u64 * size_of(fty), *foff, "GEP evidence for the fixture");
                for (p, ty, off) in addressable(fty) {
                    let mut path = vec![f];
                    path.extend(p);
                    out.push((path, ty, foff + off));
                }
            }
        }
        _ => {}
    }
    out
}

fn leaves(t: &T) -> Vec<(Vec<usize>, T)> {
    addressable(t)
        .into_iter()
        .filter(|(_, ty, _)| matches!(ty, T::U8 | T::U16 | T::U32))
        .map(|(p, ty, _)| (p, ty))
        .collect()
}

fn sub_ty(t: &T, path: &[usize]) -> T {
    let mut cur = t.clone();
    for &i in path {
        cur = match cur {
            T::Arr(e, _) => *e,
            T::S(k) => struct_defs()[k].0[i].0.clone(),
            _ => panic!("path through a scalar"),
        };
    }
    cur
}

struct Tys {
    map: BTreeMap<T, Ty>,
}

impl Tys {
    fn new(mb: &mut ModuleBuilder) -> Self {
        let mut tys = Tys { map: BTreeMap::new() };
        for (k, (fields, size, align)) in struct_defs().into_iter().enumerate() {
            let fields = fields
                .iter()
                .enumerate()
                .map(|(i, (fty, off))| FieldDef {
                    name: format!("f{i}"),
                    ty: tys.lower(mb, fty),
                    offset: Some(*off),
                })
                .collect();
            let id = mb.add_struct(StructDef {
                id: StructId::new(k as u32),
                name: format!("rev::S{k}"),
                fields,
                size: Some(size),
                align: Some(align),
                repr: StructRepr::Rust,
                origin: None,
            });
            assert_eq!(id, StructId::new(k as u32));
        }
        tys
    }

    fn lower(&mut self, mb: &mut ModuleBuilder, t: &T) -> Ty {
        if let Some(ty) = self.map.get(t) {
            return ty.clone();
        }
        let ty = match t {
            T::U8 => Ty::U8,
            T::U16 => Ty::U16,
            T::U32 => Ty::U32,
            T::Arr(e, n) => {
                let elem = self.lower(mb, e);
                let id = mb.add_type(elem);
                Ty::Array(id, *n)
            }
            T::S(k) => Ty::Struct(StructId::new(*k as u32)),
        };
        self.map.insert(t.clone(), ty.clone());
        ty
    }

    fn get(&self, t: &T) -> Ty {
        self.map.get(t).cloned().expect("lowered")
    }
}

fn lower_all(tys: &mut Tys, mb: &mut ModuleBuilder, t: &T) {
    for (_, sub, _) in addressable(t) {
        tys.lower(mb, &sub);
    }
}

fn gep_chain(
    fb: &mut FunctionBuilder<'_>,
    tys: &Tys,
    root: &T,
    cell: ValueId,
    path: &[usize],
) -> ValueId {
    let mut ptr = cell;
    for depth in 0..path.len() {
        let pointee = sub_ty(root, &path[..=depth]);
        let index = fb.iconst(Ty::I64, path[depth] as i128);
        ptr = fb.gep(tys.get(&pointee), ptr, vec![index]);
    }
    ptr
}

fn leaf_value(width: u64, counter: &mut u128) -> i128 {
    let mut v: u128 = 0;
    for b in 0..width {
        v |= (*counter & 0xFF) << (8 * b);
        *counter += 1;
    }
    v as i128
}

#[derive(Clone, Copy, Debug)]
enum Op {
    Copy { overlap: bool },
    Within { overlap: bool },
    Fill(u8),
}

#[derive(Clone, Debug)]
struct Case {
    dst_ty: T,
    src_ty: T,
    op: Op,
    dst_path: Vec<usize>,
    src_path: Vec<usize>,
    bytes: u64,
}

enum Tail {
    Return,
    Expect(Vec<u128>),
    Nothing,
}

fn build(case: &Case, tail: &Tail) -> Module {
    let mut mb = ModuleBuilder::new("rev");
    let mut tys = Tys::new(&mut mb);
    lower_all(&mut tys, &mut mb, &case.dst_ty);
    lower_all(&mut tys, &mut mb, &case.src_ty);
    let dleaves = leaves(&case.dst_ty);
    let returns = match tail {
        Tail::Return => dleaves.iter().map(|(_, t)| tys.get(t)).collect(),
        _ => vec![],
    };
    let ft = mb.add_func_type(vec![], returns);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let d = fb.alloca(tys.get(&case.dst_ty));
    let s = fb.alloca(tys.get(&case.src_ty));
    let mut counter = 0x10u128;
    for (path, lt) in &dleaves {
        let p = gep_chain(&mut fb, &tys, &case.dst_ty, d, path);
        let v = fb.iconst(tys.get(lt), leaf_value(size_of(lt), &mut counter));
        fb.store(tys.get(lt), p, v);
    }
    let mut counter = 0x80u128;
    for (path, lt) in leaves(&case.src_ty) {
        let p = gep_chain(&mut fb, &tys, &case.src_ty, s, &path);
        let v = fb.iconst(tys.get(&lt), leaf_value(size_of(&lt), &mut counter));
        fb.store(tys.get(&lt), p, v);
    }
    let count = fb.const_value(Ty::U64, Constant::Int(i128::from(case.bytes)));
    match case.op {
        Op::Copy { overlap } => {
            let dp = gep_chain(&mut fb, &tys, &case.dst_ty, d, &case.dst_path);
            let sp = gep_chain(&mut fb, &tys, &case.src_ty, s, &case.src_path);
            fb.memcopy(dp, sp, count, overlap);
        }
        Op::Within { overlap } => {
            let dp = gep_chain(&mut fb, &tys, &case.dst_ty, d, &case.dst_path);
            let sp = gep_chain(&mut fb, &tys, &case.dst_ty, d, &case.src_path);
            fb.memcopy(dp, sp, count, overlap);
        }
        Op::Fill(byte) => {
            let dp = gep_chain(&mut fb, &tys, &case.dst_ty, d, &case.dst_path);
            let b = fb.iconst(Ty::U8, i128::from(byte));
            fb.memset(dp, b, count);
        }
    }
    // Read every destination leaf back.
    let reads: Vec<ValueId> = if has_padding(&case.dst_ty) {
        // Single-lane GEP loads (no whole load of an image with uninit padding).
        dleaves
            .iter()
            .map(|(path, lt)| {
                assert_eq!(path.len(), 1);
                let p = gep_chain(&mut fb, &tys, &case.dst_ty, d, path);
                fb.load(tys.get(lt), p)
            })
            .collect()
    } else {
        let whole = fb.load(tys.get(&case.dst_ty), d);
        dleaves
            .iter()
            .map(|(path, _)| {
                let mut v = whole;
                let mut cur = case.dst_ty.clone();
                for &i in path {
                    let next = sub_ty(&cur, &[i]);
                    v = match &cur {
                        T::Arr(..) => {
                            let idx = fb.iconst(Ty::U64, i as i128);
                            fb.extract_element(tys.get(&next), v, idx)
                        }
                        T::S(_) => fb.extract_field(tys.get(&next), v, i as u32),
                        _ => unreachable!(),
                    };
                    cur = next;
                }
                v
            })
            .collect()
    };
    match tail {
        Tail::Return => fb.ret(reads),
        Tail::Expect(want) => {
            for ((read, (_, lt)), w) in reads.iter().zip(&dleaves).zip(want) {
                let wv = fb.const_value(tys.get(lt), Constant::Int(*w as i128));
                let holds = fb.icmp(ICmpOp::Eq, tys.get(lt), *read, wv);
                fb.assert(holds);
            }
            fb.ret(vec![]);
        }
        Tail::Nothing => fb.ret(vec![]),
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[derive(Debug, PartialEq)]
enum Reference {
    Lanes(Vec<u128>),
    Undefined,
}

fn reference(case: &Case) -> Reference {
    let module = build(case, &Tail::Return);
    match Interpreter::with_module(&module).execute_func(FuncId::new(0), Vec::new()) {
        Ok(out) => Reference::Lanes(
            out.returns.iter().map(|v| v.as_int().expect("int").as_unsigned()).collect(),
        ),
        Err(e) if e.code == InterpretErrorCode::UndefinedBehavior => Reference::Undefined,
        Err(e) => panic!("{case:?}: interpreter: {e:?}"),
    }
}

fn chc(case: &Case, tail: &Tail, options: &TranslateOptions) -> ChcTranslationOutput {
    let module = build(case, tail);
    trust_ir_function_to_chc_translation_output(&module, FuncId::new(0), options)
        .expect("translates")
}

#[derive(Default, Debug)]
struct Tally {
    cases: usize,
    ub: usize,
    proved_exact: usize,
    fail_closed: usize,
    false_proofs: Vec<String>,
    false_refutations: Vec<String>,
}

fn check_case(case: &Case, options: &TranslateOptions, tally: &mut Tally) {
    tally.cases += 1;
    match reference(case) {
        Reference::Undefined => {
            tally.ub += 1;
            if options.check_memory_bounds {
                let out = chc(case, &Tail::Nothing, options);
                if !chc_error_reachable(&out) {
                    tally.false_proofs.push(format!("UB not reported: {case:?}"));
                }
            }
        }
        Reference::Lanes(lanes) => {
            for i in 0..lanes.len() {
                let mut wrong = lanes.clone();
                wrong[i] ^= 1;
                let out = chc(case, &Tail::Expect(wrong), options);
                if !chc_error_reachable(&out) {
                    tally
                        .false_proofs
                        .push(format!("leaf {i} != {:#x} PROVED: {case:?}", lanes[i]));
                }
            }
            let out = chc(case, &Tail::Expect(lanes.clone()), options);
            if chc_error_reachable(&out) {
                let reasons: Vec<TrustIrChcUnsupportedReason> =
                    out.diagnostics.iter().map(|d| d.reason).collect();
                if reasons.is_empty() && options.check_memory_bounds {
                    tally.false_refutations.push(format!("{case:?} lanes {lanes:x?}"));
                } else {
                    tally.fail_closed += 1;
                }
            } else {
                tally.proved_exact += 1;
            }
        }
    }
}

fn ops() -> Vec<Op> {
    vec![
        Op::Copy { overlap: false },
        Op::Copy { overlap: true },
        Op::Within { overlap: false },
        Op::Within { overlap: true },
        Op::Fill(0xA5),
    ]
}

fn run_grid(pairs: &[(T, T, Vec<Op>)], options: &TranslateOptions) -> Tally {
    let mut tally = Tally::default();
    for (dst_ty, src_ty, pair_ops) in pairs {
        let before = (tally.cases, tally.ub, tally.proved_exact, tally.fail_closed);
        let dsize = size_of(dst_ty);
        for op in pair_ops.iter().copied() {
            if matches!(op, Op::Within { .. }) && dst_ty != src_ty {
                continue; // `Within` uses only the destination cell; run it once per dst type.
            }
            let dpaths: Vec<Vec<usize>> = addressable(dst_ty).into_iter().map(|a| a.0).collect();
            let spaths: Vec<Vec<usize>> = match op {
                Op::Copy { .. } => addressable(src_ty).into_iter().map(|a| a.0).collect(),
                Op::Within { .. } => dpaths.clone(),
                Op::Fill(_) => vec![Vec::new()],
            };
            for dp in &dpaths {
                for sp in &spaths {
                    for bytes in 0..=dsize + 1 {
                        let case = Case {
                            dst_ty: dst_ty.clone(),
                            src_ty: src_ty.clone(),
                            op,
                            dst_path: dp.clone(),
                            src_path: sp.clone(),
                            bytes,
                        };
                        check_case(&case, options, &mut tally);
                    }
                }
            }
        }
        eprintln!(
            "  pair {dst_ty:?} <- {src_ty:?}: cases {} ub {} proved {} fail_closed {}",
            tally.cases - before.0,
            tally.ub - before.1,
            tally.proved_exact - before.2,
            tally.fail_closed - before.3
        );
    }
    tally
}

fn arr(e: T, n: u64) -> T {
    T::Arr(Box::new(e), n)
}

fn pairs() -> Vec<(T, T, Vec<Op>)> {
    let nested = arr(arr(T::U8, 2), 2);
    let bytes4 = arr(T::U8, 4);
    let all = ops();
    // The 16-byte struct of structs has 7 sub-objects: a copy and a fill of each
    // carry the enclosing-object rule; the within-one-cell copies are the same
    // arithmetic as the other pairs'.
    let copy_and_fill = vec![Op::Copy { overlap: false }, Op::Fill(0xA5)];
    vec![
        (nested.clone(), nested.clone(), all.clone()),
        (T::S(0), T::S(0), all.clone()),
        (T::S(1), T::S(1), all.clone()),
        (T::S(3), T::S(3), all.clone()),
        (T::S(5), T::S(5), copy_and_fill),
        (arr(T::S(2), 2), arr(T::S(2), 2), all.clone()),
        // Cross-type, equal size.
        (T::U32, bytes4.clone(), all.clone()),
        (bytes4.clone(), T::U32, all.clone()),
        (T::S(2), T::U32, all.clone()),
        (T::U32, T::S(2), all.clone()),
        (T::S(0), bytes4.clone(), all.clone()),
        (nested.clone(), bytes4.clone(), all.clone()),
        (T::S(3), arr(T::U32, 2), all.clone()),
        (arr(T::U16, 2), T::S(0), all),
    ]
}

#[test]
fn chc_bulk_writes_agree_with_the_interpreter_checks_on() {
    let tally = run_grid(&pairs(), &TranslateOptions::default());
    eprintln!(
        "checks on: cases {} ub {} proved {} fail_closed {} false_proofs {} false_refutations {}",
        tally.cases,
        tally.ub,
        tally.proved_exact,
        tally.fail_closed,
        tally.false_proofs.len(),
        tally.false_refutations.len()
    );
    for f in tally.false_proofs.iter().take(20) {
        eprintln!("FALSE PROOF: {f}");
    }
    for f in tally.false_refutations.iter().take(20) {
        eprintln!("FALSE REFUTATION: {f}");
    }
    assert!(tally.false_proofs.is_empty(), "{} false proofs", tally.false_proofs.len());
    assert!(
        tally.false_refutations.is_empty(),
        "{} false refutations",
        tally.false_refutations.len()
    );
}

#[test]
fn chc_bulk_writes_agree_with_the_interpreter_checks_off() {
    let options = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let tally = run_grid(&pairs(), &options);
    eprintln!(
        "checks off: cases {} ub {} proved {} fail_closed/havoc {} false_proofs {}",
        tally.cases,
        tally.ub,
        tally.proved_exact,
        tally.fail_closed,
        tally.false_proofs.len()
    );
    for f in tally.false_proofs.iter().take(20) {
        eprintln!("FALSE PROOF: {f}");
    }
    assert!(tally.false_proofs.is_empty(), "{} false proofs", tally.false_proofs.len());
}

// ---------------------------------------------------------------------------
// BMC
// ---------------------------------------------------------------------------

fn bmc_vc(module: &Module, options: &TranslateOptions) -> BmcVc {
    let mut vcs = trust_ir_to_bmc_vc(module, options);
    assert_eq!(vcs.len(), 1);
    vcs.remove(0)
}

fn bmc_any_reachable(vc: &BmcVc) -> bool {
    vc.violations.iter().any(|v| bmc_reachable(vc, v))
}

/// A compound BMC cell: `[u64; 2]`, or `W { a: u64 @ 0, b: u64 @ 8 }`. Either is
/// ONE 64-bit placeholder element per region, and a `u64` lane `GEP` reads index
/// `k` of it (a lane store type-checks against the placeholder sort).
#[derive(Clone, Copy, Debug)]
enum Compound {
    Array,
    Struct,
}

/// How the whole of `x` reaches `y`.
#[derive(Clone, Copy, Debug)]
enum WholeWrite {
    MemCopy,
    LoadStore,
}

/// `y = [0, 0]`, `x = [9, 5]` through lane stores; `<x written whole into y>`;
/// `assert(y[lane] == want)`.
fn bmc_compound_probe(cell: Compound, write: WholeWrite, lane: i128, want: i128) -> Module {
    let mut mb = ModuleBuilder::new("bmc_compound");
    let ty = match cell {
        Compound::Array => {
            let u64_id = mb.add_type(Ty::U64);
            Ty::Array(u64_id, 2)
        }
        Compound::Struct => Ty::Struct(mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "bmc_compound::W".to_string(),
            fields: vec![
                FieldDef { name: "a".into(), ty: Ty::U64, offset: Some(0) },
                FieldDef { name: "b".into(), ty: Ty::U64, offset: Some(8) },
            ],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
            origin: None,
        })),
    };
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let y = fb.alloca(ty.clone());
    let x = fb.alloca(ty.clone());
    for (k, x_value) in [(0i128, 9i128), (1, 5)] {
        let index = fb.iconst(Ty::I64, k);
        let y_lane = fb.gep(Ty::U64, y, vec![index]);
        let zero = fb.iconst(Ty::U64, 0);
        fb.store(Ty::U64, y_lane, zero);
        let index = fb.iconst(Ty::I64, k);
        let x_lane = fb.gep(Ty::U64, x, vec![index]);
        let value = fb.iconst(Ty::U64, x_value);
        fb.store(Ty::U64, x_lane, value);
    }
    match write {
        WholeWrite::MemCopy => {
            let sixteen = fb.const_value(Ty::U64, Constant::Int(16));
            fb.memcopy(y, x, sixteen, false);
        }
        WholeWrite::LoadStore => {
            let value = fb.load(ty.clone(), x);
            fb.store(ty, y, value);
        }
    }
    let index = fb.iconst(Ty::I64, lane);
    let y_lane = fb.gep(Ty::U64, y, vec![index]);
    let read = fb.load(Ty::U64, y_lane);
    let want = fb.iconst(Ty::U64, want);
    let holds = fb.icmp(ICmpOp::Eq, Ty::U64, read, want);
    fb.assert(holds);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// After a whole-cell write of a compound cell, no lane keeps its pre-write
/// value. The interpreter reads `y[1] == 5`; with memory checks off (where the
/// BMC lane reads the lane at all) `y[1] == 0` is never proved, for a `memcpy`
/// and for a whole `Load` + `Store`. The `memcpy` takes the source's whole
/// region, so it proves the copied lanes exactly; the `Store` of a placeholder
/// leaves the other lanes unknown.
#[test]
fn bmc_a_whole_compound_write_leaves_no_lane_stale() {
    let unchecked = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    for cell in [Compound::Array, Compound::Struct] {
        for write in [WholeWrite::MemCopy, WholeWrite::LoadStore] {
            let stale = bmc_compound_probe(cell, write, 1, 0);
            let reference =
                Interpreter::with_module(&stale).execute_func(FuncId::new(0), Vec::new());
            assert!(reference.is_err(), "{cell:?} {write:?}: the interpreter fails y[1] == 0");
            for options in [&unchecked, &TranslateOptions::default()] {
                let vc = bmc_vc(&stale, options);
                assert!(
                    bmc_any_reachable(&vc),
                    "{cell:?} {write:?} checks={}: the stale y[1] == 0 must not be PROVED",
                    options.check_memory_bounds
                );
            }
        }
        for (lane, want) in [(0, 9), (1, 5)] {
            let copied = bmc_compound_probe(cell, WholeWrite::MemCopy, lane, want);
            let reference =
                Interpreter::with_module(&copied).execute_func(FuncId::new(0), Vec::new());
            assert!(reference.is_ok(), "{cell:?}: the interpreter reads y[{lane}] == {want}");
            let vc = bmc_vc(&copied, &unchecked);
            assert!(!bmc_any_reachable(&vc), "{cell:?}: memcpy copies lane {lane} exactly");
        }
    }
}

/// BMC scalar cells against the interpreter: every (dst, src) scalar pair, every
/// op, every count 0..=size+1, checks on. Soundness: a wrong value is never
/// proved; UB is always a reachable violation.
#[test]
fn bmc_scalar_cells_agree_with_the_interpreter() {
    let scalars = [Ty::U8, Ty::U16, Ty::U32, Ty::I32, Ty::U64, Ty::Bool];
    let size = |t: &Ty| match t {
        Ty::U8 | Ty::Bool => 1u64,
        Ty::U16 => 2,
        Ty::U32 | Ty::I32 => 4,
        Ty::U64 => 8,
        _ => unreachable!(),
    };
    let init = |t: &Ty, base: i128| -> i128 {
        match t {
            Ty::Bool => 1,
            Ty::U8 => base,
            Ty::U16 => base | (base + 1) << 8,
            Ty::U32 | Ty::I32 => base | (base + 1) << 8 | (base + 2) << 16 | (base + 3) << 24,
            Ty::U64 => (0..8).fold(0, |acc, b| acc | (base + b) << (8 * b)),
            _ => unreachable!(),
        }
    };
    let mut false_proofs = Vec::new();
    let mut proved = 0;
    let mut total = 0;
    for dt in &scalars {
        for st in &scalars {
            for op in 0..4 {
                // 0 memcpy other, 1 memmove other, 2 memcpy self, 3 memset
                if op >= 2 && dt != st {
                    continue;
                }
                for bytes in 0..=size(dt) + 1 {
                    let build = |expect: Option<i128>| {
                        let mut mb = ModuleBuilder::new("bmc_scalar");
                        let returns = if expect.is_none() { vec![dt.clone()] } else { vec![] };
                        let ft = mb.add_func_type(vec![], returns);
                        let mut fb = mb.function("f", ft);
                        let entry = fb.create_block();
                        fb.switch_to_block(entry);
                        fb.set_entry(entry);
                        let dst = fb.alloca(dt.clone());
                        let dv = if *dt == Ty::Bool {
                            fb.bool_const(true)
                        } else {
                            fb.iconst(dt.clone(), init(dt, 0x10))
                        };
                        fb.store(dt.clone(), dst, dv);
                        let src = fb.alloca(st.clone());
                        let sv = if *st == Ty::Bool {
                            fb.bool_const(false)
                        } else {
                            fb.iconst(st.clone(), init(st, 0x40))
                        };
                        fb.store(st.clone(), src, sv);
                        let count = fb.const_value(Ty::U64, Constant::Int(i128::from(bytes)));
                        match op {
                            0 => fb.memcopy(dst, src, count, false),
                            1 => fb.memcopy(dst, src, count, true),
                            2 => fb.memcopy(dst, dst, count, false),
                            _ => {
                                let byte = fb.iconst(Ty::U8, 0x01);
                                fb.memset(dst, byte, count)
                            }
                        }
                        let read = fb.load(dt.clone(), dst);
                        match expect {
                            None => fb.ret(vec![read]),
                            Some(want) => {
                                let wv = if *dt == Ty::Bool {
                                    fb.bool_const(want != 0)
                                } else {
                                    fb.iconst(dt.clone(), want)
                                };
                                let holds = fb.icmp(ICmpOp::Eq, dt.clone(), read, wv);
                                fb.assert(holds);
                                fb.ret(vec![]);
                            }
                        }
                        fb.build();
                        mb.build().expect("ModuleBuilder::build: test fixture")
                    };
                    total += 1;
                    let reference = Interpreter::with_module(&build(None))
                        .execute_func(FuncId::new(0), Vec::new());
                    match reference {
                        Err(e) if e.code == InterpretErrorCode::UndefinedBehavior => {
                            let vc = bmc_vc(&build(Some(0)), &TranslateOptions::default());
                            let ub_or_unsupported = vc
                                .violations
                                .iter()
                                .filter(|v| v.kind != PropertyKind::Assertion)
                                .any(|v| bmc_reachable(&vc, v));
                            if !ub_or_unsupported {
                                false_proofs
                                    .push(format!("UB missed {dt:?} {st:?} op{op} n={bytes}"));
                            }
                        }
                        Err(e) => panic!("{dt:?} {st:?} op{op} n={bytes}: {e:?}"),
                        Ok(out) => {
                            let v = out.returns[0]
                                .as_int()
                                .map(|i| i.as_unsigned() as i128)
                                .unwrap_or_else(|| {
                                    i128::from(out.returns[0].as_bool().expect("bool"))
                                });
                            let flip = if *dt == Ty::Bool { 1 - v } else { v ^ 1 };
                            let vc = bmc_vc(&build(Some(flip)), &TranslateOptions::default());
                            if !bmc_any_reachable(&vc) {
                                false_proofs.push(format!(
                                    "wrong value proved {dt:?} {st:?} op{op} n={bytes}"
                                ));
                            }
                            let vc = bmc_vc(&build(Some(v)), &TranslateOptions::default());
                            if !bmc_any_reachable(&vc) {
                                proved += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!("bmc scalar: total {total} proved {proved} false_proofs {}", false_proofs.len());
    for f in &false_proofs {
        eprintln!("BMC FALSE PROOF: {f}");
    }
    assert!(false_proofs.is_empty());
}

/// A closure cell under trust-ir wire v58 `Module.closure_layouts`, in the BMC
/// lane: `f(src, dst0)` over a closure type capturing `(u32, u32)`, both stored
/// in their own cells, `bytes` of `src`'s cell copied (or `0x5A` filled) into
/// `dst0`'s, then `assert(capture == want(capture))` on each capture of the
/// reloaded destination. `declared` adds the frame rustc's upvar reordering
/// gives (capture 1 at byte 0, capture 0 at byte 4).
fn bmc_closure_probe(
    declared: bool,
    fill: bool,
    bytes: u64,
    want: impl Fn(&mut FunctionBuilder<'_>, ValueId, ValueId, u32) -> ValueId,
) -> Module {
    let target = trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    };
    let mut mb = ModuleBuilder::new_with_target_info("bmc_closure", target);
    let apparent = mb.add_func_type(vec![], vec![Ty::U32]);
    let closure = mb
        .add_closure_type(trust_ir::ClosureTy { func: apparent, captures: vec![Ty::U32, Ty::U32] });
    let cty = Ty::Closure(closure);
    let ft = mb.add_func_type(vec![cty.clone(), cty.clone()], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let src = fb.add_block_param(entry, cty.clone());
    let dst0 = fb.add_block_param(entry, cty.clone());
    let dst_cell = fb.alloca(cty.clone());
    let src_cell = fb.alloca(cty.clone());
    fb.store(cty.clone(), dst_cell, dst0);
    fb.store(cty.clone(), src_cell, src);
    let count = fb.const_value(Ty::Usize, Constant::Int(i128::from(bytes)));
    if fill {
        let byte = fb.iconst(Ty::U8, 0x5A);
        fb.memset(dst_cell, byte, count);
    } else {
        fb.memcopy(dst_cell, src_cell, count, false);
    }
    let after = fb.load(cty, dst_cell);
    for capture in 0..2 {
        let got = fb.extract_field(Ty::U32, after, capture);
        let wanted = want(&mut fb, src, dst0, capture);
        let holds = fb.icmp(ICmpOp::Eq, Ty::U32, got, wanted);
        fb.assert(holds);
    }
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    if declared {
        module.closure_layouts.push(trust_ir::ClosureLayoutDescriptor {
            closure,
            size: 8,
            align: 4,
            capture_offsets: vec![4, 0],
            origin: None,
        });
    }
    module
}

/// A declared closure frame gives the BMC lane's whole-cell rule a size
/// (`bulk_cell` reads `Module::ty_layout_shape`), and nothing more: with or
/// without the frame, and with memory checks on or off, no capture value that
/// a write does not determine is ever proved after a non-empty copy or fill
/// of a closure cell — not the pre-write capture, not a wrong constant, and
/// not, after a 4-byte write into the reordered frame, either capture.
#[test]
fn bmc_closure_cells_prove_no_undetermined_capture() {
    let unchecked = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    for declared in [false, true] {
        for fill in [false, true] {
            for bytes in [4u64, 8] {
                let mut probes: Vec<(&str, Module)> = vec![
                    (
                        "old",
                        bmc_closure_probe(declared, fill, bytes, |fb, _, dst0, capture| {
                            fb.extract_field(Ty::U32, dst0, capture)
                        }),
                    ),
                    (
                        "wrong",
                        bmc_closure_probe(declared, fill, bytes, |fb, _, _, _| {
                            fb.iconst(Ty::U32, 0x5A5A_5A5B)
                        }),
                    ),
                ];
                if bytes == 4 {
                    // Half the frame: neither capture is determined by the write.
                    probes.push((
                        "source",
                        bmc_closure_probe(declared, fill, bytes, |fb, src, _, capture| {
                            fb.extract_field(Ty::U32, src, capture)
                        }),
                    ));
                    probes.push((
                        "filled",
                        bmc_closure_probe(declared, fill, bytes, |fb, _, _, _| {
                            fb.iconst(Ty::U32, 0x5A5A_5A5A)
                        }),
                    ));
                }
                for (label, module) in &probes {
                    for options in [&unchecked, &TranslateOptions::default()] {
                        let vc = bmc_vc(module, options);
                        assert!(
                            bmc_any_reachable(&vc),
                            "declared={declared} fill={fill} bytes={bytes} {label} checks={}: \
                             an undetermined capture must not be PROVED",
                            options.check_memory_bounds
                        );
                    }
                }
            }
        }
    }
}
