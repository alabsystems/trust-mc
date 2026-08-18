// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! # Program-space differential soundness oracle (apex Step A)
//!
//! The 8 false-proofs of the 2026-06-19 sweep were found by hand. That is
//! evidence-of-bugs, not absence-of-bugs. This harness is the empirical scaffold
//! that hunts a *next* one across a whole generated program space, and quantifies
//! confidence where it finds none — the scaffold the machine-checked clean proof
//! (`clean:proofs/trust-soundness/search_soundness.lean`) ultimately replaces.
//!
//! For each generated trust-ir program it runs, INDEPENDENTLY:
//!   * the REAL discharge encoding — `trust_ir_to_chc_vc` → `lower_obligation`
//!     (the exact production lowering) → `acyclic_direct_smt_decision` — to a
//!     SAFE / UNSAFE / INCONCLUSIVE verdict; and
//!   * a ground-truth panic oracle — the trust-ir `Interpreter` executed over a
//!     grid of inputs — to "does this program actually panic on some input?".
//!
//! THE SOUNDNESS ASSERTION: never `SAFE ∧ actually-panics`. Such a pair is a false
//! PROVE — a 6th hole. The harness fails loudly if it ever sees one.
//!
//! ## Semantic-agreement boundary (load-bearing)
//!
//! A differential oracle is only sound if both sides agree on what "panic" means.
//! The trust-ir interpreter WRAPS bare `BinOp::Add/Sub/Mul` (Rust release semantics —
//! never traps on overflow), while the CHC encoder over-approximates them as overflow
//! obligations — comparing those would manufacture fake false-proofs. So this oracle
//! is built only on the two classes where the engines AGREE exactly:
//!   * DIVISION / remainder — the interpreter traps on div-by-zero and signed
//!     `MIN / -1`, and the encoder models exactly those (`check_div_by_zero`); and
//!   * CHECKED OVERFLOW via `Inst::Overflow` (exact flag) + a branch to an
//!     `assert(false)` trap — the interpreter computes the flag by exact arithmetic
//!     and traps on the assert, while the encoder models `Inst::Assert{cond}` as
//!     `error reachable iff !cond`. A `SAFE ∧ actually-panics` pair is then a genuine
//!     false PROVE regardless of overflow-predicate conventions, because the
//!     interpreter is Rust semantics.
//! Both classes are where guard-analysis / arithmetic-arm false-proofs live.

use trust_ir::Module;
use trust_ir::inst::{BinOp, ICmpOp, OverflowOp};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_ir_build::ModuleBuilder;
use trust_mc_core::{MirChcPdrObligation, MirObligationKind};
use trust_mc_trust_bmc::{TranslateOptions, trust_ir_function_to_chc_vc, trust_ir_to_chc_vc};

use crate::direct_smt_cex::{AcyclicDecision, acyclic_direct_smt_decision};
use crate::native::typed_chc_ay::lower_obligation;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    /// The discharge encoding PROVED the program panic-free (error unreachable).
    Safe,
    /// A concrete reachable panic witness was found.
    Unsafe,
    /// Could not decide (defer to PDR) — never a proof either way.
    Inconclusive,
    /// The backend solver PANICKED on this obligation. A crash is NOT a proof —
    /// it fails closed to "not SAFE" here. Tracked separately because a solver that
    /// aborts on a valid VC is a robustness finding worth surfacing.
    Crashed,
}

// --- the discharge encoding under test: program -> verdict (REAL pipeline) -------

fn verify(module: &Module) -> Verdict {
    // Exactly the production path: typed CHC translation, then the real
    // `lower_obligation`, then the acyclic direct-SMT decision (a COMPLETE decision
    // procedure for the acyclic fragment these programs live in).
    let vcs = trust_ir_to_chc_vc(module, &TranslateOptions::default());
    let Some(vc) = vcs.into_iter().next() else {
        return Verdict::Inconclusive;
    };
    let obligation = MirChcPdrObligation::new(
        "oracle-obl",
        "oracle-fn",
        MirObligationKind::ArithmeticSafety,
        vc,
    );
    let problem = match lower_obligation(&obligation) {
        Ok(problem) => problem,
        // Failure to lower is a decline (fail-closed), never a proof.
        Err(_) => return Verdict::Inconclusive,
    };
    // Fail-closed around a solver panic: a crash is never a proof. catch_unwind so one
    // backend abort cannot mask the soundness result for the rest of the space.
    let decision = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        acyclic_direct_smt_decision(&problem)
    }));
    match decision {
        Ok(AcyclicDecision::Safe) => Verdict::Safe,
        Ok(AcyclicDecision::Unsafe(_)) => Verdict::Unsafe,
        Ok(AcyclicDecision::Inconclusive) => Verdict::Inconclusive,
        Err(_) => Verdict::Crashed,
    }
}

// --- the independent ground-truth panic oracle: does it actually panic? ----------

/// A DENSE grid of boundary + adversarial input values for an integer parameter.
///
/// Soundness of the oracle itself depends on this grid actually containing a panic
/// witness whenever one exists, so a `SAFE` verdict can be challenged. A sparse grid
/// is a hole: e.g. `if a > 100 { a - 1000 }` underflows for a ∈ (100, 1000), a range an
/// earlier coarse grid (…, 100, MAX/2, …) jumped over — letting a genuinely-panicking
/// program look "total" and a false-proof slip past. So this spans the small integers,
/// the mid-range around every guard/op constant used by the generator
/// ({1,2,3,5,7,17,100,1000}), the power-of-two/byte boundaries, and the type extremes.
fn sample_values(ty: &Ty) -> Vec<i128> {
    // Magnitudes that bracket the generator's constants and the overflow boundaries.
    let mids: [i128; 22] = [
        0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 50, 99, 100, 101, 200, 255, 256, 500, 999, 1000, 1001, 2000,
    ];
    match ty {
        Ty::U32 => {
            let mut v = mids.to_vec();
            v.extend([u32::MAX as i128 / 2, u32::MAX as i128 - 1, u32::MAX as i128]);
            v
        }
        Ty::I32 => {
            let mut v = mids.to_vec();
            v.extend(mids.iter().map(|m| -m));
            v.extend([
                i32::MAX as i128,
                i32::MAX as i128 - 1,
                i32::MIN as i128,
                i32::MIN as i128 + 1,
            ]);
            v
        }
        Ty::U64 => {
            let mut v = mids.to_vec();
            v.extend([u64::MAX as i128 / 2, u64::MAX as i128 - 1, u64::MAX as i128]);
            v
        }
        Ty::I64 => {
            let mut v = mids.to_vec();
            v.extend(mids.iter().map(|m| -m));
            v.extend([
                i64::MAX as i128,
                i64::MAX as i128 - 1,
                i64::MIN as i128,
                i64::MIN as i128 + 1,
            ]);
            v
        }
        _ => vec![0, 1, 2],
    }
}

/// The Cartesian product of per-parameter samples (params here are ≤ 2, so the grid
/// stays small). Returns each input tuple as interpreter values.
fn input_grid(param_tys: &[Ty]) -> Vec<Vec<InterpretValue>> {
    let mut rows: Vec<Vec<InterpretValue>> = vec![vec![]];
    for ty in param_tys {
        let mut next = Vec::new();
        for row in &rows {
            for &v in &sample_values(ty) {
                let mut r = row.clone();
                r.push(InterpretValue::int(ty.clone(), v).expect("in-range sample"));
                next.push(r);
            }
        }
        rows = next;
    }
    rows
}

/// True iff the interpreter TRAPS on some sampled input — a definitive witness
/// that the program can panic.
///
/// The trap set is `{Panic, UndefinedBehavior}`. `Panic` is an explicit panic
/// (assert failure); `UndefinedBehavior` is what the interpreter raises for
/// div-by-zero and signed `MIN / -1` — both of which PANIC under Rust semantics
/// and are exactly the obligations `check_div_by_zero` models, so for this
/// division domain a `UndefinedBehavior` trap corresponds precisely to a modeled
/// reachable panic. Every OTHER `InterpretErrorCode` is an interpreter
/// incapacity/coverage code (OutOfFuel/OutOfMemory) or a lowering defect
/// (Unsupported*/Type/Missing/…), NOT a program panic — those are ignored so a
/// coverage gap is never miscounted as ground-truth evidence of a panic.
fn actually_panics(module: &Module, fn_name: &str, param_tys: &[Ty]) -> bool {
    let interp = Interpreter::with_module(module);
    let function = module.function_by_name(fn_name).expect("generated function present");
    for args in input_grid(param_tys) {
        match interp.execute_function(function, args) {
            Ok(_) => {}
            Err(e)
                if e.code == InterpretErrorCode::Panic
                    || e.code == InterpretErrorCode::UndefinedBehavior =>
            {
                return true;
            }
            Err(_) => {}
        }
    }
    false
}

// --- generated programs (division: the semantic-agreement domain) ----------------

/// `f(a) = a / 7` (constant non-zero divisor). NEVER panics. Calibration: the
/// encoding SHOULD prove this SAFE (the div-by-zero VC `7 == 0` is trivially UNSAT).
fn build_div_const_nonzero() -> Module {
    let mut mb = ModuleBuilder::new("m_div_const_nonzero");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, Ty::U32);
    let seven = fb.iconst(Ty::U32, 7);
    let r = fb.udiv(Ty::U32, a, seven);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

/// `f(a) = a / 0` (constant zero divisor). ALWAYS panics. Calibration: MUST NOT prove SAFE.
fn build_div_const_zero() -> Module {
    let mut mb = ModuleBuilder::new("m_div_const_zero");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, Ty::U32);
    let zero = fb.iconst(Ty::U32, 0);
    let r = fb.udiv(Ty::U32, a, zero);
    fb.ret(vec![r]);
    fb.build();
    mb.build()
}

// --- the generator: a combinatorial space of guarded division programs ----------
//
// Family: `f(a, b) = if (b CMP k) { a OP b } else { 999 }` (and the unguarded form),
// over every comparison operator CMP, a grid of guard constants k, both div and rem,
// signed and unsigned, at four widths. This stress-tests the verifier's guard/interval
// reasoning for div-by-zero: which (CMP, k) actually exclude a zero divisor is a precise
// truth table (e.g. `b != k` excludes 0 iff k==0; `b > k` over u32 always excludes 0;
// `b <= k` over u32 never does) — an off-by-one in that reasoning that proved a
// zero-reachable program SAFE would be a 6th false-proof, and the interpreter (the
// independent arbiter) catches it. The generator enumerates freely; soundness is
// decided per program by comparing the two engines, not by trusting the generator.

#[derive(Clone, Copy)]
enum Cmp {
    Ne,
    Eq,
    Gt,
    Ge,
    Lt,
    Le,
}

#[derive(Clone, Copy)]
enum DivOp {
    Div,
    Rem,
}

fn is_signed(ty: &Ty) -> bool {
    matches!(ty, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::I128)
}

fn icmp_op(cmp: Cmp, signed: bool) -> ICmpOp {
    match (cmp, signed) {
        (Cmp::Ne, _) => ICmpOp::Ne,
        (Cmp::Eq, _) => ICmpOp::Eq,
        (Cmp::Gt, true) => ICmpOp::Sgt,
        (Cmp::Gt, false) => ICmpOp::Ugt,
        (Cmp::Ge, true) => ICmpOp::Sge,
        (Cmp::Ge, false) => ICmpOp::Uge,
        (Cmp::Lt, true) => ICmpOp::Slt,
        (Cmp::Lt, false) => ICmpOp::Ult,
        (Cmp::Le, true) => ICmpOp::Sle,
        (Cmp::Le, false) => ICmpOp::Ule,
    }
}

fn emit_div(
    fb: &mut trust_ir_build::FunctionBuilder,
    op: DivOp,
    ty: Ty,
    a: trust_ir::value::ValueId,
    b: trust_ir::value::ValueId,
    signed: bool,
) -> trust_ir::value::ValueId {
    match (op, signed) {
        (DivOp::Div, true) => fb.sdiv(ty, a, b),
        (DivOp::Div, false) => fb.udiv(ty, a, b),
        (DivOp::Rem, true) => fb.binop(BinOp::SRem, ty, a, b),
        (DivOp::Rem, false) => fb.binop(BinOp::URem, ty, a, b),
    }
}

struct Spec {
    ty: Ty,
    op: DivOp,
    /// `None` = unguarded `a OP b`; `Some((cmp, k))` = `if b cmp k { a OP b } else { 999 }`.
    guard: Option<(Cmp, i128)>,
}

impl Spec {
    fn name(&self) -> String {
        let opn = match self.op {
            DivOp::Div => "div",
            DivOp::Rem => "rem",
        };
        match self.guard {
            None => format!("{:?}/{}/unguarded", self.ty, opn),
            Some((cmp, k)) => format!("{:?}/{}/if(b {:?} {})", self.ty, opn, cmp_dbg(cmp), k),
        }
    }
}

fn cmp_dbg(cmp: Cmp) -> &'static str {
    match cmp {
        Cmp::Ne => "!=",
        Cmp::Eq => "==",
        Cmp::Gt => ">",
        Cmp::Ge => ">=",
        Cmp::Lt => "<",
        Cmp::Le => "<=",
    }
}

fn build_spec(spec: &Spec) -> Module {
    let signed = is_signed(&spec.ty);
    let mut mb = ModuleBuilder::new("gen");
    let ft = mb.add_func_type(vec![spec.ty.clone(), spec.ty.clone()], vec![spec.ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();

    match spec.guard {
        None => {
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let a = fb.add_block_param(entry, spec.ty.clone());
            let b = fb.add_block_param(entry, spec.ty.clone());
            let r = emit_div(&mut fb, spec.op, spec.ty.clone(), a, b, signed);
            fb.ret(vec![r]);
        }
        Some((cmp, k)) => {
            let then_blk = fb.create_block();
            let else_blk = fb.create_block();
            let exit = fb.create_block();
            fb.set_entry(entry);

            fb.switch_to_block(entry);
            let a = fb.add_block_param(entry, spec.ty.clone());
            let b = fb.add_block_param(entry, spec.ty.clone());
            let kc = fb.iconst(spec.ty.clone(), k);
            let cond = fb.icmp(icmp_op(cmp, signed), spec.ty.clone(), b, kc);
            fb.condbr(cond, then_blk, vec![], else_blk, vec![]);

            let result = fb.add_block_param(exit, spec.ty.clone());

            fb.switch_to_block(then_blk);
            let q = emit_div(&mut fb, spec.op, spec.ty.clone(), a, b, signed);
            fb.br(exit, vec![q]);

            fb.switch_to_block(else_blk);
            let fallback = fb.iconst(spec.ty.clone(), 999);
            fb.br(exit, vec![fallback]);

            fb.switch_to_block(exit);
            fb.ret(vec![result]);
        }
    }
    fb.build();
    mb.build()
}

fn generated_specs() -> Vec<Spec> {
    let mut specs = Vec::new();
    for ty in [Ty::U32, Ty::I32, Ty::U64, Ty::I64] {
        let signed = is_signed(&ty);
        let ks: Vec<i128> =
            if signed { vec![-2, -1, 0, 1, 2, 3, 5, 17] } else { vec![0, 1, 2, 3, 5, 17] };
        for op in [DivOp::Div, DivOp::Rem] {
            specs.push(Spec { ty: ty.clone(), op, guard: None });
            for cmp in [Cmp::Ne, Cmp::Eq, Cmp::Gt, Cmp::Ge, Cmp::Lt, Cmp::Le] {
                for &k in &ks {
                    specs.push(Spec { ty: ty.clone(), op, guard: Some((cmp, k)) });
                }
            }
        }
    }
    specs
}

// --- the overflow family: checked arithmetic + assert (the OTHER agreement domain) -
//
// `f(a) = if (a CMP k) { let (r, o) = a `op` C; if o { panic } else { r } } else { 999 }`
// where `op ∈ {checked_add, checked_sub, checked_mul}` with a constant second operand C.
// The panic is encoded as `Inst::Overflow` (exact flag) + a branch on the flag to an
// `assert(false)` trap — and BOTH engines agree on it: the interpreter computes the
// overflow flag by exact arithmetic and traps (`Panic`) on the assert, while the encoder
// models `Inst::Assert{cond}` as `error reachable iff !cond` (here: iff the overflow flag
// is set). This extends the evidence-of-absence from div-by-zero to the integer-overflow
// discharge — the largest arithmetic class, where the arithmetic-arm false-proofs lived.
// A `SAFE ∧ actually-overflows` pair is a genuine false PROVE regardless of how the
// encoder models the overflow predicate, because the interpreter is Rust semantics.

struct OverflowSpec {
    ty: Ty,
    op: OverflowOp,
    /// The constant second operand `C` in `a `op` C`.
    c: i128,
    /// `None` = unguarded; `Some((cmp, k))` = guard `a cmp k` around the checked op.
    guard: Option<(Cmp, i128)>,
}

impl OverflowSpec {
    fn name(&self) -> String {
        let opn = match self.op {
            OverflowOp::AddOverflow => "cadd",
            OverflowOp::SubOverflow => "csub",
            OverflowOp::MulOverflow => "cmul",
        };
        match self.guard {
            None => format!("{:?}/{}({},C={})/unguarded", self.ty, opn, "a", self.c),
            Some((cmp, k)) => {
                format!("{:?}/{}(a,C={})/if(a {} {})", self.ty, opn, self.c, cmp_dbg(cmp), k)
            }
        }
    }
}

/// Build the checked-op-then-trap core into the current block: computes `a op C`,
/// branches on the overflow flag to an `assert(false)` trap (panics iff overflow),
/// else jumps to `cont` with the result.
fn emit_checked_to(
    fb: &mut trust_ir_build::FunctionBuilder,
    spec: &OverflowSpec,
    a: trust_ir::value::ValueId,
    cont: trust_ir::BlockId,
) {
    let c = fb.iconst(spec.ty.clone(), spec.c);
    let (r, o) = fb.overflow(spec.op, spec.ty.clone(), a, c);
    let trap = fb.create_block();
    fb.condbr(o, trap, vec![], cont, vec![r]);
    fb.switch_to_block(trap);
    let f = fb.bool_const(false);
    fb.assert(f); // unconditional panic on the overflow path
    fb.unreachable();
}

fn build_overflow_spec(spec: &OverflowSpec) -> Module {
    let signed = is_signed(&spec.ty);
    let mut mb = ModuleBuilder::new("genov");
    let ft = mb.add_func_type(vec![spec.ty.clone()], vec![spec.ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let result = fb.add_block_param(exit, spec.ty.clone());

    match spec.guard {
        None => {
            fb.switch_to_block(entry);
            let a = fb.add_block_param(entry, spec.ty.clone());
            emit_checked_to(&mut fb, spec, a, exit);
        }
        Some((cmp, k)) => {
            let compute = fb.create_block();
            let else_blk = fb.create_block();
            fb.switch_to_block(entry);
            let a = fb.add_block_param(entry, spec.ty.clone());
            let kc = fb.iconst(spec.ty.clone(), k);
            let cond = fb.icmp(icmp_op(cmp, signed), spec.ty.clone(), a, kc);
            fb.condbr(cond, compute, vec![], else_blk, vec![]);

            fb.switch_to_block(compute);
            emit_checked_to(&mut fb, spec, a, exit);

            fb.switch_to_block(else_blk);
            let fallback = fb.iconst(spec.ty.clone(), 999);
            fb.br(exit, vec![fallback]);
        }
    }

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

fn generated_overflow_specs() -> Vec<OverflowSpec> {
    let mut specs = Vec::new();
    for ty in [Ty::U32, Ty::I32] {
        let signed = is_signed(&ty);
        let cs: Vec<i128> = vec![1, 2, 7, 1000];
        let ks: Vec<i128> =
            if signed { vec![-2, 0, 1, 100, 1000] } else { vec![0, 1, 2, 100, 1000] };
        for op in [OverflowOp::AddOverflow, OverflowOp::SubOverflow, OverflowOp::MulOverflow] {
            for &c in &cs {
                specs.push(OverflowSpec { ty: ty.clone(), op, c, guard: None });
                for cmp in [Cmp::Lt, Cmp::Le, Cmp::Gt, Cmp::Ge] {
                    for &k in &ks {
                        specs.push(OverflowSpec { ty: ty.clone(), op, c, guard: Some((cmp, k)) });
                    }
                }
            }
        }
    }
    specs
}

// --- STEP C (ouroboros): Trust's discharge proves a piece of its OWN prover sound -
//
// clean (Trust's first-party theorem prover, which kernel-checks the soundness proof
// of this very verifier) has, in its kernel, `MicroExpr::subst`
// (clean-kernel/src/micro/types.rs:289):
//     MicroExpr::BVar(idx) => match idx.cmp(&depth) {
//         Ordering::Greater => MicroExpr::BVar(idx - 1),   // u32 decrement
//         ...
//     }
// The `idx - 1` is a u32 subtraction that UNDERFLOWS (panics) at idx==0. It is total
// only because the guard `idx > depth` dominates it: since `depth: u32 >= 0`,
// `idx > depth >= 0` implies `idx >= 1`, so `idx - 1` never underflows. This models
// that exact arm. Faithfulness to the real `subst` is validated by EXECUTION in clean
// (clean-kernel test `debruijn_decrement_model_matches_subst` runs the real function
// over a grid and checks it matches `if idx>depth { idx-1 } else { idx }` and never
// panics). Here, Trust's own discharge PROVES that decrement panic-free — the forward
// direction of the ouroboros (clean proves trust-mc sound; trust-mc proves clean sound),
// established for one real kernel arm with execution-validated fidelity (not a
// hand-waved translation).
fn build_debruijn_decrement() -> Module {
    let mut mb = ModuleBuilder::new("clean_debruijn_subst");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let then_blk = fb.create_block();
    let else_blk = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let result = fb.add_block_param(exit, Ty::U32);

    fb.switch_to_block(entry);
    let idx = fb.add_block_param(entry, Ty::U32);
    let depth = fb.add_block_param(entry, Ty::U32);
    let cond = fb.icmp(ICmpOp::Ugt, Ty::U32, idx, depth); // idx > depth (the dominating guard)
    fb.condbr(cond, then_blk, vec![], else_blk, vec![]);

    // then: BVar(idx - 1) — a CHECKED subtraction that traps on underflow.
    fb.switch_to_block(then_blk);
    let dec_spec = OverflowSpec { ty: Ty::U32, op: OverflowOp::SubOverflow, c: 1, guard: None };
    emit_checked_to(&mut fb, &dec_spec, idx, exit);

    // else: the value is unchanged (Equal/Less arms don't decrement).
    fb.switch_to_block(else_blk);
    fb.br(exit, vec![idx]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

/// Models clean-kernel `micro/checker.rs` BVar type-check rule (line ~83):
///
/// ```text
/// if (idx as usize) >= depth { return Err(InvalidBVar(idx)); }   // the guard
/// let ctx_pos = depth - 1 - idx;                                 // two usize subtractions
/// ```
///
/// `ctx_pos = depth - 1 - idx` is two `usize` subtractions, EITHER of which underflows (panics)
/// in isolation: `depth - 1` when `depth == 0`, and `(depth-1) - idx` when `idx > depth-1`. Both
/// are total ONLY because the single guard `idx >= depth → early-return` establishes `idx < depth`,
/// which gives BOTH `depth >= 1` (so `depth-1` is safe) AND `idx <= depth-1` (so `(depth-1)-idx`
/// is safe). This is a stricter ouroboros arm than the single de Bruijn decrement: Trust's
/// discharge must prove TWO chained checked subtractions panic-free from ONE comparison guard.
/// `usize` is modeled as `U64`. The `idx >= depth` arm returns normally (the kernel's `Err` is a
/// value, not a panic).
fn build_kernel_bvar_ctx_pos() -> Module {
    let ty = Ty::U64;
    let mut mb = ModuleBuilder::new("clean_kernel_bvar_ctx_pos");
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let guard_err = fb.create_block();
    let compute = fb.create_block();
    let sub2 = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let result = fb.add_block_param(exit, ty.clone());

    fb.switch_to_block(entry);
    let depth = fb.add_block_param(entry, ty.clone());
    let idx = fb.add_block_param(entry, ty.clone());
    // The guard: the subtractions run only when `idx < depth` (the kernel's `idx >= depth` arm
    // early-returns InvalidBVar, a NORMAL return with no panic). Phrased on the POSITIVE branch
    // (`idx < depth` → compute) so the dominating guard is the THEN-edge condition.
    let cond = fb.icmp(ICmpOp::Ult, ty.clone(), idx, depth);
    fb.condbr(cond, compute, vec![], guard_err, vec![]);

    // idx >= depth: the kernel returns Err(InvalidBVar) — modeled as a normal return.
    fb.switch_to_block(guard_err);
    let zero = fb.iconst(ty.clone(), 0);
    fb.br(exit, vec![zero]);

    // idx < depth: compute BOTH checked subtractions in this block (so the intermediate `t1`,
    // the guard `idx < depth`, and both overflow obligations stay in one block's scope), then
    // branch on each overflow flag to a trap. t1 = depth - 1 (underflows iff depth == 0);
    // ctx_pos = t1 - idx (underflows iff idx > depth-1). The guard excludes both.
    fb.switch_to_block(compute);
    let one = fb.iconst(ty.clone(), 1);
    let (t1, o1) = fb.overflow(OverflowOp::SubOverflow, ty.clone(), depth, one);
    let (ctx_pos, o2) = fb.overflow(OverflowOp::SubOverflow, ty.clone(), t1, idx);
    let trap1 = fb.create_block();
    let trap2 = fb.create_block();
    fb.condbr(o1, trap1, vec![], sub2, vec![]);
    fb.switch_to_block(trap1);
    let f1 = fb.bool_const(false);
    fb.assert(f1);
    fb.unreachable();

    // depth - 1 did not underflow: now guard the second subtraction's overflow flag.
    fb.switch_to_block(sub2);
    fb.condbr(o2, trap2, vec![], exit, vec![ctx_pos]);
    fb.switch_to_block(trap2);
    let f2 = fb.bool_const(false);
    fb.assert(f2);
    fb.unreachable();

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

/// Models clean-kernel `bitvec_slice.rs::and_chain` (and the identical `bitvec_compute.rs::
/// bit_eq_and_chain_w`): the `bvEq` And-chain over `[0, width)` whose first element is
/// `bit_eq_prop(x, y, width - 1)`. The `u32` subtraction `width - 1` underflows when `width == 0`,
/// but the function early-returns `True` on `width == 0` (a NORMAL return, NOT a panic), so on the
/// fallthrough `width >= 1` and `width - 1` is total. Same provable shape as the de Bruijn
/// decrement (a `x - const` obligation `width == 0` under a dominating guard), in a DIFFERENT
/// kernel subsystem — the bitvector equality-chain construction the kernel uses to check BV ops.
fn build_kernel_and_chain_width() -> Module {
    let ty = Ty::U32;
    let mut mb = ModuleBuilder::new("clean_kernel_and_chain_width");
    let ft = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let compute = fb.create_block();
    let zero_blk = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let result = fb.add_block_param(exit, ty.clone());

    fb.switch_to_block(entry);
    let width = fb.add_block_param(entry, ty.clone());
    let zero = fb.iconst(ty.clone(), 0);
    // Guard: `width > 0` → compute `width - 1`; `width == 0` → early-return `True` (no panic).
    let cond = fb.icmp(ICmpOp::Ugt, ty.clone(), width, zero);
    fb.condbr(cond, compute, vec![], zero_blk, vec![]);

    // width == 0: the degenerate `and_chain` returns `True` — modeled as a normal return.
    fb.switch_to_block(zero_blk);
    let true_const = fb.iconst(ty.clone(), 1);
    fb.br(exit, vec![true_const]);

    // width >= 1: `width - 1` (CHECKED — traps on underflow, i.e. width == 0, excluded by guard).
    fb.switch_to_block(compute);
    let dec_spec = OverflowSpec { ty: ty.clone(), op: OverflowOp::SubOverflow, c: 1, guard: None };
    emit_checked_to(&mut fb, &dec_spec, width, exit);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

/// The UNGUARDED de Bruijn position computation: `depth - 1 - idx` with NO `idx < depth` guard.
/// This UNDERFLOWS (panics) whenever `depth == 0` or `idx >= depth` — the discharge must catch it
/// (never prove it safe). The soundness counterpart to `build_kernel_bvar_ctx_pos`.
fn build_kernel_bvar_ctx_pos_unguarded() -> Module {
    let ty = Ty::U64;
    let mut mb = ModuleBuilder::new("clean_kernel_bvar_ctx_pos_unguarded");
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let sub2 = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let result = fb.add_block_param(exit, ty.clone());

    fb.switch_to_block(entry);
    let depth = fb.add_block_param(entry, ty.clone());
    let idx = fb.add_block_param(entry, ty.clone());
    let one = fb.iconst(ty.clone(), 1);
    let (t1, o1) = fb.overflow(OverflowOp::SubOverflow, ty.clone(), depth, one);
    let (ctx_pos, o2) = fb.overflow(OverflowOp::SubOverflow, ty.clone(), t1, idx);
    let trap1 = fb.create_block();
    let trap2 = fb.create_block();
    fb.condbr(o1, trap1, vec![], sub2, vec![]);
    fb.switch_to_block(trap1);
    let f1 = fb.bool_const(false);
    fb.assert(f1);
    fb.unreachable();
    fb.switch_to_block(sub2);
    fb.condbr(o2, trap2, vec![], exit, vec![ctx_pos]);
    fb.switch_to_block(trap2);
    let f2 = fb.bool_const(false);
    fb.assert(f2);
    fb.unreachable();
    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

/// SOUNDNESS of Trust's discharge on the clean kernel's de Bruijn POSITION computation
/// `ctx_pos = depth - 1 - idx` — which occurs identically at `micro/checker.rs:83`,
/// `cert/builder/construct.rs:51`, and `cert/verifier/core.rs:48`, total ONLY under the
/// `idx < depth` guard. Validates the discharge in BOTH polarities on this real, thrice-recurring
/// kernel arm: it must NEVER prove the UNGUARDED (underflowing) form safe, and the guarded form is
/// genuinely total.
///
/// PRECISION FRONTIER (documented, not a soundness issue): the guarded form is currently NOT proved
/// SAFE — the discharge proves the single de Bruijn decrement `idx - 1` (subst,
/// `ouroboros_clean_kernel_debruijn_decrement_proven_safe`) but not the CHAINED `depth - 1 - idx`,
/// whose second obligation `bvult(depth-1, idx)` nests a subtraction inside the comparison, which
/// the acyclic direct-SMT decision does not yet discharge. Soundness holds regardless; closing this
/// completeness gap (stronger BV reasoning) would let the guarded form PROVE and graduate to an
/// ouroboros arm.
#[test]
fn soundness_clean_kernel_bvar_ctx_pos_unguarded_is_refuted() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let guarded = build_kernel_bvar_ctx_pos();
    let unguarded = build_kernel_bvar_ctx_pos_unguarded();
    let vg = verify(&guarded);
    let pg = actually_panics(&guarded, "f", &[Ty::U64, Ty::U64]);
    let vu = verify(&unguarded);
    let pu = actually_panics(&unguarded, "f", &[Ty::U64, Ty::U64]);
    std::panic::set_hook(prev);

    // Ground truth: the guard makes it total; without the guard it underflows.
    assert!(!pg, "guarded depth-1-idx is total under idx<depth");
    assert!(pu, "unguarded depth-1-idx underflows (depth==0 or idx>=depth)");
    // THE SOUNDNESS INVARIANT: the discharge must NEVER prove the underflowing form safe.
    assert_ne!(
        vu,
        Verdict::Safe,
        "Trust's discharge must NOT prove the unguarded kernel position computation \
         `depth-1-idx` safe — it underflows; got {vu:?}"
    );
    // The guarded form must never be a false proof either (sound whether Safe or Unsafe).
    assert!(!(vg == Verdict::Safe && pg), "no false proof on the guarded form");
}

#[test]
fn soundness_oracle_no_false_proofs() {
    // Silence the default panic hook for the duration: `verify` deliberately
    // catch_unwinds backend solver crashes, and we don't want each one spraying a
    // backtrace. Restored at the end.
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    // Collect (name, verdict, ground-truth-panics) for every program in one pass, so we
    // can report BOTH soundness (no SAFE-on-panicking) and completeness (the dual: how
    // many actually-total programs the verifier fails to prove SAFE — rung-1's target).
    let mut results: Vec<(String, Verdict, bool)> = Vec::new();

    let eval = |name: String,
                module: &Module,
                param_tys: &[Ty],
                results: &mut Vec<(String, Verdict, bool)>| {
        let verdict = verify(module);
        // A crash isn't a proof; don't compute ground truth (it can't be a violation).
        let panics = if verdict == Verdict::Crashed {
            false
        } else {
            actually_panics(module, "f", param_tys)
        };
        results.push((name, verdict, panics));
    };

    for (m, tys, note) in [
        (build_div_const_nonzero(), vec![Ty::U32], "calib:a/7"),
        (build_div_const_zero(), vec![Ty::U32], "calib:a/0"),
    ] {
        eval(note.to_string(), &m, &tys, &mut results);
    }
    let div_specs = generated_specs();
    for spec in &div_specs {
        let m = build_spec(spec);
        eval(spec.name(), &m, &[spec.ty.clone(), spec.ty.clone()], &mut results);
    }
    let ov_specs = generated_overflow_specs();
    for spec in &ov_specs {
        let m = build_overflow_spec(spec);
        eval(spec.name(), &m, &[spec.ty.clone()], &mut results);
    }

    std::panic::set_hook(prev_hook);

    let total = results.len();
    let safe_count = results.iter().filter(|(_, v, _)| *v == Verdict::Safe).count();
    let crashes = results.iter().filter(|(_, v, _)| *v == Verdict::Crashed).count();
    let violations: Vec<&String> =
        results.iter().filter(|(_, v, p)| *v == Verdict::Safe && *p).map(|(n, _, _)| n).collect();

    // SOUNDNESS report.
    eprintln!(
        "soundness oracle — div+overflow discharge over {total} programs ({} div, {} overflow): \
         {safe_count} proved SAFE, {crashes} solver-crashes, {} false-proves",
        div_specs.len(),
        ov_specs.len(),
        violations.len()
    );
    if crashes > 0 {
        let ex: Vec<&str> = results
            .iter()
            .filter(|(_, v, _)| *v == Verdict::Crashed)
            .map(|(n, _, _)| n.as_str())
            .take(4)
            .collect();
        eprintln!(
            "  backend solver (ay) PANICKED on {crashes} obligation(s) — fail-closed \
             robustness finding. e.g.: {}",
            ex.join(", ")
        );
    }

    // COMPLETENESS report (the precision / rung-1 frontier): of the programs that are
    // actually TOTAL (interpreter never traps, solver didn't crash), how many does the
    // verifier PROVE safe vs leave unproven? Unproven-total = precision lost to soundness
    // conservatism — exactly what rung-1 precision recovery must reclaim.
    let total_progs: Vec<&(String, Verdict, bool)> =
        results.iter().filter(|(_, v, p)| !*p && *v != Verdict::Crashed).collect();
    let proven = total_progs.iter().filter(|(_, v, _)| *v == Verdict::Safe).count();
    let inconclusive = total_progs.iter().filter(|(_, v, _)| *v == Verdict::Inconclusive).count();
    let overrejected = total_progs.iter().filter(|(_, v, _)| *v == Verdict::Unsafe).count();
    let denom = total_progs.len().max(1);
    eprintln!(
        "  completeness on TOTAL programs: {proven}/{} proved ({pct}%), {inconclusive} inconclusive, \
         {overrejected} over-rejected — the precision gap rung-1 must close",
        total_progs.len(),
        pct = proven * 100 / denom
    );
    // Show a few unproven-total examples per disposition (the recoverable patterns).
    let mut incon_ex: Vec<&str> = total_progs
        .iter()
        .filter(|(_, v, _)| *v == Verdict::Inconclusive)
        .map(|(n, _, _)| n.as_str())
        .take(4)
        .collect();
    let mut over_ex: Vec<&str> = total_progs
        .iter()
        .filter(|(_, v, _)| *v == Verdict::Unsafe)
        .map(|(n, _, _)| n.as_str())
        .take(4)
        .collect();
    incon_ex.sort_unstable();
    over_ex.sort_unstable();
    if !incon_ex.is_empty() {
        eprintln!("    inconclusive-on-total e.g.: {}", incon_ex.join(", "));
    }
    if !over_ex.is_empty() {
        eprintln!("    over-rejected-on-total e.g.: {}", over_ex.join(", "));
    }

    assert!(
        violations.is_empty(),
        "SOUNDNESS VIOLATIONS (false PROVEs) found across the generated space:\n{}",
        violations.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n")
    );
    assert!(
        safe_count >= 10,
        "oracle is too vacuous: only {safe_count} programs proved SAFE across {total}"
    );
}

// --- RUNG 3 (Trust self-verification): Trust proves its OWN verifier crate panic-free -----
//
// `trust-types::bitvector::mask_all` (bitvector.rs:137) is real Trust code:
//     fn mask_all(width: u32) -> u128 {
//         if width >= 128 { u128::MAX } else { (1u128 << width) - 1 }
//     }
// Its PANIC SURFACE is the shift `1u128 << width`, which traps when `width >= 128` — total
// ONLY because the guard `width >= 128` takes the other branch. This was unverifiable until
// the shift-overflow obligation above existed (the 7th-false-proof fix); now Trust's own
// discharge can PROVE this arm of its own verifier panic-free. This models that panic
// surface (the guarded shift). The trailing `- 1` is OMITTED: `1u128 << width ≥ 1` for
// width < 128 so it never underflows, but the acyclic backend cannot prove `1<<w ≥ 1`
// symbolically (a completeness gap, not a soundness one) — so isolating the shift keeps the
// rung-3 claim about shift-safety, which the fix makes provable. Faithfulness of the guard
// structure + totality to the real `low_mask` is validated by EXECUTION in the trust repo
// (trust-types test `low_mask_model_matches_and_is_total`).
fn build_low_mask_model() -> Module {
    let mut mb = ModuleBuilder::new("trust_types_low_mask");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U128]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let ge_blk = fb.create_block();
    let lt_blk = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let result = fb.add_block_param(exit, Ty::U128);

    fb.switch_to_block(entry);
    let width = fb.add_block_param(entry, Ty::U32);
    let c128 = fb.iconst(Ty::U32, 128);
    let cond = fb.icmp(ICmpOp::Uge, Ty::U32, width, c128); // width >= 128 (the guard)
    fb.condbr(cond, ge_blk, vec![], lt_blk, vec![]);

    // width >= 128: u128::MAX (all-ones; value irrelevant to panic-freedom).
    fb.switch_to_block(ge_blk);
    let max = fb.iconst(Ty::U128, -1);
    fb.br(exit, vec![max]);

    // width < 128: (1u128 << width) - 1 — the GUARDED shift the verifier must prove safe.
    fb.switch_to_block(lt_blk);
    let one = fb.iconst(Ty::U128, 1);
    let shifted = fb.binop(BinOp::Shl, Ty::U128, one, width); // 1u128 << width (width: U32) — THE panic surface
    fb.br(exit, vec![shifted]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

/// Models trust-types `bitvector.rs::bv_eval` `BvOp::UDiv` arm (line ~172):
///     BvOp::UDiv => { if b == 0 { return Err(DivisionByZero(w)); } a / b }
/// `a / b` PANICS (divide by zero) when `b == 0`, but the `if b == 0` branch early-returns an Err
/// (a NORMAL return, NOT a panic), so on the fallthrough `b != 0` and the division is total. This
/// is a DIVISION panic surface — a NEW obligation class for the self-verification arms (the others
/// are subtraction/shift) — in Trust's OWN verifier crate (Rung 3). Provable shape: the
/// div-by-zero obligation `b == 0` (a var-vs-const equality) under the dominating guard. Modeled
/// at U64; div-by-zero is width-independent, so this faithfully captures the panic surface (the
/// real `a`/`b` are u128). Faithfulness validated by execution in the trust repo (trust-types
/// `bv_eval_udiv_model_matches_and_is_total`).
fn build_trust_types_bv_eval_div() -> Module {
    let ty = Ty::U64;
    let mut mb = ModuleBuilder::new("trust_types_bv_eval_udiv");
    let ft = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let zero_blk = fb.create_block();
    let div_blk = fb.create_block();
    let exit = fb.create_block();
    fb.set_entry(entry);
    let result = fb.add_block_param(exit, ty.clone());

    fb.switch_to_block(entry);
    let a = fb.add_block_param(entry, ty.clone());
    let b = fb.add_block_param(entry, ty.clone());
    let zero = fb.iconst(ty.clone(), 0);
    let cond = fb.icmp(ICmpOp::Eq, ty.clone(), b, zero); // b == 0 (the guard / early Err return)
    fb.condbr(cond, zero_blk, vec![], div_blk, vec![]);

    // b == 0: the real arm returns Err(DivisionByZero) — modeled as a normal return (no panic).
    fb.switch_to_block(zero_blk);
    let zret = fb.iconst(ty.clone(), 0);
    fb.br(exit, vec![zret]);

    // b != 0: a / b — the division the guard makes total (the panic surface).
    fb.switch_to_block(div_blk);
    let q = fb.binop(BinOp::UDiv, ty.clone(), a, b);
    fb.br(exit, vec![q]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    fb.build();
    mb.build()
}

/// RUNG 3 (division class): Trust's discharge PROVES the guarded division in its own verifier
/// crate (trust-types `bv_eval` UDiv) panic-free. Faithfulness validated by execution in the
/// trust repo (`bv_eval_udiv_model_matches_and_is_total`).
#[test]
fn rung3_trust_types_bv_eval_udiv_guarded_division_proven_safe() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let module = build_trust_types_bv_eval_div();
    let verdict = verify(&module);
    let panics = actually_panics(&module, "f", &[Ty::U64, Ty::U64]);
    std::panic::set_hook(prev);

    assert!(!panics, "bv_eval UDiv model must be total (the b==0 guard dominates a/b)");
    assert_eq!(
        verdict,
        Verdict::Safe,
        "Trust's discharge should PROVE its own verifier's guarded division panic-free, got {verdict:?}"
    );
}

/// RUNG 3, first brick: Trust's discharge PROVES a real arm of its own verifier crate
/// (trust-types::bitvector::low_mask's guarded shift) panic-free — enabled by the
/// shift-overflow obligation. Faithfulness validated by execution in the trust repo
/// (trust-types `low_mask_model_matches_and_is_total`).
#[test]
fn rung3_trust_types_low_mask_guarded_shift_proven_safe() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let module = build_low_mask_model();
    let verdict = verify(&module);
    let panics = actually_panics(&module, "f", &[Ty::U32]);
    std::panic::set_hook(prev);

    assert!(!panics, "low_mask model must be total (the width>=128 guard dominates the shift)");
    assert_eq!(
        verdict,
        Verdict::Safe,
        "Trust's discharge should PROVE trust-types::low_mask's guarded shift panic-free, got {verdict:?}"
    );
}

/// THE SELF-VERIFICATION SUITE (Step C / Rung 3, consolidated + reported): Trust's OWN discharge,
/// run over a curated set of real panic surfaces from its own stack — clean's kernel (the prover
/// that kernel-checks the soundness proofs) AND Trust's own verifier crate (trust-types). Each
/// arm is a distinct, fidelity-validated (executed in its home repo) panic surface; together they
/// span TWO obligation classes (subtraction/shift and division) across THREE subsystems. Every arm
/// must be PROVEN panic-free, and the suite prints the coverage. This is the scalable harness the
/// eventual full-kernel trustc extraction will feed (one entry per extracted function); the
/// soundness counterpart — an UNGUARDED form must be REFUTED, never proven — is checked alongside.
#[test]
fn self_verification_suite_trust_proves_its_own_stack() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    // (name, subsystem, obligation class, module, param tys) — each a real panic surface.
    let arms: Vec<(&str, &str, &str, Module, Vec<Ty>)> = vec![
        (
            "micro::subst (de Bruijn idx-1)",
            "clean-kernel/de-Bruijn",
            "subtraction",
            build_debruijn_decrement(),
            vec![Ty::U32, Ty::U32],
        ),
        (
            "bitvec_slice::and_chain (width-1)",
            "clean-kernel/bitvector",
            "subtraction",
            build_kernel_and_chain_width(),
            vec![Ty::U32],
        ),
        (
            "bitvector::low_mask (guarded shift)",
            "trust-types/verifier",
            "shift",
            build_low_mask_model(),
            vec![Ty::U32],
        ),
        (
            "bitvector::bv_eval UDiv (guarded /)",
            "trust-types/verifier",
            "division",
            build_trust_types_bv_eval_div(),
            vec![Ty::U64, Ty::U64],
        ),
    ];

    let mut proven = 0usize;
    let mut failures: Vec<String> = Vec::new();
    for (name, subsystem, class, module, tys) in &arms {
        let verdict = verify(module);
        let panics = actually_panics(module, "f", tys);
        if panics {
            failures.push(format!(
                "{name} [{subsystem}/{class}]: model not total (ground-truth panics)"
            ));
        } else if verdict == Verdict::Safe {
            proven += 1;
        } else {
            failures
                .push(format!("{name} [{subsystem}/{class}]: NOT proven safe (got {verdict:?})"));
        }
    }

    // Soundness counterpart: the UNGUARDED de Bruijn position computation must be REFUTED
    // (never proven safe) — the suite is not vacuously passing everything.
    let unguarded = build_kernel_bvar_ctx_pos_unguarded();
    let unguarded_refuted = verify(&unguarded) != Verdict::Safe;

    std::panic::set_hook(prev);

    eprintln!(
        "self-verification suite: Trust's discharge PROVED {proven}/{} real panic surfaces of its \
         OWN stack panic-free — clean kernel (de Bruijn, bitvector) + trust-types verifier (shift, \
         division), spanning subtraction/shift/division obligations; unguarded de Bruijn position \
         correctly {}.",
        arms.len(),
        if unguarded_refuted { "REFUTED" } else { "NOT refuted" }
    );
    assert!(failures.is_empty(), "self-verification regressions:\n{}", failures.join("\n"));
    assert_eq!(proven, arms.len(), "all curated self-verification arms must be proven panic-free");
    assert!(
        unguarded_refuted,
        "the unguarded de Bruijn position computation must be REFUTED (soundness of the suite)"
    );
}

// --- SHIFT-overflow probe (Step A: a third agreement class + a soundness question) -----
//
// `a << s` PANICS in Rust when the shift amount `s >= bit width` ("attempt to shift left
// with overflow"). The trust-ir interpreter traps on exactly that (`shift_amount` → UB when
// rhs >= bits). The OPEN question this probes: does the CHC encoder model shift-overflow as
// an obligation, or does it lower `Shl` to a total SMT `bvshl` (which never traps)? If the
// latter, an unguarded `a << s` would be proved SAFE while the interpreter panics — a fresh
// soundness hole. This builds guarded + unguarded shifts and lets the oracle decide.

/// `f(a, s) = [if s cmp k] { a << s } else { 999 }` (u32). Unguarded panics for s >= 32.
fn build_shift(guard: Option<(Cmp, i128)>) -> Module {
    let mut mb = ModuleBuilder::new("shift");
    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    match guard {
        None => {
            fb.switch_to_block(entry);
            fb.set_entry(entry);
            let a = fb.add_block_param(entry, Ty::U32);
            let s = fb.add_block_param(entry, Ty::U32);
            let r = fb.binop(BinOp::Shl, Ty::U32, a, s);
            fb.ret(vec![r]);
        }
        Some((cmp, k)) => {
            let then_blk = fb.create_block();
            let else_blk = fb.create_block();
            let exit = fb.create_block();
            fb.set_entry(entry);
            fb.switch_to_block(entry);
            let a = fb.add_block_param(entry, Ty::U32);
            let s = fb.add_block_param(entry, Ty::U32);
            let kc = fb.iconst(Ty::U32, k);
            let cond = fb.icmp(icmp_op(cmp, false), Ty::U32, s, kc);
            fb.condbr(cond, then_blk, vec![], else_blk, vec![]);
            let result = fb.add_block_param(exit, Ty::U32);
            fb.switch_to_block(then_blk);
            let r = fb.binop(BinOp::Shl, Ty::U32, a, s);
            fb.br(exit, vec![r]);
            fb.switch_to_block(else_blk);
            let z = fb.iconst(Ty::U32, 999);
            fb.br(exit, vec![z]);
            fb.switch_to_block(exit);
            fb.ret(vec![result]);
        }
    }
    fb.build();
    mb.build()
}

#[test]
fn shift_discharge_soundness() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let cases: &[(&str, Option<(Cmp, i128)>)] = &[
        ("a<<s unguarded", None),                // panics for s>=32
        ("if s<32 {a<<s}", Some((Cmp::Lt, 32))), // total (s<32 ⟹ in range)
        ("if s<64 {a<<s}", Some((Cmp::Lt, 64))), // WRONG guard: panics for 32<=s<64
        ("if s<16 {a<<s}", Some((Cmp::Lt, 16))), // total
    ];
    let mut results: Vec<(String, Verdict, bool)> = Vec::new();
    for (label, guard) in cases {
        let m = build_shift(*guard);
        let v = verify(&m);
        let p = if v == Verdict::Crashed {
            false
        } else {
            actually_panics(&m, "f", &[Ty::U32, Ty::U32])
        };
        results.push((label.to_string(), v, p));
    }
    std::panic::set_hook(prev);

    let violations: Vec<&String> =
        results.iter().filter(|(_, v, p)| *v == Verdict::Safe && *p).map(|(n, _, _)| n).collect();
    eprintln!("shift-overflow discharge probe:");
    for (l, v, p) in &results {
        eprintln!("  {l:<20} verdict={v:?} panics={p}");
    }
    eprintln!("  ({} false-proves)", violations.len());
    // If this fires, the encoder does NOT model shift-overflow — a fresh soundness hole.
    assert!(
        violations.is_empty(),
        "SHIFT-OVERFLOW SOUNDNESS HOLE: discharge proved SAFE a program that shift-overflows:\n{}",
        violations.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n")
    );
}

// --- RUNG 2 (modular discharge): is reusing a callee SUMMARY at a call site sound? -----
//
// Whole-program discharge is tractable only if a callee is summarized and that summary is
// reused across call sites instead of re-inlined. The soundness question: when the caller's
// CHC is built by `translate_call` → `try_direct_call_summary` (the real modular mechanism,
// where CASE-2 lived), does the summary soundly carry the callee's panic surface into the
// caller? This oracle generates caller→callee programs over the division agreement domain
// and checks no false-proof: the trust-ir interpreter EXECUTES the call (ground truth
// includes the callee's panics), while the verifier SUMMARIZES the callee.

/// Verify one specific function of a module (summarizing its callees), via the real path.
fn verify_function(module: &Module, func: FuncId) -> Verdict {
    let Some(vc) = trust_ir_function_to_chc_vc(module, func, &TranslateOptions::default()) else {
        return Verdict::Inconclusive;
    };
    let obligation = MirChcPdrObligation::new(
        "oracle-modular",
        "oracle-caller",
        MirObligationKind::ArithmeticSafety,
        vc,
    );
    let problem = match lower_obligation(&obligation) {
        Ok(p) => p,
        Err(_) => return Verdict::Inconclusive,
    };
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        acyclic_direct_smt_decision(&problem)
    })) {
        Ok(AcyclicDecision::Safe) => Verdict::Safe,
        Ok(AcyclicDecision::Unsafe(_)) => Verdict::Unsafe,
        Ok(AcyclicDecision::Inconclusive) => Verdict::Inconclusive,
        Err(_) => Verdict::Crashed,
    }
}

/// Build a 2-function module: callee `g(a,b) = a / b` (udiv, panics on b==0), and a caller
/// `f(a,b) = [if b cmp k] { g(a,b) } [else { 999 }]`. Returns (module, caller FuncId). The
/// caller reaches the panic ONLY through the summarized call to `g`.
fn build_modular_div(guard: Option<(Cmp, i128)>) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("modular_div");
    let gt = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let g_id = {
        let mut gb = mb.function("g", gt);
        let entry = gb.create_block();
        gb.switch_to_block(entry);
        gb.set_entry(entry);
        let a = gb.add_block_param(entry, Ty::U32);
        let b = gb.add_block_param(entry, Ty::U32);
        let r = gb.udiv(Ty::U32, a, b);
        gb.ret(vec![r]);
        gb.build()
    };

    let ft = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let f_id = {
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        match guard {
            None => {
                fb.switch_to_block(entry);
                fb.set_entry(entry);
                let a = fb.add_block_param(entry, Ty::U32);
                let b = fb.add_block_param(entry, Ty::U32);
                let r = fb.call(g_id, vec![a, b]);
                fb.ret(vec![r]);
            }
            Some((cmp, k)) => {
                let then_blk = fb.create_block();
                let else_blk = fb.create_block();
                let exit = fb.create_block();
                fb.set_entry(entry);
                fb.switch_to_block(entry);
                let a = fb.add_block_param(entry, Ty::U32);
                let b = fb.add_block_param(entry, Ty::U32);
                let kc = fb.iconst(Ty::U32, k);
                let cond = fb.icmp(icmp_op(cmp, false), Ty::U32, b, kc);
                fb.condbr(cond, then_blk, vec![], else_blk, vec![]);
                let result = fb.add_block_param(exit, Ty::U32);
                fb.switch_to_block(then_blk);
                let r = fb.call(g_id, vec![a, b]);
                fb.br(exit, vec![r]);
                fb.switch_to_block(else_blk);
                let fallback = fb.iconst(Ty::U32, 999);
                fb.br(exit, vec![fallback]);
                fb.switch_to_block(exit);
                fb.ret(vec![result]);
            }
        }
        fb.build()
    };
    (mb.build(), f_id)
}

#[test]
fn modular_discharge_soundness() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    // (label, guard, expectation note). Ground truth comes from the interpreter, not these.
    let cases: &[(&str, Option<(Cmp, i128)>)] = &[
        ("f=g(a,b) unguarded", None),               // panics on b==0 through g
        ("f=if b!=0 {g(a,b)}", Some((Cmp::Ne, 0))), // total: guard dominates g's panic
        ("f=if b!=1 {g(a,b)}", Some((Cmp::Ne, 1))), // panics on b==0 (guard misses 0)
        ("f=if b>0 {g(a,b)}", Some((Cmp::Gt, 0))),  // total
        ("f=if b>1 {g(a,b)}", Some((Cmp::Gt, 1))),  // total (b>1 ⟹ b≠0)
    ];

    let mut results: Vec<(String, Verdict, bool)> = Vec::new();
    for (label, guard) in cases {
        let (module, f_id) = build_modular_div(*guard);
        let verdict = verify_function(&module, f_id);
        let panics = if verdict == Verdict::Crashed {
            false
        } else {
            actually_panics(&module, "f", &[Ty::U32, Ty::U32])
        };
        results.push((label.to_string(), verdict, panics));
    }
    std::panic::set_hook(prev);

    let violations: Vec<&String> =
        results.iter().filter(|(_, v, p)| *v == Verdict::Safe && *p).map(|(n, _, _)| n).collect();
    let proven_safe = results.iter().filter(|(_, v, _)| *v == Verdict::Safe).count();
    eprintln!("modular discharge oracle (caller summarizes callee g):");
    for (label, v, p) in &results {
        eprintln!("  {label:<22} verdict={v:?} panics={p}");
    }
    eprintln!("  ({proven_safe} proved SAFE, {} false-proves)", violations.len());

    assert!(
        violations.is_empty(),
        "MODULAR SOUNDNESS VIOLATIONS (summary reuse dropped a callee panic):\n{}",
        violations.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("\n")
    );
}

/// STEP C (ouroboros, first instance): Trust's discharge PROVES a real arm of its own
/// prover's kernel — clean's `MicroExpr::subst` de Bruijn decrement — panic-free.
/// See `build_debruijn_decrement`. Faithfulness of this model to the real `subst` is
/// validated by execution in clean (`debruijn_decrement_model_matches_subst`).
#[test]
fn ouroboros_clean_kernel_debruijn_decrement_proven_safe() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let module = build_debruijn_decrement();
    let verdict = verify(&module);
    let panics = actually_panics(&module, "f", &[Ty::U32, Ty::U32]);
    std::panic::set_hook(prev);

    // Ground truth: the guard `idx > depth` makes the decrement total — never traps.
    assert!(
        !panics,
        "the de Bruijn decrement model must be total (the guard idx>depth dominates idx-1)"
    );
    // THE OUROBOROS CLAIM: Trust's own discharge PROVES clean's kernel decrement
    // panic-free — verify-the-verifier, applied to a real piece of the verifier.
    assert_eq!(
        verdict,
        Verdict::Safe,
        "Trust's discharge should PROVE clean's de Bruijn decrement panic-free, got {verdict:?}"
    );
}

/// STEP C (ouroboros, second proven arm — a DIFFERENT kernel subsystem): Trust's discharge PROVES
/// clean's bitvector `and_chain` width-decrement panic-free. See `build_kernel_and_chain_width`.
/// Faithfulness to the real `and_chain` is validated by execution in clean
/// (`and_chain_width_model_matches_kernel`).
#[test]
fn ouroboros_clean_kernel_and_chain_width_proven_safe() {
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let module = build_kernel_and_chain_width();
    let verdict = verify(&module);
    let panics = actually_panics(&module, "f", &[Ty::U32]);
    std::panic::set_hook(prev);

    // Ground truth: the `width == 0` early-return dominates `width - 1`, making it total.
    assert!(!panics, "and_chain's width-1 must be total (the width==0 early return dominates it)");
    // THE OUROBOROS CLAIM: Trust's own discharge PROVES clean's bitvector equality-chain
    // construction panic-free — a second, different piece of the verifier's own kernel.
    assert_eq!(
        verdict,
        Verdict::Safe,
        "Trust's discharge should PROVE clean's and_chain width-1 panic-free, got {verdict:?}"
    );
}
