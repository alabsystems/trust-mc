// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Decision TMC-1's differential evidence (`docs/DECISION_QUEUE.md`): the
//! proof-grade lane against the trust-ir reference interpreter over randomly
//! generated array programs.
//!
//! Every generated program is one function `f` wrapped in a compiler-shaped
//! native bundle whose single request asks for `f`'s whole-function panic
//! freedom. For each program the harness runs, independently:
//!
//! * the PROOF-GRADE LANE exactly as a consumer does:
//!   `validate_native_bundle_proof_authority_input` (the gate) and then
//!   `NativeTrustIrChcPdrRunner::solve_bundle_native_proof_grade`, whose
//!   `obligations` are the privately authorized proofs and whose `refuted` rows
//!   are the witnessed refutations; plus, for every request the lane leaves
//!   `not_proved`, the engine's own verdict on the same translated obligation
//!   (`solve_typed_chc_pdr_full_verification`), so an acyclic direct-SMT
//!   refutation witness is replayed too;
//! * the GROUND TRUTH: `trust_ir::interpret::Interpreter` on every input of the
//!   program's domain — every value of the program's FIRST 8-bit parameter,
//!   boundary grids of the others (every length and guard constant of the
//!   program, plus and minus a few, the top bit, `-1`, the type's extremes), and
//!   several contents of an array parameter. The product of the INDEX parameters'
//!   domains (the indices and loop bounds, `Param::Index`) is always run in full;
//!   when the whole product exceeds `MAX_EXECUTIONS_PER_PROGRAM`, only the value
//!   parameters are sampled, per index tuple. "Complete" in a report therefore
//!   means the whole grid product, never the whole input space of a wide type. A
//!   trap is `Panic` (a failed `Assert`) or `UndefinedBehavior` (an out-of-bounds
//!   element access, a negative signed index).
//!
//! and asserts
//!
//! 1. the gate's verdict is the one the generator predicts from the program's
//!    structure (TMC-1: admitted exactly when every element read is of a
//!    non-empty tracked array, with an integer index, in a block no cycle
//!    reaches; the promoted cells of TMC-2 are admitted at every length);
//! 2. every PROVED request — every row an authorized proof, none refuted or left
//!    unproved — holds on every interpreted execution: no input of the domain
//!    traps, and no witness refutes it;
//! 3. every refutation witness — the `refuted` channel's, and the engine's own
//!    on a GROUNDED encoding (no translation havoc,
//!    `bounded_unroll::problem_is_grounded_for_refutation`) or, for a direct-SMT
//!    witness, along a derivation that reads no translation havoc under its
//!    model (`bounded_unroll::derivation_reads_translation_havoc`, the
//!    consumer's gate; how a large-block query is judged) — drives the
//!    interpreter to a trap once its entry values are decoded into inputs
//!    (`witness_entry_fact_assignment`; an input the derivation leaves free is
//!    replayed at every value of its domain); a `refuted`-channel witness must
//!    also pass the consumer's own independent replay
//!    (`independently_replay_typed_chc_pdr_refutation_witness_with_options`). An engine
//!    witness the consumer replay refuses is counted with its reason (see the
//!    partial-model note in `docs/DECISION_QUEUE.md`, TMC-1), and an ungrounded
//!    one is replayed and counted but asserted nothing about — unless the
//!    consumer's replay ACCEPTS it, since an accepted witness is a Failed verdict
//!    a consumer would surface: every accepted witness must trap;
//! 4. BEHIND THE GATE: a program the gate refuses is still translated and solved
//!    (`check_behind_the_gate`), and every witness the consumer accepts must trap.
//!    The refusal is defense in depth; the refutation lanes must be sound without
//!    it (the TMC-1 review's false refutation lived exactly there).
//!
//! The report line each family prints carries those counts; the assertions on
//! them (proofs and refutations actually happen) keep the check from passing
//! vacuously.
//!
//! The generator draws from a fixed seed, so every run checks the same
//! programs; the program families cover reads and writes at constant and
//! symbolic indices, narrow unsigned and signed index types (and `u128` and
//! `usize`), guards that are exact, off by one, or signed where the read is
//! not, unguarded out-of-bounds accesses, list literals, byte strings, splats,
//! constant splats, array parameters, nested arrays, loops that write
//! the array (and read it before, in or after the loop), promoted stack cells
//! across the retired 256-lane extent (TMC-2), and reads inside a summarized
//! callee; and, added by the TMC-1 review, arrays joined by a block parameter or
//! a `Select`, callees with their own branches and nested callees, reading
//! callees called from a loop (with `!=` properties), borrowed block-local cells,
//! arrays of tuples and of `bool`, arrays returned by a callee and read with a
//! widened index, and two reads of an array parameter. An array loaded through a
//! raw pointer parameter is a fixed case: the interpreter cannot be handed its
//! pointee from outside `f`, and the lane must leave it undecided.
//!
//! The whole sweep runs by default, deliberately: the owner's approval of TMC-1
//! is conditional on it, and a sweep that runs only on request is one that does
//! not run. `-- --skip array_gate_differential` leaves it out of a quick local
//! iteration.
//!
//! The only operations generated are the ones on which the interpreter and the
//! CHC encoding agree exactly — element reads and writes, splats, literals,
//! comparisons, `And`, widening casts, `Assert`, a `u64` loop counter that never
//! overflows: no bare `Add`/`Sub`/`Mul` of data (the interpreter wraps them, the
//! encoder checks them), no narrowing cast (the encoder checks a lossy one, the
//! interpreter wraps it), no `Assume` (the gate refuses it without source
//! authority).

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::time::Duration;

use trust_ir::inst::{BinOp, CastOp, ICmpOp};
use trust_ir::interpret::{
    ArrayValue, InterpretErrorCode, InterpretOptions, InterpretValue, InterpretValueKind,
    Interpreter,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{Constant, Module};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

use super::{
    DirectSmtRefutationReplayPayload, NativeSolveError, NativeTrustIrChcPdrRunner, bounded_unroll,
    independently_replay_typed_chc_pdr_refutation_witness_with_options,
    prepare_validated_typed_chc_pdr_input, solve_typed_chc_pdr_full_verification,
    validate_native_bundle_proof_authority_input,
};
use crate::direct_smt_cex::{AcyclicUnsafeWitness, witness_entry_fact_assignment};

/// Wall-clock budget of one solve. A program the engine does not decide in it is
/// an honest `not_proved`, which asserts nothing.
const SOLVE_TIMEOUT: Duration = Duration::from_secs(6);

/// The anchor's budget: its assertion that the proof HAPPENS must hold on a loaded
/// machine (the solve options carry no deterministic resource bound to use
/// instead), so it is far above the seconds the proof takes.
const ANCHOR_SOLVE_TIMEOUT: Duration = Duration::from_secs(120);

/// Interpreter fuel per execution: far above the longest generated loop.
const INTERPRETER_FUEL: u64 = 200_000;

/// Ceiling on the executions one program's ground truth takes. The domain is the
/// product of the per-parameter domains; past this many tuples the product is
/// SAMPLED (deterministically), and the report counts the executions run.
const MAX_EXECUTIONS_PER_PROGRAM: usize = 24_000;

// ---------------------------------------------------------------------------
// Deterministic randomness
// ---------------------------------------------------------------------------

/// SplitMix64: small, seedable, and good enough to pick program shapes.
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    fn pick<T: Clone>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize].clone()
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

// ---------------------------------------------------------------------------
// Integer helpers (a value is its raw bit pattern, masked to the type's width)
// ---------------------------------------------------------------------------

fn int_width(ty: &Ty) -> u32 {
    match ty {
        Ty::U8 | Ty::I8 => 8,
        Ty::U16 | Ty::I16 => 16,
        Ty::U32 | Ty::I32 => 32,
        Ty::U64 | Ty::I64 | Ty::Usize | Ty::Isize => 64,
        Ty::U128 | Ty::I128 => 128,
        other => panic!("not a generated integer type: {other}"),
    }
}

fn is_signed_int(ty: &Ty) -> bool {
    matches!(ty, Ty::I8 | Ty::I16 | Ty::I32 | Ty::I64 | Ty::Isize | Ty::I128)
}

fn int_mask(width: u32) -> u128 {
    if width == 128 { u128::MAX } else { (1u128 << width) - 1 }
}

/// `raw` (masked to `ty`) as the `i128` constant `iconst` takes for `ty`.
fn const_of(ty: &Ty, raw: u128) -> i128 {
    let width = int_width(ty);
    let raw = raw & int_mask(width);
    if is_signed_int(ty) && width < 128 && raw >> (width - 1) == 1 {
        (raw as i128) - (1i128 << width)
    } else {
        raw as i128
    }
}

/// The largest value of an unsigned reading of `ty` that `iconst` can spell, for
/// clamping a constant such as a guard bound: the type's maximum, or `i128::MAX`
/// for a 128-bit type.
fn max_spellable(ty: &Ty) -> u128 {
    let width = int_width(ty);
    if is_signed_int(ty) {
        int_mask(width) >> 1
    } else if width == 128 {
        i128::MAX as u128
    } else {
        int_mask(width)
    }
}

fn int_value(ty: &Ty, raw: u128) -> InterpretValue {
    InterpretValue::int(ty.clone(), raw as i128).expect("a generated integer value")
}

/// Every value of an 8-bit type; for a wider one, a boundary grid around the
/// program's own constants (`pivots`), the top bit, `-1` and the extremes.
fn int_domain(ty: &Ty, pivots: &[u128], exhaustive: bool) -> Vec<u128> {
    let width = int_width(ty);
    let mask = int_mask(width);
    if width <= 8 && exhaustive {
        return (0..=mask).collect();
    }
    let mut values = BTreeSet::new();
    for value in 0..=5u128 {
        values.insert(value & mask);
    }
    let top = 1u128 << (width - 1);
    for delta in 0..3u128 {
        values.insert(top.wrapping_add(delta) & mask);
        values.insert(top.wrapping_sub(delta) & mask);
        values.insert(mask.wrapping_sub(delta) & mask);
    }
    for bit in [7u32, 8, 15, 16, 31, 32, 63, 64, 127] {
        if bit < width {
            let power = 1u128 << bit;
            for value in [power - 1, power, power + 1] {
                values.insert(value & mask);
            }
        }
    }
    for &pivot in pivots {
        for delta in 0..3u128 {
            values.insert(pivot.wrapping_add(delta) & mask);
            values.insert(pivot.wrapping_sub(delta) & mask);
        }
        values.insert(pivot.wrapping_neg() & mask);
    }
    values.into_iter().collect()
}

// ---------------------------------------------------------------------------
// Generated programs
// ---------------------------------------------------------------------------

/// A parameter of the generated function `f`.
#[derive(Clone, Debug)]
enum Param {
    /// An integer that decides an element access: an index, or a loop bound. The
    /// ground truth enumerates the product of these parameters' domains in full.
    Index(Ty),
    /// An integer value (an element, a selector): sampled when the whole input
    /// product is larger than `MAX_EXECUTIONS_PER_PROGRAM`.
    Int(Ty),
    /// A fixed-size array of an integer element.
    Array { ty: Ty, elem: Ty, len: u64 },
}

/// What the gate must say about a program (TMC-1 / TMC-2).
#[derive(Clone, Debug, PartialEq, Eq)]
enum GateExpectation {
    Admitted,
    /// Refused at an `ExtractElement`, or at a `Call` that would fold one into a
    /// block a cycle reaches, for the named `ExtractElementReject` kind.
    RefusedRead(&'static str),
}

struct Program {
    label: String,
    module: Module,
    params: Vec<Param>,
    /// The program's own constants (lengths, guard bounds, lanes, values): the
    /// pivots the boundary grids are built around.
    pivots: Vec<u128>,
    gate: GateExpectation,
}

impl Param {
    /// The parameter's declared type.
    fn ty(&self) -> Ty {
        match self {
            Param::Index(ty) | Param::Int(ty) | Param::Array { ty, .. } => ty.clone(),
        }
    }
}

const INDEX_TYS: [Ty; 11] = [
    Ty::U8,
    Ty::I8,
    Ty::U16,
    Ty::I16,
    Ty::U32,
    Ty::I32,
    Ty::U64,
    Ty::I64,
    Ty::Usize,
    Ty::U128,
    Ty::I128,
];

const ELEM_TYS: [Ty; 4] = [Ty::U8, Ty::U32, Ty::I8, Ty::I64];

/// Lengths across the narrow index types' boundaries (127/128 for `i8`, 255/256
/// for `u8`) and the retired per-lane model's extent (256 lanes, 4096 leaves).
const LENGTHS: [u64; 16] = [1, 2, 3, 4, 5, 8, 100, 127, 128, 129, 200, 255, 256, 257, 300, 4097];

/// A builder-side view of one integer value and its type.
#[derive(Clone)]
struct IntVal {
    value: ValueId,
    ty: Ty,
}

/// The per-program building state: the program's constants, as they are made.
#[derive(Default)]
struct Pivots(Vec<u128>);

impl Pivots {
    fn note(&mut self, raw: u128) {
        self.0.push(raw);
    }
}

fn iconst(fb: &mut FunctionBuilder<'_>, pivots: &mut Pivots, ty: &Ty, raw: u128) -> IntVal {
    pivots.note(raw);
    IntVal { value: fb.iconst(ty.clone(), const_of(ty, raw)), ty: ty.clone() }
}

/// A constant lane below `len`, typed by a random integer type that can spell it.
fn const_index(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pivots: &mut Pivots,
    len: u64,
) -> IntVal {
    let lane = u128::from(rng.below(len));
    let candidates: Vec<Ty> =
        INDEX_TYS.iter().filter(|ty| lane <= max_spellable(ty)).cloned().collect();
    let ty = rng.pick(&candidates);
    iconst(fb, pivots, &ty, lane)
}

/// A symbolic index derived from the index parameter `base`: itself, masked with
/// a constant, or widened (sign-extended when `base` is signed, so a negative
/// index stays one — or turns huge in an unsigned wider type).
fn derived_index(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pivots: &mut Pivots,
    base: &IntVal,
    len: u64,
) -> IntVal {
    match rng.below(4) {
        0 | 1 => base.clone(),
        2 => {
            let width = int_width(&base.ty);
            let mask_raw = if rng.chance(50) {
                u128::from(len.next_power_of_two().saturating_sub(1)).min(int_mask(width))
            } else {
                u128::from(rng.below(1 << 10)) & int_mask(width)
            };
            let mask = iconst(fb, pivots, &base.ty, mask_raw);
            IntVal {
                value: fb.binop(BinOp::And, base.ty.clone(), base.value, mask.value),
                ty: base.ty.clone(),
            }
        }
        _ => {
            let width = int_width(&base.ty);
            let wider: Vec<Ty> =
                INDEX_TYS.iter().filter(|ty| int_width(ty) > width).cloned().collect();
            if wider.is_empty() {
                return base.clone();
            }
            let dst = rng.pick(&wider);
            let op = if is_signed_int(&base.ty) { CastOp::SExt } else { CastOp::ZExt };
            IntVal { value: fb.cast(op, base.ty.clone(), dst.clone(), base.value), ty: dst }
        }
    }
}

/// A guard on `index` against `len`: exact, off by one, or a SIGNED comparison
/// that lets a negative index through. Returns the Bool condition.
fn guard(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pivots: &mut Pivots,
    index: &IntVal,
    len: u64,
) -> ValueId {
    // Mostly exact (or one short), a third of the time one past the end.
    let bound = u128::from(match rng.below(10) {
        0..=1 => len.saturating_sub(1),
        2..=6 => len,
        _ => len + 1,
    })
    .min(max_spellable(&index.ty));
    let bound_v = iconst(fb, pivots, &index.ty, bound);
    if is_signed_int(&index.ty) {
        match rng.below(4) {
            // `index < bound` read signed: a negative index passes.
            0 => fb.icmp(ICmpOp::Slt, index.ty.clone(), index.value, bound_v.value),
            // `0 <= index < bound`, signed.
            1 | 2 => {
                let zero = iconst(fb, pivots, &index.ty, 0);
                let non_negative = fb.icmp(ICmpOp::Sge, index.ty.clone(), index.value, zero.value);
                let below = fb.icmp(ICmpOp::Slt, index.ty.clone(), index.value, bound_v.value);
                fb.binop(BinOp::And, Ty::Bool, non_negative, below)
            }
            // `index < bound` read unsigned: a negative index is huge and fails.
            _ => fb.icmp(ICmpOp::Ult, index.ty.clone(), index.value, bound_v.value),
        }
    } else {
        fb.icmp(ICmpOp::Ult, index.ty.clone(), index.value, bound_v.value)
    }
}

/// How an array value is built.
#[derive(Clone, Copy, Debug)]
enum Construct {
    SplatConst,
    SplatParam,
    ConstSplat,
    ConstList,
    Bytes,
    Param,
}

/// The constructions valid at `len` (trust-ir's one-spelling rule: a uniform
/// array of 2+ lanes is a splat, a splat has 2+ lanes, a list is not uniform).
///
/// `MakeAggregate` is not generated: at the pinned trust-ir it has no binary
/// encoding (the deferred INST wire batch), so a module holding one has no
/// `stable_digest` and cannot travel in a native bundle at all.
fn constructs_for(len: u64, elem: &Ty, with_x: bool) -> Vec<Construct> {
    let mut out = Vec::new();
    if len >= 2 {
        out.push(Construct::SplatConst);
        out.push(Construct::ConstSplat);
        if with_x {
            out.push(Construct::SplatParam);
        }
    }
    if len <= 6 {
        out.push(Construct::ConstList);
        if *elem == Ty::U8 {
            out.push(Construct::Bytes);
        }
    }
    if len <= 300 {
        out.push(Construct::Param);
    }
    out
}

/// Distinct raw lane values for a literal of `len` lanes (never uniform).
fn distinct_lanes(rng: &mut Rng, elem: &Ty, len: u64) -> Vec<u128> {
    let mask = int_mask(int_width(elem));
    let start = u128::from(rng.below(200));
    (0..u128::from(len)).map(|k| (start + k * 7 + 1) & mask).collect()
}

/// Build the array value. Returns it and every value an in-bounds lane of it can
/// hold, when the program spells them all (`None` for an array parameter, whose
/// content is the caller's). `x` is the element-typed value parameter, when the
/// program has one.
#[allow(clippy::too_many_arguments)]
fn build_array(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pivots: &mut Pivots,
    construct: Construct,
    arr: &Ty,
    elem: &Ty,
    len: u64,
    x: Option<ValueId>,
    array_param: Option<ValueId>,
) -> (ValueId, Option<Vec<Lane>>) {
    let mask = int_mask(int_width(elem));
    match construct {
        Construct::SplatConst => {
            let c = iconst(fb, pivots, elem, u128::from(rng.below(300)) & mask);
            (fb.array_splat(arr.clone(), c.value), Some(vec![Lane::Const(c.value)]))
        }
        Construct::SplatParam => {
            let x = x.expect("a value parameter");
            (fb.array_splat(arr.clone(), x), Some(vec![Lane::Value(x)]))
        }
        Construct::ConstSplat => {
            let c = u128::from(rng.below(300)) & mask;
            pivots.note(c);
            (
                fb.const_value(arr.clone(), Constant::splat(Constant::Int(const_of(elem, c)), len)),
                Some(vec![Lane::Raw(c)]),
            )
        }
        Construct::ConstList => {
            let lanes = distinct_lanes(rng, elem, len);
            for lane in &lanes {
                pivots.note(*lane);
            }
            (
                fb.const_value(
                    arr.clone(),
                    Constant::Array(
                        lanes.iter().map(|raw| Constant::Int(const_of(elem, *raw))).collect(),
                    ),
                ),
                Some(lanes.into_iter().map(Lane::Raw).collect()),
            )
        }
        Construct::Bytes => {
            let lanes = distinct_lanes(rng, elem, len);
            for lane in &lanes {
                pivots.note(*lane);
            }
            (
                fb.const_value(
                    arr.clone(),
                    Constant::Bytes {
                        data: lanes.iter().map(|raw| *raw as u8).collect(),
                        utf8: false,
                    },
                ),
                Some(lanes.into_iter().map(Lane::Raw).collect()),
            )
        }
        Construct::Param => (array_param.expect("an array parameter"), None),
    }
}

/// A value an in-bounds lane can hold, as the program spells it.
#[derive(Clone, Copy, Debug)]
enum Lane {
    /// An SSA value of the element type (a parameter, a constant already made).
    Value(ValueId),
    /// The raw bits of a constant not yet materialized as a value.
    Raw(u128),
    /// A constant already materialized.
    Const(ValueId),
}

/// An `Assert` on the read `read` (element type `elem`). `lanes` is every value an
/// in-bounds lane of the array can hold, when the program spells them all: then
/// the property is often the TRUE `read ∈ lanes` (a proof candidate whose only
/// possible violation is the access's own bounds), sometimes the trivially true
/// `read <= MAX`, otherwise a random comparison (usually false: a refutation
/// candidate).
fn assert_on_read(
    fb: &mut FunctionBuilder<'_>,
    rng: &mut Rng,
    pivots: &mut Pivots,
    elem: &Ty,
    read: ValueId,
    lanes: Option<&[Lane]>,
) {
    let mask = int_mask(int_width(elem));
    let roll = rng.below(100);
    let holds = match lanes {
        Some(lanes) if roll < 50 && !lanes.is_empty() => {
            let mut any = None;
            for lane in lanes {
                let value = match *lane {
                    Lane::Value(value) | Lane::Const(value) => value,
                    Lane::Raw(raw) => iconst(fb, pivots, elem, raw).value,
                };
                let equal = fb.icmp(ICmpOp::Eq, elem.clone(), read, value);
                any = Some(match any {
                    None => equal,
                    Some(before) => fb.binop(BinOp::Or, Ty::Bool, before, equal),
                });
            }
            any.expect("at least one lane")
        }
        _ if roll < 65 => {
            let max = iconst(fb, pivots, elem, mask);
            fb.icmp(ICmpOp::Ule, elem.clone(), read, max.value)
        }
        _ => {
            let raw = if rng.chance(50) && !pivots.0.is_empty() {
                let pick = rng.below(pivots.0.len() as u64) as usize;
                pivots.0[pick]
            } else {
                u128::from(rng.below(300))
            } & mask;
            let rhs = iconst(fb, pivots, elem, raw).value;
            let op = rng.pick(&[ICmpOp::Eq, ICmpOp::Ne, ICmpOp::Ule, ICmpOp::Uge]);
            fb.icmp(op, elem.clone(), read, rhs)
        }
    };
    fb.assert(holds);
}

/// Family A: straight-line (acyclic) reads and writes over one array, at
/// constant and symbolic indices, optionally under a guard.
fn gen_straight(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&ELEM_TYS);
    let len = rng.pick(&LENGTHS);
    let i_ty = rng.pick(&INDEX_TYS);
    let j_ty = rng.pick(&INDEX_TYS);
    let with_j = rng.chance(50);
    let with_x = rng.chance(70);
    let constructs = constructs_for(len, &elem, with_x);
    let construct = rng.pick(&constructs);

    let mut mb = ModuleBuilder::new(format!("tmc1_straight_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let mut params = Vec::new();
    if matches!(construct, Construct::Param) {
        params.push(Param::Array { ty: arr.clone(), elem: elem.clone(), len });
    }
    params.push(Param::Index(i_ty.clone()));
    if with_j {
        params.push(Param::Index(j_ty.clone()));
    }
    if with_x {
        params.push(Param::Int(elem.clone()));
    }
    let param_tys: Vec<Ty> = params.iter().map(Param::ty).collect();
    let ft = mb.add_func_type(param_tys.clone(), vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let values: Vec<ValueId> =
        param_tys.iter().map(|ty| fb.add_block_param(entry, ty.clone())).collect();
    let mut cursor = 0;
    let array_param = matches!(construct, Construct::Param).then(|| {
        cursor += 1;
        values[0]
    });
    let i = IntVal { value: values[cursor], ty: i_ty.clone() };
    cursor += 1;
    let j = with_j.then(|| {
        let j = IntVal { value: values[cursor], ty: j_ty.clone() };
        cursor += 1;
        j
    });
    let x = with_x.then(|| values[cursor]);

    let (a0, mut lanes) =
        build_array(&mut fb, rng, &mut pivots, construct, &arr, &elem, len, x, array_param);
    let write_index = if rng.chance(25) {
        const_index(&mut fb, rng, &mut pivots, len)
    } else {
        derived_index(&mut fb, rng, &mut pivots, &i, len)
    };
    let read_index = match rng.below(4) {
        0 => const_index(&mut fb, rng, &mut pivots, len),
        1 => match &j {
            Some(j) => derived_index(&mut fb, rng, &mut pivots, j, len),
            None => write_index.clone(),
        },
        _ => write_index.clone(),
    };
    let guarded = rng.chance(75);
    if guarded {
        // Both indices, or (sometimes) only one of them.
        let mut ok = guard(&mut fb, rng, &mut pivots, &write_index, len);
        if read_index.value != write_index.value && rng.chance(80) {
            let read_ok = guard(&mut fb, rng, &mut pivots, &read_index, len);
            ok = fb.binop(BinOp::And, Ty::Bool, ok, read_ok);
        }
        fb.condbr(ok, body, vec![], exit, vec![]);
    } else {
        fb.br(body, vec![]);
    }
    fb.switch_to_block(body);
    let write = rng.chance(75);
    let (array, written) = if write {
        let value = match x {
            Some(x) if rng.chance(70) => x,
            _ => {
                iconst(
                    &mut fb,
                    &mut pivots,
                    &elem,
                    u128::from(rng.below(300)) & int_mask(int_width(&elem)),
                )
                .value
            }
        };
        if let Some(lanes) = &mut lanes {
            lanes.push(Lane::Value(value));
        }
        (fb.insert_element(arr.clone(), a0, write_index.value, value), Some(value))
    } else {
        (a0, None)
    };
    let read = fb.extract_element(elem.clone(), array, read_index.value);
    // A read of the lane just written holds the written value whatever the array
    // held before; otherwise it holds one of the array's spelled lanes.
    let same_lane = written.filter(|_| read_index.value == write_index.value);
    let lanes = match same_lane {
        Some(value) => Some(vec![Lane::Value(value)]),
        None => lanes,
    };
    assert_on_read(&mut fb, rng, &mut pivots, &elem, read, lanes.as_deref());
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!(
            "straight#{id} [{elem}; {len}] {construct:?} i:{i_ty} j:{} x:{with_x} guarded:{guarded} write:{write}",
            if with_j { j_ty.to_string() } else { "-".to_string() }
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family B: nested arrays `[[E; m]; n]` — a row read, a lane write into it, the
/// row written back, and a read of a (possibly other) lane of a (possibly other)
/// row.
fn gen_nested(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32]);
    let row_len = rng.pick(&[2u64, 3, 4, 200, 257]);
    let rows = rng.pick(&[2u64, 3, 5, 256, 300]);
    let i_ty = rng.pick(&INDEX_TYS);
    let j_ty = rng.pick(&INDEX_TYS);
    let mut mb = ModuleBuilder::new(format!("tmc1_nested_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let row = Ty::Array(elem_id, row_len);
    let row_id = mb.add_type(row.clone());
    let grid = Ty::Array(row_id, rows);
    let params =
        vec![Param::Index(i_ty.clone()), Param::Index(j_ty.clone()), Param::Int(elem.clone())];
    let ft = mb.add_func_type(vec![i_ty.clone(), j_ty.clone(), elem.clone()], vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(row_len));
    pivots.note(u128::from(rows));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
    let j = IntVal { value: fb.add_block_param(entry, j_ty.clone()), ty: j_ty.clone() };
    let value_param = fb.add_block_param(entry, elem.clone());
    let fill = iconst(&mut fb, &mut pivots, &elem, u128::from(rng.below(250)));
    let inner = fb.array_splat(row.clone(), fill.value);
    let outer = fb.array_splat(grid.clone(), inner);
    let guarded = rng.chance(75);
    if guarded {
        let row_ok = guard(&mut fb, rng, &mut pivots, &i, rows);
        let lane_ok = guard(&mut fb, rng, &mut pivots, &j, row_len);
        let both = fb.binop(BinOp::And, Ty::Bool, row_ok, lane_ok);
        fb.condbr(both, body, vec![], exit, vec![]);
    } else {
        fb.br(body, vec![]);
    }
    fb.switch_to_block(body);
    let picked = fb.extract_element(row.clone(), outer, i.value);
    let row2 = fb.insert_element(row.clone(), picked, j.value, value_param);
    let outer2 = fb.insert_element(grid, outer, i.value, row2);
    let (row_index, lane_index) = match rng.below(3) {
        0 => (i.clone(), j.clone()),
        1 => (const_index(&mut fb, rng, &mut pivots, rows), j.clone()),
        _ => (i.clone(), const_index(&mut fb, rng, &mut pivots, row_len)),
    };
    let read_row = fb.extract_element(row, outer2, row_index.value);
    let read = fb.extract_element(elem.clone(), read_row, lane_index.value);
    let lanes = [Lane::Const(fill.value), Lane::Value(value_param)];
    assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!(
            "nested#{id} [[{elem}; {row_len}]; {rows}] i:{i_ty} j:{j_ty} guarded:{guarded}"
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Where a loop program reads its array.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LoopRead {
    /// No read: the loop's writes carry the only obligations.
    Nowhere,
    Before,
    Inside,
    After,
}

/// Family C: `a = [c; n]; [r0 = a[i]]; for k in 0..bound { a[k] = v; [a[k]] }; [a[j]]`,
/// the bound a constant around `n` or the parameter `p: u8`. A read inside or
/// after the loop is of a shape-only array: the gate must refuse it.
fn gen_loop(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32]);
    let len = rng.pick(&[2u64, 3, 4, 5, 8, 16]);
    let i_ty = rng.pick(&INDEX_TYS);
    let read_at = match rng.below(20) {
        0..=4 => LoopRead::Nowhere,
        5..=11 => LoopRead::Before,
        12..=15 => LoopRead::Inside,
        _ => LoopRead::After,
    };
    let param_bound = rng.chance(15);
    let mut mb = ModuleBuilder::new(format!("tmc1_loop_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let mut params = vec![Param::Index(i_ty.clone()), Param::Int(elem.clone())];
    if param_bound {
        params.push(Param::Index(Ty::U8));
    }
    let param_tys: Vec<Ty> = params.iter().map(Param::ty).collect();
    let ft = mb.add_func_type(param_tys.clone(), vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let head = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let values: Vec<ValueId> =
        param_tys.iter().map(|ty| fb.add_block_param(entry, ty.clone())).collect();
    let i = IntVal { value: values[0], ty: i_ty.clone() };
    let value_param = values[1];
    let fill = iconst(&mut fb, &mut pivots, &elem, u128::from(rng.below(250)));
    let a0 = fb.array_splat(arr.clone(), fill.value);
    if read_at == LoopRead::Before {
        let index = if rng.chance(50) {
            const_index(&mut fb, rng, &mut pivots, len)
        } else {
            derived_index(&mut fb, rng, &mut pivots, &i, len)
        };
        let read = fb.extract_element(elem.clone(), a0, index.value);
        assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&[Lane::Const(fill.value)]));
    }
    let bound = if param_bound {
        fb.cast(CastOp::ZExt, Ty::U8, Ty::U64, values[2])
    } else {
        let raw = u128::from(match rng.below(6) {
            0 | 1 => len - 1,
            2..=4 => len,
            _ => len + 1,
        });
        iconst(&mut fb, &mut pivots, &Ty::U64, raw).value
    };
    let start = fb.iconst(Ty::U64, 0);
    fb.br(head, vec![a0, start]);

    fb.switch_to_block(head);
    let carried = fb.add_block_param(head, arr.clone());
    let counter = fb.add_block_param(head, Ty::U64);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, counter, bound);
    fb.condbr(more, body, vec![carried, counter], exit, vec![carried]);

    fb.switch_to_block(body);
    let a_body = fb.add_block_param(body, arr.clone());
    let k_body = fb.add_block_param(body, Ty::U64);
    let value = if rng.chance(50) { value_param } else { fill.value };
    let a_next = fb.insert_element(arr.clone(), a_body, k_body, value);
    if read_at == LoopRead::Inside {
        let read = fb.extract_element(elem.clone(), a_next, k_body);
        assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&[Lane::Value(value)]));
    }
    let one = fb.iconst(Ty::U64, 1);
    let k_next = fb.binop(BinOp::Add, Ty::U64, k_body, one);
    fb.br(head, vec![a_next, k_next]);

    fb.switch_to_block(exit);
    let a_exit = fb.add_block_param(exit, arr.clone());
    if read_at == LoopRead::After {
        let index = derived_index(&mut fb, rng, &mut pivots, &i, len);
        let read = fb.extract_element(elem.clone(), a_exit, index.value);
        let lanes = [Lane::Const(fill.value), Lane::Value(value)];
        assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
    }
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!(
            "loop#{id} [{elem}; {len}] i:{i_ty} read:{read_at:?} bound:{}",
            if param_bound { "p:u8" } else { "const" }
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: match read_at {
            LoopRead::Nowhere | LoopRead::Before => GateExpectation::Admitted,
            LoopRead::Inside | LoopRead::After => GateExpectation::RefusedRead("shape_only_array"),
        },
    }
}

/// Family D (TMC-2): a stack cell of an array, promoted across blocks — stored in
/// the entry, written through a whole-cell load/store in the next block, read in
/// the last — at lengths on both sides of the retired 256-lane extent.
fn gen_cell(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32]);
    let len = rng.pick(&[2u64, 4, 255, 256, 257, 300, 4097]);
    let i_ty = rng.pick(&INDEX_TYS);
    let j_ty = rng.pick(&INDEX_TYS);
    let mut mb = ModuleBuilder::new(format!("tmc2_cell_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let params =
        vec![Param::Index(i_ty.clone()), Param::Index(j_ty.clone()), Param::Int(elem.clone())];
    let ft = mb.add_func_type(vec![i_ty.clone(), j_ty.clone(), elem.clone()], vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let mid = fb.create_block();
    let last = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
    let j = IntVal { value: fb.add_block_param(entry, j_ty.clone()), ty: j_ty.clone() };
    let value_param = fb.add_block_param(entry, elem.clone());
    let slot = fb.alloca(arr.clone());
    let fill = iconst(&mut fb, &mut pivots, &elem, u128::from(rng.below(250)));
    let v0 = fb.array_splat(arr.clone(), fill.value);
    fb.store(arr.clone(), slot, v0);
    let guarded = rng.chance(75);
    if guarded {
        let ok = guard(&mut fb, rng, &mut pivots, &i, len);
        fb.condbr(ok, mid, vec![], exit, vec![]);
    } else {
        fb.br(mid, vec![]);
    }
    fb.switch_to_block(mid);
    let loaded = fb.load(arr.clone(), slot);
    let v1 = fb.insert_element(arr.clone(), loaded, i.value, value_param);
    fb.store(arr.clone(), slot, v1);
    fb.br(last, vec![]);
    fb.switch_to_block(last);
    let reloaded = fb.load(arr.clone(), slot);
    let read_index = if rng.chance(70) { i.clone() } else { j.clone() };
    let read = fb.extract_element(elem.clone(), reloaded, read_index.value);
    let lanes = [Lane::Const(fill.value), Lane::Value(value_param)];
    assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!("cell#{id} [{elem}; {len}] i:{i_ty} j:{j_ty} guarded:{guarded}"),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family E: the read is in a callee `g(a, i) = a[i]` the caller may summarize
/// into its own CHC, so the callee's bounds obligation must reach the caller.
fn gen_callee(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32, Ty::I8]);
    let len = rng.pick(&[2u64, 3, 4, 100, 128, 200, 256, 257]);
    let i_ty = rng.pick(&INDEX_TYS);
    let mut mb = ModuleBuilder::new(format!("tmc1_callee_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let params = vec![Param::Index(i_ty.clone()), Param::Int(elem.clone())];
    let caller_ty = mb.add_func_type(vec![i_ty.clone(), elem.clone()], vec![]);
    let callee_ty = mb.add_func_type(vec![arr.clone(), i_ty.clone()], vec![elem.clone()]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let guarded = rng.chance(75);
    {
        let mut fb = mb.function("f", caller_ty);
        let entry = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
        let x = fb.add_block_param(entry, elem.clone());
        let c = iconst(&mut fb, &mut pivots, &elem, u128::from(rng.below(120)));
        let a0 = fb.array_splat(arr.clone(), c.value);
        let lane = const_index(&mut fb, rng, &mut pivots, len);
        let a1 = fb.insert_element(arr.clone(), a0, lane.value, x);
        if guarded {
            let ok = guard(&mut fb, rng, &mut pivots, &i, len);
            fb.condbr(ok, body, vec![], exit, vec![]);
        } else {
            fb.br(body, vec![]);
        }
        fb.switch_to_block(body);
        let read = fb.call(FuncId::new(1), vec![a1, i.value]);
        let lanes = [Lane::Const(c.value), Lane::Value(x)];
        assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
        fb.br(exit, vec![]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("g", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr);
        let i = fb.add_block_param(entry, i_ty.clone());
        let read = fb.extract_element(elem.clone(), a, i);
        fb.ret(vec![read]);
        fb.build();
    }
    Program {
        label: format!("callee#{id} [{elem}; {len}] i:{i_ty} guarded:{guarded}"),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family F: a SIMD vector read. The translator states its bounds rule (the
/// vector's lane count is its length) but does not model its lanes, so the read
/// is a fresh value, not a `select`: the gate must refuse it.
fn gen_vector(rng: &mut Rng, id: usize) -> Program {
    let lanes = rng.pick(&[2u32, 4, 8]);
    let i_ty = rng.pick(&[Ty::U32, Ty::U8, Ty::I32]);
    let mut mb = ModuleBuilder::new(format!("tmc1_vector_{id}"));
    let vector = Ty::Vector(Box::new(Ty::U32), lanes);
    let params = vec![Param::Index(i_ty.clone())];
    let ft = mb.add_func_type(vec![i_ty.clone()], vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(lanes));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = fb.add_block_param(entry, i_ty.clone());
    let v = fb.const_value(
        vector,
        Constant::Vector((0..lanes).map(|k| Constant::Int(i128::from(k) * 3 + 1)).collect()),
    );
    let read = fb.extract_element(Ty::U32, v, i);
    assert_on_read(&mut fb, rng, &mut pivots, &Ty::U32, read, None);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!("vector#{id} <{lanes} x u32> i:{i_ty}"),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::RefusedRead("not_an_smt_array"),
    }
}

/// The constructions of `constructs_for` that are not an array parameter.
fn non_param_constructs(len: u64, elem: &Ty) -> Vec<Construct> {
    constructs_for(len, elem, true)
        .into_iter()
        .filter(|construct| !matches!(construct, Construct::Param))
        .collect()
}

/// Family G (TMC-1 review): an acyclic JOIN of two different arrays — a block
/// parameter with two predecessors, or an array-typed `Select` — then a read in
/// the join's successor. Sometimes the property holds on only one side.
fn gen_join(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&ELEM_TYS);
    let len = rng.pick(&[1u64, 2, 3, 4, 8, 128, 129, 256, 257, 300]);
    let i_ty = rng.pick(&INDEX_TYS);
    let use_select = rng.chance(40);
    let mut mb = ModuleBuilder::new(format!("tmc1_join_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let params = vec![Param::Index(i_ty.clone()), Param::Int(elem.clone()), Param::Int(Ty::U8)];
    let ft = mb.add_func_type(params.iter().map(Param::ty).collect(), vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let join = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
    let x = fb.add_block_param(entry, elem.clone());
    let c = fb.add_block_param(entry, Ty::U8);
    let constructs = non_param_constructs(len, &elem);
    let construct = rng.pick(&constructs);
    let (a0, lanes0) =
        build_array(&mut fb, rng, &mut pivots, construct, &arr, &elem, len, Some(x), None);
    let lane = const_index(&mut fb, rng, &mut pivots, len);
    let a1 = fb.insert_element(arr.clone(), a0, lane.value, x);
    let half = iconst(&mut fb, &mut pivots, &Ty::U8, 128);
    let pick_left = fb.icmp(ICmpOp::Ult, Ty::U8, c, half.value);
    if use_select {
        let selected = fb.select(arr.clone(), pick_left, a0, a1);
        fb.br(join, vec![selected]);
    } else {
        let left = fb.create_block();
        let right = fb.create_block();
        fb.condbr(pick_left, left, vec![], right, vec![]);
        fb.switch_to_block(left);
        fb.br(join, vec![a0]);
        fb.switch_to_block(right);
        fb.br(join, vec![a1]);
    }
    fb.switch_to_block(join);
    let a = fb.add_block_param(join, arr.clone());
    let read_index = if rng.chance(30) {
        const_index(&mut fb, rng, &mut pivots, len)
    } else {
        derived_index(&mut fb, rng, &mut pivots, &i, len)
    };
    let guarded = rng.chance(70);
    if guarded {
        let ok = guard(&mut fb, rng, &mut pivots, &read_index, len);
        fb.condbr(ok, body, vec![], exit, vec![]);
    } else {
        fb.br(body, vec![]);
    }
    fb.switch_to_block(body);
    let read = fb.extract_element(elem.clone(), a, read_index.value);
    let mut lanes = lanes0;
    if let Some(lanes) = &mut lanes {
        lanes.push(Lane::Value(x));
    }
    let lanes = if rng.chance(25) { Some(vec![Lane::Value(x)]) } else { lanes };
    assert_on_read(&mut fb, rng, &mut pivots, &elem, read, lanes.as_deref());
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!(
            "join#{id} [{elem}; {len}] {construct:?} i:{i_ty} select:{use_select} guarded:{guarded}"
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family H (TMC-1 review): a summarized callee with its OWN control flow (a
/// guarded read with a fallback, in the callee or the caller), sometimes with a
/// NESTED callee doing the read (a summary at depth 1).
fn gen_callee_paths(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32, Ty::I8]);
    let len = rng.pick(&[2u64, 4, 127, 128, 129, 256, 257]);
    let i_ty = rng.pick(&INDEX_TYS);
    let nested = rng.chance(35);
    let guard_where = rng.below(3); // 0 none, 1 in the callee, 2 in the caller
    let mut mb = ModuleBuilder::new(format!("tmc1_callee_paths_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let params = vec![Param::Index(i_ty.clone()), Param::Int(elem.clone())];
    let caller_ty = mb.add_func_type(params.iter().map(Param::ty).collect(), vec![]);
    let callee_ty = mb.add_func_type(vec![arr.clone(), i_ty.clone()], vec![elem.clone()]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let fallback = u128::from(rng.below(100)) & int_mask(int_width(&elem));
    pivots.note(fallback);
    {
        let mut fb = mb.function("f", caller_ty);
        let entry = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
        let x = fb.add_block_param(entry, elem.clone());
        let c = iconst(&mut fb, &mut pivots, &elem, u128::from(rng.below(120)));
        let a0 = fb.array_splat(arr.clone(), c.value);
        let lane = const_index(&mut fb, rng, &mut pivots, len);
        let a1 = fb.insert_element(arr.clone(), a0, lane.value, x);
        if guard_where == 2 {
            let ok = guard(&mut fb, rng, &mut pivots, &i, len);
            fb.condbr(ok, body, vec![], exit, vec![]);
        } else {
            fb.br(body, vec![]);
        }
        fb.switch_to_block(body);
        let read = fb.call(FuncId::new(1), vec![a1, i.value]);
        let lanes = [Lane::Const(c.value), Lane::Value(x), Lane::Raw(fallback)];
        assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
        fb.br(exit, vec![]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("g", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr.clone());
        let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
        let read_in = |fb: &mut FunctionBuilder<'_>| {
            if nested {
                fb.call(FuncId::new(2), vec![a, i.value])
            } else {
                fb.extract_element(elem.clone(), a, i.value)
            }
        };
        if guard_where == 1 {
            let then_block = fb.create_block();
            let else_block = fb.create_block();
            let ok = guard(&mut fb, rng, &mut pivots, &i, len);
            fb.condbr(ok, then_block, vec![], else_block, vec![]);
            fb.switch_to_block(then_block);
            let read = read_in(&mut fb);
            fb.ret(vec![read]);
            fb.switch_to_block(else_block);
            let d = iconst(&mut fb, &mut pivots, &elem, fallback);
            fb.ret(vec![d.value]);
        } else {
            let read = read_in(&mut fb);
            fb.ret(vec![read]);
        }
        fb.build();
    }
    if nested {
        let mut fb = mb.function("h", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr.clone());
        let i = fb.add_block_param(entry, i_ty.clone());
        let read = fb.extract_element(elem.clone(), a, i);
        fb.ret(vec![read]);
        fb.build();
    }
    Program {
        label: format!(
            "callee_paths#{id} [{elem}; {len}] i:{i_ty} nested:{nested} guard_where:{guard_where}"
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family I (TMC-1 review): a reading callee `g(a, k) = a[k]` called from INSIDE
/// the caller's loop. The callee's read is acyclic in the callee, but the summary
/// runs in the call's block, where the caller carries arrays shape-only, so the
/// gate refuses the call (`shape_only_array_in_callee`). Half the properties are
/// `read != K` with `K` no lane holds — TRUE, and exactly the shape whose CHC
/// equates a translation havoc with `K`: behind the gate, no witness the consumer
/// accepts may "refute" it (`check_behind_the_gate`).
fn gen_callee_in_loop(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32]);
    let len = rng.pick(&[2u64, 3, 4, 5, 8, 16]);
    let carried = rng.chance(50);
    let param_bound = rng.chance(20);
    let mut mb = ModuleBuilder::new(format!("tmc1_callee_in_loop_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let mut params = vec![Param::Int(elem.clone())];
    if param_bound {
        params.push(Param::Index(Ty::U8));
    }
    let param_tys: Vec<Ty> = params.iter().map(Param::ty).collect();
    let caller_ty = mb.add_func_type(param_tys.clone(), vec![]);
    let callee_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![elem.clone()]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    {
        let mut fb = mb.function("f", caller_ty);
        let entry = fb.create_block();
        let head = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let values: Vec<ValueId> =
            param_tys.iter().map(|ty| fb.add_block_param(entry, ty.clone())).collect();
        let x = values[0];
        let c_raw = u128::from(rng.below(200));
        let c = iconst(&mut fb, &mut pivots, &elem, c_raw);
        let a0 = fb.array_splat(arr.clone(), c.value);
        let bound = if param_bound {
            fb.cast(CastOp::ZExt, Ty::U8, Ty::U64, values[1])
        } else {
            let raw = u128::from(match rng.below(6) {
                0 | 1 => len - 1,
                2..=4 => len,
                _ => len + 1,
            });
            iconst(&mut fb, &mut pivots, &Ty::U64, raw).value
        };
        let start = fb.iconst(Ty::U64, 0);
        if carried {
            fb.br(head, vec![a0, start]);
        } else {
            fb.br(head, vec![start]);
        }
        fb.switch_to_block(head);
        let a_head = carried.then(|| fb.add_block_param(head, arr.clone()));
        let k = fb.add_block_param(head, Ty::U64);
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, k, bound);
        match a_head {
            Some(a_head) => fb.condbr(more, body, vec![a_head, k], exit, vec![]),
            None => fb.condbr(more, body, vec![k], exit, vec![]),
        }
        fb.switch_to_block(body);
        let a_body = carried.then(|| fb.add_block_param(body, arr.clone()));
        let k_body = fb.add_block_param(body, Ty::U64);
        let (array, lanes) = match a_body {
            Some(a_body) => {
                // A write the loop carries: lane 0 holds `x` afterwards.
                let zero = fb.iconst(Ty::U64, 0);
                let written = fb.insert_element(arr.clone(), a_body, zero, x);
                (written, vec![Lane::Const(c.value), Lane::Value(x)])
            }
            None => (a0, vec![Lane::Const(c.value)]),
        };
        let read = fb.call(FuncId::new(1), vec![array, k_body]);
        if rng.chance(50) && !carried {
            // `read != K` with `K` no lane holds: true on every execution that
            // reads in bounds.
            let k_raw = (c_raw + 1 + u128::from(rng.below(50))) & int_mask(int_width(&elem));
            let k_value = iconst(&mut fb, &mut pivots, &elem, k_raw);
            let holds = fb.icmp(ICmpOp::Ne, elem.clone(), read, k_value.value);
            fb.assert(holds);
        } else {
            assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
        }
        let one = fb.iconst(Ty::U64, 1);
        let k_next = fb.binop(BinOp::Add, Ty::U64, k_body, one);
        if carried {
            fb.br(head, vec![array, k_next]);
        } else {
            fb.br(head, vec![k_next]);
        }
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("g", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr);
        let k = fb.add_block_param(entry, Ty::U64);
        let read = fb.extract_element(elem.clone(), a, k);
        fb.ret(vec![read]);
        fb.build();
    }
    Program {
        label: format!(
            "callee_in_loop#{id} [{elem}; {len}] carried:{carried} bound:{}",
            if param_bound { "p:u8" } else { "const" }
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::RefusedRead("shape_only_array_in_callee"),
    }
}

/// Family J (TMC-1 review): lane 4, an initialized block-local array cell written
/// and read through a reference alias, spelled as the compiler spells a reference
/// (a `Copy` of the cell's address; before 2026-10-08 a `Borrow`/`BorrowMut`).
fn gen_borrowed_cell(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32]);
    let len = rng.pick(&[2u64, 4, 255, 256, 257, 300, 4097]);
    let i_ty = rng.pick(&INDEX_TYS);
    let mutable = rng.chance(60);
    let mut mb = ModuleBuilder::new(format!("tmc1_borrowed_cell_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let params = vec![Param::Index(i_ty.clone()), Param::Int(elem.clone())];
    let ft = mb.add_func_type(params.iter().map(Param::ty).collect(), vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
    let x = fb.add_block_param(entry, elem.clone());
    let slot = fb.alloca(arr.clone());
    let c = iconst(&mut fb, &mut pivots, &elem, u128::from(rng.below(200)));
    let v0 = fb.array_splat(arr.clone(), c.value);
    fb.store(arr.clone(), slot, v0);
    let lanes;
    // The reference is spelled as the compiler spells one: a `Copy` of the cell's
    // address (trust-ir SPEC "A Rust reference carries no permission
    // instruction"; the MIR bridge's `&mut cell` / `&cell` since 2026-10-08). The
    // borrowed-cell lane admits it as an alias with no permission transition.
    let whole = if mutable {
        let alias = fb.copy(Ty::Ptr, slot);
        let loaded = fb.load(arr.clone(), alias);
        let lane = const_index(&mut fb, rng, &mut pivots, len);
        let written = fb.insert_element(arr.clone(), loaded, lane.value, x);
        fb.store(arr.clone(), alias, written);
        lanes = vec![Lane::Const(c.value), Lane::Value(x)];
        fb.load(arr.clone(), alias)
    } else {
        let alias = fb.copy(Ty::Ptr, slot);
        lanes = vec![Lane::Const(c.value)];
        fb.load(arr.clone(), alias)
    };
    let read_index = if rng.chance(40) {
        const_index(&mut fb, rng, &mut pivots, len)
    } else {
        derived_index(&mut fb, rng, &mut pivots, &i, len)
    };
    let read = fb.extract_element(elem.clone(), whole, read_index.value);
    assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!("borrowed_cell#{id} [{elem}; {len}] i:{i_ty} mutable:{mutable}"),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family K (TMC-1 review): an array of TUPLES `[(u8, u32); n]` — a tuple element
/// written, read, and projected.
fn gen_struct_elem(rng: &mut Rng, id: usize) -> Program {
    let len = rng.pick(&[2u64, 3, 4, 128, 129, 256, 257, 300]);
    let i_ty = rng.pick(&INDEX_TYS);
    let mut mb = ModuleBuilder::new(format!("tmc1_struct_elem_{id}"));
    let pair = Ty::Tuple(vec![Ty::U8, Ty::U32]);
    let pair_id = mb.add_type(pair.clone());
    let arr = Ty::Array(pair_id, len);
    let params = vec![Param::Index(i_ty.clone()), Param::Int(Ty::U8)];
    let ft = mb.add_func_type(params.iter().map(Param::ty).collect(), vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let c0 = u128::from(rng.below(200));
    let c1 = u128::from(rng.below(300));
    pivots.note(c0);
    pivots.note(c1);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
    let x = fb.add_block_param(entry, Ty::U8);
    let a0 = fb.const_value(
        arr.clone(),
        Constant::splat(
            Constant::Aggregate(vec![
                Constant::Int(const_of(&Ty::U8, c0)),
                Constant::Int(const_of(&Ty::U32, c1)),
            ]),
            len,
        ),
    );
    let t0 =
        fb.const_value(pair.clone(), Constant::Aggregate(vec![Constant::Int(0), Constant::Int(7)]));
    pivots.note(7);
    let t1 = fb.insert_field(pair.clone(), t0, 0, x);
    let lane = const_index(&mut fb, rng, &mut pivots, len);
    let a1 = fb.insert_element(arr.clone(), a0, lane.value, t1);
    let read_index = if rng.chance(30) {
        const_index(&mut fb, rng, &mut pivots, len)
    } else {
        derived_index(&mut fb, rng, &mut pivots, &i, len)
    };
    let guarded = rng.chance(70);
    if guarded {
        let ok = guard(&mut fb, rng, &mut pivots, &read_index, len);
        fb.condbr(ok, body, vec![], exit, vec![]);
    } else {
        fb.br(body, vec![]);
    }
    fb.switch_to_block(body);
    let element = fb.extract_element(pair.clone(), a1, read_index.value);
    if rng.chance(50) {
        let first = fb.extract_field(Ty::U8, element, 0);
        let lanes = [Lane::Raw(c0), Lane::Value(x)];
        assert_on_read(&mut fb, rng, &mut pivots, &Ty::U8, first, Some(&lanes));
    } else {
        let second = fb.extract_field(Ty::U32, element, 1);
        let lanes = [Lane::Raw(c1), Lane::Raw(7)];
        assert_on_read(&mut fb, rng, &mut pivots, &Ty::U32, second, Some(&lanes));
    }
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!("struct_elem#{id} [(u8, u32); {len}] i:{i_ty} guarded:{guarded}"),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family L (TMC-1 review): an array of `bool`, from a constant splat or an
/// `ArraySplat`, one lane written with a comparison's result.
fn gen_bool_elem(rng: &mut Rng, id: usize) -> Program {
    let len = rng.pick(&[2u64, 3, 4, 128, 129, 256, 257]);
    let i_ty = rng.pick(&INDEX_TYS);
    let fill = rng.chance(50);
    let mut mb = ModuleBuilder::new(format!("tmc1_bool_elem_{id}"));
    let bool_id = mb.add_type(Ty::Bool);
    let arr = Ty::Array(bool_id, len);
    let params = vec![Param::Index(i_ty.clone()), Param::Int(Ty::U8)];
    let ft = mb.add_func_type(params.iter().map(Param::ty).collect(), vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
    let p = fb.add_block_param(entry, Ty::U8);
    let a0 = if rng.chance(50) {
        fb.const_value(arr.clone(), Constant::splat(Constant::Bool(fill), len))
    } else {
        let b = fb.bool_const(fill);
        fb.array_splat(arr.clone(), b)
    };
    let threshold = iconst(&mut fb, &mut pivots, &Ty::U8, u128::from(rng.below(256)));
    let x = fb.icmp(ICmpOp::Ult, Ty::U8, p, threshold.value);
    let lane = const_index(&mut fb, rng, &mut pivots, len);
    let a1 = fb.insert_element(arr.clone(), a0, lane.value, x);
    let read_index = if rng.chance(30) {
        const_index(&mut fb, rng, &mut pivots, len)
    } else {
        derived_index(&mut fb, rng, &mut pivots, &i, len)
    };
    let guarded = rng.chance(70);
    if guarded {
        let ok = guard(&mut fb, rng, &mut pivots, &read_index, len);
        fb.condbr(ok, body, vec![], exit, vec![]);
    } else {
        fb.br(body, vec![]);
    }
    fb.switch_to_block(body);
    let read = fb.extract_element(Ty::Bool, a1, read_index.value);
    let truth = fb.bool_const(true);
    let holds = match rng.below(4) {
        0 => read,
        1 => fb.binop(BinOp::Xor, Ty::Bool, read, truth),
        // read == x || read == fill: true whenever in bounds.
        2 => {
            let same_x = fb.binop(BinOp::Xor, Ty::Bool, read, x);
            let same_x = fb.binop(BinOp::Xor, Ty::Bool, same_x, truth);
            let fill_v = fb.bool_const(fill);
            let same_fill = fb.binop(BinOp::Xor, Ty::Bool, read, fill_v);
            let same_fill = fb.binop(BinOp::Xor, Ty::Bool, same_fill, truth);
            fb.binop(BinOp::Or, Ty::Bool, same_x, same_fill)
        }
        // read == fill: false when the written lane is read and x != fill.
        _ => {
            let fill_v = fb.bool_const(fill);
            let same_fill = fb.binop(BinOp::Xor, Ty::Bool, read, fill_v);
            fb.binop(BinOp::Xor, Ty::Bool, same_fill, truth)
        }
    };
    fb.assert(holds);
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!("bool_elem#{id} [bool; {len}] fill:{fill} i:{i_ty} guarded:{guarded}"),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family M (TMC-1 review): an array RETURNED by a callee (`pass(a) = a`), read
/// in the caller or by a second callee that first widens its signed or unsigned
/// index (`SExt`/`ZExt`).
fn gen_callee_passthrough(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&[Ty::U8, Ty::U32]);
    let len = rng.pick(&[2u64, 4, 127, 128, 129, 255, 256, 257, 300]);
    let i_ty = rng.pick(&[Ty::I8, Ty::I16, Ty::U8, Ty::I32]);
    let widen_op = if rng.chance(50) { CastOp::SExt } else { CastOp::ZExt };
    let widen_to = rng.pick(&[Ty::U64, Ty::I64, Ty::Usize, Ty::I128]);
    let mut mb = ModuleBuilder::new(format!("tmc1_passthrough_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let params = vec![Param::Index(i_ty.clone()), Param::Int(elem.clone())];
    let caller_ty = mb.add_func_type(params.iter().map(Param::ty).collect(), vec![]);
    let pass_ty = mb.add_func_type(vec![arr.clone()], vec![arr.clone()]);
    let read_ty = mb.add_func_type(vec![arr.clone(), i_ty.clone()], vec![elem.clone()]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let via_read_callee = rng.chance(50);
    {
        let mut fb = mb.function("f", caller_ty);
        let entry = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
        let x = fb.add_block_param(entry, elem.clone());
        let c = iconst(&mut fb, &mut pivots, &elem, u128::from(rng.below(200)));
        let a0 = fb.array_splat(arr.clone(), c.value);
        let lane = const_index(&mut fb, rng, &mut pivots, len);
        let a1 = fb.insert_element(arr.clone(), a0, lane.value, x);
        let b = fb.call(FuncId::new(1), vec![a1]);
        let guarded = rng.chance(70);
        if guarded {
            let ok = guard(&mut fb, rng, &mut pivots, &i, len);
            fb.condbr(ok, body, vec![], exit, vec![]);
        } else {
            fb.br(body, vec![]);
        }
        fb.switch_to_block(body);
        let read = if via_read_callee {
            fb.call(FuncId::new(2), vec![b, i.value])
        } else {
            fb.extract_element(elem.clone(), b, i.value)
        };
        let lanes = [Lane::Const(c.value), Lane::Value(x)];
        assert_on_read(&mut fb, rng, &mut pivots, &elem, read, Some(&lanes));
        fb.br(exit, vec![]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("pass", pass_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr.clone());
        fb.ret(vec![a]);
        fb.build();
    }
    {
        let mut fb = mb.function("read", read_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr.clone());
        let i = fb.add_block_param(entry, i_ty.clone());
        let wide = fb.cast(widen_op, i_ty.clone(), widen_to.clone(), i);
        let read = fb.extract_element(elem.clone(), a, wide);
        fb.ret(vec![read]);
        fb.build();
    }
    Program {
        label: format!(
            "passthrough#{id} [{elem}; {len}] i:{i_ty} read_callee:{via_read_callee} widen:{widen_op:?}->{widen_to}"
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// Family N (TMC-1 review): two reads of an array PARAMETER in different blocks,
/// related by a comparison.
fn gen_two_reads(rng: &mut Rng, id: usize) -> Program {
    let elem = rng.pick(&ELEM_TYS);
    let len = rng.pick(&[1u64, 2, 3, 4, 8, 100, 128, 129, 200, 256, 257, 300]);
    let i_ty = rng.pick(&INDEX_TYS);
    let j_ty = rng.pick(&INDEX_TYS);
    let mut mb = ModuleBuilder::new(format!("tmc1_two_reads_{id}"));
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, len);
    let params = vec![
        Param::Array { ty: arr.clone(), elem: elem.clone(), len },
        Param::Index(i_ty.clone()),
        Param::Index(j_ty.clone()),
    ];
    let ft = mb.add_func_type(params.iter().map(Param::ty).collect(), vec![]);
    let mut pivots = Pivots::default();
    pivots.note(u128::from(len));
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let first = fb.create_block();
    let second = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let a = fb.add_block_param(entry, arr.clone());
    let i = IntVal { value: fb.add_block_param(entry, i_ty.clone()), ty: i_ty.clone() };
    let j = IntVal { value: fb.add_block_param(entry, j_ty.clone()), ty: j_ty.clone() };
    let ok_i = guard(&mut fb, rng, &mut pivots, &i, len);
    fb.condbr(ok_i, first, vec![], exit, vec![]);
    fb.switch_to_block(first);
    let r1 = fb.extract_element(elem.clone(), a, i.value);
    let second_index = if rng.chance(50) { i.clone() } else { j.clone() };
    let ok_second = guard(&mut fb, rng, &mut pivots, &second_index, len);
    fb.condbr(ok_second, second, vec![], exit, vec![]);
    fb.switch_to_block(second);
    let r2 = fb.extract_element(elem.clone(), a, second_index.value);
    let op = rng.pick(&[ICmpOp::Eq, ICmpOp::Ne, ICmpOp::Ule, ICmpOp::Uge]);
    let holds = fb.icmp(op, elem.clone(), r1, r2);
    fb.assert(holds);
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    Program {
        label: format!(
            "two_reads#{id} [{elem}; {len}] i:{i_ty} j:{j_ty} same:{} op:{op:?}",
            second_index.value == i.value
        ),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params,
        pivots: pivots.0,
        gate: GateExpectation::Admitted,
    }
}

/// The TMC-1 review's counterexample program, SAFE on every input:
/// `a = [19u32; 5]; for k in 0..bound { assert(g(a, k) != 263) }` with
/// `g(a, k) = a[k]`, or the same read written directly in the loop body.
fn safe_loop_program(bound: i128, via_callee: bool) -> Program {
    let mut mb = ModuleBuilder::new(format!("tmc1_review_safe_loop_{bound}_{via_callee}"));
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 5);
    let caller_ty = mb.add_func_type(vec![Ty::U8], vec![]);
    let callee_ty = mb.add_func_type(vec![arr.clone(), Ty::U64], vec![Ty::U32]);
    {
        let mut fb = mb.function("f", caller_ty);
        let entry = fb.create_block();
        let head = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let _p = fb.add_block_param(entry, Ty::U8);
        let nineteen = fb.iconst(Ty::U32, 19);
        let a = fb.array_splat(arr.clone(), nineteen);
        let limit = fb.iconst(Ty::U64, bound);
        let start = fb.iconst(Ty::U64, 0);
        fb.br(head, vec![start]);
        fb.switch_to_block(head);
        let k = fb.add_block_param(head, Ty::U64);
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, k, limit);
        fb.condbr(more, body, vec![k], exit, vec![]);
        fb.switch_to_block(body);
        let k_body = fb.add_block_param(body, Ty::U64);
        let read = if via_callee {
            fb.call(FuncId::new(1), vec![a, k_body])
        } else {
            fb.extract_element(Ty::U32, a, k_body)
        };
        let bad = fb.iconst(Ty::U32, 263);
        let ok = fb.icmp(ICmpOp::Ne, Ty::U32, read, bad);
        fb.assert(ok);
        let one = fb.iconst(Ty::U64, 1);
        let next = fb.binop(BinOp::Add, Ty::U64, k_body, one);
        fb.br(head, vec![next]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
    }
    {
        let mut fb = mb.function("g", callee_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let a = fb.add_block_param(entry, arr);
        let k = fb.add_block_param(entry, Ty::U64);
        let read = fb.extract_element(Ty::U32, a, k);
        fb.ret(vec![read]);
        fb.build();
    }
    Program {
        label: format!("review safe loop bound={bound} via_callee={via_callee}"),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params: vec![Param::Int(Ty::U8)],
        pivots: vec![5, 19, 263],
        gate: GateExpectation::RefusedRead(if via_callee {
            "shape_only_array_in_callee"
        } else {
            "shape_only_array"
        }),
    }
}

// ---------------------------------------------------------------------------
// The bundle around a program (the shape the compiler emits)
// ---------------------------------------------------------------------------

fn bundle_of(program: &Program) -> trust_ir::NativeVerificationBundle {
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

    let source_digest = ProofDigest::sha256([0x51; 32]);
    let mut module = program.module.clone();
    let function =
        module.functions.iter().find(|function| function.name == "f").expect("f is generated").id;
    let public_id = format!("vc:trust-mc-driver:tmc1-differential:{}", program.module.name);
    module.proof_obligations.push(
        ProofObligation::new(
            ProofId::new(0),
            ObligationKind::PanicFreedom,
            ProofStatus::Pending,
            "the generated array program is panic- and UB-free",
        )
        .with_formula(ProofFormula::smtlib2("tmc1_f_safe", "Bool"))
        .with_function(function)
        .with_source(
            trust_ir::ProofObligationSourceIdentity::new(
                format!("rust:{}::f", program.module.name),
                "assertion:0",
            )
            .with_public(trust_ir::PublicObligationIdentity {
                obligation_id: public_id.clone(),
                semantic_digest: ProofDigest::sha256_domain(
                    "trust-mc-driver.tmc1-differential.public-obligation.v1",
                    program.module.name.as_bytes(),
                ),
            }),
        ),
    );
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("sysv64".to_string()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let digest = module.stable_digest();
    let mut node = ProofLineageNode::new(
        ProofLineageId::new(0),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "rustc-mir-to-trust_ir",
            "tRust",
            "native-request-schema-v1",
        ),
        source_digest,
        digest,
    );
    node.obligations.push(ProofId::new(0));
    let lineage = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        nodes: vec![node],
        roots: vec![ProofLineageId::new(0)],
    };
    let mut bundle = NativeVerificationBundle::new(
        NativeBundleProducer::TRust,
        NativeAdapterInput::RustMir { body_digest: source_digest },
        digest,
        module,
        lineage,
    );
    let span = trust_ir::SourceSpan { file: 0, line: 1, col: 1 };
    bundle.compiler_facts = NativeCompilerFacts {
        monomorphizations: vec![NativeMonomorphizationFact {
            id: NativeMonomorphizationId::new(0),
            source_item: format!("{}::f", program.module.name),
            symbol: format!("_RNvC{}1f", program.module.name.len()),
            generic_args: Vec::new(),
            function: Some(function),
            stable_digest: ProofDigest::sha256([0x53; 32]),
        }],
        obligation_sources: vec![NativeObligationSource {
            obligation: ProofId::new(0),
            public_obligation_id: public_id,
            function: Some(function),
            span: Some(span),
            assertion_id: Some(NativeAssertionId::new(0)),
            cause: NativeObligationCause::Assert,
            monomorphization: Some(NativeMonomorphizationId::new(0)),
            facts: vec![NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(0))],
        }],
        ..NativeCompilerFacts::default()
    };
    bundle.requests.push(NativeVerificationRequest::TrustMc(TrustMcNativeRequest {
        id: NativeRequestId::new(0),
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
            ProofReplayIdentity::new("trust-mc", "tmc1 differential replay")
                .with_transcript_digest(ProofDigest::sha256([0x54; 32])),
        )
        .with_replay_context(
            NativeReplayContext::default().with_atom(
                NativeReplayAtom::assertion(
                    NativeReplayAtomId::new(0),
                    ProofFormula::smtlib2("tmc1_f_safe", "Bool"),
                )
                .with_obligation(ProofId::new(0))
                .with_assertion_id(NativeAssertionId::new(0))
                .with_span(span),
            ),
        ),
    }));
    bundle
}

// ---------------------------------------------------------------------------
// Ground truth: the reference interpreter
// ---------------------------------------------------------------------------

/// One interpreted execution.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Execution {
    Completed,
    /// A trap: `Panic` (a failed `Assert`) or `UndefinedBehavior`.
    Trap(InterpretErrorCode, String),
    /// Anything else the interpreter reports: an incapacity, never a verdict.
    Incapable(InterpretErrorCode, String),
}

fn execute(module: &Module, args: Vec<InterpretValue>) -> Execution {
    let function = module.function_by_name("f").expect("f is generated");
    let interpreter = Interpreter::with_module(module)
        .with_options(InterpretOptions { fuel: INTERPRETER_FUEL, ..InterpretOptions::default() });
    match interpreter.execute_function(function, args) {
        Ok(_) => Execution::Completed,
        Err(error)
            if matches!(
                error.code,
                InterpretErrorCode::Panic | InterpretErrorCode::UndefinedBehavior
            ) =>
        {
            Execution::Trap(error.code, error.message)
        }
        Err(error) => Execution::Incapable(error.code, error.message),
    }
}

/// An array value of `ty` whose lane `k` is `lane(k)`.
fn array_value(ty: &Ty, elem: &Ty, len: u64, lane: impl Fn(u64) -> u128) -> InterpretValue {
    InterpretValue {
        ty: ty.clone(),
        kind: InterpretValueKind::Array(ArrayValue::from_vec(
            (0..len).map(|k| int_value(elem, lane(k))).collect(),
        )),
    }
}

/// The domain of one parameter, as interpreter values.
fn param_domain(param: &Param, pivots: &[u128], exhaustive: bool) -> Vec<InterpretValue> {
    match param {
        Param::Index(ty) | Param::Int(ty) => {
            int_domain(ty, pivots, exhaustive).into_iter().map(|raw| int_value(ty, raw)).collect()
        }
        Param::Array { ty, elem, len } => {
            let mask = int_mask(int_width(elem));
            let mut contents: Vec<InterpretValue> = vec![
                array_value(ty, elem, *len, |_| 0),
                array_value(ty, elem, *len, |_| mask),
                array_value(ty, elem, *len, |k| u128::from(k) & mask),
                array_value(ty, elem, *len, |k| (u128::from(k) * 37 + 11) & mask),
            ];
            let mut seen = BTreeSet::new();
            for &pivot in pivots {
                if seen.insert(pivot & mask) && seen.len() <= 6 {
                    contents.push(array_value(ty, elem, *len, |_| pivot & mask));
                }
            }
            contents
        }
    }
}

/// Every tuple of the cartesian product of `domains`, in order.
fn cartesian(domains: &[&Vec<InterpretValue>]) -> Vec<Vec<InterpretValue>> {
    let mut tuples = vec![Vec::new()];
    for domain in domains {
        tuples = tuples
            .into_iter()
            .flat_map(|prefix: Vec<InterpretValue>| {
                domain.iter().map(move |value| {
                    let mut tuple = prefix.clone();
                    tuple.push(value.clone());
                    tuple
                })
            })
            .collect();
    }
    tuples
}

/// The program's input domain, and whether it is the WHOLE product of the
/// per-parameter domains (the first 8-bit parameter takes every value, every other
/// one its boundary grid). The INDEX parameters' product — what decides every
/// element access — is always enumerated in full. When the whole product is larger
/// than `MAX_EXECUTIONS_PER_PROGRAM`, the value parameters (`Param::Int`, arrays)
/// are sampled deterministically for each index tuple, at least one each.
fn input_domain(program: &Program, rng: &mut Rng) -> (Vec<Vec<InterpretValue>>, bool) {
    let mut exhaustive_left = true;
    let domains: Vec<Vec<InterpretValue>> = program
        .params
        .iter()
        .map(|param| {
            let exhaustive = exhaustive_left
                && matches!(param, Param::Index(ty) | Param::Int(ty) if int_width(ty) <= 8);
            if exhaustive {
                exhaustive_left = false;
            }
            param_domain(param, &program.pivots, exhaustive)
        })
        .collect();
    let total = domains.iter().map(Vec::len).fold(1usize, usize::saturating_mul);
    if total <= MAX_EXECUTIONS_PER_PROGRAM {
        return (cartesian(&domains.iter().collect::<Vec<_>>()), true);
    }
    let is_index: Vec<bool> =
        program.params.iter().map(|param| matches!(param, Param::Index(_))).collect();
    let index_tuples = cartesian(
        &domains
            .iter()
            .zip(&is_index)
            .filter(|(_, index)| **index)
            .map(|(d, _)| d)
            .collect::<Vec<_>>(),
    );
    let per_index = (MAX_EXECUTIONS_PER_PROGRAM / index_tuples.len().max(1)).max(1);
    let mut tuples = Vec::with_capacity(index_tuples.len() * per_index);
    for index_tuple in &index_tuples {
        for _ in 0..per_index {
            let mut indices = index_tuple.iter();
            tuples.push(
                domains
                    .iter()
                    .zip(&is_index)
                    .map(|(domain, index)| {
                        if *index {
                            indices.next().expect("one value per index parameter").clone()
                        } else {
                            domain[rng.below(domain.len() as u64) as usize].clone()
                        }
                    })
                    .collect(),
            );
        }
    }
    (tuples, false)
}

// ---------------------------------------------------------------------------
// Witness replay: model values back to interpreter inputs
// ---------------------------------------------------------------------------

fn json_bitvec(value: &serde_json::Value) -> Result<u128, String> {
    if value["kind"] != "bit_vec" {
        return Err(format!("expected a bit-vector model value, got {value}"));
    }
    value["value"]
        .as_str()
        .ok_or_else(|| format!("bit-vector value without a decimal: {value}"))?
        .parse::<u128>()
        .map_err(|error| format!("bit-vector value {value}: {error}"))
}

/// Lane `lane` of an array-sorted model value.
fn json_lane(value: &serde_json::Value, lane: u64) -> Result<serde_json::Value, String> {
    match value["kind"].as_str() {
        Some("const_array") => Ok(value["default"].clone()),
        Some("array_map") => {
            let entries = value["entries"].as_array().ok_or("array_map without entries")?;
            for entry in entries {
                if json_bitvec(&entry["index"])? == u128::from(lane) {
                    return Ok(entry["value"].clone());
                }
            }
            Ok(value["default"].clone())
        }
        _ => Err(format!("expected an array model value, got {value}")),
    }
}

/// The interpreter value of `param` that the witness's model value denotes: an
/// integer's bit pattern, or an array's lanes `0..len` (the junk lanes past the
/// length are not part of the value and are never read).
fn decode_param(param: &Param, value: &serde_json::Value) -> Result<InterpretValue, String> {
    match param {
        Param::Index(ty) | Param::Int(ty) => Ok(int_value(ty, json_bitvec(value)?)),
        Param::Array { ty, elem, len } => {
            let mut lanes = Vec::with_capacity(*len as usize);
            for lane in 0..*len {
                lanes.push(int_value(elem, json_bitvec(&json_lane(value, lane)?)?));
            }
            Ok(InterpretValue {
                ty: ty.clone(),
                kind: InterpretValueKind::Array(ArrayValue::from_vec(lanes)),
            })
        }
    }
}

/// One refutation witness, decoded.
struct DecodedWitness {
    /// The entry values, one per parameter of `f`; `None` for an input the
    /// derivation never pins (its model leaves it free).
    inputs: Vec<Option<InterpretValue>>,
    /// `direct-smt` or `bounded-unroll k=<k>`.
    class: String,
    /// The consumer's own independent replay
    /// (`independently_replay_typed_chc_pdr_refutation_witness_with_options`): `Err` names why it
    /// refused the witness.
    consumer: Result<(), String>,
}

/// Decode one refutation witness of `obligation` to interpreter inputs (the entry
/// fact's model values, per parameter), after running the consumer's own
/// independent replay on it.
fn replay_options(
    obligation: &trust_mc_core::MirChcPdrObligation,
    engine: trust_mc_core::ChcPdrEngine,
) -> trust_mc_core::ChcPdrSolveOptions {
    let mut options = trust_mc_core::ChcPdrSolveOptions::default().with_engine(engine);
    options.native_request =
        obligation.native_metadata.as_ref().and_then(|m| m.request_config.clone());
    if options.native_request.is_some() {
        options.engine = trust_mc_core::ChcPdrEngine::Pdr;
    }
    options
}

fn witness_inputs(
    program: &Program,
    obligation: &trust_mc_core::MirChcPdrObligation,
    engine: trust_mc_core::ChcPdrEngine,
    witness: &trust_mc_core::ChcPdrRefutationWitness,
) -> Result<DecodedWitness, String> {
    let consumer = independently_replay_typed_chc_pdr_refutation_witness_with_options(
        obligation,
        &replay_options(obligation, engine),
        witness,
    )
    .map(|_| ())
    .map_err(|error| error.to_string());
    let payload: DirectSmtRefutationReplayPayload =
        serde_json::from_str(&witness.counterexample_json).map_err(|error| error.to_string())?;
    let problem = prepare_validated_typed_chc_pdr_input(obligation)
        .map_err(|error| error.to_string())?
        .problem
        .ok_or("the obligation lowers to no CHC problem")?;
    let (problem, class) = match payload.unroll_k {
        Some(k) => (
            bounded_unroll::bounded_unroll_chc_for_refutation(&problem, k)
                .ok_or("the witness's bounded unroll does not rebuild")?
                .problem,
            format!("bounded-unroll k={k}"),
        ),
        None => (std::sync::Arc::unwrap_or_clone(problem), "direct-smt".to_string()),
    };
    let witness = AcyclicUnsafeWitness {
        model: payload.witness_model,
        derivation_clause_indices: payload.derivation_clause_indices,
    };
    let entry = witness_entry_fact_assignment(&problem, &witness)?;
    if entry.len() != program.params.len() {
        return Err(format!(
            "the entry fact has {} arguments for {} parameters",
            entry.len(),
            program.params.len()
        ));
    }
    let inputs = program
        .params
        .iter()
        .zip(&entry)
        .map(|(param, value)| value.as_ref().map(|value| decode_param(param, value)).transpose())
        .collect::<Result<Vec<_>, _>>()?;
    Ok(DecodedWitness { inputs, class, consumer })
}

/// Whether `witness` is a direct-SMT witness whose derivation reads no
/// translation havoc under its own model (the consumer's havoc gate).
fn direct_witness_reads_no_havoc(
    problem: &ay_chc::ChcProblem,
    witness: &trust_mc_core::ChcPdrRefutationWitness,
) -> bool {
    if witness.verification != trust_mc_core::ChcPdrCexVerification::DirectSmtModel {
        return false;
    }
    let Ok(payload) =
        serde_json::from_str::<DirectSmtRefutationReplayPayload>(&witness.counterexample_json)
    else {
        return false;
    };
    payload.unroll_k.is_none()
        && bounded_unroll::derivation_reads_translation_havoc(
            problem,
            &payload.derivation_clause_indices,
            &payload.witness_model,
        ) == Some(false)
}

// ---------------------------------------------------------------------------
// The differential
// ---------------------------------------------------------------------------

#[derive(Default, Debug)]
struct Tally {
    programs: usize,
    gate_refused: usize,
    proved: usize,
    proved_executions: usize,
    proved_sampled: usize,
    refuted_channel: usize,
    engine_witnesses: usize,
    engine_witnesses_ungrounded: usize,
    /// Of those, the ones that still replay to a trap.
    engine_witnesses_ungrounded_trapping: usize,
    /// Engine witnesses that replayed to a trap although the consumer's own replay
    /// refuses them (for example a partial model: a solver drops variables it
    /// eliminated, and the consumer requires a total one).
    engine_witnesses_consumer_refused: usize,
    consumer_refusals: BTreeSet<String>,
    /// Witness inputs the derivation leaves free, each replayed at every value of
    /// its domain.
    witness_free_inputs: usize,
    /// Engine refutations whose witness carries no model (an ay-chc
    /// replay-verified trace), and how many of those programs the interpreter's
    /// domain search confirms unsafe.
    engine_refutations_without_model: usize,
    engine_refutations_without_model_confirmed: usize,
    not_proved: usize,
    truly_unsafe: usize,
    truly_unsafe_refuted: usize,
    truly_safe: usize,
    truly_safe_proved: usize,
    /// Programs the gate refused whose obligations were still translated and
    /// solved BEHIND the gate (`check_behind_the_gate`), the model-carrying
    /// witnesses that produced, and how many of those the consumer's own replay
    /// accepted (each of which must replay to a trap).
    behind_gate_solved: usize,
    behind_gate_witnesses: usize,
    behind_gate_accepted: usize,
    failures: Vec<String>,
}

impl Tally {
    fn report(&self, name: &str) -> String {
        let mut out = String::new();
        let _ = write!(
            out,
            "TMC-1 differential [{name}]: {} programs, {} refused at the gate, {} PROVED \
             ({} interpreted executions, {} sampled domains), {} refuted-channel witnesses \
             and {} engine witnesses replayed to a trap ({} of them refused by the consumer \
             replay: {:?}; {} free witness inputs replayed over their whole domain; {} \
             ungrounded engine witnesses not asserted, {} of which replay to a trap anyway; {} \
             engine refutations without a model, \
             {} of them confirmed unsafe by the interpreter), {} not proved; ground truth over the admitted programs: {} safe \
             ({} proved), {} unsafe ({} refuted with a replayed witness); behind the gate: {} refused programs solved, \
             {} witnesses, {} accepted by the consumer replay and replayed to a trap",
            self.programs,
            self.gate_refused,
            self.proved,
            self.proved_executions,
            self.proved_sampled,
            self.refuted_channel,
            self.engine_witnesses,
            self.engine_witnesses_consumer_refused,
            self.consumer_refusals,
            self.witness_free_inputs,
            self.engine_witnesses_ungrounded,
            self.engine_witnesses_ungrounded_trapping,
            self.engine_refutations_without_model,
            self.engine_refutations_without_model_confirmed,
            self.not_proved,
            self.truly_safe,
            self.truly_safe_proved,
            self.truly_unsafe,
            self.truly_unsafe_refuted,
            self.behind_gate_solved,
            self.behind_gate_witnesses,
            self.behind_gate_accepted,
        );
        out
    }
}

/// Run the whole differential on one program.
fn check_program(
    program: &Program,
    runner: &NativeTrustIrChcPdrRunner,
    rng: &mut Rng,
    tally: &mut Tally,
) {
    tally.programs += 1;
    let label = &program.label;
    let report = trust_ir_build::validate_module_report(&program.module);
    if !report.is_ok() {
        tally.failures.push(format!(
            "{label}: the generator built an invalid module: {}",
            report.errors().iter().take(3).map(ToString::to_string).collect::<Vec<_>>().join("; ")
        ));
        return;
    }
    let bundle = bundle_of(program);

    // 1. The gate says what the structure predicts.
    let gate = validate_native_bundle_proof_authority_input(&bundle, None);
    match (&program.gate, &gate) {
        (GateExpectation::Admitted, Ok(())) => {}
        (
            GateExpectation::RefusedRead(kind),
            Err(NativeSolveError::InvalidInput { detail, .. }),
        ) if detail.contains("ExtractElement")
            && (detail.contains(&format!("({kind})")) || detail.contains(&format!("({kind}("))) =>
        {
            tally.gate_refused += 1;
            check_behind_the_gate(program, runner, &bundle, tally);
            return;
        }
        (expected, got) => {
            tally.failures.push(format!("{label}: gate expected {expected:?}, got {got:?}"));
            return;
        }
    }

    // 2. The proof-grade lane.
    let evidence = match runner.solve_bundle_native_proof_grade(&bundle) {
        Ok(evidence) => evidence,
        Err(error) => {
            tally
                .failures
                .push(format!("{label}: the admitted bundle failed structurally: {error}"));
            return;
        }
    };
    // PROVED means the whole request: every row an authorized proof, none refuted,
    // none left unproved (a bundle carries one request; with several, `any` would
    // credit a proof the other rows contradict).
    let proved = !evidence.obligations.is_empty()
        && evidence.refuted.is_empty()
        && evidence.not_proved.is_empty()
        && evidence
            .obligations
            .iter()
            .all(|row| row.verification.authorized_native_proof().is_ok());
    let engine = runner.solve_options().engine;

    let mut witnesses = Vec::new();
    for row in &evidence.refuted {
        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
            &row.verification.outcome.status
        else {
            tally.failures.push(format!("{label}: a refuted row without a witness"));
            continue;
        };
        witnesses.push((
            "refuted channel",
            row.translated.obligation.clone(),
            (**witness).clone(),
            true,
        ));
    }
    let mut engine_refuted_without_model = false;
    for row in &evidence.not_proved {
        // The lane diverts an acyclic problem's direct-SMT witness to `not_proved`
        // (only the bounded-unroll lane's witnesses ride the `refuted` channel),
        // so the engine's own verdict is asked for again here. A cyclic problem's
        // witnessed refutation already rode the channel; re-solving it would only
        // repeat the lane's work.
        let Some(problem) = prepare_validated_typed_chc_pdr_input(&row.translated.obligation)
            .ok()
            .and_then(|prepared| prepared.problem)
        else {
            continue;
        };
        if problem.has_cycles() {
            continue;
        }
        let request = trust_mc_core::ChcPdrSolveRequest::new(row.translated.obligation.clone())
            .with_options(row.translated.request_config.solve_options(runner.solve_options()));
        if let Ok(solved) = solve_typed_chc_pdr_full_verification(request)
            && let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
                &solved.outcome.status
        {
            if !matches!(
                witness.verification,
                trust_mc_core::ChcPdrCexVerification::DirectSmtModel
                    | trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { .. }
            ) {
                // An ay-chc replay-verified trace carries a debug rendering, no
                // model: there is nothing to decode into inputs.
                engine_refuted_without_model = true;
                continue;
            }
            // An engine witness is a claim about the CHC; it is a claim about the
            // program when the encoding is GROUNDED — every clause variable
            // defined from the body relation's arguments, no translation havoc —
            // or, for a direct-SMT witness, when its derivation reads no
            // translation havoc under its model: the consumer's own gate
            // (`bounded_unroll::derivation_reads_translation_havoc`), which is how
            // a large-block query (design step 8e), one clause with every block
            // under its own Boolean, is judged.
            let grounded = bounded_unroll::problem_is_grounded_for_refutation(&problem)
                || direct_witness_reads_no_havoc(&problem, witness);
            witnesses.push((
                "engine",
                row.translated.obligation.clone(),
                (**witness).clone(),
                grounded,
            ));
        }
    }

    // 3. Every asserted witness replays to a trap. A witness on the `refuted`
    // channel must also pass the consumer's own replay (that channel is what a
    // consumer turns into a Failed verdict); an engine witness the consumer refuses
    // is counted, and must still drive the interpreter to a trap.
    let mut refuted = false;
    for (source, obligation, witness, asserted) in &witnesses {
        let decoded = match witness_inputs(program, obligation, engine, witness) {
            Ok(decoded) => decoded,
            Err(error) if *asserted => {
                tally
                    .failures
                    .push(format!("{label}: a {source} witness cannot be decoded: {error}"));
                continue;
            }
            Err(error) => {
                if independently_replay_typed_chc_pdr_refutation_witness_with_options(
                    obligation,
                    &replay_options(obligation, engine),
                    witness,
                )
                .is_ok()
                {
                    tally.failures.push(format!(
                        "{label}: a {source} witness the consumer accepts cannot be decoded: {error}"
                    ));
                }
                tally.engine_witnesses_ungrounded += 1;
                continue;
            }
        };
        // Whatever the consumer's own replay accepts is a claim it would surface as
        // a Failed verdict, so it must be a real counterexample even where this
        // harness judges the encoding ungrounded.
        let asserted = *asserted || decoded.consumer.is_ok();
        match (&decoded.consumer, *source == "refuted channel") {
            _ if !asserted => {}
            (Ok(()), _) => {}
            (Err(error), true) => tally.failures.push(format!(
                "{label}: the consumer replay refuses a refuted-channel {} witness: {error}",
                decoded.class
            )),
            (Err(error), false) => {
                tally.engine_witnesses_consumer_refused += 1;
                // The reason, with its counts masked, so the report lists kinds.
                tally.consumer_refusals.insert(
                    error
                        .split(':')
                        .next_back()
                        .unwrap_or_default()
                        .trim()
                        .chars()
                        .map(|c| if c.is_ascii_digit() { '#' } else { c })
                        .collect(),
                );
            }
        }
        let free = decoded.inputs.iter().filter(|value| value.is_none()).count();
        if free > 0 {
            tally.witness_free_inputs += free;
        }
        let missed = first_non_trapping_replay(program, &decoded);
        if !asserted {
            // An UNGROUNDED encoding may carry translation havoc, so its witness
            // is not a claim about the program: replayed, counted, never asserted.
            tally.engine_witnesses_ungrounded += 1;
            tally.engine_witnesses_ungrounded_trapping += usize::from(missed.is_none());
            continue;
        }
        match missed {
            None => {
                refuted = true;
                if *source == "refuted channel" {
                    tally.refuted_channel += 1;
                } else {
                    tally.engine_witnesses += 1;
                }
            }
            Some((inputs, execution)) => tally.failures.push(format!(
                "{label}: a {source} {} witness does not replay to a trap: inputs {:?} ran to {execution:?}",
                decoded.class,
                inputs.iter().map(|value| format!("{value:?}")).collect::<Vec<_>>()
            )),
        }
    }

    // 4. Ground truth on the whole domain.
    let (domain, complete) = input_domain(program, rng);
    let mut trap = None;
    let mut executions = 0;
    for inputs in domain {
        executions += 1;
        match execute(&program.module, inputs.clone()) {
            Execution::Completed => {}
            Execution::Trap(code, message) => {
                trap = Some((inputs, code, message));
                if !proved {
                    break;
                }
            }
            Execution::Incapable(code, message) => tally.failures.push(format!(
                "{label}: the interpreter could not execute an input ({code}: {message})"
            )),
        }
        if trap.is_some() && proved {
            break;
        }
    }
    if proved {
        tally.proved += 1;
        tally.proved_executions += executions;
        if !complete {
            tally.proved_sampled += 1;
        }
        if let Some((inputs, code, message)) = &trap {
            tally.failures.push(format!(
                "{label}: FALSE PROOF — PROVED, but the interpreter traps ({code}: {message}) on {:?}",
                inputs.iter().map(|value| format!("{value:?}")).collect::<Vec<_>>()
            ));
        }
    } else {
        tally.not_proved += usize::from(!refuted);
    }
    if engine_refuted_without_model {
        tally.engine_refutations_without_model += 1;
        tally.engine_refutations_without_model_confirmed += usize::from(trap.is_some());
    }
    if proved && refuted {
        tally
            .failures
            .push(format!("{label}: PROVED and REFUTED at once — a witness contradicts the proof"));
    }
    match (&trap, proved, refuted) {
        (Some(_), _, true) => {
            tally.truly_unsafe += 1;
            tally.truly_unsafe_refuted += 1;
        }
        (Some(_), _, false) => tally.truly_unsafe += 1,
        (None, true, _) => {
            tally.truly_safe += 1;
            tally.truly_safe_proved += 1;
        }
        (None, false, _) => tally.truly_safe += 1,
    }
}

/// The first replay of `decoded` that does NOT trap, or `None` when every one
/// does. A free input (one the derivation never pins) stands for every value of
/// its type: each one must reach the violation, so the replay runs the witness at
/// every value of its domain — a stronger check than any single completion of the
/// model.
fn first_non_trapping_replay(
    program: &Program,
    decoded: &DecodedWitness,
) -> Option<(Vec<InterpretValue>, Execution)> {
    let mut replays = vec![Vec::new()];
    for (param, value) in program.params.iter().zip(&decoded.inputs) {
        let choices = match value {
            Some(value) => vec![value.clone()],
            None => param_domain(param, &program.pivots, true),
        };
        replays = replays
            .into_iter()
            .flat_map(|prefix: Vec<InterpretValue>| {
                choices.iter().map(move |choice| {
                    let mut row = prefix.clone();
                    row.push(choice.clone());
                    row
                })
            })
            .collect();
    }
    replays.iter().find_map(|inputs| match execute(&program.module, inputs.clone()) {
        Execution::Trap(..) => None,
        execution => Some((inputs.clone(), execution)),
    })
}

/// A program the gate refused is still translated and solved, BEHIND the gate:
/// the refusal is defense in depth, and the refutation lanes must be sound on
/// their own. Every model-carrying witness the engine produces is handed to the
/// consumer's own replay; each one it accepts — a Failed verdict a consumer would
/// surface — must drive the interpreter to a trap. (This is where the TMC-1
/// review's false refutation lived: a safe loop calling a summarized element
/// reader, whose CHC equated a translation havoc with a constant.)
fn check_behind_the_gate(
    program: &Program,
    runner: &NativeTrustIrChcPdrRunner,
    bundle: &trust_ir::NativeVerificationBundle,
    tally: &mut Tally,
) {
    let label = &program.label;
    let Ok(translated) = runner.translate_obligations(bundle) else {
        return;
    };
    tally.behind_gate_solved += 1;
    let engine = runner.solve_options().engine;
    for row in translated {
        let request = trust_mc_core::ChcPdrSolveRequest::new(row.obligation.clone())
            .with_options(row.request_config.solve_options(runner.solve_options()));
        let Ok(solved) = solve_typed_chc_pdr_full_verification(request) else {
            continue;
        };
        let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
            &solved.outcome.status
        else {
            continue;
        };
        if !matches!(
            witness.verification,
            trust_mc_core::ChcPdrCexVerification::DirectSmtModel
                | trust_mc_core::ChcPdrCexVerification::BoundedUnrollDirectSmtModel { .. }
        ) {
            continue;
        }
        tally.behind_gate_witnesses += 1;
        if independently_replay_typed_chc_pdr_refutation_witness_with_options(
            &row.obligation,
            &row.request_config.solve_options(runner.solve_options()),
            witness,
        )
        .is_err()
        {
            continue;
        }
        tally.behind_gate_accepted += 1;
        match witness_inputs(program, &row.obligation, engine, witness) {
            Err(error) => tally.failures.push(format!(
                "{label}: BEHIND THE GATE, a witness the consumer accepts cannot be decoded: {error}"
            )),
            Ok(decoded) => {
                if let Some((inputs, execution)) = first_non_trapping_replay(program, &decoded) {
                    tally.failures.push(format!(
                        "{label}: BEHIND THE GATE, FALSE REFUTATION — the consumer accepts a {} witness that does not replay to a trap: inputs {:?} ran to {execution:?}",
                        decoded.class,
                        inputs.iter().map(|value| format!("{value:?}")).collect::<Vec<_>>()
                    ));
                }
            }
        }
    }
}

/// The compiler-shaped bundles of `per_family` generated programs from each
/// family, drawn from fixed seeds of their own (not the sweeps'), labelled
/// `family/program`. Design step 8c's shared-versus-per-request differential
/// (`native/tests/shared_solve_tests.rs`) solves them; the ground truth here
/// stays with the sweeps below.
pub(super) fn sample_program_bundles(
    per_family: usize,
) -> Vec<(String, trust_ir::NativeVerificationBundle)> {
    let families: [(&str, u64, fn(&mut Rng, usize) -> Program); 14] = [
        ("straight", 0x8C5A_0001, gen_straight),
        ("nested", 0x8C5A_0002, gen_nested),
        ("loop", 0x8C5A_0003, gen_loop),
        ("cell", 0x8C5A_0004, gen_cell),
        ("callee", 0x8C5A_0005, gen_callee),
        ("vector", 0x8C5A_0006, gen_vector),
        ("join", 0x8C5A_0007, gen_join),
        ("callee_paths", 0x8C5A_0008, gen_callee_paths),
        ("callee_in_loop", 0x8C5A_0009, gen_callee_in_loop),
        ("borrowed_cell", 0x8C5A_000A, gen_borrowed_cell),
        ("struct_elem", 0x8C5A_000B, gen_struct_elem),
        ("bool_elem", 0x8C5A_000C, gen_bool_elem),
        ("passthrough", 0x8C5A_000D, gen_callee_passthrough),
        ("two_reads", 0x8C5A_000E, gen_two_reads),
    ];
    let mut bundles = Vec::new();
    for (family, seed, generate) in families {
        let mut rng = Rng(seed);
        for id in 0..per_family {
            let program = generate(&mut rng, id);
            bundles.push((format!("{family}/{}", program.label), bundle_of(&program)));
        }
    }
    bundles
}

fn run_family(
    name: &str,
    seed: u64,
    count: usize,
    generate: fn(&mut Rng, usize) -> Program,
) -> Tally {
    let runner = NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default().with_timeout(SOLVE_TIMEOUT),
    );
    let mut rng = Rng(seed);
    let mut tally = Tally::default();
    for id in 0..count {
        let program = generate(&mut rng, id);
        check_program(&program, &runner, &mut rng, &mut tally);
    }
    eprintln!("{}", tally.report(name));
    assert!(tally.failures.is_empty(), "{}:\n{}", tally.report(name), tally.failures.join("\n"));
    tally
}

#[test]
fn tmc1_differential_straight_line_reads_and_writes() {
    let tally = run_family("straight", 0x7A1C_0001, 160, gen_straight);
    assert!(tally.proved >= 10, "the family must exercise proofs: {tally:?}");
    assert!(tally.engine_witnesses >= 10, "the family must exercise refutations: {tally:?}");
}

#[test]
fn tmc1_differential_nested_arrays() {
    let tally = run_family("nested", 0x7A1C_0002, 60, gen_nested);
    assert!(tally.proved >= 3, "the family must exercise proofs: {tally:?}");
    assert!(tally.engine_witnesses >= 3, "the family must exercise refutations: {tally:?}");
}

#[test]
fn tmc1_differential_loops() {
    let tally = run_family("loop", 0x7A1C_0003, 50, gen_loop);
    assert!(tally.gate_refused >= 5, "reads a cycle reaches must be refused: {tally:?}");
    assert!(tally.proved + tally.refuted_channel >= 5, "loops must be decided: {tally:?}");
}

#[test]
fn tmc2_differential_promoted_cells_across_the_retired_extent() {
    let tally = run_family("cell", 0x7A1C_0004, 50, gen_cell);
    assert!(tally.proved >= 3, "the family must exercise proofs: {tally:?}");
}

#[test]
fn tmc1_differential_reads_in_a_summarized_callee() {
    let tally = run_family("callee", 0x7A1C_0005, 50, gen_callee);
    assert!(tally.proved >= 3, "the family must exercise proofs: {tally:?}");
}

#[test]
fn tmc1_differential_vector_reads_are_refused() {
    let tally = run_family("vector", 0x7A1C_0006, 12, gen_vector);
    assert_eq!(tally.gate_refused, tally.programs, "{tally:?}");
}

#[test]
fn tmc1_differential_reads_after_an_array_join() {
    let tally = run_family("join", 0x7A1C_0007, 40, gen_join);
    assert!(tally.proved >= 1, "the family must exercise proofs: {tally:?}");
}

#[test]
fn tmc1_differential_summarized_callees_with_their_own_paths() {
    let tally = run_family("callee_paths", 0x7A1C_0008, 40, gen_callee_paths);
    assert!(tally.proved >= 3, "the family must exercise proofs: {tally:?}");
}

/// Every reading callee called from a loop is refused at the call, and behind the
/// gate no refutation the consumer would accept is false.
#[test]
fn tmc1_differential_reading_callees_called_from_a_loop() {
    let tally = run_family("callee_in_loop", 0x7A1C_0009, 30, gen_callee_in_loop);
    assert_eq!(tally.gate_refused, tally.programs, "{tally:?}");
    assert_eq!(tally.behind_gate_solved, tally.programs, "{tally:?}");
}

#[test]
fn tmc1_differential_borrowed_array_cells() {
    let tally = run_family("borrowed_cell", 0x7A1C_000A, 30, gen_borrowed_cell);
    assert!(tally.proved >= 3, "the family must exercise proofs: {tally:?}");
}

#[test]
fn tmc1_differential_arrays_of_tuples() {
    let tally = run_family("struct_elem", 0x7A1C_000B, 30, gen_struct_elem);
    assert!(tally.proved >= 1, "the family must exercise proofs: {tally:?}");
}

#[test]
fn tmc1_differential_arrays_of_bool() {
    let tally = run_family("bool_elem", 0x7A1C_000C, 30, gen_bool_elem);
    assert!(tally.proved >= 1, "the family must exercise proofs: {tally:?}");
}

#[test]
fn tmc1_differential_arrays_returned_by_a_callee() {
    let tally = run_family("passthrough", 0x7A1C_000D, 40, gen_callee_passthrough);
    assert!(tally.proved >= 1, "the family must exercise proofs: {tally:?}");
}

#[test]
fn tmc1_differential_two_reads_of_an_array_parameter() {
    let tally = run_family("two_reads", 0x7A1C_000E, 40, gen_two_reads);
    assert!(tally.proved >= 1, "the family must exercise proofs: {tally:?}");
}

/// The TMC-1 review's blocker, pinned: `a = [19u32; 5]; for k in 0..5 {
/// assert(g(a, k) != 263) }` with `g(a, k) = a[k]` is safe on every input, yet the
/// branch under review admitted it and the bounded-unroll lane delivered a
/// witnessed refutation the consumer's replay accepted. Closed twice:
///
/// 1. at the gate: the call folds `g`'s read into a block the loop reaches, where
///    the caller carries arrays shape-only (`shape_only_array_in_callee`), exactly
///    as the same read written in the loop is refused (`shape_only_array`);
/// 2. at the root, BEHIND the gate: the read is a translation havoc, and the CHC's
///    `(= havoc 263)` no longer grounds it, so the bounded-unroll lane declines the
///    problem and nothing the consumer accepts refutes the program.
#[test]
fn tmc1_review_a_safe_loop_calling_an_element_reader_is_never_refuted() {
    let runner = NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default().with_timeout(SOLVE_TIMEOUT),
    );
    for (bound, via_callee) in [(5, true), (4, true), (5, false)] {
        let program = safe_loop_program(bound, via_callee);
        let label = &program.label;
        for p in 0..=255u128 {
            assert_eq!(
                execute(&program.module, vec![int_value(&Ty::U8, p)]),
                Execution::Completed,
                "{label}: the program is safe on every input"
            );
        }
        let mut tally = Tally::default();
        let mut rng = Rng(0x7A1C_00FE);
        check_program(&program, &runner, &mut rng, &mut tally);
        assert!(tally.failures.is_empty(), "{label}: {:#?}", tally.failures);
        assert_eq!((tally.gate_refused, tally.behind_gate_solved), (1, 1), "{label}: {tally:?}");
        assert_eq!(tally.behind_gate_accepted, 0, "{label}: no refutation survives: {tally:?}");

        // The root cause, on the translator's own CHC.
        let translated = runner.translate_obligations(&bundle_of(&program)).expect("translates");
        assert!(!translated.is_empty(), "{label}");
        for row in &translated {
            let problem = prepare_validated_typed_chc_pdr_input(&row.obligation)
                .expect("lowers")
                .problem
                .expect("a CHC problem");
            assert!(problem.has_cycles(), "{label}");
            assert!(
                !bounded_unroll::problem_is_grounded_for_refutation(&problem),
                "{label}: the read is a translation havoc, which no equality grounds"
            );
            for k in bounded_unroll::BOUNDED_UNROLL_K_LADDER {
                assert!(
                    bounded_unroll::bounded_unroll_chc_for_refutation(&problem, k).is_none(),
                    "{label}: the bounded-unroll lane declines at k={k}"
                );
            }
        }
    }
}

/// An array loaded through a raw POINTER parameter: its lanes are an input no
/// harness can hand the interpreter from outside `f`, and the translator gives the
/// load no precise model (`MemoryAccessWithoutPreciseModel`, fail closed), so the
/// lane must neither prove the request nor deliver a refutation.
#[test]
fn tmc1_a_read_of_an_array_loaded_through_a_pointer_parameter_is_never_decided() {
    let mut mb = ModuleBuilder::new("tmc1_pointer_loaded");
    let u32_id = mb.add_type(Ty::U32);
    let arr = Ty::Array(u32_id, 4);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::U8], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let p = fb.add_block_param(entry, Ty::Ptr);
    let i = fb.add_block_param(entry, Ty::U8);
    let four = fb.iconst(Ty::U8, 4);
    let ok = fb.icmp(ICmpOp::Ult, Ty::U8, i, four);
    fb.condbr(ok, body, vec![], exit, vec![]);
    fb.switch_to_block(body);
    let a = fb.load(arr, p);
    let read = fb.extract_element(Ty::U32, a, i);
    let same = fb.icmp(ICmpOp::Eq, Ty::U32, read, read);
    fb.assert(same);
    fb.br(exit, vec![]);
    fb.switch_to_block(exit);
    fb.ret(vec![]);
    fb.build();
    let program = Program {
        label: "pointer-loaded [u32; 4]".to_string(),
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        params: vec![Param::Int(Ty::Ptr), Param::Index(Ty::U8)],
        pivots: vec![4],
        gate: GateExpectation::Admitted,
    };
    let bundle = bundle_of(&program);
    let runner = NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default().with_timeout(SOLVE_TIMEOUT),
    );
    match runner.solve_bundle_native_proof_grade(&bundle) {
        Ok(evidence) => {
            assert!(evidence.obligations.is_empty(), "never proved: {:?}", evidence.not_proved);
            assert!(evidence.refuted.is_empty(), "never refuted");
        }
        // Refused outright is as good: nothing is decided.
        Err(error) => assert!(
            matches!(error, NativeSolveError::InvalidInput { .. }),
            "a refusal, not a failure: {error}"
        ),
    }
}

/// Two fixed anchors, independent of the generator: the proof-grade lane PROVES
/// an in-bounds read of an SMT-modeled array (a symbolic `u8` index under
/// `i < 200` into `[u32; 200]`), and never proves the same read with the guard
/// one past the end. The anchor's assertion that a proof HAPPENS must not depend
/// on machine load, and the solve options offer no deterministic resource bound,
/// so it solves under `ANCHOR_SOLVE_TIMEOUT`, far above the time the proof takes.
#[test]
fn tmc1_anchor_a_guarded_read_is_proved_and_an_off_by_one_read_is_not() {
    let build = |bound: i128| {
        let mut mb = ModuleBuilder::new(format!("tmc1_anchor_{bound}"));
        let u32_id = mb.add_type(Ty::U32);
        let arr = Ty::Array(u32_id, 200);
        let ft = mb.add_func_type(vec![Ty::U8, Ty::U32], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let i = fb.add_block_param(entry, Ty::U8);
        let x = fb.add_block_param(entry, Ty::U32);
        let seven = fb.iconst(Ty::U32, 7);
        let a0 = fb.array_splat(arr.clone(), seven);
        let limit = fb.iconst(Ty::U8, bound);
        let ok = fb.icmp(ICmpOp::Ult, Ty::U8, i, limit);
        fb.condbr(ok, body, vec![], exit, vec![]);
        fb.switch_to_block(body);
        let a1 = fb.insert_element(arr, a0, i, x);
        let read = fb.extract_element(Ty::U32, a1, i);
        let same = fb.icmp(ICmpOp::Eq, Ty::U32, read, x);
        fb.assert(same);
        fb.br(exit, vec![]);
        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();
        Program {
            label: format!("anchor bound {bound}"),
            module: mb.build().expect("ModuleBuilder::build: test fixture"),
            params: vec![Param::Index(Ty::U8), Param::Int(Ty::U32)],
            pivots: vec![200, u128::try_from(bound).expect("non-negative")],
            gate: GateExpectation::Admitted,
        }
    };
    let runner = NativeTrustIrChcPdrRunner::with_solve_options(
        trust_mc_core::ChcPdrSolveOptions::default().with_timeout(ANCHOR_SOLVE_TIMEOUT),
    );
    let mut rng = Rng(0x7A1C_00FF);

    let mut tally = Tally::default();
    check_program(&build(200), &runner, &mut rng, &mut tally);
    assert!(tally.failures.is_empty(), "{:?}", tally.failures);
    assert_eq!((tally.proved, tally.truly_safe), (1, 1), "the exact guard is PROVED: {tally:?}");

    let mut tally = Tally::default();
    check_program(&build(201), &runner, &mut rng, &mut tally);
    assert!(tally.failures.is_empty(), "{:?}", tally.failures);
    assert_eq!(tally.proved, 0, "one lane past the end is never proved: {tally:?}");
    assert_eq!(tally.truly_unsafe, 1, "and the interpreter traps at i = 200: {tally:?}");
    assert_eq!(tally.engine_witnesses, 1, "its witness replays to the trap: {tally:?}");
}
