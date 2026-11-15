// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `MemCopy` / `MemSet` over stack cells (`translate_chc_bulk_memory.rs`).
//!
//! Pinned here:
//!
//! * EXACTNESS against trust-ir's byte-level reference interpreter. On a grid
//!   of small cases — every destination and source lane, every byte count from
//!   0 to past the cell, `memcpy`, `memmove`, `memset`, `u8` and `u32` lanes —
//!   each case is classified by an independent byte-range oracle, and: a no-op
//!   or whole-object write proves exactly the interpreter's post-state and is
//!   refuted at every lane that differs from it; undefined behaviour (out of
//!   bounds, `memcpy` overlap) is a reachable error with no fail-closed
//!   diagnostic, exactly where the interpreter faults; a defined lane run fails
//!   closed by name and is never proved.
//! * SIZE: the encoding is identical at every array length and does not depend
//!   on the byte count, constant or symbolic.
//! * COUNTEREXAMPLES are real: with a symbolic count and fill byte, every model
//!   of a reachable error replays as a failing run of the interpreter, and the
//!   verdict agrees with the interpreter on a grid of concrete inputs.
//! * THE GATE is unchanged: every proof-authority lane still refuses a cell a
//!   bulk operation reaches; only the translator's own cell decision tracks it.

use std::collections::BTreeMap;

use ay_bindings::Expr;
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::{Constant, FieldDef, Module, StructDef, StructRepr};
use trust_ir_build::ModuleBuilder;

use super::smt_array_tests::{VcSize, error_reachable, error_rule_bodies, satisfiable, vc_size};
use super::*;

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// Where a bulk operand points inside its cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum At {
    /// The cell itself.
    Cell,
    /// `gep(elem, cell, [k])`: lane `k`.
    Lane(u64),
}

#[derive(Clone, Copy, Debug)]
enum Bulk {
    /// `memcpy` / `memmove` into the destination cell from the OTHER cell.
    Copy { dst: At, src: At, overlap: bool },
    /// `memcpy` / `memmove` within the destination cell.
    Within { dst: At, src: At, overlap: bool },
    /// `memset(dst, byte, n)`.
    Fill { dst: At, byte: u8 },
}

#[derive(Clone, Copy, Debug)]
enum Count {
    Const(u64),
    /// The entry parameter `n: u64`.
    Param,
}

/// The cells' initial contents.
#[derive(Clone, Copy, Debug)]
enum Init {
    /// Destination lane `j` holds `j + 1`, source lane `j` holds `0x41 + j`.
    Distinct,
    /// Destination lanes all `7`, source lanes all `9` (constant size at any length).
    Splat,
}

#[derive(Clone, Debug)]
struct Fixture {
    elem: Ty,
    len: u64,
    init: Init,
    bulk: Bulk,
    count: Count,
    /// `assume(n <op> k)` on the count parameter, in order.
    assume: Vec<(ICmpOp, u64)>,
}

#[derive(Clone, Debug)]
enum Tail {
    /// Return every destination lane (the interpreter's reference).
    Lanes,
    /// `assert(dst[lane] == value)` for each pair.
    Expect(Vec<(u64, u128)>),
    /// Observe nothing: only the instruction's own rules can fire.
    Nothing,
}

struct Built {
    module: Module,
    func: FuncId,
    /// Both cells' type, `[elem; len]`.
    cell_ty: Ty,
    dst_cell: ValueId,
    src_cell: ValueId,
}

fn elem_size(elem: &Ty) -> u64 {
    match elem {
        Ty::U8 => 1,
        Ty::U32 => 4,
        other => panic!("fixture element {other:?}"),
    }
}

fn initial(init: Init, base: u128, len: u64) -> Constant {
    match init {
        Init::Distinct => Constant::Array(
            (0..len).map(|j| Constant::Int(i128::from(j) + 1 + base as i128)).collect(),
        ),
        Init::Splat => Constant::splat(Constant::Int(if base == 0 { 7 } else { 9 }), len),
    }
}

fn build(fx: &Fixture, tail: &Tail) -> Built {
    let mut mb = ModuleBuilder::new("bulk_memory");
    let elem_id = mb.add_type(fx.elem.clone());
    let arr = Ty::Array(elem_id, fx.len);
    let params = match fx.count {
        Count::Param => vec![Ty::U64],
        Count::Const(_) => vec![],
    };
    let returns = match tail {
        Tail::Lanes => vec![fx.elem.clone(); usize::try_from(fx.len).expect("small fixture")],
        _ => vec![],
    };
    let ft = mb.add_func_type(params, returns);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = match fx.count {
        Count::Param => Some(fb.add_block_param(entry, Ty::U64)),
        Count::Const(_) => None,
    };
    let dst_cell = fb.alloca(arr.clone());
    let src_cell = fb.alloca(arr.clone());
    let dst_init = fb.const_value(arr.clone(), initial(fx.init, 0, fx.len));
    fb.store(arr.clone(), dst_cell, dst_init);
    let src_init = fb.const_value(arr.clone(), initial(fx.init, 0x40, fx.len));
    fb.store(arr.clone(), src_cell, src_init);
    if let Some(n) = n {
        for (op, bound) in &fx.assume {
            let bound = fb.iconst(Ty::U64, i128::from(*bound));
            let holds = fb.icmp(*op, Ty::U64, n, bound);
            fb.assume(holds);
        }
    }
    let point = |fb: &mut trust_ir_build::FunctionBuilder<'_>, cell: ValueId, at: At| match at {
        At::Cell => cell,
        At::Lane(k) => {
            let index = fb.iconst(Ty::I64, i128::from(k));
            fb.gep(fx.elem.clone(), cell, vec![index])
        }
    };
    let bytes = match (fx.count, n) {
        (Count::Const(k), _) => fb.const_value(Ty::U64, Constant::Int(i128::from(k))),
        (Count::Param, Some(n)) => n,
        (Count::Param, None) => unreachable!(),
    };
    match fx.bulk {
        Bulk::Copy { dst, src, overlap } => {
            let d = point(&mut fb, dst_cell, dst);
            let s = point(&mut fb, src_cell, src);
            fb.memcopy(d, s, bytes, overlap);
        }
        Bulk::Within { dst, src, overlap } => {
            let d = point(&mut fb, dst_cell, dst);
            let s = point(&mut fb, dst_cell, src);
            fb.memcopy(d, s, bytes, overlap);
        }
        Bulk::Fill { dst, byte } => {
            let d = point(&mut fb, dst_cell, dst);
            let b = fb.iconst(Ty::U8, i128::from(byte));
            fb.memset(d, b, bytes);
        }
    }
    let after = fb.load(arr.clone(), dst_cell);
    match tail {
        Tail::Lanes => {
            let lanes = (0..fx.len)
                .map(|lane| {
                    let index = fb.iconst(Ty::U64, i128::from(lane));
                    fb.extract_element(fx.elem.clone(), after, index)
                })
                .collect();
            fb.ret(lanes);
        }
        Tail::Expect(expected) => {
            for (lane, value) in expected {
                let index = fb.iconst(Ty::U64, i128::from(*lane));
                let read = fb.extract_element(fx.elem.clone(), after, index);
                let want = fb.const_value(fx.elem.clone(), Constant::Int(*value as i128));
                let holds = fb.icmp(ICmpOp::Eq, fx.elem.clone(), read, want);
                fb.assert(holds);
            }
            fb.ret(vec![]);
        }
        Tail::Nothing => fb.ret(vec![]),
    }
    fb.build();
    Built {
        module: mb.build().expect("ModuleBuilder::build: test fixture"),
        func: FuncId::new(0),
        cell_ty: arr,
        dst_cell,
        src_cell,
    }
}

fn chc(fx: &Fixture, tail: &Tail) -> ChcTranslationOutput {
    let built = build(fx, tail);
    trust_ir_function_to_chc_translation_output(
        &built.module,
        built.func,
        &TranslateOptions::default(),
    )
    .expect("fixture translates")
}

fn reasons(output: &ChcTranslationOutput) -> Vec<TrustIrChcUnsupportedReason> {
    output.diagnostics.iter().map(|diagnostic| diagnostic.reason).collect()
}

/// What the byte-level reference interpreter does with the fixture.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Reference {
    /// It returns, with these destination lanes.
    Lanes(Vec<u128>),
    /// It faults on undefined behaviour.
    Undefined,
}

fn reference(fx: &Fixture, n: Option<u64>) -> Reference {
    let built = build(fx, &Tail::Lanes);
    let args: Vec<InterpretValue> = n
        .map(|n| InterpretValue::int(Ty::U64, i128::from(n)).expect("u64 argument"))
        .into_iter()
        .collect();
    match Interpreter::with_module(&built.module).execute_func(built.func, args) {
        Ok(outcome) => Reference::Lanes(
            outcome
                .returns
                .iter()
                .map(|lane| lane.as_int().expect("an integer lane").as_unsigned())
                .collect(),
        ),
        Err(error) if error.code == InterpretErrorCode::UndefinedBehavior => Reference::Undefined,
        Err(error) => panic!("{fx:?}: the reference interpreter failed: {error:?}"),
    }
}

// ---------------------------------------------------------------------------
// The independent byte-range oracle
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// `bytes == 0`, or one whole object (a lane, or the whole cell from its start).
    Exact,
    /// Out of bounds, or a `memcpy` whose ranges overlap.
    Undefined,
    /// Defined, but a run of lanes that is neither one lane nor the whole cell.
    Unplaced,
}

fn offset(at: At, size: u64) -> u64 {
    match at {
        At::Cell => 0,
        At::Lane(k) => k * size,
    }
}

fn expected_kind(fx: &Fixture, bytes: u64) -> Kind {
    let size = elem_size(&fx.elem);
    let total = fx.len * size;
    if bytes == 0 {
        return Kind::Exact;
    }
    let (dst, src, memcpy_within) = match fx.bulk {
        Bulk::Copy { dst, src, .. } => (dst, Some(src), false),
        Bulk::Within { dst, src, overlap } => (dst, Some(src), !overlap),
        Bulk::Fill { dst, .. } => (dst, None, false),
    };
    let dst_off = offset(dst, size);
    let mut undefined = bytes > total - dst_off;
    if let Some(src) = src {
        let src_off = offset(src, size);
        undefined |= bytes > total - src_off;
        undefined |= memcpy_within && dst_off.abs_diff(src_off) < bytes;
    }
    if undefined {
        return Kind::Undefined;
    }
    let whole_from_start =
        bytes == total && dst_off == 0 && src.is_none_or(|src| offset(src, size) == 0);
    if bytes == size || whole_from_start { Kind::Exact } else { Kind::Unplaced }
}

fn grid_bulks(len: u64) -> Vec<Bulk> {
    let mut points = vec![At::Cell];
    points.extend((0..len).map(At::Lane));
    let mut bulks = Vec::new();
    for &dst in &points {
        for &src in &points {
            for overlap in [false, true] {
                bulks.push(Bulk::Copy { dst, src, overlap });
                bulks.push(Bulk::Within { dst, src, overlap });
            }
        }
        bulks.push(Bulk::Fill { dst, byte: 0xA5 });
    }
    bulks
}

// ---------------------------------------------------------------------------
// Exactness against the reference interpreter
// ---------------------------------------------------------------------------

/// The grid: `[u8; 4]` and `[u32; 3]` cells, every operand lane, every byte count
/// from 0 to two past the cell.
#[test]
fn every_bulk_write_agrees_with_the_byte_level_reference() {
    let mut seen = BTreeMap::<&'static str, usize>::new();
    for (elem, len) in [(Ty::U8, 4u64), (Ty::U32, 3)] {
        let total = len * elem_size(&elem);
        for bulk in grid_bulks(len) {
            for bytes in 0..=total + 2 {
                let fx = Fixture {
                    elem: elem.clone(),
                    len,
                    init: Init::Distinct,
                    bulk,
                    count: Count::Const(bytes),
                    assume: Vec::new(),
                };
                let kind = expected_kind(&fx, bytes);
                let reference = reference(&fx, None);
                match kind {
                    Kind::Exact => {
                        *seen.entry("exact").or_default() += 1;
                        let Reference::Lanes(lanes) = reference else {
                            panic!("{fx:?}: the oracle says defined, the interpreter faulted");
                        };
                        let expected: Vec<(u64, u128)> =
                            lanes.iter().enumerate().map(|(j, v)| (j as u64, *v)).collect();
                        let proved = chc(&fx, &Tail::Expect(expected.clone()));
                        assert!(proved.diagnostics.is_empty(), "{fx:?}: {:?}", reasons(&proved));
                        assert!(
                            !error_reachable(&proved),
                            "{fx:?}: the reference post-state {lanes:?} must be PROVED"
                        );
                        for lane in 0..len {
                            let mut wrong = expected.clone();
                            wrong[lane as usize].1 ^= 1;
                            let refuted = chc(&fx, &Tail::Expect(wrong));
                            assert!(refuted.diagnostics.is_empty(), "{fx:?}");
                            assert!(
                                error_reachable(&refuted),
                                "{fx:?}: lane {lane} != {} must be REFUTED",
                                lanes[lane as usize]
                            );
                        }
                    }
                    Kind::Undefined => {
                        *seen.entry("undefined").or_default() += 1;
                        assert_eq!(reference, Reference::Undefined, "{fx:?}");
                        let out = chc(&fx, &Tail::Nothing);
                        assert!(out.diagnostics.is_empty(), "{fx:?}: {:?}", reasons(&out));
                        assert!(error_reachable(&out), "{fx:?}: undefined behaviour is an error");
                    }
                    Kind::Unplaced => {
                        *seen.entry("unplaced").or_default() += 1;
                        let Reference::Lanes(lanes) = reference else {
                            panic!("{fx:?}: the oracle says defined, the interpreter faulted");
                        };
                        let expected: Vec<(u64, u128)> =
                            lanes.iter().enumerate().map(|(j, v)| (j as u64, *v)).collect();
                        let out = chc(&fx, &Tail::Expect(expected));
                        assert_eq!(
                            reasons(&out),
                            vec![TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange],
                            "{fx:?}"
                        );
                        assert!(error_reachable(&out), "{fx:?}: a lane run is never proved");
                        let silent = chc(&fx, &Tail::Nothing);
                        assert!(error_reachable(&silent), "{fx:?}: it fails closed by itself");
                    }
                }
            }
        }
    }
    // The grid reaches every class.
    assert!(seen.get("exact").copied().unwrap_or(0) > 100, "{seen:?}");
    assert!(seen.get("undefined").copied().unwrap_or(0) > 100, "{seen:?}");
    assert!(seen.get("unplaced").copied().unwrap_or(0) > 10, "{seen:?}");
}

/// A struct cell: `S { a: u32 @ 0, b: u32 @ 4 }`. A copy of the whole struct, of
/// its first field through the cell pointer (the field at byte 0), and of `b`
/// through its own `GEP`; a fill of either; anything else in bounds fails closed.
#[test]
fn struct_cells_are_written_field_exactly() {
    #[derive(Clone, Copy, Debug)]
    enum Dst {
        Cell,
        FieldB,
    }
    fn probe(dst: Dst, fill: bool, bytes: u64, tail: Option<(u128, u128)>) -> (Module, FuncId) {
        let mut mb = ModuleBuilder::new("bulk_struct");
        let id = mb.add_struct(StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "bulk_struct::S".to_string(),
            fields: vec![
                FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
                FieldDef { name: "b".into(), ty: Ty::U32, offset: Some(4) },
            ],
            size: Some(8),
            align: Some(4),
            repr: StructRepr::Rust,
            origin: None,
        });
        let sty = Ty::Struct(id);
        let returns = if tail.is_none() { vec![Ty::U32, Ty::U32] } else { vec![] };
        let ft = mb.add_func_type(vec![], returns);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        // Each field stored through its own lane: a struct constant is not part
        // of the CHC value model, and the interpreter does not run `undef` of one.
        let init =
            |fb: &mut trust_ir_build::FunctionBuilder<'_>, cell: ValueId, a: i128, b: i128| {
                for (field, value) in [(0, a), (1, b)] {
                    let index = fb.iconst(Ty::I64, field);
                    let lane = fb.gep(Ty::U32, cell, vec![index]);
                    let value = fb.iconst(Ty::U32, value);
                    fb.store(Ty::U32, lane, value);
                }
            };
        let dst_cell = fb.alloca(sty.clone());
        let src_cell = fb.alloca(sty.clone());
        init(&mut fb, dst_cell, 1, 2);
        init(&mut fb, src_cell, 0x31, 0x32);
        let d = match dst {
            Dst::Cell => dst_cell,
            Dst::FieldB => {
                let one = fb.iconst(Ty::I64, 1);
                fb.gep(Ty::U32, dst_cell, vec![one])
            }
        };
        let count = fb.const_value(Ty::U64, Constant::Int(i128::from(bytes)));
        if fill {
            let byte = fb.iconst(Ty::U8, 0x5A);
            fb.memset(d, byte, count);
        } else {
            fb.memcopy(d, src_cell, count, false);
        }
        let after = fb.load(sty, dst_cell);
        let a = fb.extract_field(Ty::U32, after, 0);
        let b = fb.extract_field(Ty::U32, after, 1);
        match tail {
            None => fb.ret(vec![a, b]),
            Some((want_a, want_b)) => {
                for (got, want) in [(a, want_a), (b, want_b)] {
                    let want = fb.const_value(Ty::U32, Constant::Int(want as i128));
                    let holds = fb.icmp(ICmpOp::Eq, Ty::U32, got, want);
                    fb.assert(holds);
                }
                fb.ret(vec![]);
            }
        }
        fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
    }
    for dst in [Dst::Cell, Dst::FieldB] {
        for fill in [false, true] {
            for bytes in [0u64, 1, 4, 8, 9] {
                let (module, func) = probe(dst, fill, bytes, None);
                let outcome = Interpreter::with_module(&module).execute_func(func, Vec::new());
                let room = match dst {
                    Dst::Cell => 8,
                    Dst::FieldB => 4,
                };
                let what = format!("{dst:?} fill={fill} bytes={bytes}");
                if bytes > room {
                    let error = outcome.expect_err(&what);
                    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{what}");
                    let (module, func) = probe(dst, fill, bytes, Some((0, 0)));
                    let out = trust_ir_function_to_chc_translation_output(
                        &module,
                        func,
                        &TranslateOptions::default(),
                    )
                    .expect("translates");
                    assert!(error_reachable(&out), "{what}: out of bounds");
                    continue;
                }
                let returns = outcome.expect(&what).returns;
                let lane = |index: usize| returns[index].as_int().expect("u32").as_unsigned();
                let (a, b) = (lane(0), lane(1));
                let (module, func) = probe(dst, fill, bytes, Some((a, b)));
                let out = trust_ir_function_to_chc_translation_output(
                    &module,
                    func,
                    &TranslateOptions::default(),
                )
                .expect("translates");
                let whole = bytes == 0 || bytes == 4 || (bytes == 8 && matches!(dst, Dst::Cell));
                if whole {
                    assert!(out.diagnostics.is_empty(), "{what}: {:?}", reasons(&out));
                    assert!(!error_reachable(&out), "{what}: ({a:#x}, {b:#x}) must be PROVED");
                    let (module, func) = probe(dst, fill, bytes, Some((a ^ 1, b)));
                    let wrong = trust_ir_function_to_chc_translation_output(
                        &module,
                        func,
                        &TranslateOptions::default(),
                    )
                    .expect("translates");
                    assert!(error_reachable(&wrong), "{what}: a wrong `a` must be REFUTED");
                } else {
                    assert_eq!(
                        reasons(&out),
                        vec![TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange],
                        "{what}"
                    );
                    assert!(error_reachable(&out), "{what}");
                }
            }
        }
    }
}

/// A fill writes only integer leaves exactly: a `bool` cell's byte image has
/// invalid values, so a fill of it fails closed; a copy between different types
/// (a `u32` image into `[u8; 4]`) has no exact value either.
#[test]
fn a_fill_of_a_non_integer_and_a_reinterpreting_copy_fail_closed() {
    let mut mb = ModuleBuilder::new("bulk_bool");
    let u8_id = mb.add_type(Ty::U8);
    let bytes4 = Ty::Array(u8_id, 4);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let flag = fb.alloca(Ty::Bool);
    let t = fb.const_value(Ty::Bool, Constant::Bool(true));
    fb.store(Ty::Bool, flag, t);
    let one = fb.iconst(Ty::U8, 1);
    let count = fb.const_value(Ty::U64, Constant::Int(1));
    fb.memset(flag, one, count);
    let word = fb.alloca(Ty::U32);
    let w = fb.iconst(Ty::U32, 0x0403_0201);
    fb.store(Ty::U32, word, w);
    let image = fb.alloca(bytes4.clone());
    let z = fb.const_value(bytes4.clone(), Constant::splat(Constant::Int(0), 4));
    fb.store(bytes4.clone(), image, z);
    let four = fb.const_value(Ty::U64, Constant::Int(4));
    fb.memcopy(image, word, four, false);
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let out = trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates");
    assert_eq!(
        reasons(&out),
        vec![
            TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange,
            TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange
        ]
    );
    assert!(error_reachable(&out));
}

// ---------------------------------------------------------------------------
// trust-ir wire v58: declared closure frames and nominal type origins
// ---------------------------------------------------------------------------

/// What a closure probe declares for its closure type in `Module.closure_layouts`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Frame {
    /// No row: the closure type has no byte image (every closure before v58).
    Undeclared,
    /// rustc's upvar reordering: capture 1 at byte 0, capture 0 at byte 4.
    Reordered,
}

/// What a closure probe asserts about the destination's captures after the write.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClosureExpect {
    /// Each capture equals the destination's initial capture.
    Old,
    /// Each capture equals the source's capture.
    Source,
    /// Each capture is the fill byte `0x5A` repeated.
    Filled,
    /// Each capture is `0x5A5A_5A5B` (refuted by every write).
    Wrong,
}

/// `f(src, dst0)` over a closure type capturing `(u32, u32)`: both values stored
/// in their own stack cells, one bulk write (a copy from the source cell or a
/// fill with `0x5A`) of `bytes` into the destination cell, then an assertion of
/// `expect` on each capture of the reloaded destination.
fn closure_probe(frame: Frame, fill: bool, bytes: u64, expect: ClosureExpect) -> Module {
    closure_probe_input(frame, fill, bytes, expect, true)
}

fn closure_probe_input(
    frame: Frame,
    fill: bool,
    bytes: u64,
    expect: ClosureExpect,
    initialized: bool,
) -> Module {
    let target = trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    };
    let mut mb = ModuleBuilder::new_with_target_info("bulk_closure", target);
    let apparent = mb.add_func_type(vec![], vec![Ty::U32]);
    let closure = mb
        .add_closure_type(trust_ir::ClosureTy { func: apparent, captures: vec![Ty::U32, Ty::U32] });
    let cty = Ty::Closure(closure);
    let ft = mb.add_func_type(
        if initialized {
            vec![cty.clone(), cty.clone(), Ty::U32, Ty::U32, Ty::U32, Ty::U32]
        } else {
            vec![cty.clone(), cty.clone()]
        },
        vec![],
    );
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let (src, dst0) = if initialized {
        let src_seed = fb.add_block_param(entry, cty.clone());
        let dst_seed = fb.add_block_param(entry, cty.clone());
        let a = fb.add_block_param(entry, Ty::U32);
        let b = fb.add_block_param(entry, Ty::U32);
        let c = fb.add_block_param(entry, Ty::U32);
        let d = fb.add_block_param(entry, Ty::U32);
        let src_a = fb.insert_field(cty.clone(), src_seed, 0, a);
        let src = fb.insert_field(cty.clone(), src_a, 1, b);
        let dst_c = fb.insert_field(cty.clone(), dst_seed, 0, c);
        (src, fb.insert_field(cty.clone(), dst_c, 1, d))
    } else {
        (fb.add_block_param(entry, cty.clone()), fb.add_block_param(entry, cty.clone()))
    };
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
        let want = match expect {
            ClosureExpect::Old => fb.extract_field(Ty::U32, dst0, capture),
            ClosureExpect::Source => fb.extract_field(Ty::U32, src, capture),
            ClosureExpect::Filled => fb.uconst(Ty::U32, 0x5A5A_5A5A),
            ClosureExpect::Wrong => fb.uconst(Ty::U32, 0x5A5A_5A5B),
        };
        let holds = fb.icmp(ICmpOp::Eq, Ty::U32, got, want);
        fb.assert(holds);
    }
    fb.ret(vec![]);
    fb.build();
    // A genuine matching closure implementation: captures precede the apparent
    // arguments. No invocation or proof authority is substituted by this body.
    let implementation = mb.add_func_type(vec![Ty::U32, Ty::U32], vec![Ty::U32]);
    let mut body = mb.function("closure_body", implementation);
    let entry = body.create_block();
    body.set_entry(entry);
    body.switch_to_block(entry);
    let captured = body.add_block_param(entry, Ty::U32);
    body.add_block_param(entry, Ty::U32);
    body.ret(vec![captured]);
    body.build();
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    if frame == Frame::Reordered {
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

/// trust-ir wire v58 `Module.closure_layouts` gives a first-class closure a
/// declared byte frame whose capture offsets follow CAPTURE order in any
/// physical order. This lane models a closure as the aggregate of its captures
/// and takes only the frame's SIZE from trust-ir (`Module::ty_layout_shape`):
///
/// * a bulk write naming the WHOLE closure object is exact (a copy moves every
///   capture, a fill sets every integer capture to the repeated byte), which
///   holds whatever the offsets are;
/// * a range strictly inside the frame fails closed by name
///   (`BulkMemoryUnplacedRange`): the lane never derives a capture's byte
///   offset, so the reordered frame below, where bytes `0..4` are capture 1,
///   can never be read as capture 0;
/// * a closure type with no row has no byte image, so every non-empty write
///   keeps the pre-v58 unplaced-operand refusal (`BulkMemoryTransfer`).
#[test]
fn closure_cells_take_only_the_declared_frame_size() {
    let translate = |module: &Module| {
        trust_ir_function_to_chc_translation_output(
            module,
            FuncId::new(0),
            &TranslateOptions::default(),
        )
        .expect("translates")
    };
    // The fixture is a valid v58 module: the reordered frame is coherent.
    let declared = closure_probe(Frame::Reordered, false, 8, ClosureExpect::Source);
    let errors = trust_ir_build::validate_module(&declared);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(
        declared
            .ty_layout_shape(&Ty::Closure(trust_ir::ClosureTyId::new(0)))
            .ok()
            .map(|shape| shape.size_bits),
        Some(64)
    );
    assert!(
        closure_probe(Frame::Undeclared, false, 8, ClosureExpect::Source)
            .ty_layout_shape(&Ty::Closure(trust_ir::ClosureTyId::new(0)))
            .is_err(),
        "a closure type with no row has no byte image"
    );

    for fill in [false, true] {
        let whole = if fill { ClosureExpect::Filled } else { ClosureExpect::Source };
        let what = |frame: Frame, bytes: u64| format!("{frame:?} fill={fill} bytes={bytes}");

        // Declared frame, the whole object: exact, proved, and the wrong twin refuted.
        let out = translate(&closure_probe(Frame::Reordered, fill, 8, whole));
        let label = what(Frame::Reordered, 8);
        assert!(out.diagnostics.is_empty(), "{label}: {:?}", reasons(&out));
        assert!(!error_reachable(&out), "{label}: the whole-object write must be PROVED");
        let wrong = translate(&closure_probe(Frame::Reordered, fill, 8, ClosureExpect::Wrong));
        assert!(error_reachable(&wrong), "{label}: a wrong capture must be REFUTED");
        let old = translate(&closure_probe(Frame::Reordered, fill, 8, ClosureExpect::Old));
        assert!(error_reachable(&old), "{label}: the pre-write capture must be REFUTED");

        // Declared frame, a zero count: a no-op.
        let out = translate(&closure_probe(Frame::Reordered, fill, 0, ClosureExpect::Old));
        let label = what(Frame::Reordered, 0);
        assert!(out.diagnostics.is_empty(), "{label}: {:?}", reasons(&out));
        assert!(!error_reachable(&out), "{label}: a zero count must leave the cell");

        // Declared frame, a range inside it: refused by name, never proved.
        for bytes in [1u64, 4] {
            for expect in [ClosureExpect::Old, whole] {
                let out = translate(&closure_probe(Frame::Reordered, fill, bytes, expect));
                let label = format!("{} {expect:?}", what(Frame::Reordered, bytes));
                assert_eq!(
                    reasons(&out),
                    vec![TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange],
                    "{label}"
                );
                assert!(error_reachable(&out), "{label}");
            }
        }

        // Declared frame, past it: undefined behaviour is a reachable error.
        let out = translate(&closure_probe(Frame::Reordered, fill, 9, whole));
        assert!(error_reachable(&out), "{}: out of bounds", what(Frame::Reordered, 9));

        // No frame: no byte image, so the write keeps the unplaced-operand refusal.
        for bytes in [4u64, 8] {
            let out = translate(&closure_probe(Frame::Undeclared, fill, bytes, whole));
            let label = what(Frame::Undeclared, bytes);
            let mut expected = vec![TrustIrChcUnsupportedReason::BulkMemoryTransfer];
            if !fill {
                // Without a frame the copy has no source byte image. The
                // following load, two projections, two comparisons and two
                // assertions must retain their separate consumption refusals.
                expected.extend([TrustIrChcUnsupportedReason::OperandConsumption; 7]);
            }
            assert_eq!(reasons(&out), expected, "{label}");
            assert!(error_reachable(&out), "{label}");
        }
    }
}

#[test]
fn original_partial_closure_entry_store_remains_unsupported_and_refused() {
    let module = closure_probe_input(Frame::Reordered, false, 8, ClosureExpect::Source, false);
    let ty = module.func_types[module.functions[0].ty.as_usize()].params[0].clone();
    let closure = |poison| InterpretValue {
        ty: ty.clone(),
        kind: trust_ir::interpret::InterpretValueKind::Closure {
            func: FuncId::new(1),
            captures: vec![
                if poison {
                    InterpretValue {
                        ty: Ty::U32,
                        kind: trust_ir::interpret::InterpretValueKind::Uninit,
                    }
                } else {
                    InterpretValue::int(Ty::U32, 0).unwrap()
                },
                InterpretValue::int(Ty::U32, 0).unwrap(),
            ],
        },
    };
    let error = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [closure(true), closure(false)])
        .unwrap_err();
    assert_eq!(
        error.code,
        // This entry-only fixture has no MakeClosure binding for its storage
        // target. The interpreter declines with an unsupported TypeError; it
        // supplies no UB or byte/refinement oracle for the CHC frame model.
        InterpretErrorCode::TypeError,
        "{error:?}"
    );
    assert!(error.message.contains("missing closure storage target"), "{error:?}");
    assert!(
        reasons(
            &trust_ir_function_to_chc_translation_output(
                &module,
                FuncId::new(0),
                &TranslateOptions::default()
            )
            .unwrap()
        )
        .contains(&TrustIrChcUnsupportedReason::OperandConsumption)
    );
}

/// trust-ir wire v58 `StructDef.origin` names the source entity a definition is
/// the image of. It is identity for cross-module joins (where it may only split
/// or refuse) and carries no value semantics: this lane encodes a struct by its
/// id, fields and declared layout, so a keyed definition must translate to
/// exactly the encoding of its unkeyed twin, under either key form.
#[test]
fn a_struct_origin_key_changes_no_encoding() {
    /// The CHC without `declared_var_names`, a `HashSet` index over the declared
    /// variables whose `Debug` order is not deterministic.
    fn encoding(vc: &trust_mc_core::chc::ChcVc) -> String {
        let text = format!("{vc:?}");
        let start = text.find("declared_var_names: {").expect("ChcVc's Debug names its index");
        let end = start + text[start..].find("}, ").expect("the index closes") + 3;
        format!("{}{}", &text[..start], &text[end..])
    }

    use trust_ir::proof::{ProofDigest, ProofDigestAlgorithm};
    use trust_ir::ty::TypeOrigin;

    fn probe(origin: Option<TypeOrigin>, want_a: u128) -> Module {
        probe_case(origin, want_a, true)
    }

    fn probe_case(origin: Option<TypeOrigin>, want_a: u128, initialized: bool) -> Module {
        let mut mb = ModuleBuilder::new("keyed_struct");
        let id = mb.add_struct(StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "keyed_struct::S".to_string(),
            fields: vec![
                FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
                FieldDef { name: "b".into(), ty: Ty::U32, offset: Some(4) },
            ],
            size: Some(8),
            align: Some(4),
            repr: StructRepr::Rust,
            origin,
        });
        let sty = Ty::Struct(id);
        let ft = mb.add_func_type(if initialized { vec![Ty::U32] } else { vec![] }, vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let cell = fb.alloca(sty.clone());
        if initialized {
            let b = fb.add_block_param(entry, Ty::U32);
            let one = fb.iconst(Ty::I64, 1);
            let lane_b = fb.gep(Ty::U32, cell, vec![one]);
            fb.store(Ty::U32, lane_b, b);
        }
        let zero = fb.iconst(Ty::I64, 0);
        let lane = fb.gep(Ty::U32, cell, vec![zero]);
        let value = fb.iconst(Ty::U32, 0x31);
        fb.store(Ty::U32, lane, value);
        let byte = fb.iconst(Ty::U8, 0x5A);
        let four = fb.const_value(Ty::U64, Constant::Int(4));
        fb.memset(cell, byte, four);
        let after = fb.load(sty, cell);
        let a = fb.extract_field(Ty::U32, after, 0);
        let want = fb.const_value(Ty::U32, Constant::Int(want_a as i128));
        let holds = fb.icmp(ICmpOp::Eq, Ty::U32, a, want);
        fb.assert(holds);
        fb.ret(vec![]);
        fb.build();
        mb.build().expect("ModuleBuilder::build: test fixture")
    }
    let original = probe_case(None, 0x5A5A_5A5A, false);
    assert_eq!(
        Interpreter::with_module(&original).execute_func(FuncId::new(0), []).unwrap_err().code,
        InterpretErrorCode::UndefinedBehavior
    );
    let refused = trust_ir_function_to_chc_translation_output(
        &original,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .unwrap();
    assert!(reasons(&refused).contains(&TrustIrChcUnsupportedReason::OperandConsumption));
    let digest =
        |seed: u8| ProofDigest { algorithm: ProofDigestAlgorithm::Sha256, bytes: [seed; 32] };
    let keys = [
        TypeOrigin::Rust {
            stable_crate_id: 0x0123_4567_89ab_cdef,
            def_path_hash: [0xA5; 16],
            args_digest: digest(1),
        },
        TypeOrigin::Clean { decl: "Keyed.S".to_string(), env_digest: digest(2) },
    ];
    for want_a in [0x5A5A_5A5A_u128, 0x31] {
        let unkeyed = probe(None, want_a);
        let unkeyed_out = trust_ir_function_to_chc_translation_output(
            &unkeyed,
            FuncId::new(0),
            &TranslateOptions::default(),
        )
        .expect("translates");
        assert!(unkeyed_out.diagnostics.is_empty(), "{:?}", reasons(&unkeyed_out));
        assert_eq!(error_reachable(&unkeyed_out), want_a != 0x5A5A_5A5A, "want_a={want_a:#x}");
        for key in &keys {
            let keyed = probe(Some(key.clone()), want_a);
            assert_eq!(
                format!("{:?}", trust_ir_build::validate_module(&keyed)),
                format!("{:?}", trust_ir_build::validate_module(&unkeyed)),
                "{key}: the key must add no validation verdict"
            );
            let keyed_out = trust_ir_function_to_chc_translation_output(
                &keyed,
                FuncId::new(0),
                &TranslateOptions::default(),
            )
            .expect("translates");
            assert_eq!(
                encoding(&keyed_out.vc),
                encoding(&unkeyed_out.vc),
                "{key}: the key must not change the encoding"
            );
            assert_eq!(reasons(&keyed_out), reasons(&unkeyed_out), "{key}");
        }
    }
}

// ---------------------------------------------------------------------------
// Symbolic counts
// ---------------------------------------------------------------------------

fn copy_u8x4(bulk: Bulk, assume: Vec<(ICmpOp, u64)>) -> Fixture {
    Fixture { elem: Ty::U8, len: 4, init: Init::Distinct, bulk, count: Count::Param, assume }
}

fn expect_all(lanes: [u128; 4]) -> Tail {
    Tail::Expect(lanes.iter().enumerate().map(|(j, v)| (j as u64, *v)).collect())
}

/// One encoding serves every count: pinned to a whole object it is that write,
/// pinned to 0 it is a no-op, and the fail-closed rule fires exactly on a lane
/// run (here `n` in `{2, 3}`) and the bounds rule exactly past the cell.
#[test]
fn a_symbolic_count_is_exact_wherever_it_names_a_whole_object() {
    let whole = Bulk::Copy { dst: At::Cell, src: At::Cell, overlap: false };
    let pinned = |n: u64, tail: Tail| chc(&copy_u8x4(whole, vec![(ICmpOp::Eq, n)]), &tail);
    assert!(!error_reachable(&pinned(4, expect_all([0x41, 0x42, 0x43, 0x44]))));
    assert!(!error_reachable(&pinned(0, expect_all([1, 2, 3, 4]))));
    assert!(!error_reachable(&pinned(1, expect_all([0x41, 2, 3, 4]))));
    assert!(error_reachable(&pinned(4, expect_all([1, 2, 3, 4]))));
    assert!(error_reachable(&pinned(1, expect_all([0x41, 0x42, 3, 4]))));

    // Unpinned: a lane run (2 or 3) and an overrun (5+) are reachable errors.
    let free = chc(&copy_u8x4(whole, Vec::new()), &Tail::Nothing);
    assert!(reasons(&free).contains(&TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange));
    assert!(error_reachable(&free));
    for (n, reachable) in [(0, false), (1, false), (2, true), (3, true), (4, false), (5, true)] {
        let out = chc(&copy_u8x4(whole, vec![(ICmpOp::Eq, n)]), &Tail::Nothing);
        assert_eq!(error_reachable(&out), reachable, "n = {n}");
    }
    // Excluding exactly the lane runs and the overrun leaves nothing reachable.
    let excluded = chc(
        &copy_u8x4(whole, vec![(ICmpOp::Ule, 4), (ICmpOp::Ne, 2), (ICmpOp::Ne, 3)]),
        &Tail::Nothing,
    );
    assert!(!error_reachable(&excluded), "the guards are exact");
}

/// `memcpy(&a[0], &a[1], n)` overlaps exactly when `n >= 2`; `memmove` never
/// faults and reads its whole source first.
#[test]
fn overlap_is_undefined_for_memcpy_and_defined_for_memmove() {
    for overlap in [false, true] {
        let bulk = Bulk::Within { dst: At::Lane(0), src: At::Lane(1), overlap };
        let one = chc(&copy_u8x4(bulk, vec![(ICmpOp::Eq, 1)]), &expect_all([2, 2, 3, 4]));
        assert!(!error_reachable(&one), "overlap={overlap}: one lane shifts down exactly");
        let two = chc(&copy_u8x4(bulk, vec![(ICmpOp::Eq, 2)]), &Tail::Nothing);
        // memcpy: undefined; memmove: a two-lane run, which fails closed.
        assert!(error_reachable(&two), "overlap={overlap}");
        if overlap {
            assert!(reasons(&two).contains(&TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange));
        }
    }
    // A memmove of a cell onto itself is the identity; a memcpy of it faults.
    let onto_itself = |overlap| {
        chc(
            &copy_u8x4(
                Bulk::Within { dst: At::Cell, src: At::Cell, overlap },
                vec![(ICmpOp::Eq, 4)],
            ),
            &expect_all([1, 2, 3, 4]),
        )
    };
    assert!(!error_reachable(&onto_itself(true)));
    assert!(error_reachable(&onto_itself(false)));
}

// ---------------------------------------------------------------------------
// Counterexamples
// ---------------------------------------------------------------------------

/// `f(n, b) { d = [1, 2, 3, 4]; assume(n is not a lane run); memset(d, b, n);
/// assert(d[0] != 0x11) }`.
fn fill_probe() -> (Module, FuncId, ValueId, ValueId) {
    let mut mb = ModuleBuilder::new("bulk_cex");
    let u8_id = mb.add_type(Ty::U8);
    let arr = Ty::Array(u8_id, 4);
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U8], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = fb.add_block_param(entry, Ty::U64);
    let b = fb.add_block_param(entry, Ty::U8);
    let cell = fb.alloca(arr.clone());
    let init = fb.const_value(arr.clone(), initial(Init::Distinct, 0, 4));
    fb.store(arr.clone(), cell, init);
    for excluded in [2, 3] {
        let k = fb.iconst(Ty::U64, excluded);
        let ne = fb.icmp(ICmpOp::Ne, Ty::U64, n, k);
        fb.assume(ne);
    }
    fb.memset(cell, b, n);
    let after = fb.load(arr, cell);
    let zero = fb.iconst(Ty::U64, 0);
    let first = fb.extract_element(Ty::U8, after, zero);
    let bad = fb.iconst(Ty::U8, 0x11);
    let holds = fb.icmp(ICmpOp::Ne, Ty::U8, first, bad);
    fb.assert(holds);
    fb.ret(vec![]);
    fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0), n, b)
}

/// Does the interpreter fail (assertion or undefined behaviour) on these inputs?
fn interpreter_fails(module: &Module, func: FuncId, n: u64, b: u8) -> bool {
    let args = vec![
        InterpretValue::int(Ty::U64, i128::from(n)).expect("u64"),
        InterpretValue::int(Ty::U8, i128::from(b)).expect("u8"),
    ];
    match Interpreter::with_module(module).execute_func(func, args) {
        Ok(_) => false,
        Err(error) => {
            assert_ne!(error.code, InterpretErrorCode::AssumeViolated, "n={n} b={b}");
            true
        }
    }
}

fn parse_bv(text: &str) -> Option<u128> {
    let text = text.trim();
    if let Some(hex) = text.strip_prefix("#x") {
        return u128::from_str_radix(hex, 16).ok();
    }
    if let Some(bin) = text.strip_prefix("#b") {
        return u128::from_str_radix(bin, 2).ok();
    }
    if let Some(rest) = text.strip_prefix("(_ bv") {
        return rest.split_whitespace().next()?.parse().ok();
    }
    text.parse().ok()
}

/// A model of `constraints`, when they are satisfiable.
fn model(vc: &trust_mc_core::chc::ChcVc, constraints: &[Expr]) -> Option<BTreeMap<String, String>> {
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic("QF_ABV");
    for var in vc.vars() {
        let _ = program.declare_const(var.name.to_string(), var.sort.clone());
    }
    for constraint in constraints {
        program.assert(constraint.clone());
    }
    program.check_sat();
    match ay_bindings::execute_direct::execute(&program).expect("in-process AY") {
        ay_bindings::execute_direct::ExecuteResult::Counterexample { model, .. } => {
            Some(model.into_iter().collect())
        }
        _ => None,
    }
}

/// Every reachable error is a real failing run: each error rule's model replays
/// as a failure of the reference interpreter, and on a grid of concrete inputs
/// the verdict is exactly the interpreter's.
#[test]
fn every_counterexample_replays_as_a_real_failure() {
    let (module, func, n, b) = fill_probe();
    let out =
        trust_ir_function_to_chc_translation_output(&module, func, &TranslateOptions::default())
            .expect("translates");
    let n_var = format!("bb0_v{}", n.index());
    let b_var = format!("bb0_v{}", b.index());
    let n_expr = super::smt_array_tests::var_named(&out, &n_var);
    let b_expr = super::smt_array_tests::var_named(&out, &b_var);

    let mut replayed = 0;
    for body in error_rule_bodies(&out.vc) {
        let Some(model) = model(&out.vc, &body) else {
            continue;
        };
        let n_value = model.get(&n_var).and_then(|v| parse_bv(v)).expect("n in the model");
        let b_value = model.get(&b_var).and_then(|v| parse_bv(v)).expect("b in the model");
        let (n_value, b_value) = (n_value as u64, b_value as u8);
        assert!(
            interpreter_fails(&module, func, n_value, b_value),
            "the counterexample n={n_value} b={b_value:#x} must be a real failure"
        );
        replayed += 1;
    }
    assert!(replayed >= 2, "both the assertion and the overrun are reachable");

    for n_value in 0..=6u64 {
        for b_value in [0x00u8, 0x11, 0xFF] {
            if n_value == 2 || n_value == 3 {
                continue;
            }
            let pin = [
                n_expr.clone().eq(Expr::bitvec_const(n_value, 64)),
                b_expr.clone().eq(Expr::bitvec_const(b_value, 8)),
            ];
            let reachable = error_rule_bodies(&out.vc).iter().any(|body| {
                let mut body = body.clone();
                body.extend(pin.iter().cloned());
                satisfiable(&out.vc, &body)
            });
            assert_eq!(
                reachable,
                interpreter_fails(&module, func, n_value, b_value),
                "n={n_value} b={b_value:#x}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Size
// ---------------------------------------------------------------------------

/// Small lengths on purpose (see `translate_chc_smt_array_tests.rs`): an equal
/// encoding at these lengths already shows nothing is sized by the length or the
/// byte count, and a regression fails as a cheap `assert_eq!`.
const LENGTHS: [u64; 5] = [3, 4, 256, 257, 4097];

#[test]
fn the_encoding_does_not_depend_on_the_length_or_the_byte_count() {
    type Shape = fn(u64) -> Fixture;
    let shapes: [(&str, Shape); 7] = [
        ("whole copy", |len| Fixture {
            elem: Ty::U32,
            len,
            init: Init::Splat,
            bulk: Bulk::Copy { dst: At::Cell, src: At::Cell, overlap: false },
            count: Count::Const(len * 4),
            assume: Vec::new(),
        }),
        ("lane copy", |len| Fixture {
            elem: Ty::U32,
            len,
            init: Init::Splat,
            bulk: Bulk::Copy { dst: At::Lane(1), src: At::Lane(2), overlap: false },
            count: Count::Const(4),
            assume: Vec::new(),
        }),
        ("lane run", |len| Fixture {
            elem: Ty::U32,
            len,
            init: Init::Splat,
            bulk: Bulk::Copy { dst: At::Lane(0), src: At::Lane(0), overlap: false },
            count: Count::Const(8),
            assume: Vec::new(),
        }),
        ("whole fill", |len| Fixture {
            elem: Ty::U32,
            len,
            init: Init::Splat,
            bulk: Bulk::Fill { dst: At::Cell, byte: 0xAB },
            count: Count::Const(len * 4),
            assume: Vec::new(),
        }),
        ("overrun", |len| Fixture {
            elem: Ty::U32,
            len,
            init: Init::Splat,
            bulk: Bulk::Fill { dst: At::Lane(1), byte: 0xAB },
            count: Count::Const(len * 4),
            assume: Vec::new(),
        }),
        ("symbolic copy", |len| Fixture {
            elem: Ty::U32,
            len,
            init: Init::Splat,
            bulk: Bulk::Within { dst: At::Lane(0), src: At::Lane(1), overlap: true },
            count: Count::Param,
            assume: Vec::new(),
        }),
        ("symbolic fill", |len| Fixture {
            elem: Ty::U32,
            len,
            init: Init::Splat,
            bulk: Bulk::Fill { dst: At::Cell, byte: 0xAB },
            count: Count::Param,
            assume: Vec::new(),
        }),
    ];
    let tail = Tail::Expect(vec![(0, 7), (1, 9)]);
    for (name, shape) in shapes {
        let sizes: Vec<VcSize> =
            LENGTHS.iter().map(|len| vc_size(&chc(&shape(*len), &tail))).collect();
        for (len, size) in LENGTHS.iter().zip(&sizes) {
            assert_eq!(
                size, &sizes[0],
                "{name}: the encoding at length {len} differs from length 3"
            );
        }
    }

    // At one length, the constant count enters nowhere but a folded comparison:
    // every count that lands on the same class has the same encoding.
    let at = |bulk: Bulk, bytes: u64| {
        vc_size(&chc(
            &Fixture {
                elem: Ty::U8,
                len: 4097,
                init: Init::Splat,
                bulk,
                count: Count::Const(bytes),
                assume: Vec::new(),
            },
            &tail,
        ))
    };
    let run = Bulk::Fill { dst: At::Cell, byte: 1 };
    assert_eq!(at(run, 2), at(run, 4000), "two lane runs");
    let over = Bulk::Fill { dst: At::Lane(5), byte: 1 };
    assert_eq!(at(over, 4093), at(over, 1 << 40), "two overruns");
}

// ---------------------------------------------------------------------------
// The gate and the translator's own cell decision
// ---------------------------------------------------------------------------

/// The translator tracks a cell whose address reaches a bulk operation (its arm
/// writes the cell exactly or havocs it), but every proof-authority lane still
/// refuses that cell, so a proof-grade bundle never reaches the exact arm with a
/// stack operand: its `MemCopy`/`MemSet` keep the old fail-closed model. Widening
/// the gate is decision TMC-3 (`docs/DECISION_QUEUE.md`).
#[test]
fn the_gate_still_refuses_every_cell_a_bulk_operation_reaches() {
    for bulk in [
        Bulk::Copy { dst: At::Cell, src: At::Cell, overlap: false },
        Bulk::Copy { dst: At::Lane(1), src: At::Lane(2), overlap: true },
        Bulk::Fill { dst: At::Cell, byte: 0 },
    ] {
        let fx = Fixture {
            elem: Ty::U8,
            len: 4,
            init: Init::Distinct,
            bulk,
            count: Count::Const(1),
            assume: Vec::new(),
        };
        let built = build(&fx, &Tail::Nothing);
        let function = built.module.function_by_id(built.func).expect("f");
        let mut cells = vec![built.dst_cell];
        if matches!(bulk, Bulk::Copy { .. }) {
            cells.push(built.src_cell);
        }
        for cell in cells {
            assert_eq!(
                stack_alloca_escape_classification(function, cell),
                StackCellEscape::Unbounded,
                "{bulk:?}: the gate's classification is unchanged"
            );
            assert_ne!(
                stack_alloca_escape_classification_with(function, cell, BulkMemoryUse::Tracked),
                StackCellEscape::Unbounded,
                "{bulk:?}: the translator tracks the cell"
            );
            assert!(
                !single_cell_alloca_is_admissible(&built.module, function, cell, &built.cell_ty),
                "{bulk:?}: no proof-authority lane admits the cell"
            );
        }
    }
}

/// A destination with no exact place keeps the old model, now silent where the
/// count is zero (a no-op even through a dangling pointer).
#[test]
fn a_zero_count_through_an_unknown_pointer_is_a_no_op() {
    for bytes in [0u64, 4] {
        let mut mb = ModuleBuilder::new("bulk_null");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let null = fb.null_ptr();
        let byte = fb.iconst(Ty::U8, 0);
        let count = fb.const_value(Ty::U64, Constant::Int(i128::from(bytes)));
        fb.memset(null, byte, count);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let out = trust_ir_function_to_chc_translation_output(
            &module,
            FuncId::new(0),
            &TranslateOptions::default(),
        )
        .expect("translates");
        if bytes == 0 {
            assert!(out.diagnostics.is_empty());
            assert!(!error_reachable(&out));
        } else {
            assert_eq!(reasons(&out), vec![TrustIrChcUnsupportedReason::BulkMemoryTransfer]);
            assert!(error_reachable(&out));
        }
    }
}

/// With memory checks off there is no rule, and an undefined execution leaves
/// the destination unknown: an overrun never proves what an in-bounds write would.
#[test]
fn with_checks_off_an_undefined_write_havocs_the_cell() {
    let fx = |n| Fixture {
        elem: Ty::U8,
        len: 4,
        init: Init::Distinct,
        bulk: Bulk::Fill { dst: At::Cell, byte: 0x22 },
        count: Count::Const(n),
        assume: Vec::new(),
    };
    let unchecked = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let translate = |fx: &Fixture, tail: &Tail| {
        let built = build(fx, tail);
        trust_ir_function_to_chc_translation_output(&built.module, built.func, &unchecked)
            .expect("translates")
    };
    let filled = expect_all([0x22, 0x22, 0x22, 0x22]);
    assert!(!error_reachable(&translate(&fx(4), &filled)), "in bounds: exact");
    let overrun = translate(&fx(5), &filled);
    assert!(overrun.diagnostics.is_empty());
    assert!(error_reachable(&overrun), "past the cell: unknown, never proved");
    let run = translate(&fx(2), &expect_all([0x22, 0x22, 3, 4]));
    assert!(run.diagnostics.is_empty());
    assert!(error_reachable(&run), "a lane run havocs the cell, even unchecked");
    // THE STALE-READ ORACLE: with no fail-closed rule to hide behind, only the
    // havoc stands between the pre-write `[1, 2, 3, 4]` and a false proof.
    for n in [2, 3, 5] {
        let stale = translate(&fx(n), &expect_all([1, 2, 3, 4]));
        assert!(error_reachable(&stale), "n = {n}: the pre-write cell is never read back");
    }
}

/// Every value the bulk arm makes up — the havoc of an unplaced range, the other
/// cases of a symbolic count, an undefined write with checks off — is declared as
/// a TRANSLATION HAVOC (`ChcVc::declare_havoc_var`), so a refutation gate never
/// takes a constraint on it for a definition (the bounded-unroll grounding gate
/// reads `trust_mc_core::chc::is_translation_havoc_var`). Every other variable is
/// a block-relation argument. Each probe declares MORE havocs than the same
/// fixture with an exact count, so the havocs counted are the arm's own.
#[test]
fn every_value_the_bulk_arm_makes_up_is_a_declared_havoc() {
    use trust_mc_core::chc::is_translation_havoc_var;

    let fx = |bulk, count| Fixture {
        elem: Ty::U8,
        len: 4,
        init: Init::Distinct,
        bulk,
        count,
        assume: Vec::new(),
    };
    let unchecked = TranslateOptions { check_memory_bounds: false, ..TranslateOptions::default() };
    let translate = |fx: &Fixture, options: &TranslateOptions| {
        let built = build(fx, &Tail::Expect(vec![(0, 1)]));
        trust_ir_function_to_chc_translation_output(&built.module, built.func, options)
            .expect("translates")
    };
    let havocs = |output: &ChcTranslationOutput| {
        let names: Vec<String> = output.vc.vars().iter().map(|var| var.name.to_string()).collect();
        for name in &names {
            assert!(
                name.starts_with("bb") || is_translation_havoc_var(name),
                "{name}: neither a block-relation argument nor a declared havoc ({names:?})"
            );
        }
        names.iter().filter(|name| is_translation_havoc_var(name)).count()
    };
    let lane_copy = Bulk::Copy { dst: At::Lane(0), src: At::Lane(0), overlap: false };
    let fill = Bulk::Fill { dst: At::Cell, byte: 0x5A };
    let checked = TranslateOptions::default();
    for (what, probe, exact, options) in [
        ("lane run", fx(lane_copy, Count::Const(2)), fx(lane_copy, Count::Const(1)), &checked),
        ("symbolic count", fx(fill, Count::Param), fx(fill, Count::Const(4)), &checked),
        ("unchecked overrun", fx(fill, Count::Const(5)), fx(fill, Count::Const(4)), &unchecked),
    ] {
        let made_up = havocs(&translate(&probe, options));
        let baseline = havocs(&translate(&exact, options));
        assert!(made_up > baseline, "{what}: {made_up} havocs vs {baseline} for the exact write");
    }
}

// ---------------------------------------------------------------------------
// Size in the nesting depth
// ---------------------------------------------------------------------------

/// What `depth_chain` does to the cell before it reads it back.
#[derive(Clone, Copy, Debug)]
enum ChainWrite {
    Nothing,
    LoadStore,
    ConstFill,
    SymbolicFill,
    ConstCopy,
    SymbolicCopy,
}

/// `S_0 = { inner: u8 @ 0, tail: u8 @ 1 }`, `S_k = { inner: S_{k-1} @ 0, tail:
/// u8 @ k + 1 }`: `depth` objects start at the cell's address, one per level, and
/// the cell has `depth + 1` leaves. The written cell is carried whole into a
/// successor block, so every leaf is a relation argument.
fn depth_chain(depth: usize, write: ChainWrite) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("depth_chain");
    let mut ty = Ty::U8;
    let mut size = 1u64;
    for level in 0..depth {
        let id = mb.add_struct(StructDef {
            id: trust_ir::value::StructId::new(u32::try_from(level).expect("small")),
            name: format!("depth_chain::S{level}"),
            fields: vec![
                FieldDef { name: "inner".into(), ty: ty.clone(), offset: Some(0) },
                FieldDef { name: "tail".into(), ty: Ty::U8, offset: Some(size) },
            ],
            size: Some(size + 1),
            align: Some(1),
            repr: StructRepr::Rust,
            origin: None,
        });
        ty = Ty::Struct(id);
        size += 1;
    }
    let symbolic = matches!(write, ChainWrite::SymbolicFill | ChainWrite::SymbolicCopy);
    let ft = mb.add_func_type(if symbolic { vec![Ty::U64] } else { vec![] }, vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = symbolic.then(|| fb.add_block_param(entry, Ty::U64));
    let cell = fb.alloca(ty.clone());
    let other = fb.alloca(ty.clone());
    // Both cells hold a value before the write (each its own fresh one).
    for slot in [other, cell] {
        let value = fb.load(ty.clone(), slot);
        fb.store(ty.clone(), slot, value);
    }
    let byte = fb.iconst(Ty::U8, 0x5A);
    let whole = |fb: &mut trust_ir_build::FunctionBuilder<'_>| {
        fb.const_value(Ty::U64, Constant::Int(i128::from(size)))
    };
    match write {
        ChainWrite::Nothing => {}
        ChainWrite::LoadStore => {
            let value = fb.load(ty.clone(), other);
            fb.store(ty.clone(), cell, value);
        }
        ChainWrite::ConstFill => {
            let count = whole(&mut fb);
            fb.memset(cell, byte, count);
        }
        ChainWrite::SymbolicFill => fb.memset(cell, byte, n.expect("parameter")),
        ChainWrite::ConstCopy => {
            let count = whole(&mut fb);
            fb.memcopy(cell, other, count, false);
        }
        ChainWrite::SymbolicCopy => fb.memcopy(cell, other, n.expect("parameter"), false),
    }
    let after = fb.load(ty.clone(), cell);
    let next = fb.create_block();
    fb.br(next, vec![after]);
    fb.switch_to_block(next);
    let carried = fb.add_block_param(next, ty);
    let tail = fb.extract_field(Ty::U8, carried, 1);
    let holds = fb.icmp(ICmpOp::Eq, Ty::U8, tail, byte);
    fb.assert(holds);
    fb.ret(vec![]);
    fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), FuncId::new(0))
}

/// One bulk write costs the cell's leaves plus its path, never their product:
/// at nesting depths 8, 16, 24 and 32 (every level one more object at the
/// pointer and one more leaf), the variables and expression nodes the write adds
/// over the same function without it grow by the SAME amount per 8 levels, for a
/// constant and a symbolic count, a fill and a copy. The encoding this replaced
/// built one whole-cell binding per object (`d` objects of `O(d)` leaves): 158,
/// 422, 1334 and 4694 nodes at depths 8, 16, 32 and 64 for the symbolic fill.
#[test]
fn one_write_is_linear_in_the_nesting_depth() {
    const DEPTHS: [usize; 4] = [8, 16, 24, 32];
    let measure = |depth: usize, write: ChainWrite| {
        let (module, func) = depth_chain(depth, write);
        let out = trust_ir_function_to_chc_translation_output(
            &module,
            func,
            &TranslateOptions::default(),
        )
        .expect("translates");
        let nodes =
            i64::try_from(super::smt_array_tests::distinct_expr_nodes(&out.vc)).expect("small");
        let vars = i64::try_from(out.vc.vars().len()).expect("small");
        (nodes, vars)
    };
    for write in [
        ChainWrite::LoadStore,
        ChainWrite::ConstFill,
        ChainWrite::SymbolicFill,
        ChainWrite::ConstCopy,
        ChainWrite::SymbolicCopy,
    ] {
        let added: Vec<(i64, i64)> = DEPTHS
            .iter()
            .map(|depth| {
                let (nodes, vars) = measure(*depth, write);
                let (base_nodes, base_vars) = measure(*depth, ChainWrite::Nothing);
                (nodes - base_nodes, vars - base_vars)
            })
            .collect();
        let steps: Vec<(i64, i64)> =
            added.windows(2).map(|pair| (pair[1].0 - pair[0].0, pair[1].1 - pair[0].1)).collect();
        assert!(
            steps.windows(2).all(|pair| pair[0] == pair[1]),
            "{write:?}: the (nodes, vars) a write adds at depths {DEPTHS:?} are {added:?}, \
             not linear in the depth"
        );
    }
}

// ---------------------------------------------------------------------------
// Operands the grid does not reach
// ---------------------------------------------------------------------------

/// A bulk write through a pointer whose PROVENANCE is known (the tracked cell)
/// but whose PLACE is not (a symbolic `GEP` index) has no exact place, so the
/// whole cell is havocked (`invalidate_store_targets`' provenance arm). The cell
/// stays tracked for the translator's own decision, so with memory checks off —
/// no fail-closed rule to hide behind — only that havoc stands between the
/// pre-write `cell[0] == 1` and a false proof: `i == 0` overwrites it.
#[test]
fn a_symbolic_index_into_a_tracked_cell_havocs_the_cell() {
    for fill in [true, false] {
        let mut mb = ModuleBuilder::new("symbolic_index");
        let u8_id = mb.add_type(Ty::U8);
        let arr = Ty::Array(u8_id, 4);
        let ft = mb.add_func_type(vec![Ty::I64], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let i = fb.add_block_param(entry, Ty::I64);
        let cell = fb.alloca(arr.clone());
        let init = fb.const_value(arr.clone(), initial(Init::Distinct, 0, 4));
        fb.store(arr.clone(), cell, init);
        let other = fb.alloca(arr.clone());
        let other_init = fb.const_value(arr.clone(), initial(Init::Distinct, 0x40, 4));
        fb.store(arr.clone(), other, other_init);
        let lane = fb.gep(Ty::U8, cell, vec![i]);
        let one = fb.const_value(Ty::U64, Constant::Int(1));
        if fill {
            let zero = fb.iconst(Ty::U8, 0);
            fb.memset(lane, zero, one);
        } else {
            fb.memcopy(lane, other, one, false);
        }
        let after = fb.load(arr.clone(), cell);
        let first = fb.iconst(Ty::U64, 0);
        let read = fb.extract_element(Ty::U8, after, first);
        let want = fb.iconst(Ty::U8, 1);
        let holds = fb.icmp(ICmpOp::Eq, Ty::U8, read, want);
        fb.assert(holds);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let function = module.function_by_id(FuncId::new(0)).expect("f");
        assert_ne!(
            stack_alloca_escape_classification_with(function, cell, BulkMemoryUse::Tracked),
            StackCellEscape::Unbounded,
            "fill={fill}: the translator tracks the cell, so the havoc is what keeps it sound"
        );
        for checked in [false, true] {
            let options =
                TranslateOptions { check_memory_bounds: checked, ..TranslateOptions::default() };
            let out =
                trust_ir_function_to_chc_translation_output(&module, FuncId::new(0), &options)
                    .expect("translates");
            assert!(error_reachable(&out), "fill={fill} checked={checked}: must not PROVE");
            if checked {
                assert_eq!(
                    reasons(&out),
                    vec![TrustIrChcUnsupportedReason::BulkMemoryTransfer],
                    "fill={fill}"
                );
            }
        }
    }
}

/// `T { inner: I { a: u32 @ 0, b: u32 @ 4 } @ 0, c: u32 @ 8 }`: a pointer to
/// `dst.inner.b` is at byte 4, where neither `inner` nor `T` starts, so an 8-byte
/// copy through it is not a write of `inner` (8 bytes too, but from byte 0): it
/// writes `b` and `c`, a range of two objects, which fails closed. The stale
/// `dst.c == 3` is never proved. The control copies `src.inner` onto
/// `dst.inner` (a whole object) and is exact.
#[test]
fn an_object_that_starts_before_the_pointer_is_not_written() {
    let probe = |into_b: bool, want: (i128, i128, i128)| {
        let mut mb = ModuleBuilder::new("nested_offset");
        let inner = mb.add_struct(StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "nested_offset::I".to_string(),
            fields: vec![
                FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
                FieldDef { name: "b".into(), ty: Ty::U32, offset: Some(4) },
            ],
            size: Some(8),
            align: Some(4),
            repr: StructRepr::Rust,
            origin: None,
        });
        let ity = Ty::Struct(inner);
        let outer = mb.add_struct(StructDef {
            id: trust_ir::value::StructId::new(1),
            name: "nested_offset::T".to_string(),
            fields: vec![
                FieldDef { name: "inner".into(), ty: ity.clone(), offset: Some(0) },
                FieldDef { name: "c".into(), ty: Ty::U32, offset: Some(8) },
            ],
            size: Some(12),
            align: Some(4),
            repr: StructRepr::Rust,
            origin: None,
        });
        let tty = Ty::Struct(outer);
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        // `c` (field 1, at byte 8) is no single-scale `GEP` lane of `T` (`1 *
        // size_of(u32) != 8`), so the cells are written and read whole.
        let init =
            |fb: &mut trust_ir_build::FunctionBuilder<'_>, cell: ValueId, values: [i128; 3]| {
                let [a, b, c] = values.map(|value| fb.iconst(Ty::U32, value));
                let undef_inner =
                    fb.const_value(ity.clone(), Constant::Aggregate(vec![Constant::Uninit; 2]));
                let with_a = fb.insert_field(ity.clone(), undef_inner, 0, a);
                let inner = fb.insert_field(ity.clone(), with_a, 1, b);
                let undef_outer =
                    fb.const_value(tty.clone(), Constant::Aggregate(vec![Constant::Uninit; 2]));
                let with_inner = fb.insert_field(tty.clone(), undef_outer, 0, inner);
                let whole = fb.insert_field(tty.clone(), with_inner, 1, c);
                fb.store(tty.clone(), cell, whole);
            };
        let dst = fb.alloca(tty.clone());
        let src = fb.alloca(tty.clone());
        init(&mut fb, dst, [1, 2, 3]);
        init(&mut fb, src, [0x41, 0x42, 0x43]);
        let zero = fb.iconst(Ty::I64, 0);
        let one = fb.iconst(Ty::I64, 1);
        let dst_inner = fb.gep(ity.clone(), dst, vec![zero]);
        let src_inner = fb.gep(ity.clone(), src, vec![zero]);
        let dst_b = fb.gep(Ty::U32, dst_inner, vec![one]);
        let eight = fb.const_value(Ty::U64, Constant::Int(8));
        if into_b {
            fb.memcopy(dst_b, src, eight, false);
        } else {
            fb.memcopy(dst_inner, src_inner, eight, false);
        }
        let after = fb.load(tty.clone(), dst);
        let inner = fb.extract_field(ity.clone(), after, 0);
        let a = fb.extract_field(Ty::U32, inner, 0);
        let b = fb.extract_field(Ty::U32, inner, 1);
        let c = fb.extract_field(Ty::U32, after, 1);
        for (read, value) in [a, b, c].into_iter().zip([want.0, want.1, want.2]) {
            let value = fb.iconst(Ty::U32, value);
            let holds = fb.icmp(ICmpOp::Eq, Ty::U32, read, value);
            fb.assert(holds);
        }
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let mut original = module.clone();
        let mut restored = 0;
        for node in original.functions[0].blocks.iter_mut().flat_map(|block| &mut block.body) {
            if let Inst::Const { ty, value: Constant::Aggregate(fields) } = &node.inst
                && fields.iter().all(|field| matches!(field, Constant::Uninit))
            {
                node.inst = Inst::Undef { ty: ty.clone() };
                restored += 1;
            }
        }
        assert_eq!(restored, 4, "the two original nested builders are retained exactly");
        assert_eq!(
            Interpreter::with_module(&original).execute_func(FuncId::new(0), []).unwrap_err().code,
            InterpretErrorCode::UndefinedBehavior
        );
        let refused = trust_ir_function_to_chc_translation_output(
            &original,
            FuncId::new(0),
            &TranslateOptions::default(),
        )
        .unwrap();
        assert!(reasons(&refused).contains(&TrustIrChcUnsupportedReason::OperandConsumption));
        trust_ir_function_to_chc_translation_output(
            &module,
            FuncId::new(0),
            &TranslateOptions::default(),
        )
        .expect("translates")
    };
    // `b := src.a`, `c := src.b`: the stale `c` must not be proved.
    let stale = probe(true, (1, 0x41, 3));
    assert_eq!(reasons(&stale), vec![TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange]);
    assert!(error_reachable(&stale), "the stale dst.c == 3 must not be PROVED");
    let control = probe(false, (0x41, 0x42, 3));
    assert!(control.diagnostics.is_empty(), "{:?}", reasons(&control));
    assert!(!error_reachable(&control), "a whole `inner` copy is exact");
    let wrong = probe(false, (0x41, 0x42, 0x43));
    assert!(error_reachable(&wrong), "`c` is not part of `inner`");
}

// ---------------------------------------------------------------------------
// Blocks a cycle reaches (arrays carry only a shape there)
// ---------------------------------------------------------------------------

/// Where `block_write` writes its cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BlockWrite {
    /// `store elem 1` through `gep(elem, cell, [1])`.
    LaneStore,
    /// `memset(gep(elem, cell, [1]), 1, size_of(elem))`.
    LaneFill,
    /// `memset(cell, 1, size_of(cell))`.
    CellFill,
}

/// A block that allocates `cell: [elem; 4]` and writes it, in a loop body (a
/// block a cycle reaches, where arrays carry only a shape) or in straight-line
/// code. Nothing is asserted: only the write's own rules and diagnostics show.
fn block_write(
    elem: &Ty,
    elem_size: u64,
    write: BlockWrite,
    looping: bool,
) -> ChcTranslationOutput {
    let mut mb = ModuleBuilder::new("block_write");
    let elem_id = mb.add_type(elem.clone());
    let arr = Ty::Array(elem_id, 4);
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let n = fb.add_block_param(entry, Ty::U64);
    let (body, i) = if looping {
        let body = fb.create_block();
        let zero = fb.iconst(Ty::U64, 0);
        fb.br(body, vec![zero]);
        fb.switch_to_block(body);
        (Some(body), Some(fb.add_block_param(body, Ty::U64)))
    } else {
        (None, None)
    };
    let cell = fb.alloca(arr);
    let one = fb.iconst(Ty::I64, 1);
    let byte = fb.iconst(Ty::U8, 1);
    match write {
        BlockWrite::LaneStore => {
            let lane = fb.gep(elem.clone(), cell, vec![one]);
            let value =
                if *elem == Ty::Bool { fb.bool_const(true) } else { fb.iconst(elem.clone(), 1) };
            fb.store(elem.clone(), lane, value);
        }
        BlockWrite::LaneFill => {
            let lane = fb.gep(elem.clone(), cell, vec![one]);
            let count = fb.const_value(Ty::U64, Constant::Int(i128::from(elem_size)));
            fb.memset(lane, byte, count);
        }
        BlockWrite::CellFill => {
            let count = fb.const_value(Ty::U64, Constant::Int(i128::from(4 * elem_size)));
            fb.memset(cell, byte, count);
        }
    }
    if let (Some(body), Some(i)) = (body, i) {
        // A loop with no arithmetic, so no obligation but the write's own.
        let exit = fb.create_block();
        let more = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
        fb.condbr(more, body, vec![i], exit, vec![]);
        fb.switch_to_block(exit);
    }
    fb.ret(vec![]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(0),
        &TranslateOptions::default(),
    )
    .expect("translates")
}

/// In a block a cycle reaches, a write of one whole lane is absorbed by the
/// shape-only array exactly as the byte-identical lane `Store` is — no
/// fail-closed diagnostic, no error — and a fill obeys the same rule as in
/// straight-line code: an integer array is filled, a `bool` array (whose bytes
/// have invalid images) fails closed in both kinds of block.
#[test]
fn a_loop_block_writes_by_the_same_rules_as_straight_line_code() {
    for looping in [true, false] {
        for write in [BlockWrite::LaneStore, BlockWrite::LaneFill, BlockWrite::CellFill] {
            let out = block_write(&Ty::U8, 1, write, looping);
            assert!(
                out.diagnostics.is_empty(),
                "looping={looping} {write:?} on [u8; 4]: {:?}",
                reasons(&out)
            );
            assert!(!error_reachable(&out), "looping={looping} {write:?}: no error");
        }
        let out = block_write(&Ty::Bool, 1, BlockWrite::CellFill, looping);
        assert_eq!(
            reasons(&out),
            vec![TrustIrChcUnsupportedReason::BulkMemoryUnplacedRange],
            "looping={looping}: a fill of [bool; 4]"
        );
        assert!(error_reachable(&out), "looping={looping}: a fill of [bool; 4] fails closed");
    }
}

// ---------------------------------------------------------------------------
// The count and the fill byte are defined values
// ---------------------------------------------------------------------------

/// An initialized unknown entry byte preserves the original positive assertions.
/// Retain the EXACT old annotated-Undef program separately: canonical IR still
/// consumes that poison even at count zero; an annotation supplies no value.
#[test]
fn a_fresh_symbolic_fill_byte_is_a_defined_byte() {
    use trust_ir::proof::ProofAnnotation;
    for (bytes, poison) in [(0u64, false), (1, false), (0, true), (1, true)] {
        let mut mb = ModuleBuilder::new("havoc_fill_byte");
        let ft =
            mb.add_func_type(if poison { vec![Ty::Ptr] } else { vec![Ty::Ptr, Ty::U8] }, vec![]);
        let mut fb = mb.function("f", ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let dst = fb.add_block_param(entry, Ty::Ptr);
        let byte = if poison {
            fb.undef_proven(Ty::U8, vec![ProofAnnotation::FreshSymbolicHavoc])
        } else {
            fb.add_block_param(entry, Ty::U8)
        };
        let count = fb.const_value(Ty::U64, Constant::Int(i128::from(bytes)));
        fb.memset(dst, byte, count);
        fb.ret(vec![]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let out = trust_ir_function_to_chc_translation_output(
            &module,
            FuncId::new(0),
            &TranslateOptions::default(),
        )
        .expect("translates");
        if poison {
            let null = InterpretValue {
                ty: Ty::Ptr,
                kind: trust_ir::interpret::InterpretValueKind::NullPtr,
            };
            let error =
                Interpreter::with_module(&module).execute_func(FuncId::new(0), [null]).unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
            assert!(reasons(&out).contains(&TrustIrChcUnsupportedReason::OperandConsumption));
            assert!(error_reachable(&out));
            continue;
        }
        if bytes == 0 {
            assert!(out.diagnostics.is_empty(), "{:?}", reasons(&out));
            assert!(!error_reachable(&out));
        } else {
            assert_eq!(reasons(&out), vec![TrustIrChcUnsupportedReason::BulkMemoryTransfer]);
            assert!(error_reachable(&out));
        }
    }
}

// ---------------------------------------------------------------------------
// The memoized type facts (`translate_chc_ty_facts.rs`)
// ---------------------------------------------------------------------------

/// A module holding `structs` (in id order) and one trivial function, for a
/// translator to ask about types.
fn facts_module(build: impl FnOnce(&mut ModuleBuilder) -> Vec<Ty>) -> (Module, Vec<Ty>) {
    let mut mb = ModuleBuilder::new("ty_facts");
    let roots = build(&mut mb);
    let ft = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    fb.ret(vec![]);
    fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), roots)
}

fn add_struct(
    mb: &mut ModuleBuilder,
    id: u32,
    fields: Vec<(Ty, Option<u64>)>,
    size: u64,
    align: u64,
) -> Ty {
    Ty::Struct(
        mb.add_struct(StructDef {
            id: trust_ir::value::StructId::new(id),
            name: format!("ty_facts::S{id}"),
            fields: fields
                .into_iter()
                .enumerate()
                .map(|(index, (ty, offset))| FieldDef { name: format!("f{index}"), ty, offset })
                .collect(),
            size: Some(size),
            align: Some(align),
            repr: StructRepr::Rust,
            origin: None,
        }),
    )
}

/// trust-ir's own answer, in the memo's terms.
fn direct_layout(module: &Module, ty: &Ty) -> Option<ty_facts::LayoutFact> {
    module.ty_layout_shape(ty).ok().map(|shape| ty_facts::LayoutFact {
        size_bits: shape.size_bits,
        stride_bits: match shape.kind {
            trust_ir::TyLayoutKind::Array { stride_bits, .. } => Some(stride_bits),
            _ => None,
        },
    })
}

/// Every struct and array type nested in `root` (field and element types), once.
fn nested_layout_tys(module: &Module, root: &Ty) -> Vec<Ty> {
    let mut seen: Vec<Ty> = Vec::new();
    let mut pending = vec![root.clone()];
    while let Some(ty) = pending.pop() {
        let children: Vec<Ty> = match &ty {
            Ty::Struct(id) => module
                .struct_def(*id)
                .map(|definition| definition.fields.iter().map(|field| field.ty.clone()).collect())
                .unwrap_or_default(),
            Ty::Array(element, _) => {
                module.types.get(element.as_usize()).cloned().into_iter().collect()
            }
            _ => Vec::new(),
        };
        for child in children {
            if matches!(child, Ty::Struct(_) | Ty::Array(..)) && !seen.contains(&child) {
                seen.push(child.clone());
                pending.push(child);
            }
        }
    }
    seen
}

/// ONE trust-ir walk of a type seeds every struct and array nested in it, and
/// every seeded fact is exactly what trust-ir answers for that type on its own:
/// padding, arrays of structs, nested arrays, a struct-sharing DAG. Under a root
/// trust-ir refuses (an overlapping field), nothing is seeded, and each nested
/// type is asked on its own.
#[test]
fn seeded_layouts_are_trust_irs_own_answers() {
    let (module, roots) = facts_module(|mb| {
        let u16_id = mb.add_type(Ty::U16);
        // S0 { a: u8 @ 0, b: u32 @ 4 }: padding.
        let s0 = add_struct(mb, 0, vec![(Ty::U8, Some(0)), (Ty::U32, Some(4))], 8, 4);
        let s0_id = mb.add_type(s0.clone());
        // S1 { x: [S0; 3] @ 0, y: u16 @ 24 }.
        let s1 =
            add_struct(mb, 1, vec![(Ty::Array(s0_id, 3), Some(0)), (Ty::U16, Some(24))], 28, 4);
        // S2 { p: S1 @ 0, q: S1 @ 28 }.
        let s2 = add_struct(mb, 2, vec![(s1.clone(), Some(0)), (s1, Some(28))], 56, 4);
        let s2_id = mb.add_type(s2.clone());
        // P0 = { u8, u8 }, P{k+1} = { a: Pk, b: Pk }.
        let mut dag = add_struct(mb, 3, vec![(Ty::U8, Some(0)), (Ty::U8, Some(1))], 2, 1);
        let mut size = 2;
        for id in 4..10 {
            dag = add_struct(mb, id, vec![(dag.clone(), Some(0)), (dag, Some(size))], size * 2, 1);
            size *= 2;
        }
        let row = mb.add_type(Ty::Array(u16_id, 3));
        // Bad { a: u32 @ 0, b: u32 @ 2 }: overlapping, no layout.
        let bad = add_struct(mb, 10, vec![(Ty::U32, Some(0)), (Ty::U32, Some(2))], 8, 4);
        let holder = add_struct(mb, 11, vec![(s0, Some(0)), (bad, Some(8))], 16, 4);
        vec![s2, dag, Ty::Array(row, 2), Ty::Array(s2_id, 2), holder]
    });
    let function = module.function_by_id(FuncId::new(0)).expect("f");
    let options = TranslateOptions::default();
    for root in &roots {
        let translator = ChcFuncTranslator::new(function, &module, &options);
        let nested = nested_layout_tys(&module, root);
        assert!(!nested.is_empty(), "{root:?}");
        let fact = translator.layout_fact(root);
        assert_eq!(fact, direct_layout(&module, root), "{root:?}");
        for ty in &nested {
            let memo = translator.memoized_layout(ty);
            if fact.is_some() {
                assert_eq!(memo, Some(direct_layout(&module, ty)), "{root:?}: seeded {ty:?}");
            } else {
                assert_eq!(memo, None, "{root:?}: nothing is seeded under a refused root");
            }
            assert_eq!(translator.layout_fact(ty), direct_layout(&module, ty), "{root:?}: {ty:?}");
        }
    }
}

/// The sorted sweep in `exact_struct_ranges` gives the same verdict as comparing
/// every pair of fields, including zero-sized fields at, inside and at the end of
/// another field's range — layouts trust-ir accepts, but which are not exact
/// lane evidence when two fields start at one byte or one sits inside another.
#[test]
fn exact_struct_ranges_agree_with_every_pair() {
    let cases: Vec<(Vec<(Ty, Option<u64>)>, u64)> = vec![
        (vec![(Ty::U32, Some(0)), (Ty::U32, Some(4))], 8),
        (vec![(Ty::U32, Some(4)), (Ty::U32, Some(0))], 8),
        (vec![(Ty::U8, Some(3)), (Ty::U16, Some(0)), (Ty::U8, Some(2))], 4),
        (vec![(Ty::Unit, Some(0)), (Ty::U32, Some(0))], 4),
        (vec![(Ty::U32, Some(0)), (Ty::Unit, Some(2))], 4),
        (vec![(Ty::U32, Some(0)), (Ty::Unit, Some(4))], 4),
        (vec![(Ty::Unit, Some(1)), (Ty::Unit, Some(1)), (Ty::U8, Some(0))], 2),
        (vec![(Ty::Unit, Some(1)), (Ty::Unit, Some(2)), (Ty::U8, Some(0))], 3),
        (vec![(Ty::Unit, None), (Ty::U32, Some(0))], 4),
        (vec![(Ty::U16, Some(2)), (Ty::U8, Some(0)), (Ty::U8, Some(1))], 4),
    ];
    for (index, (fields, size)) in cases.into_iter().enumerate() {
        let (module, roots) = facts_module(|mb| vec![add_struct(mb, 0, fields.clone(), size, 1)]);
        let function = module.function_by_id(FuncId::new(0)).expect("f");
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(function, &module, &options);
        let Ty::Struct(id) = roots[0] else { unreachable!() };
        let field_tys: Vec<Ty> = fields.iter().map(|(ty, _)| ty.clone()).collect();
        let pairwise = module.ty_layout_shape(&roots[0]).is_ok() && {
            let ranges: Option<Vec<(u64, u64)>> = fields
                .iter()
                .map(|(ty, offset)| {
                    let start = (*offset)? * 8;
                    Some((start, start + module.ty_layout_shape(ty).ok()?.size_bits))
                })
                .collect();
            ranges.is_some_and(|ranges| {
                (0..ranges.len()).all(|left| {
                    ((left + 1)..ranges.len()).all(|right| {
                        let ((ls, le), (rs, re)) = (ranges[left], ranges[right]);
                        !(ls == rs || (ls < re && rs < le))
                    })
                })
            })
        };
        assert_eq!(
            translator.exact_struct_ranges(id, &field_tys).is_some(),
            pairwise,
            "case {index}: {fields:?}"
        );
    }
}
