// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A write through an interior pointer must never be silently dropped.
//!
//! `translate_stack_store` is keyed by the ALLOCA's `ValueId`. A store whose ptr
//! is `BorrowMut(GEP(alloca, k))` — what `&mut local.field` lowers to — misses the
//! precise `stack_cell`, and the `ValidBorrow` annotation then suppresses the
//! `MemoryAccessWithoutPreciseModel` fail-close. Before the interior-pointer
//! provenance fix the write was dropped with NO diagnostic while the alloca's cell
//! kept its PRE-store value, so the next `Load` read back the value the function
//! had just overwritten and every obligation over it was discharged against a
//! stale value. That is a false-PROVE generator, the worst state a verifier has.
//!
//! The modules below are the shape `trustc -Ztrust-dump=native-bundle` emits for
//!
//! ```ignore
//! pub struct S { pub a: u32, pub b: u32 }
//! pub fn f(seed: u32) -> u32 { let mut s = S { a: 1, b: seed };
//!                              let r = &mut s.a; *r = K; 100 / s.a }
//! ```
//!
//! The obligation is the divide-by-zero check on `s.a`, encoded as the reachability
//! of the `error` relation. With the seeded field (`1`) and the written constant
//! both literal, the whole error constraint folds to a constant, so each test can
//! read the verdict EXACTLY rather than diffing rule text: `Some(true)` = error
//! reachable (correctly refuted), `Some(false)` = error unreachable (PROVED),
//! `None` = the value went symbolic (havoc — sound, imprecise).

use trust_ir::inst::ICmpOp;
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::value::{FuncId, ValueId};
use trust_ir::{Constant, FieldDef, ProofAnnotation, StructDef, StructRepr, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};
use trust_mc_core::chc::ChcVc;
use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;
use trust_mc_trust_bmc::{
    TranslateOptions, TrustIrChcDiagnostic, single_cell_alloca_rejection,
    stack_alloca_cell_accesses_match_type, stack_alloca_pointer_is_non_escaping,
    trust_ir_function_to_chc_translation_output,
};

/// How the pointer stored through is derived from the `s` alloca.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Target {
    /// `&mut s.a` — `BorrowMut(GEP(alloca, 0))`, the pervasive shape.
    FieldBorrow,
    /// `&mut s.a` with the field index computed, not constant — the offset is
    /// unknown, so the whole cell must be havoced rather than left stale.
    SymbolicLaneBorrow,
    /// `&mut s` — `BorrowMut(alloca)`, no `GEP` at all.
    WholeBorrow,
    /// A pointer with no provenance into the alloca, stored through AFTER the
    /// alloca's interior address escaped into a call. It may alias `s`.
    UnknownAfterEscape,
    /// A pointer with no provenance into the alloca and no escape anywhere: it
    /// provably cannot reach the cell, so the cell must stay precise.
    UnknownWithNoEscape,
    /// `sink(&mut s.a)` and NOTHING after it — the interior address escapes into a
    /// call and no store follows. The callee may write through it, so the readback
    /// must NOT see the seeded value. This is the pure call-invalidation case:
    /// `UnknownAfterEscape` above always appends a store, which is what triggered
    /// the only pre-existing consumer of `escaped_cell_bases`.
    CallEscapeNoStore,
}

struct Probe {
    module: trust_ir::Module,
    function: FuncId,
    vc: ChcVc,
    module_input_refusal: Option<String>,
    diagnostics: Vec<TrustIrChcDiagnostic>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Construction {
    Complete,
    LegacyUndef,
}

fn pair(
    fb: &mut FunctionBuilder<'_>,
    ty: Ty,
    first: ValueId,
    second: ValueId,
    construction: Construction,
) -> ValueId {
    match construction {
        Construction::Complete => fb.make_aggregate(ty, vec![first, second]),
        Construction::LegacyUndef => {
            let undef = fb.undef(ty.clone());
            let first = fb.insert_field(ty.clone(), undef, 0, first);
            fb.insert_field(ty, first, 1, second)
        }
    }
}

fn translate_probe(module: trust_ir::Module, function: FuncId) -> Probe {
    let out = trust_ir_function_to_chc_translation_output(
        &module,
        function,
        &TranslateOptions::default(),
    )
    .expect("interior-pointer fixture translates");
    Probe {
        module,
        function,
        vc: out.vc,
        module_input_refusal: out.module_input_refusal,
        diagnostics: out.diagnostics,
    }
}

/// Build `f`, writing `written` into `s.a` through `target`, and translate it.
fn probe(target: Target, written: i128, valid_borrow: bool) -> Probe {
    probe_construction(target, written, valid_borrow, Construction::Complete)
}

fn probe_construction(
    target: Target,
    written: i128,
    valid_borrow: bool,
    construction: Construction,
) -> Probe {
    let mut mb = ModuleBuilder::new("interior_ptr");
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "interior_ptr::S".to_string(),
        fields: vec![
            FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
            FieldDef { name: "b".into(), ty: Ty::U32, offset: Some(4) },
        ],
        size: Some(8),
        align: Some(4),
        repr: StructRepr::Rust,
        origin: None,
    });
    let sty = Ty::Struct(struct_id);
    let has_unknown_pointer = construction == Construction::Complete
        && matches!(target, Target::UnknownAfterEscape | Target::UnknownWithNoEscape);
    let params = if has_unknown_pointer { vec![Ty::U32, Ty::Ptr] } else { vec![Ty::U32] };
    let ft = mb.add_func_type(params, vec![Ty::U32]);
    // A callee an interior pointer can escape into.
    // The positive sink returns no values. Keep the original malformed unit
    // return signature in the retained LegacyUndef input.
    let returns = if construction == Construction::Complete { vec![] } else { vec![Ty::Unit] };
    let sink_ty = mb.add_func_type(vec![Ty::Ptr], returns);
    let sink_id = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
    {
        let mut sink = mb.function("sink", sink_ty);
        let sink_entry = sink.create_block();
        sink.switch_to_block(sink_entry);
        sink.set_entry(sink_entry);
        sink.add_block_param(sink_entry, Ty::Ptr);
        sink.ret(vec![]);
        sink.build();
    }

    let mut fb = mb.function("f", ft);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);
    let seed = fb.add_block_param(entry, Ty::U32);
    let unknown_pointer = has_unknown_pointer.then(|| fb.add_block_param(entry, Ty::Ptr));

    // s = S { a: 1, b: seed }, spilled to the stack because its address is taken.
    let one = fb.const_value(Ty::U32, Constant::Int(1));
    let agg1 = pair(&mut fb, sty.clone(), one, seed, construction);
    let slot = fb.alloca(sty.clone());
    fb.store(sty.clone(), slot, agg1);

    let k = fb.const_value(Ty::U32, Constant::Int(written));
    let proofs = if valid_borrow { vec![ProofAnnotation::ValidBorrow] } else { Vec::new() };

    match target {
        Target::FieldBorrow => {
            let lane = fb.const_value(Ty::I64, Constant::Int(0));
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.store_proven(Ty::U32, borrow, k, proofs);
        }
        Target::SymbolicLaneBorrow => {
            // A lane index the translator cannot fold: `seed & 0` is 0 in fact, but
            // the GEP index is not a `BitVecConst`, so the offset is unknown.
            let mask = fb.const_value(Ty::U32, Constant::Int(0));
            let masked = fb.binop(trust_ir::inst::BinOp::And, Ty::U32, seed, mask);
            let lane = fb.zext(Ty::U32, Ty::I64, masked);
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.store_proven(Ty::U32, borrow, k, proofs);
        }
        Target::WholeBorrow => {
            // `*(&mut s) = S { a: K, b: seed }` — no GEP, the borrow IS the alloca.
            let n1 = pair(&mut fb, sty.clone(), k, seed, construction);
            let borrow = fb.borrow_mut(slot);
            fb.store_proven(sty.clone(), borrow, n1, proofs);
        }
        Target::UnknownAfterEscape => {
            // `sink(&mut s.a)` — the interior address leaves the model...
            let lane = fb.const_value(Ty::I64, Constant::Int(0));
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.call_void(sink_id, vec![borrow]);
            // ...and this store is through a pointer that may be the escaped one.
            // The positive model probe takes an unknown, potentially valid
            // caller pointer. A null store is not a canonical execution oracle.
            // The LegacyUndef variant retains the original null instruction.
            let opaque = unknown_pointer.unwrap_or_else(|| fb.null_ptr());
            fb.store_proven(Ty::U32, opaque, k, proofs);
        }
        Target::UnknownWithNoEscape => {
            let opaque = unknown_pointer.unwrap_or_else(|| fb.null_ptr());
            fb.store_proven(Ty::U32, opaque, k, proofs);
        }
        Target::CallEscapeNoStore => {
            // `sink(&mut s.a)` — and deliberately NO store afterwards.
            let lane = fb.const_value(Ty::I64, Constant::Int(0));
            let field_ptr = fb.gep(Ty::U32, slot, vec![lane]);
            let borrow = fb.borrow_mut(field_ptr);
            fb.call_void(sink_id, vec![borrow]);
        }
    }

    // 100 / s.a — read back through the SAME alloca.
    let reloaded = fb.load(sty.clone(), slot);
    let a = fb.extract_field(Ty::U32, reloaded, 0);
    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, a, zero);
    let f = fb.const_value(Ty::Bool, Constant::Bool(false));
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, f);
    fb.assert(ok);
    fb.ret(vec![a]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    if construction == Construction::Complete {
        let errors = trust_ir_build::validate_module(&module);
        assert!(errors.is_empty(), "positive interior-pointer input must be valid: {errors:?}");
    }
    translate_probe(module, FuncId::new(1))
}

/// TrustIR GEP is `base + index * size_of(pointee_ty)`, not structural field
/// selection. In `{ u64, u32 }`, `gep u32 base, [1]` is byte offset 4, inside
/// the first field; it does NOT select the second field at byte offset 8.
///
/// The pre-fix lane mapper nevertheless saw `fields[1] == u32`, overwrote the
/// modeled second field with 7, and falsely proved the assertion below even
/// though the real second field remains zero. The sound fallback is to havoc
/// the cell because this heterogeneous byte offset has no exact aggregate lane.
fn heterogeneous_non_lane_gep_probe() -> Probe {
    heterogeneous_non_lane_gep_construction(Construction::Complete)
}

fn heterogeneous_non_lane_gep_construction(construction: Construction) -> Probe {
    let mut mb = ModuleBuilder::new("heterogeneous_interior_ptr");
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "heterogeneous_interior_ptr::S".to_string(),
        fields: vec![
            FieldDef { name: "wide".into(), ty: Ty::U64, offset: Some(0) },
            FieldDef { name: "divisor".into(), ty: Ty::U32, offset: Some(8) },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    let struct_ty = Ty::Struct(struct_id);
    let fn_ty = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("heterogeneous_gep", fn_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let wide = fb.const_value(Ty::U64, Constant::Int(0));
    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let aggregate = pair(&mut fb, struct_ty.clone(), wide, zero, construction);
    let slot = fb.alloca(struct_ty.clone());
    fb.store(struct_ty.clone(), slot, aggregate);

    let one = fb.const_value(Ty::I64, Constant::Int(1));
    let byte_four = fb.gep(Ty::U32, slot, vec![one]);
    let borrowed = fb.borrow_mut(byte_four);
    let seven = fb.const_value(Ty::U32, Constant::Int(7));
    fb.store_proven(Ty::U32, borrowed, seven, vec![ProofAnnotation::ValidBorrow]);

    let reloaded = fb.load(struct_ty.clone(), slot);
    let divisor = fb.extract_field(Ty::U32, reloaded, 1);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, divisor, zero);
    let false_value = fb.const_value(Ty::Bool, Constant::Bool(false));
    let nonzero = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, false_value);
    fb.assert(nonzero);
    fb.ret(vec![divisor]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    translate_probe(module, FuncId::new(0))
}

/// Build a homogeneous `{ u32, u32 }` pair and attempt to write logical field 1
/// with `gep u32 [1]` (byte offset 4). The supplied layout decides whether that
/// address is evidence-grade field identity or must degrade to whole-cell havoc.
fn homogeneous_field_one_probe(
    name: &str,
    offsets: [Option<u64>; 2],
    size: Option<u64>,
    align: Option<u64>,
) -> Probe {
    homogeneous_field_one_construction(name, offsets, size, align, Construction::Complete)
}

fn homogeneous_field_one_construction(
    name: &str,
    offsets: [Option<u64>; 2],
    size: Option<u64>,
    align: Option<u64>,
    construction: Construction,
) -> Probe {
    let mut mb = ModuleBuilder::new(name);
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: format!("{name}::S"),
        fields: vec![
            FieldDef { name: "first".into(), ty: Ty::U32, offset: offsets[0] },
            FieldDef { name: "divisor".into(), ty: Ty::U32, offset: offsets[1] },
        ],
        size,
        align,
        repr: StructRepr::Rust,
        origin: None,
    });
    let struct_ty = Ty::Struct(struct_id);
    let fn_ty = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("homogeneous_gep", fn_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let aggregate = pair(&mut fb, struct_ty.clone(), zero, zero, construction);
    let slot = fb.alloca(struct_ty.clone());
    fb.store(struct_ty.clone(), slot, aggregate);

    let one = fb.const_value(Ty::I64, Constant::Int(1));
    let byte_four = fb.gep(Ty::U32, slot, vec![one]);
    let borrowed = fb.borrow_mut(byte_four);
    let seven = fb.const_value(Ty::U32, Constant::Int(7));
    fb.store_proven(Ty::U32, borrowed, seven, vec![ProofAnnotation::ValidBorrow]);

    let reloaded = fb.load(struct_ty.clone(), slot);
    let divisor = fb.extract_field(Ty::U32, reloaded, 1);
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U32, divisor, zero);
    let false_value = fb.const_value(Ty::Bool, Constant::Bool(false));
    let nonzero = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, false_value);
    fb.assert(nonzero);
    fb.ret(vec![divisor]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    translate_probe(module, FuncId::new(0))
}

/// Two logical fields alias the same four bytes. A write through the field-0
/// address changes BOTH observable field reads, so updating only logical field 0
/// would leave field 1 stale and could falsely prove `field1 == 0`.
fn overlapping_fields_probe() -> Probe {
    overlapping_fields_construction(Construction::Complete)
}

fn overlapping_fields_construction(construction: Construction) -> Probe {
    let mut mb = ModuleBuilder::new("overlapping_fields");
    let struct_id = mb.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "overlapping_fields::S".into(),
        fields: vec![
            FieldDef { name: "first".into(), ty: Ty::U32, offset: Some(0) },
            FieldDef { name: "alias".into(), ty: Ty::U32, offset: Some(0) },
        ],
        size: Some(4),
        align: Some(4),
        repr: StructRepr::Rust,
        origin: None,
    });
    let struct_ty = Ty::Struct(struct_id);
    let fn_ty = mb.add_func_type(vec![], vec![Ty::U32]);
    let mut fb = mb.function("overlapping_gep", fn_ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    fb.set_entry(entry);

    let zero = fb.const_value(Ty::U32, Constant::Int(0));
    let aggregate = pair(&mut fb, struct_ty.clone(), zero, zero, construction);
    let slot = fb.alloca(struct_ty.clone());
    fb.store(struct_ty.clone(), slot, aggregate);

    let index_zero = fb.const_value(Ty::I64, Constant::Int(0));
    let overlapping_address = fb.gep(Ty::U32, slot, vec![index_zero]);
    let borrowed = fb.borrow_mut(overlapping_address);
    let seven = fb.const_value(Ty::U32, Constant::Int(7));
    fb.store_proven(Ty::U32, borrowed, seven, vec![ProofAnnotation::ValidBorrow]);

    let reloaded = fb.load(struct_ty.clone(), slot);
    let alias = fb.extract_field(Ty::U32, reloaded, 1);
    let alias_still_zero = fb.icmp(ICmpOp::Eq, Ty::U32, alias, zero);
    fb.assert(alias_still_zero);
    fb.ret(vec![alias]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    translate_probe(module, FuncId::new(0))
}

/// Constant-fold the `error`-head rules' constraints.
///
/// `Some(true)`  — the error is reachable on a constant path: the obligation is
///                 (correctly) refuted.
/// `Some(false)` — every error path folds to false: the obligation is PROVED.
/// `None`        — a constraint stayed symbolic: the value was havoced, so the
///                 solver decides. Sound, imprecise — never a false proof.
fn error_reachability(vc: &ChcVc) -> Option<bool> {
    let mut any_reachable = false;
    let mut saw_error_rule = false;
    for rule in &vc.rules {
        if rule.head.name.as_str() != "error" {
            continue;
        }
        saw_error_rule = true;
        let mut conjunction = Some(true);
        for constraint in rule.body.constraints.iter() {
            match try_eval_to_bool(constraint) {
                Some(true) => {}
                Some(false) => {
                    conjunction = Some(false);
                    break;
                }
                None => conjunction = None,
            }
        }
        match conjunction {
            Some(true) => any_reachable = true,
            Some(false) => {}
            None => return None,
        }
    }
    assert!(saw_error_rule, "the assert must emit an error rule");
    Some(any_reachable)
}

#[test]
fn original_aggregate_undef_constructions_remain_ub_and_refused() {
    let mut originals = Vec::new();
    for target in [
        Target::FieldBorrow,
        Target::SymbolicLaneBorrow,
        Target::WholeBorrow,
        Target::UnknownAfterEscape,
        Target::UnknownWithNoEscape,
        Target::CallEscapeNoStore,
    ] {
        for written in [0, 7] {
            for valid_borrow in [false, true] {
                originals.push(probe_construction(
                    target,
                    written,
                    valid_borrow,
                    Construction::LegacyUndef,
                ));
            }
        }
    }
    originals.push(heterogeneous_non_lane_gep_construction(Construction::LegacyUndef));
    for (name, offsets, size, align) in [
        ("explicit_matching_layout", [Some(0), Some(4)], Some(8), Some(4)),
        ("explicit_offset_mismatch", [Some(0), Some(8)], Some(12), Some(4)),
        ("missing_layout", [None, None], None, None),
    ] {
        originals.push(homogeneous_field_one_construction(
            name,
            offsets,
            size,
            align,
            Construction::LegacyUndef,
        ));
    }
    originals.push(overlapping_fields_construction(Construction::LegacyUndef));
    originals.push(cross_block_projected_construction(1, 1, Construction::LegacyUndef));
    originals.push(cross_block_projected_construction(1, 0, Construction::LegacyUndef));
    for original in originals {
        let arguments = original
            .module
            .func_type(original.module.function_by_id(original.function).unwrap().ty)
            .unwrap()
            .params
            .iter()
            .map(|ty| match ty {
                Ty::Bool => InterpretValue::bool(true),
                _ => InterpretValue::int(ty.clone(), 7).unwrap(),
            })
            .collect::<Vec<_>>();
        let error = Interpreter::with_module(&original.module)
            .execute_func(original.function, arguments)
            .expect_err("the original non-scalar Undef is UB at its definition");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error:?}");
        if trust_ir_build::validate_module(&original.module).is_empty() {
            assert!(original.module_input_refusal.is_none());
            assert!(!original.diagnostics.is_empty(), "valid but undefined input stays refused");
        } else {
            assert!(original.module_input_refusal.is_some(), "invalid original stays refused");
            assert!(original.diagnostics.is_empty(), "invalidity has no invented instruction site");
        }
        assert_ne!(error_reachability(&original.vc), Some(false));
    }
}

#[test]
fn initialized_interior_pointer_writes_have_canonical_values() {
    for target in [Target::FieldBorrow, Target::WholeBorrow] {
        let complete = probe(target, 7, true);
        let execution = Interpreter::with_module(&complete.module)
            .execute_func(complete.function, [InterpretValue::int(Ty::U32, 19).unwrap()])
            .expect("complete fields and a real borrowed pointer execute");
        assert_eq!(execution.returns, vec![InterpretValue::int(Ty::U32, 7).unwrap()]);
        assert_eq!(error_reachability(&complete.vc), Some(false));
    }
}

fn integer_byte_write_probe(field: Ty, offset: i128, byte: i128) -> Probe {
    let mut module = ModuleBuilder::new("byte_write_initializedness");
    let size = if field == Ty::Bool { 1 } else { 4 };
    let structure = module.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "ByteWritten".into(),
        fields: vec![FieldDef { name: "field".into(), ty: field.clone(), offset: Some(0) }],
        size: Some(size),
        align: Some(size),
        repr: StructRepr::Rust,
        origin: None,
    });
    let ty = Ty::Struct(structure);
    let signature = module.add_func_type(vec![], vec![field.clone()]);
    let mut function = module.function("byte_write", signature);
    let entry = function.create_block();
    function.set_entry(entry);
    function.switch_to_block(entry);
    let initial = if field == Ty::Bool { Constant::Bool(true) } else { Constant::Int(0) };
    let initial = function.const_value(field.clone(), initial);
    let aggregate = function.make_aggregate(ty.clone(), vec![initial]);
    let cell = function.alloca(ty.clone());
    function.store(ty.clone(), cell, aggregate);
    let offset = function.const_value(Ty::I64, Constant::Int(offset));
    let address = function.gep(Ty::U8, cell, vec![offset]);
    let address = function.borrow_mut(address);
    let stored = if field == Ty::Char { Ty::U32 } else { Ty::U8 };
    let byte = function.const_value(stored.clone(), Constant::Int(byte));
    function.store_proven(stored, address, byte, vec![ProofAnnotation::ValidBorrow]);
    let loaded = function.load(ty, cell);
    let field = function.extract_field(field, loaded, 0);
    let yes = function.bool_const(true);
    function.assert(yes);
    function.ret(vec![field]);
    function.build();
    translate_probe(module.build().unwrap(), FuncId::new(0))
}

#[test]
fn byte_write_preserves_integer_initializedness_without_donating_field_values() {
    let probe = integer_byte_write_probe(Ty::U32, 0, 255);
    let result = Interpreter::with_module(&probe.module).execute_func(probe.function, []).unwrap();
    assert_eq!(result.returns, [InterpretValue::int(Ty::U32, 255).unwrap()]);
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
    assert_eq!(error_reachability(&probe.vc), Some(false));
}

fn integer_word_write_probe(
    offset: i128,
    object_alignment: u64,
    allocation_alignment: Option<u64>,
    access_alignment: Option<u64>,
    prefix_byte: bool,
) -> Probe {
    let mut module = ModuleBuilder::new("integer_write_alignment");
    let structure = module.add_struct(StructDef {
        id: trust_ir::value::StructId::new(0),
        name: "ThreeBytes".into(),
        fields: (0..3)
            .map(|index| FieldDef { name: format!("byte{index}"), ty: Ty::U8, offset: Some(index) })
            .collect(),
        size: Some(if object_alignment == 1 { 3 } else { 4 }),
        align: Some(object_alignment),
        repr: StructRepr::Rust,
        origin: None,
    });
    let ty = Ty::Struct(structure);
    let signature = module.add_func_type(vec![], vec![Ty::U8]);
    let mut function = module.function("integer_word_write", signature);
    let entry = function.create_block();
    function.set_entry(entry);
    function.switch_to_block(entry);
    if prefix_byte {
        // Make under-alignment observable; the first stack address happens to
        // be word-aligned even when the allocation guarantees only one byte.
        function.alloca(Ty::U8);
    }
    let fields = [1, 2, 3]
        .into_iter()
        .map(|byte| function.const_value(Ty::U8, Constant::Int(byte)))
        .collect();
    let aggregate = function.make_aggregate(ty.clone(), fields);
    let cell = match allocation_alignment {
        Some(align) => function.alloca_aligned(ty.clone(), align),
        None => function.alloca(ty.clone()),
    };
    function.store(ty.clone(), cell, aggregate);
    let offset = function.const_value(Ty::I64, Constant::Int(offset));
    let address = function.gep(Ty::U8, cell, vec![offset]);
    let word = function.const_value(Ty::U16, Constant::Int(0x0605));
    match access_alignment {
        Some(align) => function.store_aligned(Ty::U16, address, word, align),
        None => function.store(Ty::U16, address, word),
    }
    let loaded = function.load(ty, cell);
    let first = function.extract_field(Ty::U8, loaded, 0);
    let yes = function.bool_const(true);
    function.assert(yes);
    function.ret(vec![first]);
    function.build();
    translate_probe(module.build().unwrap(), FuncId::new(0))
}

#[test]
fn integer_write_preservation_refuses_misaligned_accesses() {
    for probe in [
        integer_word_write_probe(1, 1, None, None, false),
        integer_word_write_probe(0, 1, None, None, true),
        integer_word_write_probe(0, 2, None, Some(4), true),
        integer_word_write_probe(0, 2, Some(1), None, true),
    ] {
        let error = Interpreter::with_module(&probe.module)
            .execute_func(probe.function, [])
            .expect_err("in-range initialized bytes do not prove an aligned access");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error:?}");
        assert!(error.message.contains("not aligned"), "{error:?}");
        assert!(
            probe.diagnostics.iter().any(|diagnostic| {
                diagnostic.reason
                    == trust_mc_trust_bmc::TrustIrChcUnsupportedReason::OperandConsumption
            }),
            "misaligned write must remain refused: {:?}",
            probe.diagnostics
        );
        assert_ne!(error_reachability(&probe.vc), Some(false));
    }
}

#[test]
fn integer_write_preservation_accepts_naturally_aligned_offsets() {
    for (offset, expected) in [(0, 5), (2, 1)] {
        let probe = integer_word_write_probe(offset, 2, None, None, true);
        let result = Interpreter::with_module(&probe.module)
            .execute_func(probe.function, [])
            .expect("the natural allocation alignment and byte offset prove this access");
        assert_eq!(result.returns, [InterpretValue::int(Ty::U8, expected).unwrap()]);
        assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
        assert_eq!(error_reachability(&probe.vc), Some(false));
    }
}

#[test]
fn initialized_bytes_do_not_validate_char_representations_or_out_of_range_writes() {
    for probe in
        [integer_byte_write_probe(Ty::Char, 0, 0x110000), integer_byte_write_probe(Ty::U32, 4, 255)]
    {
        let error = Interpreter::with_module(&probe.module)
            .execute_func(probe.function, [])
            .expect_err("invalid Char bytes or out-of-bounds writes are real UB");
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior, "{error:?}");
        assert!(
            probe.diagnostics.iter().any(|diagnostic| {
                diagnostic.reason
                    == trust_mc_trust_bmc::TrustIrChcUnsupportedReason::OperandConsumption
            }),
            "{:?}",
            probe.diagnostics
        );
        assert_ne!(error_reachability(&probe.vc), Some(false));
    }
}

#[test]
fn bool_byte_writes_retain_the_conservative_representation_boundary() {
    // This interpreter normalizes a nonzero Bool byte to true; that is not
    // Rust validity evidence or permission for the integer-only rule.
    let probe = integer_byte_write_probe(Ty::Bool, 0, 2);
    let result = Interpreter::with_module(&probe.module).execute_func(probe.function, []).unwrap();
    assert_eq!(result.returns, [InterpretValue::bool(true)]);
    assert!(probe.diagnostics.iter().any(|diagnostic| diagnostic.reason
        == trust_mc_trust_bmc::TrustIrChcUnsupportedReason::OperandConsumption));
    assert_ne!(error_reachability(&probe.vc), Some(false));
}

/// THE REGRESSION. Writing `0` through `&mut s.a` makes `100 / s.a` a genuine
/// divide-by-zero, so the error MUST be reachable. Before the fix the write was
/// dropped and the readback was the seeded `1`, folding the error constraint to
/// `false` — a false PROVE of a function that actually divides by zero.
#[test]
fn field_store_through_borrow_is_not_dropped() {
    let bad = probe(Target::FieldBorrow, 0, true);
    assert_eq!(
        error_reachability(&bad.vc),
        Some(true),
        "DROPPED WRITE: `*(&mut s.a) = 0` was not modeled, so the readback folded to the \
         PRE-store field value and the divide-by-zero obligation was falsely PROVED"
    );
    assert!(
        bad.diagnostics.is_empty(),
        "the write is modeled exactly, so nothing should fail closed: {:?}",
        bad.diagnostics
    );
}

/// The other side of the same coin: a write that FIXES the divisor must be
/// believed, so the obligation still proves. Guards against "fix" by blanket
/// havoc, which would leave this `None` instead of `Some(false)`.
#[test]
fn field_store_through_borrow_is_modeled_precisely() {
    let good = probe(Target::FieldBorrow, 7, true);
    assert_eq!(
        error_reachability(&good.vc),
        Some(false),
        "`*(&mut s.a) = 7` must be modeled at the field lane, so the divisor is 7"
    );
    assert!(good.diagnostics.is_empty(), "{:?}", good.diagnostics);
}

/// A matching non-I8 field type is not enough to turn TrustIR byte arithmetic
/// into field identity. Heterogeneous aggregates must fail closed by havocing.
#[test]
fn heterogeneous_non_i8_gep_does_not_update_a_rederived_field_lane() {
    let probe = heterogeneous_non_lane_gep_probe();
    assert_eq!(
        error_reachability(&probe.vc),
        None,
        "`gep u32` index 1 into `{{u64,u32}}` is byte offset 4, not field 1; an exact field-1 update falsely proves the zero-divisor assertion"
    );
    assert!(
        probe.diagnostics.is_empty(),
        "the owned cell was soundly invalidated; no unsupported rule is needed: {:?}",
        probe.diagnostics
    );
}

/// Complete, non-overlapping layout evidence keeps the intended direct lane
/// precise: byte offset 4 is exactly the second u32 field.
#[test]
fn explicit_matching_layout_updates_the_proved_field_lane() {
    let probe = homogeneous_field_one_probe(
        "explicit_matching_layout",
        [Some(0), Some(4)],
        Some(8),
        Some(4),
    );
    assert_eq!(
        error_reachability(&probe.vc),
        Some(false),
        "declared byte offset 4 uniquely identifies field 1"
    );
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
}

/// Homogeneous field types are not layout evidence. With field 1 declared at
/// byte 8, `gep u32 [1]` lands at byte 4 (padding), so updating field 1 would
/// falsely prove the assertion.
#[test]
fn explicit_offset_mismatch_havocs_instead_of_updating_a_field() {
    let probe = homogeneous_field_one_probe(
        "explicit_offset_mismatch",
        [Some(0), Some(8)],
        Some(12),
        Some(4),
    );
    assert_eq!(
        error_reachability(&probe.vc),
        None,
        "a raw byte offset in padding must not be reinterpreted as logical field 1"
    );
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
}

/// `offset: null` is absence of authority, not permission to assume declaration
/// order. Even a homogeneous pair must degrade to havoc without layout evidence.
#[test]
fn missing_struct_layout_havocs_instead_of_assuming_field_identity() {
    let probe = homogeneous_field_one_probe("missing_layout", [None, None], None, None);
    assert_eq!(
        error_reachability(&probe.vc),
        None,
        "missing field offsets cannot authorize an exact derived-pointer update"
    );
    assert!(probe.diagnostics.is_empty(), "{:?}", probe.diagnostics);
}

/// Exact logical-lane replacement is unsound when another declared field aliases
/// the written bytes. The canonical validator and interpreter reject this
/// contradictory layout before a logical lane can authorize a clean execution.
#[test]
fn overlapping_declared_fields_are_refused_instead_of_leaving_a_sibling_stale() {
    let probe = overlapping_fields_probe();
    assert!(!trust_ir_build::validate_module(&probe.module).is_empty());
    assert!(probe.module_input_refusal.is_some());
    assert_eq!(
        error_reachability(&probe.vc),
        Some(true),
        "invalid overlapping layout must produce an unconditional input refusal"
    );
    let error = Interpreter::with_module(&probe.module)
        .execute_func(probe.function, [])
        .expect_err("a declared overlapping struct image is not a valid layout");
    assert_eq!(error.code, InterpretErrorCode::TypeError, "{error:?}");
    assert!(probe.diagnostics.is_empty(), "invalidity has no invented instruction site");
}

/// A `BorrowMut` straight off the alloca (no `GEP`) carries the same provenance.
#[test]
fn whole_cell_store_through_borrow_is_not_dropped() {
    assert_eq!(
        error_reachability(&probe(Target::WholeBorrow, 0, true).vc),
        Some(true),
        "`*(&mut s) = S {{ a: 0, .. }}` was dropped: the readback is stale"
    );
    assert_eq!(
        error_reachability(&probe(Target::WholeBorrow, 7, true).vc),
        Some(false),
        "`*(&mut s) = S {{ a: 7, .. }}` must be modeled exactly"
    );
}

/// An unknown offset cannot be written at a lane, but it also cannot be dropped:
/// the cell is havoced, so the readback is unconstrained and the obligation is
/// left to the solver (`None`) instead of being proved from a stale value.
#[test]
fn symbolic_lane_store_havocs_rather_than_going_stale() {
    for written in [0, 7] {
        assert_eq!(
            error_reachability(&probe(Target::SymbolicLaneBorrow, written, true).vc),
            None,
            "a store at an unknown offset into `s` must havoc the cell (write {written})"
        );
    }
}

/// A store through an unknown pointer, made after `&mut s.a` escaped into a call,
/// may alias `s`. It must invalidate the cell — not be dropped while the cell
/// keeps its pre-store value.
#[test]
fn unknown_store_after_an_address_escape_invalidates_the_cell() {
    assert_eq!(
        error_reachability(&probe(Target::UnknownAfterEscape, 0, true).vc),
        None,
        "the escaped interior address may be this store's target, so `s` must be havoced"
    );
}

/// The precision floor: with no escape anywhere, an unknown store provably cannot
/// reach the cell, so the cell stays precise and the obligation still proves. This
/// is what keeps the fix from degenerating into "havoc everything on any store".
#[test]
fn unknown_store_with_no_escape_leaves_the_cell_precise() {
    assert_eq!(
        error_reachability(&probe(Target::UnknownWithNoEscape, 0, true).vc),
        Some(false),
        "nothing aliases `s`, so `s.a` is still the seeded 1 and the divisor is nonzero"
    );
}

/// THE CALL-INVALIDATION ORACLE. `sink(&mut s.a)` with no store after it. The callee
/// may write any value through the escaped interior pointer, so the readback of `s.a`
/// must be a havoc and `s.a != 0` must NOT prove.
///
/// If this reads `Some(false)`, the translator proved the assertion from the value that
/// was in the cell BEFORE the call — a stale read, and a completed false proof.
///
/// THIS ORACLE IS LOAD-BEARING, AND THAT IS MEASURED, NOT ASSUMED. It was vacuous while
/// `translate_alloca`'s coarse whole-function escape guard demoted every escaping cell —
/// the havoc came from the guard. Now that the guard is narrowed to admit
/// `StackCellEscape::IntoCallsOnly`, commenting out the single
/// `invalidate_cells_escaping_into_call` call in `translate_node` makes THIS test, and
/// only this test, fail: 12 passed / 1 failed. That failure is the translator proving
/// `s.a != 0` from the value the cell held BEFORE the call — the exact false proof the
/// narrowing would have shipped had the two halves been landed in the other order.
#[test]
fn call_escape_without_a_following_store_invalidates_the_cell() {
    assert_eq!(
        error_reachability(&probe(Target::CallEscapeNoStore, 0, true).vc),
        None,
        "the callee may write through the escaped `&mut s.a`, so `s.a` must be havoced"
    );
}

/// `ValidBorrow` asserts the BORROW is valid, never that the WRITE was modeled.
/// Whether it is present must not change what the cell holds afterwards.
#[test]
fn valid_borrow_annotation_does_not_change_the_modeled_write() {
    for target in [Target::FieldBorrow, Target::WholeBorrow] {
        for written in [0, 7] {
            let annotated = probe(target, written, true);
            let bare = probe(target, written, false);
            assert_eq!(
                error_reachability(&annotated.vc),
                error_reachability(&bare.vc),
                "`ValidBorrow` changed the modeled value of the write (write {written})"
            );
        }
    }
}

// ===========================================================================
// THE CROSS-BLOCK PROJECTED-READ ORACLE
//
// `aggregate_cell_hazards_stay_fail_closed` pins that a `FieldProjected` cell is REFUSED
// by both admission lanes, which is what keeps the 181-row aggregate slice of the
// `store_/load_in_other_block` bucket (221 rows at R59) unpromotable. But that pin checks
// REJECTION only, and its fixture DISCARDS the GEP result (`let _addr = fb.gep(..)`), so
// nothing anywhere exercises a projected READ or checks what the model would COMPUTE if
// the cell were promoted.
//
// Widening promotion therefore cannot be justified by the existing suite — it would swap
// a conservative alias rule for an unverified correctness claim. These are the missing
// oracles. They are TESTS, so they cannot introduce a false proof; they can only reveal
// whether the hazard is modelled.
//
// The shape is the hazard itself, not a weaker cousin: the cell is written in BOTH arms
// of a branch and read back THROUGH A GEP in the join — the block that CONSUMES the
// threaded value. That is exactly where a stale or fabricated leaf would surface.
// ===========================================================================

/// `{ u64, u64 }` written in both arms, field 0 read back via `GEP` in the join block.
/// `then_a`/`else_a` are what each arm stores into field 0.
fn cross_block_projected(then_a: i128, else_a: i128) -> ChcVc {
    cross_block_projected_construction(then_a, else_a, Construction::Complete).vc
}

fn cross_block_projected_construction(
    then_a: i128,
    else_a: i128,
    construction: Construction,
) -> Probe {
    let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let mut mb = ModuleBuilder::new("cross_block_projected_read");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let mut fb = mb.function("projected_join", ft);

    let entry = fb.create_block();
    let then_block = fb.create_block();
    let else_block = fb.create_block();
    let join = fb.create_block();
    fb.set_entry(entry);

    fb.switch_to_block(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let cell = fb.alloca(pair.clone());
    fb.condbr(cond, then_block, vec![], else_block, vec![]);

    for (blk, a) in [(then_block, then_a), (else_block, else_a)] {
        fb.switch_to_block(blk);
        let av = fb.const_value(Ty::U64, Constant::Int(a));
        let bv = fb.const_value(Ty::U64, Constant::Int(7));
        let p1 = match construction {
            Construction::Complete => fb.make_aggregate(pair.clone(), vec![av, bv]),
            Construction::LegacyUndef => {
                let undef = fb.undef(pair.clone());
                let p0 = fb.insert_field(pair.clone(), undef, 0, av);
                fb.insert_field(pair.clone(), p0, 1, bv)
            }
        };
        fb.store(pair.clone(), cell, p1);
        fb.br(join, vec![]);
    }

    // THE JOIN: field 0 read back THROUGH a GEP, in the block consuming the threaded
    // value. This is the `FieldProjected` hazard actually exercised.
    fb.switch_to_block(join);
    let lane = fb.const_value(Ty::I64, Constant::Int(0));
    let field_ptr = fb.gep(Ty::U64, cell, vec![lane]);
    let a = fb.load(Ty::U64, field_ptr);
    let zero = fb.const_value(Ty::U64, Constant::Int(0));
    let is_zero = fb.icmp(ICmpOp::Eq, Ty::U64, a, zero);
    let f = fb.const_value(Ty::Bool, Constant::Bool(false));
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, is_zero, f);
    fb.assert(ok);
    fb.ret(vec![a]);
    fb.build();

    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    // This builder makes exactly ONE function, so it is id 0 — unlike `probe()` above,
    // whose `sink` callee occupies 0 and whose subject is 1.
    translate_probe(module, FuncId::new(0))
}

/// BASELINE / ACCEPTANCE TARGET. Field 0 is the SAME nonzero constant on both paths, so
/// `a != 0` is genuinely TRUE. Today the cell is unpromoted (its pointer feeds a `GEP`),
/// the join's projected read havocs, and the obligation is NOT proved.
///
/// A correct widening must turn this into `Some(false)` — WITHOUT changing the tripwire
/// below. That pair is the acceptance criterion for touching
/// `aggregate_cell_hazards_stay_fail_closed`.
#[test]
fn cross_block_projected_read_is_unproved_while_the_cell_is_unpromoted() {
    assert_eq!(
        error_reachability(&cross_block_projected(1, 1)),
        None,
        "baseline: unpromoted cell => the join's projected read havocs => not proved"
    );
}

/// THE FALSE-PROOF TRIPWIRE, and why the target above is not sufficient alone.
///
/// The `else` arm stores ZERO into field 0, so `a != 0` is genuinely FALSE on that path.
/// No model may prove it — not today's havoc, not a future promoted per-leaf model. A
/// widening that makes this report `Some(false)` is threading only ONE arm's leaf into
/// the join and is UNSOUND.
#[test]
fn a_zero_storing_arm_must_never_let_the_projected_read_prove() {
    assert_ne!(
        error_reachability(&cross_block_projected(1, 0)),
        Some(false),
        "FALSE PROOF: else arm stores 0 into field 0, so `a != 0` must not be provable"
    );
}

/// DIAGNOSTIC for the 181-row cross-block bucket: WHICH condition refuses the oracle's
/// cell? Lifting the GEP disqualification alone left the projected read unproved, so a
/// further blocker exists and this names it rather than leaving it to inference.
#[test]
fn why_is_the_cross_block_projected_cell_refused() {
    let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
    let mut mb = ModuleBuilder::new("diag");
    let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
    let mut fb = mb.function("projected_join", ft);
    let (entry, t, e, join) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let cond = fb.add_block_param(entry, Ty::Bool);
    let cell = fb.alloca(pair.clone());
    fb.condbr(cond, t, vec![], e, vec![]);
    for blk in [t, e] {
        fb.switch_to_block(blk);
        let av = fb.const_value(Ty::U64, Constant::Int(1));
        let bv = fb.const_value(Ty::U64, Constant::Int(7));
        let p1 = fb.make_aggregate(pair.clone(), vec![av, bv]);
        fb.store(pair.clone(), cell, p1);
        fb.br(join, vec![]);
    }
    fb.switch_to_block(join);
    let lane = fb.const_value(Ty::I64, Constant::Int(0));
    let fp = fb.gep(Ty::U64, cell, vec![lane]);
    let a = fb.load(Ty::U64, fp);
    fb.ret(vec![a]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let function = &module.functions[0];

    let rejection = single_cell_alloca_rejection(&module, function, cell, &pair);
    println!(
        "CROSS-BLOCK DIAGNOSTIC: lane1={:?} lane2={:?}  non_escaping={} ty_match={}",
        rejection.as_ref().map(|r| r.block_local.kind()),
        rejection.as_ref().map(|r| r.promoted.kind()),
        stack_alloca_pointer_is_non_escaping(function, cell),
        stack_alloca_cell_accesses_match_type(function, cell, &pair),
    );
}
