// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Direct typed trust_ir to CHC translation.
//!
//! This module builds `trust_mc_core::ChcVc` directly from `trust_ir` library values.
//! It does not route through BMC VCs and does not accept caller-provided
//! SMT-LIB strings. Unsupported trust_ir semantics are represented as reachable
//! error rules so the CHC/PDR path fails closed.

use std::collections::{BTreeMap, BTreeSet};

use ay_bindings::Expr;
use trust_ir::constant::Constant;
use trust_ir::dialect::trust_rust::is_thread_local_addr;
use trust_ir::inst::{BinOp, CastOp, ICmpOp, Inst, SwitchCase, UnOp};
use trust_ir::node::InstrNode;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Block, Function, Module};
use trust_mc_core::chc::{ChcQuery, ChcVc, RelationApp, RelationDecl, Rule, RuleBody};

use crate::coverage::{SemanticsFamily, family_for_inst};
use crate::translate::{
    TranslateOptions, bounded_output_out_of_range, const_to_expr,
    integer_binop_div_by_zero_condition, integer_binop_no_overflow_condition, is_eq_comparable_ty,
    is_ordered_scalar_ty, normalize_expr_to_ty, overflow_op_to_binop, switch_case_expr, ty_to_sort,
};

const ERROR_REL: &str = "error";
const DIRECT_CALL_SUMMARY_MAX_STATES: usize = 64;

/// Trust: cap on the number of scalar CHC leaves a single trackable aggregate may
/// flatten into when its block-relation signature is declared. A nested fixed-size
/// array such as `[[[u8; 256]; 256]; 256]` is "trackable" (every leaf is a scalar)
/// yet expands to `256^3 ≈ 16.7M` permanently-declared CHC variables
/// (`declare_relation_binding_rec` → `vc.declare_var` per leaf, plus a `flat_args`
/// re-clone of the whole leaf vector at every relation application), which exhausts
/// RAM + swap. Beyond this budget the aggregate is treated as NON-trackable so it
/// falls back to a single opaque scalar var — the same fail-closed handling a
/// `len > 256` array or an enum already gets (spurious-unverified, never a false
/// proof). Regression guard for the array-aggregate arm added in `bd37bce4a`.
const MAX_AGGREGATE_LEAVES: usize = 4096;

/// Typed result of lowering one trust_ir function to a CHC verification condition.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ChcTranslationOutput {
    /// Generated typed CHC verification condition.
    pub vc: ChcVc,
    /// Fail-closed diagnostics emitted while lowering unsupported trust_ir semantics.
    pub diagnostics: Vec<TrustIrChcDiagnostic>,
}

/// Structured diagnostic for trust_ir constructs that were represented by a
/// reachable `error` rule rather than by complete CHC semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct TrustIrChcDiagnostic {
    /// Function containing the unsupported construct.
    pub function: String,
    /// Basic block containing the unsupported construct.
    pub block: BlockId,
    /// Zero-based instruction index within `block`.
    pub instruction_index: usize,
    /// Coarse semantics family used by production routing.
    pub family: SemanticsFamily,
    /// Typed fail-closed reason.
    pub reason: TrustIrChcUnsupportedReason,
    /// Result values bound to placeholders before the error rule was emitted.
    pub result_values: Vec<ValueId>,
}

/// Typed reason an unsupported trust_ir construct forced CHC lowering to fail closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum TrustIrChcUnsupportedReason {
    FloatingPointArithmetic,
    NonIntegerBinaryOperation,
    FloatingPointComparison,
    UnsupportedComparison,
    /// A constant with no exact bit-level encoding (an F16 float constant, an
    /// F32 constant whose f64 payload is not an exactly-widened f32, or a
    /// malformed vector constant). Wrong placeholder bits could decide an
    /// obligation, so the value is havoced and the lowering fails closed.
    UnmodeledConstant,
    /// A `BoundedOutput` postcondition whose f64 bounds have no exact integer
    /// encoding against the annotated return type (float-typed return,
    /// fractional or out-of-range bound). Encoding it with bitvector
    /// comparisons over wrong values/bits could falsely prove or falsely
    /// refute the postcondition, so it fails closed instead.
    UnsupportedBoundedOutput,
    Cast,
    UnaryOperation,
    OverflowIntrinsic,
    AggregateProjection,
    AggregateUpdate,
    BindingFrame,
    BindingFrameSlotLoad,
    BindingFrameClose,
    SequenceMap,
    MemoryAccessWithoutPreciseModel,
    HeapAllocation,
    GlobalAddress,
    SymbolAddress,
    PointerArithmetic,
    AtomicReadModifyWrite,
    CompareExchange,
    BorrowPermission,
    ReferenceCounting,
    ReferenceCountUniqueness,
    HeapDeallocation,
    PointerMetadata,
    Switch,
    IndirectCall,
    UnknownDirectCall,
    UnsupportedDirectCallSummary,
    RecursiveDirectCall,
    Fence,
    EndBorrow,
    DialectOperation,
    MalformedControlFlow,
    ReturnArityMismatch,
    ReturnInstructionWithResults,
    UnreachableInstruction,
    NonBooleanCondition,
}

/// Translate every function in a `trust_ir::Module` into typed CHC VCs.
pub fn trust_ir_to_chc_vc(module: &Module, options: &TranslateOptions) -> Vec<ChcVc> {
    trust_ir_to_chc_translation_outputs(module, options)
        .into_iter()
        .map(|output| output.vc)
        .collect()
}

/// Translate every function in a `trust_ir::Module` into typed CHC VCs plus
/// fail-closed unsupported-construct diagnostics.
pub fn trust_ir_to_chc_translation_outputs(
    module: &Module,
    options: &TranslateOptions,
) -> Vec<ChcTranslationOutput> {
    module.functions.iter().map(|func| translate_function(func, module, options)).collect()
}

/// Translate one function from a `trust_ir::Module` into a typed CHC VC.
///
/// Returns `None` when `function` does not exist in `module`.
pub fn trust_ir_function_to_chc_vc(
    module: &Module,
    function: FuncId,
    options: &TranslateOptions,
) -> Option<ChcVc> {
    trust_ir_function_to_chc_translation_output(module, function, options).map(|output| output.vc)
}

/// Translate one function from a `trust_ir::Module` into a typed CHC VC plus
/// fail-closed unsupported-construct diagnostics.
///
/// Returns `None` when `function` does not exist in `module`.
pub fn trust_ir_function_to_chc_translation_output(
    module: &Module,
    function: FuncId,
    options: &TranslateOptions,
) -> Option<ChcTranslationOutput> {
    module.function_by_id(function).map(|func| translate_function(func, module, options))
}

struct ChcFuncTranslator<'a> {
    func: &'a Function,
    module: &'a Module,
    options: &'a TranslateOptions,
    vc: ChcVc,
    values: BTreeMap<ValueId, Expr>,
    aggregates: BTreeMap<ValueId, AggregateValue>,
    stack_cells: BTreeMap<ValueId, StackCell>,
    // Result pointers of every `Alloca` in the current block — owned stack memory.
    // A store/load through one is a SAFE access even when the value can't be
    // precisely modeled (a non-scalar struct gets no `stack_cell`), so it must not
    // fail closed; the value is simply left untracked (loads → fresh-symbolic).
    stack_ptrs: BTreeSet<ValueId>,
    // Pointers that are SAFE references (`&T`/`&mut T`): reference-typed function
    // parameters and field/element addresses (`GEP`) derived from them. A field
    // projection off a safe reference is borrow-checker-guaranteed in-bounds, so it
    // must NOT emit a fail-closed `PointerArithmetic` error — that error would poison
    // the function's single shared `ERROR` relation and spuriously refute EVERY
    // obligation (notably the otherwise→Unreachable of any field-carrying match).
    valid_ref_ptrs: BTreeSet<ValueId>,
    // Interior-pointer provenance: for every pointer value derived IN THIS BLOCK
    // from an `Alloca` result (through `GEP` / `Borrow` / `BorrowMut`), which
    // alloca it points into and along which constant field lanes. This is what
    // makes a `Store` through `&mut local.field` reach the alloca's `stack_cell`
    // instead of being silently dropped (a dropped write is a false-PROVE
    // generator: the later `Load` of the same alloca returns the PRE-store value).
    ptr_provenance: BTreeMap<ValueId, PtrProvenance>,
    // Alloca bases whose interior address reached an operand position this
    // translator does not model (a call argument, a stored *value*, a `Select`,
    // an instruction whose reads are not statically enumerable, …). A store
    // through a pointer with no provenance may alias exactly these, so it
    // invalidates them. Recorded in instruction order, which is sound because a
    // cell only exists in the block that allocas it (`stack_cells` is cleared per
    // block) and promoted cells are alias-free by construction, so a pointer used
    // by a store cannot have captured an address that escapes only later.
    escaped_cell_bases: BTreeSet<ValueId>,
    ptr_parts: BTreeMap<ValueId, (Expr, Expr)>,
    // Deterministic slice-length metadata per SSA fat value: the real
    // fat-pointer metadata IS a function of the value, so every `PtrMetadata`
    // read of the SAME `ValueId` must yield the SAME symbol — otherwise a
    // producer-asserted length fact (e.g. trust-ir-bridge's faithful `&str`
    // constant, `Assume(PtrMetadata(v) == len)`) constrains one fresh symbol
    // while a later `s.len()` read of the same value mints another,
    // unconstrained one, and the fact is silently inert. Keyed by the PTR
    // value id, so distinct values keep independent symbols (no cross-value
    // equality is ever asserted) and `ptr_parts`-backed values keep their
    // exact expression (checked first, unchanged). Sound both ways: reusing
    // one symbol per value only removes valuations in which one value has two
    // metadata readings — no real execution is excluded.
    ptr_metadata_syms: BTreeMap<ValueId, Expr>,
    block_param_bindings: BTreeMap<BlockId, Vec<ValueBinding>>,
    // Immutable function parameters (entry-block params), threaded through every
    // block relation so dominance-scoped uses in downstream blocks resolve to the
    // entry value instead of a fresh, unconstrained symbolic.
    threaded_params: Vec<(ValueId, Ty)>,
    // Per-block subset of `threaded_params` actually carried by that block's
    // relation (excludes the entry block and any param the block redeclares).
    block_threaded_params: BTreeMap<BlockId, Vec<(ValueId, Ty)>>,
    // Liveness over-approximation: the set of immutable entry-param `ValueId`s
    // that are live-in at each block (referenced by the block or a block
    // reachable from it without an intervening redefinition). Only live params
    // are threaded into a block relation; threading a dead param is sound but
    // imprecise, while *failing* to thread a live param would be unsound.
    block_live_params: BTreeMap<BlockId, std::collections::BTreeSet<u32>>,
    // Fresh formal-parameter expressions for each block's threaded prefix, in the
    // same order as `block_threaded_params`.
    block_threaded_bindings: BTreeMap<BlockId, Vec<ValueBinding>>,
    // mem2reg: scalar single-cell allocas used ONLY via direct Load/Store, whose
    // CURRENT value is threaded through block relations like an SSA param but
    // UPDATED by stores — recovers loop-carried mutable state the per-block
    // stack_cells reset drops. Promotion requires no aliasing (see compute_promotable_cells).
    promoted_cells: Vec<(ValueId, Ty)>,
    cell_def_block: std::collections::BTreeMap<u32, BlockId>,
    block_promoted_cells: BTreeMap<BlockId, Vec<(ValueId, Ty)>>,
    block_live_cells: BTreeMap<BlockId, std::collections::BTreeSet<u32>>,
    block_cell_bindings: BTreeMap<BlockId, Vec<ValueBinding>>,
    diagnostics: Vec<TrustIrChcDiagnostic>,
    next_sym_id: u32,
}

#[derive(Debug, Clone)]
struct AggregateValue {
    // Trust (#46): a field is itself a `ValueBinding`, so an aggregate field may be
    // a NESTED aggregate (e.g. the `(usize, &T)` tuple payload of an `Option` in an
    // `enumerate`/`?`/`match Some((a,b))` desugar) rather than only a scalar. The
    // CHC relation flattening (`flat_args`, the block-param threading sites) and the
    // declaration↔application leaf order stay consistent by recursing identically.
    fields: Vec<ValueBinding>,
}

#[derive(Debug, Clone)]
struct StackCell {
    ty: Ty,
    value: ValueBinding,
}

/// Where an interior pointer points: the `Alloca` result it derives from, plus the
/// aggregate lanes whose declared layout proves exact byte identity. `lanes == None`
/// means the byte offset cannot be identified with one non-overlapping field (a
/// symbolic or multi-index `GEP`, a struct with missing/mismatched layout evidence,
/// or an unsupported aggregate), so the pointer may target ANY part of `base`.
#[derive(Debug, Clone)]
struct PtrProvenance {
    base: ValueId,
    /// `(field index, the GEP's own `pointee_ty`)` per step. TrustIR GEP is
    /// single-scale byte arithmetic: `index * size_of(pointee_ty)`, not a generic
    /// struct-field selector. A step is recorded only when explicit TrustIR layout
    /// evidence proves that byte offset names exactly that non-overlapping field
    /// (or when an array's element layout proves the same fact). Any unevidenced
    /// step degrades to havoc.
    lanes: Option<Vec<(usize, Ty)>>,
}

/// What `model_indirect_store` did with a `Store` that `translate_stack_store` could
/// not apply directly. There is deliberately NO "dropped" variant: dropping a write
/// while a precise cell for its target survives is the fail-open that lets the
/// verifier read back a value the function already overwrote.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IndirectStoreOutcome {
    /// The write landed exactly, on the base cell or on one constant field lane.
    Exact,
    /// The write was over-approximated: every cell it could target was reset to a
    /// fresh unconstrained value. Sound, imprecise.
    Invalidated,
    /// The store provably cannot reach any surviving precise cell (no provenance
    /// into a tracked alloca, and no tracked cell's address has escaped), so there
    /// is nothing to update or invalidate.
    NoTrackedTarget,
}

/// Result of an exact-or-unknown CFG reachability query used by
/// per-obligation narrowing.
///
/// `ProvenUnreachable` is authority-bearing: it is the only result that may
/// suppress an unsupported-semantics error rule. Missing blocks, dangling
/// successor ids, duplicate block ids, or malformed/unsupported terminators
/// produce `Unknown`, which keeps the rule and therefore fails closed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CfgReachability {
    Reachable,
    ProvenUnreachable,
    Unknown,
}

#[derive(Debug, Clone)]
enum ValueBinding {
    Scalar(Expr),
    Aggregate(AggregateValue),
}

#[derive(Debug, Clone)]
struct DirectCallSummary {
    returns: Vec<ValueBinding>,
    error_conditions: Vec<Expr>,
}

#[derive(Debug, Clone)]
struct CallSummaryState {
    block: BlockId,
    locals: BTreeMap<ValueId, ValueBinding>,
    path_conditions: Vec<Expr>,
    visited_blocks: Vec<BlockId>,
}

#[derive(Debug, Clone)]
struct CallSummaryReturn {
    values: Vec<ValueBinding>,
    path_conditions: Vec<Expr>,
}

impl ValueBinding {
    fn flat_args(&self) -> Vec<Expr> {
        match self {
            Self::Scalar(expr) => vec![expr.clone()],
            // Trust (#46): recurse depth-first, left-to-right — the SAME order the
            // block-relation declaration pushes `arg_sorts`, so the relation's
            // application args line up leaf-for-leaf with its formal signature.
            Self::Aggregate(aggregate) => {
                aggregate.fields.iter().flat_map(ValueBinding::flat_args).collect()
            }
        }
    }
}

impl<'a> ChcFuncTranslator<'a> {
    fn new(func: &'a Function, module: &'a Module, options: &'a TranslateOptions) -> Self {
        Self {
            func,
            module,
            options,
            vc: ChcVc::new(),
            values: BTreeMap::new(),
            aggregates: BTreeMap::new(),
            stack_cells: BTreeMap::new(),
            stack_ptrs: BTreeSet::new(),
            valid_ref_ptrs: BTreeSet::new(),
            ptr_provenance: BTreeMap::new(),
            escaped_cell_bases: BTreeSet::new(),
            ptr_parts: BTreeMap::new(),
            ptr_metadata_syms: BTreeMap::new(),
            block_param_bindings: BTreeMap::new(),
            threaded_params: Vec::new(),
            block_threaded_params: BTreeMap::new(),
            block_live_params: BTreeMap::new(),
            block_threaded_bindings: BTreeMap::new(),
            promoted_cells: Vec::new(),
            cell_def_block: BTreeMap::new(),
            block_promoted_cells: BTreeMap::new(),
            block_live_cells: BTreeMap::new(),
            block_cell_bindings: BTreeMap::new(),
            diagnostics: Vec::new(),
            next_sym_id: 0,
        }
    }

    fn translate(mut self) -> ChcTranslationOutput {
        self.declare_block_relations();
        self.add_entry_rule();

        for block in &self.func.blocks {
            self.translate_block(block);
        }

        ChcTranslationOutput { vc: self.vc, diagnostics: self.diagnostics }
    }

    fn declare_block_relations(&mut self) {
        // Immutable function parameters are defined once at the entry block and
        // are in scope (by dominance) in every block. The producer references
        // them directly in dominated blocks without re-passing them as block
        // arguments, so thread them through every block relation here. Threading
        // an SSA-immutable value is sound: the value never changes, so each block
        // carries the same entry value and every transition forwards it unchanged.
        // (a) Entry params: defined once at the entry block, in scope (by
        // dominance) in every block.
        let mut threaded =
            self.func.block(self.func.entry).map(|entry| entry.params.clone()).unwrap_or_default();
        let mut def_block: BTreeMap<u32, BlockId> = BTreeMap::new();
        for (value, _) in &threaded {
            def_block.insert(value.index(), self.func.entry);
        }
        // (b) SSA-immutable INSTRUCTION results referenced outside their defining
        // block. A total-call `Undef` result (a slice iterator's `next()`, an
        // `s.first()`, etc.) is defined in one block (the call block, possibly a
        // loop body) and matched/field-extracted in a successor — the producer
        // references it by dominance, never re-passing it as a block argument, so
        // it must be threaded exactly like an entry param. Soundness is identical
        // (an SSA value is constant; each block carries the same one and every
        // transition forwards it unchanged) and its def block is excluded below
        // (it COMPUTES the value rather than receiving it). A result type the
        // relation cannot carry is left un-threaded — a downstream use then fails
        // closed, never falsely proved.
        //
        // An `InsertField` aggregate result is threaded the same way: a checked
        // arithmetic op lowers to `(_result, _overflow)` built by `InsertField`
        // in the op block, asserted there, then field-extracted in a SUCCESSOR
        // block by dominance (no block-arg passing). Without threading, the
        // successor's `ExtractField` finds no tracked aggregate and fails closed
        // as a spurious reachable `error` (a false overflow failure on code the
        // op block already proved safe). SSA-immutable, so threading unchanged is
        // sound.
        // GENERAL cross-block SSA threading: ANY value-producing instruction whose
        // PRIMARY result is a precise scalar or a trackable aggregate AND is referenced
        // OUTSIDE its defining block is threaded the same way. This recovers a loop-body
        // COMPUTED value that is DEFINED in one block and USED in a successor — e.g.
        // `count = count.wrapping_add(1)`'s `count + 1` (a `BinOp` in the update block)
        // or `acc = !acc`'s call result — which the per-block `self.values` reset
        // (`translate_block`) would otherwise re-`resolve` to a FRESH symbolic (havoc)
        // at the successor use, leaving the loop-carried state free and the loop
        // invariant unprovable. Soundness is the same as the entry-param / Undef /
        // InsertField threading above: an SSA result is immutable, each block carries the
        // identical value, every transition forwards it unchanged, and a result whose
        // type the relation cannot precisely carry is left un-threaded and fails closed
        // at the cross-block use — never a false proof. The "referenced outside its
        // defining block" gate is computed PRECISELY (`cross_block_general_results`)
        // rather than relying on `compute_live_params`, whose conservative fallback
        // carries every threaded value into every block: threading a result used only
        // within its own block would merely bloat every relation with a dead column.
        // POINTER results are intentionally excluded (`is_precise_stack_scalar_ty` omits
        // `Ptr`) so instruction-result pointers do not enter `valid_ref_ptrs`; only the
        // `Undef` and sealed TLS-address special cases still thread pointer values.
        let cross_block_general = self.cross_block_general_results();
        for block in &self.func.blocks {
            for node in &block.body {
                let threadable = match &node.inst {
                    Inst::Undef { ty } if self.is_call_summary_value_ty(ty) => Some(ty.clone()),
                    Inst::DialectOp(op) if node.results.len() == 1 && is_thread_local_addr(op) => {
                        Some(Ty::Ptr)
                    }
                    Inst::InsertField { ty, .. } if self.aggregate_field_tys(ty).is_some() => {
                        Some(ty.clone())
                    }
                    other => node
                        .results
                        .first()
                        .filter(|result| cross_block_general.contains(&result.index()))
                        .and_then(|_| {
                            self.threadable_result_ty(other).filter(|ty| {
                                is_precise_stack_scalar_ty(ty)
                                    || self.aggregate_field_tys(ty).is_some()
                            })
                        }),
                };
                if let Some(ty) = threadable
                    && let Some(result) = node.results.first()
                {
                    threaded.push((*result, ty));
                    def_block.insert(result.index(), block.id);
                }
            }
        }
        self.threaded_params = threaded.clone();
        // Seed the safe-base set with pointer-typed parameters. A field/element
        // address (`GEP`) derived from a parameter pointer must not fail-close: the
        // `GEP` only computes an address (a fresh symbolic), and any ACCESS through it
        // is independently checked at the Load/Store (which keep their own ValidBorrow
        // guards — a raw deref with no ValidBorrow still fails closed there). The
        // borrow checker maps both `&T` and `*const T` to `TrustIrTy::Ptr`, so we
        // cannot (and need not) distinguish them here: skipping the GEP's redundant
        // fail-close is sound for either, and stops the spurious `PointerArithmetic`
        // error on the pervasive `&param.field` projection from poisoning the shared
        // ERROR relation (which else false-refutes every obligation in the function).
        self.valid_ref_ptrs = threaded
            .iter()
            .filter(|(_, ty)| matches!(ty, Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_)))
            .map(|(id, _)| *id)
            .collect();

        // Restrict threading to values actually live-in at each block (a value is
        // never threaded into its own defining block). Threading every value into
        // every block is sound but imprecise; the precise, still-sound choice
        // threads a value only where a downstream `resolve` could otherwise
        // observe it. See `compute_live_params` for the soundness argument.
        self.block_live_params = self.compute_live_params(&threaded, &def_block);

        // mem2reg: promote scalar single-cell allocas that are used ONLY via direct
        // Load/Store (never aliased) into a THREADED prefix of every block relation,
        // whose value is UPDATED by stores. This recovers loop-carried mutable state
        // (`let mut acc`/`let mut count`) that the per-block `stack_cells` reset drops,
        // turning otherwise-nullary loop-block predicates into real threaded state.
        // `compute_live_params` is reused verbatim: a cell's Load/Store `ptr` operand
        // is collected exactly like a value use, so a cell is threaded into precisely
        // the blocks whose reachable code can Load/Store it (and never its def block,
        // which is excluded via `cell_def`). Threading it is exact — not an
        // over-approximation — because promotion is granted only to un-aliased cells,
        // whose threaded value is provably the cell's only value.
        let (promoted, cell_def) = self.compute_promotable_cells();
        self.promoted_cells = promoted.clone();
        self.cell_def_block = cell_def.clone();
        self.block_live_cells = self.compute_live_params(&promoted, &cell_def);

        // Trust (#46): `&'a Module` is independent of `&self`, so capturing it lets
        // the recursive relation declaration borrow `&mut self.vc` while `block`
        // (from `&self.func`) is live — disjoint fields.
        let module = self.module;
        for block in &self.func.blocks {
            let is_entry = block.id == self.func.entry;
            let own_param_ids: std::collections::BTreeSet<u32> =
                block.params.iter().map(|(value, _)| value.index()).collect();
            let live_here = self.block_live_params.get(&block.id).cloned().unwrap_or_default();

            let mut arg_sorts = Vec::new();
            let mut threaded_bindings = Vec::new();
            let mut threaded_list = Vec::new();

            // Threaded immutable-parameter prefix. The entry block already
            // declares these as its own params, and a block that redeclares a
            // param (e.g. a loop back-edge target) carries it as its own param,
            // so both are skipped here to avoid a duplicate relation argument.
            if !is_entry {
                for (value, ty) in &threaded {
                    if own_param_ids.contains(&value.index()) {
                        continue;
                    }
                    // Skip params that cannot be observed in this block or any
                    // block reachable from it: a dead param needs no transport.
                    if !live_here.contains(&value.index()) {
                        continue;
                    }
                    let binding = declare_relation_binding_rec(
                        module,
                        &mut self.vc,
                        &format!("bb{}_thr_v{}", block.id.index(), value.index()),
                        ty,
                        &mut arg_sorts,
                    );
                    threaded_bindings.push(binding);
                    threaded_list.push((*value, ty.clone()));
                }
            }

            // mem2reg cell prefix — declared AFTER the threaded prefix and BEFORE
            // the own params, so every block relation's signature is exactly
            // [SSA threaded] ++ [promoted cells] ++ [own params]. A cell is never
            // carried by its own def block (it is created there by the Alloca), and
            // dead cells (no reachable Load/Store) are dropped. Each promoted cell is
            // a precise scalar, so it flattens to a single relation leaf.
            let live_cells = self.block_live_cells.get(&block.id).cloned().unwrap_or_default();
            let mut cell_bindings = Vec::new();
            let mut cell_list = Vec::new();
            for (cell, ty) in &promoted {
                if cell_def.get(&cell.index()) == Some(&block.id) {
                    continue;
                }
                if !live_cells.contains(&cell.index()) {
                    continue;
                }
                let binding = declare_relation_binding_rec(
                    module,
                    &mut self.vc,
                    &format!("bb{}_cell_v{}", block.id.index(), cell.index()),
                    ty,
                    &mut arg_sorts,
                );
                cell_bindings.push(binding);
                cell_list.push((*cell, ty.clone()));
            }

            let mut bindings = Vec::new();
            for (value, ty) in &block.params {
                let binding = declare_relation_binding_rec(
                    module,
                    &mut self.vc,
                    &format!("bb{}_v{}", block.id.index(), value.index()),
                    ty,
                    &mut arg_sorts,
                );
                bindings.push(binding);
            }

            self.vc.add_relation(RelationDecl::new(block_relation_name(block.id), arg_sorts));
            self.block_param_bindings.insert(block.id, bindings);
            self.block_threaded_params.insert(block.id, threaded_list);
            self.block_threaded_bindings.insert(block.id, threaded_bindings);
            self.block_promoted_cells.insert(block.id, cell_list);
            self.block_cell_bindings.insert(block.id, cell_bindings);
        }

        self.vc.add_relation(RelationDecl::nullary(ERROR_REL));
        let mut query = ChcQuery::new().with_target(ERROR_REL);
        if let Some(timeout_ms) = self.options.timeout_ms {
            query = query.with_timeout(timeout_ms);
        }
        self.vc.query = query;
    }

    /// The PRIMARY result type of a value-producing SSA instruction, when it is
    /// statically known. Drives the general cross-block SSA threading in
    /// `declare_block_relations` (the caller further gates on the type being
    /// relation-carryable). Returns `None` for instructions whose result is not a
    /// plain scalar/aggregate value the CHC lowering models directly — pointers,
    /// memory/atomic effects, control flow, and opaque/multi-lane results — which
    /// are then left un-threaded and fail closed at a cross-block use (sound, never a
    /// false proof). `ICmp`/`FCmp` yield a `Bool`; `Cast` yields its `dst_ty`; a
    /// direct `Call` yields the callee's first return type. Only the primary result
    /// is typed — a secondary result (e.g. an `Overflow` overflow flag) keeps today's
    /// un-threaded, fail-closed behavior. `Undef`/`InsertField` are handled by their
    /// own dedicated cases at the call site, so they are intentionally not mapped here.
    fn threadable_result_ty(&self, inst: &Inst) -> Option<Ty> {
        Some(match inst {
            Inst::BinOp { ty, .. }
            | Inst::UnOp { ty, .. }
            | Inst::Overflow { ty, .. }
            | Inst::Copy { ty, .. }
            | Inst::Select { ty, .. }
            | Inst::Const { ty, .. }
            | Inst::Load { ty, .. }
            | Inst::LoadSlot { ty, .. }
            | Inst::ExtractField { ty, .. } => ty.clone(),
            Inst::ICmp { .. } | Inst::FCmp { .. } => Ty::Bool,
            Inst::Cast { dst_ty, .. } => dst_ty.clone(),
            Inst::Call { callee, .. } => {
                let callee_func = self.module.function_by_id(*callee)?;
                self.module.func_types.get(callee_func.ty.as_usize())?.returns.first()?.clone()
            }
            _ => return None,
        })
    }

    /// The set of general-threadable instruction-result value ids (see
    /// `threadable_result_ty`) that are referenced OUTSIDE their defining block — the
    /// precise "(a) referenced outside its defining block" gate for cross-block SSA
    /// threading. Uses are collected with the same enumerator `compute_live_params`
    /// uses; a block containing an instruction whose reads are not statically
    /// enumerable (`collect_inst_value_uses` reports conservative) is treated as
    /// possibly using every candidate, so a genuine cross-block use is never missed
    /// (missing one would only lose precision — a fresh havoc — never soundness).
    fn cross_block_general_results(&self) -> std::collections::BTreeSet<u32> {
        // Candidate primary-result value id -> its defining block.
        let mut candidate_def: BTreeMap<u32, BlockId> = BTreeMap::new();
        for block in &self.func.blocks {
            for node in &block.body {
                // Mirror the general-case gate in `declare_block_relations`; the
                // `Undef`/`InsertField` special cases are threaded unconditionally and
                // are not candidates here.
                if matches!(&node.inst, Inst::Undef { .. } | Inst::InsertField { .. })
                    || matches!(&node.inst, Inst::DialectOp(op) if is_thread_local_addr(op))
                {
                    continue;
                }
                let carryable = self.threadable_result_ty(&node.inst).is_some_and(|ty| {
                    is_precise_stack_scalar_ty(&ty) || self.aggregate_field_tys(&ty).is_some()
                });
                if carryable && let Some(result) = node.results.first() {
                    candidate_def.insert(result.index(), block.id);
                }
            }
        }

        let mut cross_block: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
        for block in &self.func.blocks {
            let mut raw_uses = Vec::new();
            let mut conservative = false;
            for node in &block.body {
                conservative |= collect_inst_value_uses(&node.inst, &mut raw_uses);
            }
            if conservative {
                for (&id, &def) in &candidate_def {
                    if def != block.id {
                        cross_block.insert(id);
                    }
                }
            } else {
                for used in &raw_uses {
                    if let Some(&def) = candidate_def.get(&used.index())
                        && def != block.id
                    {
                        cross_block.insert(used.index());
                    }
                }
            }
        }
        cross_block
    }

    /// Backward liveness over-approximation for the immutable entry parameters.
    ///
    /// Returns, per block, the subset of `entry_param` ids that are *live-in*:
    /// referenced by an instruction in the block, or live-in at a successor and
    /// not redeclared as the block's own parameter (the only way an SSA id is
    /// "redefined" here is a back-edge target re-declaring the same id as a
    /// block parameter, which the existing prefix logic already shadows).
    ///
    /// Soundness: the per-block use set is a sound over-approximation — every
    /// statically enumerable read is recorded, and any instruction or
    /// terminator this translator does not recognize marks *all* entry params
    /// as used in that block (and, via the fixpoint, in every block that can
    /// reach it). Consequently a parameter that any reachable block could read
    /// is always threaded, so a downstream `resolve` always finds the threaded
    /// binding rather than minting an unconstrained fresh symbolic. Dropping a
    /// genuinely dead parameter changes neither the reachable states nor the
    /// error rules; it only removes an unused relation column.
    fn compute_live_params(
        &self,
        threaded: &[(ValueId, Ty)],
        def_block: &BTreeMap<u32, BlockId>,
    ) -> BTreeMap<BlockId, std::collections::BTreeSet<u32>> {
        use std::collections::BTreeSet;

        let param_ids: BTreeSet<u32> = threaded.iter().map(|(v, _)| v.index()).collect();
        if param_ids.is_empty() {
            return BTreeMap::new();
        }

        // Per-block direct uses (restricted to threaded values) and successors.
        let mut direct_uses: BTreeMap<BlockId, BTreeSet<u32>> = BTreeMap::new();
        let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
        // The threaded values DEFINED in each block (entry params here, or an
        // instruction result there). A value is never live-in to its own def
        // block — that block computes it rather than receiving it — so it is
        // excluded from both that block's direct uses and the live-out it
        // propagates inward, exactly like a block's own params.
        let mut block_defs: BTreeMap<BlockId, BTreeSet<u32>> = BTreeMap::new();
        for (&id, &blk) in def_block {
            if param_ids.contains(&id) {
                block_defs.entry(blk).or_default().insert(id);
            }
        }

        for block in &self.func.blocks {
            let mut own: BTreeSet<u32> = block.params.iter().map(|(v, _)| v.index()).collect();
            if let Some(defs) = block_defs.get(&block.id) {
                own.extend(defs.iter().copied());
            }

            let mut raw_uses: Vec<ValueId> = Vec::new();
            let mut succs: Vec<BlockId> = Vec::new();
            let mut conservative = false;
            for node in &block.body {
                conservative |= collect_inst_value_uses(&node.inst, &mut raw_uses);
                conservative |= collect_terminator_successors(&node.inst, &mut succs);
            }

            let mut uses: BTreeSet<u32> = if conservative {
                // Unknown instruction/terminator: assume it reads every threaded
                // value so liveness stays a sound over-approximation.
                param_ids.clone()
            } else {
                raw_uses
                    .into_iter()
                    .map(|v| v.index())
                    .filter(|id| param_ids.contains(id))
                    .collect()
            };
            // A block reading an id it also declares/defines (own param or local
            // instruction result) is reading the local definition, not the
            // threaded value; do not count it.
            for d in &own {
                uses.remove(d);
            }

            direct_uses.insert(block.id, uses);
            successors.insert(block.id, succs);
        }

        let mut live: BTreeMap<BlockId, BTreeSet<u32>> =
            self.func.blocks.iter().map(|b| (b.id, BTreeSet::new())).collect();

        // Standard backward-liveness fixpoint, where `defs[B]` = own params ∪
        // locally-defined threaded values:
        //   live_in[B] = uses[B] ∪ ⋃_{S ∈ succ(B)} (live_in[S] \ defs[B])
        let mut changed = true;
        while changed {
            changed = false;
            for block in &self.func.blocks {
                let mut next = direct_uses.get(&block.id).cloned().unwrap_or_default();
                let mut own: BTreeSet<u32> = block.params.iter().map(|(v, _)| v.index()).collect();
                if let Some(defs) = block_defs.get(&block.id) {
                    own.extend(defs.iter().copied());
                }
                for succ in successors.get(&block.id).into_iter().flatten() {
                    if let Some(succ_live) = live.get(succ) {
                        for id in succ_live {
                            if !own.contains(id) {
                                next.insert(*id);
                            }
                        }
                    }
                }
                if let Some(current) = live.get_mut(&block.id)
                    && *current != next
                {
                    *current = next;
                    changed = true;
                }
            }
        }

        live
    }

    /// mem2reg candidate analysis: find scalar single-cell allocas whose result
    /// pointer is NEVER aliased, so their current value can be threaded through
    /// block relations (like an SSA param, but updated by stores) exactly.
    ///
    /// Returns the promotable `(ValueId, Ty)` list (deterministic, ordered by the
    /// alloca result's index) and a `result_index -> def_block` map.
    ///
    /// Soundness — promotion is granted ONLY when the alloca result `R` is used
    /// solely as the `ptr` operand of a matching-type `Inst::Load`/`Inst::Store`.
    /// Any other appearance means the address escaped: as a Store *value* (the
    /// pointer itself is written somewhere), a `GEP` base, a call argument, a
    /// compare operand, a block-argument on a terminator, or a use inside any
    /// instruction this translator does not statically enumerate. In every such
    /// case a hidden write through the alias could change the cell without a
    /// `translate_stack_store` update, so the threaded value would NOT be the
    /// cell's only value — hence the candidate is disqualified and keeps today's
    /// (per-block, non-threaded) behavior. A type-mismatched Load/Store also
    /// disqualifies, since the flattened relation leaf would not match the cell.
    fn compute_promotable_cells(
        &self,
    ) -> (Vec<(ValueId, Ty)>, std::collections::BTreeMap<u32, BlockId>) {
        use std::collections::{BTreeMap, BTreeSet};

        // 1. Candidates: every `Alloca { count: None }` of a precise scalar type
        //    with a first result. Keyed by result index for cheap membership tests.
        let mut candidate_ty: BTreeMap<u32, Ty> = BTreeMap::new();
        let mut candidate_val: BTreeMap<u32, ValueId> = BTreeMap::new();
        let mut def_block: BTreeMap<u32, BlockId> = BTreeMap::new();
        for block in &self.func.blocks {
            for node in &block.body {
                if let Inst::Alloca { ty, count: None, .. } = &node.inst
                    && is_precise_stack_scalar_ty(ty)
                    && let Some(result) = node.results.first()
                {
                    candidate_ty.insert(result.index(), ty.clone());
                    candidate_val.insert(result.index(), *result);
                    def_block.insert(result.index(), block.id);
                }
            }
        }
        if candidate_ty.is_empty() {
            return (Vec::new(), BTreeMap::new());
        }

        // 2. Disqualify any candidate whose pointer is aliased (escapes past a
        //    direct, matching-type Load/Store `ptr` use).
        let mut disqualified: BTreeSet<u32> = BTreeSet::new();
        for block in &self.func.blocks {
            for node in &block.body {
                match &node.inst {
                    // A Load reads only through `ptr`; that use is allowed. The
                    // loaded type must match the alloca type (else the threaded
                    // leaf would not correspond to the cell).
                    Inst::Load { ty, ptr, .. } => {
                        if let Some(cell_ty) = candidate_ty.get(&ptr.index())
                            && cell_ty != ty
                        {
                            disqualified.insert(ptr.index());
                        }
                    }
                    // A Store's `ptr` use is allowed (matching type); its `value`
                    // use is NOT — a candidate appearing as the stored value means
                    // the pointer itself escaped into memory (aliasing).
                    Inst::Store { ty, ptr, value, .. } => {
                        if let Some(cell_ty) = candidate_ty.get(&ptr.index())
                            && cell_ty != ty
                        {
                            disqualified.insert(ptr.index());
                        }
                        if candidate_ty.contains_key(&value.index()) {
                            disqualified.insert(value.index());
                        }
                    }
                    // Every other instruction: ANY value use of a candidate is an
                    // alias. `collect_inst_value_uses` returns `true` for opaque /
                    // unrecognized instructions (pushing nothing); treat that
                    // conservatively by disqualifying all remaining candidates —
                    // such an instruction could read a candidate pointer invisibly.
                    other => {
                        let mut uses = Vec::new();
                        let conservative = collect_inst_value_uses(other, &mut uses);
                        if conservative {
                            for id in candidate_ty.keys() {
                                disqualified.insert(*id);
                            }
                        } else {
                            for used in uses {
                                if candidate_ty.contains_key(&used.index()) {
                                    disqualified.insert(used.index());
                                }
                            }
                        }
                    }
                }
            }
        }

        // 3. Surviving candidates, deterministic order by result index.
        let mut promoted = Vec::new();
        let mut promoted_def: BTreeMap<u32, BlockId> = BTreeMap::new();
        for (index, ty) in &candidate_ty {
            if disqualified.contains(index) {
                continue;
            }
            promoted.push((candidate_val[index], ty.clone()));
            promoted_def.insert(*index, def_block[index]);
        }
        (promoted, promoted_def)
    }

    fn add_entry_rule(&mut self) {
        let Some(entry_block) = self.func.block(self.func.entry) else {
            self.add_global_unsupported_error(TrustIrChcUnsupportedReason::MalformedControlFlow);
            return;
        };
        let Some(entry_app) = self.block_app(entry_block.id) else {
            self.add_global_unsupported_error(TrustIrChcUnsupportedReason::MalformedControlFlow);
            return;
        };
        self.vc.add_rule(Rule::new(RuleBody::empty(), entry_app));
    }

    fn translate_block(&mut self, block: &Block) {
        let Some(from) = self.block_app(block.id) else {
            return;
        };

        self.values.clear();
        self.aggregates.clear();
        self.stack_cells.clear();
        self.stack_ptrs.clear();
        self.ptr_provenance.clear();
        self.escaped_cell_bases.clear();
        // Bind the threaded immutable-parameter prefix first so a block's own
        // params (which redeclare a threaded id on a back-edge) win on conflict.
        if let (Some(threaded), Some(bindings)) = (
            self.block_threaded_params.get(&block.id).cloned(),
            self.block_threaded_bindings.get(&block.id).cloned(),
        ) {
            for ((value, _), binding) in threaded.iter().zip(bindings.iter()) {
                match binding {
                    ValueBinding::Scalar(expr) => {
                        self.values.insert(*value, expr.clone());
                    }
                    ValueBinding::Aggregate(aggregate) => {
                        self.aggregates.insert(*value, aggregate.clone());
                    }
                }
            }
        }
        // mem2reg: seed each promoted cell that is threaded INTO this block (i.e.
        // every block except the cell's def block) from its incoming relation
        // argument, so a Load reads the threaded value and a Store overwrites it in
        // `stack_cells` (which `add_transition_rule` then forwards to successors).
        // The def block is excluded here — `translate_alloca` creates the cell fresh
        // there and the initial store sets it. Runs AFTER `stack_cells.clear()`.
        if let (Some(cells), Some(bindings)) = (
            self.block_promoted_cells.get(&block.id).cloned(),
            self.block_cell_bindings.get(&block.id).cloned(),
        ) {
            for ((cell, ty), binding) in cells.iter().zip(bindings.iter()) {
                self.stack_cells
                    .insert(*cell, StackCell { ty: ty.clone(), value: binding.clone() });
                self.stack_ptrs.insert(*cell);
            }
        }
        if let Some(bindings) = self.block_param_bindings.get(&block.id) {
            for ((value, _), binding) in block.params.iter().zip(bindings.iter()) {
                match binding {
                    ValueBinding::Scalar(expr) => {
                        self.values.insert(*value, expr.clone());
                    }
                    ValueBinding::Aggregate(aggregate) => {
                        self.aggregates.insert(*value, aggregate.clone());
                    }
                }
            }
        }

        let mut path_constraints = Vec::new();
        for (instruction_index, node) in block.body.iter().enumerate() {
            if self.translate_node(node, block.id, instruction_index, &from, &mut path_constraints)
            {
                break;
            }
        }
    }

    fn translate_node(
        &mut self,
        node: &InstrNode,
        block: BlockId,
        instruction_index: usize,
        from: &RelationApp,
        path_constraints: &mut Vec<Expr>,
    ) -> bool {
        self.record_interior_pointer_escapes(&node.inst);
        match &node.inst {
            Inst::BinOp { op, ty, lhs, rhs } if ty.is_integer() => {
                self.translate_integer_binop(*op, ty, *lhs, *rhs, node, from, path_constraints);
                // A float op on an INTEGER type is ill-typed IR; eval_binop
                // havocs the result ("float_on_int"), so fail closed rather
                // than let the unconstrained value silently feed obligations
                // (mirrors the BMC lane's translate_integer_binop).
                if matches!(
                    op,
                    BinOp::FAdd
                        | BinOp::FSub
                        | BinOp::FMul
                        | BinOp::FDiv
                        | BinOp::FRem
                        | BinOp::FMin
                        | BinOp::FMax
                ) {
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::FloatingPointArithmetic,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::BinOp { op, ty, lhs, rhs } => {
                let lhs_expr = self.resolve(*lhs, ty);
                let rhs_expr = self.resolve(*rhs, ty);
                let result = self.eval_binop(*op, ty, &lhs_expr, &rhs_expr);
                self.bind_first_result(node, result);
                // Boolean And/Or/Xor are modeled PRECISELY by `eval_binop` as
                // logical connectives — they are not unsupported, so do not poison
                // the translation with a fail-closed diagnostic (which previously
                // made every boolean combination, e.g. a discriminant-validity
                // assume, fall out of native CHC verification). Float arithmetic
                // and every other non-integer binop remain fail-closed.
                let modeled_precisely =
                    matches!(ty, Ty::Bool) && matches!(op, BinOp::And | BinOp::Or | BinOp::Xor);
                if !modeled_precisely {
                    let reason = if ty.is_float()
                        || matches!(
                            op,
                            BinOp::FAdd
                                | BinOp::FSub
                                | BinOp::FMul
                                | BinOp::FDiv
                                | BinOp::FRem
                                | BinOp::FMin
                                | BinOp::FMax
                        ) {
                        TrustIrChcUnsupportedReason::FloatingPointArithmetic
                    } else {
                        TrustIrChcUnsupportedReason::NonIntegerBinaryOperation
                    };
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        reason,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::Const { ty, value } => {
                if matches!(value, Constant::SymbolAddr { .. }) {
                    let result = self.fresh_symbolic("symbol_addr", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::SymbolAddress,
                        from,
                        path_constraints,
                    );
                } else if let Some(expr) = const_to_expr(ty, value) {
                    self.bind_first_result(node, expr);
                } else {
                    // No exact bit-level encoding — havoc + fail closed,
                    // mirroring the BMC lane (never substitute wrong bits).
                    let result = self.fresh_symbolic("unmodeled_const", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::UnmodeledConstant,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let lhs_expr = self.resolve(*lhs, ty);
                let rhs_expr = self.resolve(*rhs, ty);
                if let Some(result) = self.eval_icmp(*op, ty, &lhs_expr, &rhs_expr) {
                    self.bind_first_result(node, result);
                } else {
                    let result = self.fresh_symbolic("unsupported_icmp_result", &Ty::Bool);
                    self.bind_first_result(node, result);
                    let reason = if ty.is_float() {
                        TrustIrChcUnsupportedReason::FloatingPointComparison
                    } else {
                        TrustIrChcUnsupportedReason::UnsupportedComparison
                    };
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        reason,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::Assert { cond } => {
                if let Some(cond_expr) = self.resolve_bool_condition(
                    *cond,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                ) {
                    self.add_error_rule(from, path_constraints, cond_expr.not());
                }
                false
            }
            Inst::Assume { cond } => {
                if let Some(cond_expr) = self.resolve_bool_condition(
                    *cond,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                ) {
                    path_constraints.push(cond_expr);
                }
                false
            }
            Inst::Return { values } => {
                self.translate_return(
                    values,
                    node,
                    block,
                    instruction_index,
                    from,
                    path_constraints,
                );
                true
            }
            Inst::Br { target, args } => {
                self.add_transition_rule(
                    *target,
                    args,
                    None,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                true
            }
            Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                let Some(cond_expr) = self.resolve_bool_condition(
                    *cond,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                ) else {
                    return true;
                };
                self.add_transition_rule(
                    *then_target,
                    then_args,
                    Some(cond_expr.clone()),
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                self.add_transition_rule(
                    *else_target,
                    else_args,
                    Some(cond_expr.not()),
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                true
            }
            // `exhaustive_enum_unreachable` (trust_ir) would let this CHC encoder
            // conjoin `selector ∈ {case values}` into the default arm to prove it
            // UNSAT. Ignoring it is the sound fallback (and the prior behavior):
            // the default arm stays reachable, so a genuinely-unreachable default
            // is reported Unknown/Fail rather than discharged. Honoring the hint
            // for the stronger result is a future optimization.
            Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable: _,
            } => {
                self.translate_switch(
                    *value,
                    *default,
                    default_args,
                    cases,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                true
            }
            Inst::Copy { ty, operand } => {
                if let Some(aggregate) = self.resolve_aggregate(*operand, ty) {
                    self.bind_aggregate_result(node, aggregate, ty);
                } else {
                    let expr = self.resolve(*operand, ty);
                    self.bind_first_result(node, expr);
                }
                if let Some(result) = node.results.first()
                    && let Some(parts) = self.ptr_parts.get(operand).cloned()
                {
                    self.ptr_parts.insert(*result, parts);
                }
                false
            }
            Inst::Select { ty, cond, then_val, else_val } => {
                let Some(cond_expr) = self.resolve_bool_condition(
                    *cond,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                ) else {
                    let result = self.fresh_symbolic("unsupported_result", ty);
                    self.bind_first_result(node, result);
                    return false;
                };
                let then_expr = self.resolve(*then_val, ty);
                let else_expr = self.resolve(*else_val, ty);
                self.bind_first_result(node, Expr::ite(cond_expr, then_expr, else_expr));
                false
            }
            Inst::NullPtr => {
                self.bind_first_result(node, Expr::bitvec_const(0u64, 64));
                false
            }
            Inst::GlobalAddr { .. } => {
                let ptr = self.fresh_symbolic("global_addr", &Ty::Ptr);
                self.bind_first_result(node, ptr);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::GlobalAddress,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::DialectOp(op) if node.results.len() == 1 && is_thread_local_addr(op) => {
                // This exact Rust-source dialect op denotes one demonic TLS
                // address. It adds no path constraint or validity assumption;
                // `ValidBorrow` on a later safe-reference access is checked at
                // that access, while raw-pointer loads/stores still fail closed.
                let ptr = self.fresh_symbolic("thread_local_addr", &Ty::Ptr);
                self.bind_first_result(node, ptr);
                false
            }
            Inst::Undef { ty } => {
                // A struct/tuple `Undef` with scalar fields is modeled as a
                // *tracked* aggregate of fresh-symbolic fields (the same shape
                // `fresh_call_summary_value` builds for a total call result), so a
                // later `ExtractField` — e.g. reading the discriminant of a
                // fresh-symbolic `Option` returned by a modeled total slice-iterator
                // `next()` — resolves to that precise field instead of falling to
                // the unsupported path (which poisoned the obligation). Sound: each
                // field is an independent unconstrained symbolic, exactly the
                // semantics of an undefined aggregate, so nothing depending on a
                // field is ever falsely proved. A scalar or opaque-field type keeps
                // a single fresh symbolic, unchanged from before.
                match self.fresh_call_summary_value("undef", ty) {
                    Some(ValueBinding::Aggregate(aggregate)) => {
                        self.bind_aggregate_result(node, aggregate, ty);
                    }
                    Some(ValueBinding::Scalar(expr)) => {
                        self.bind_first_result(node, expr);
                    }
                    None => {
                        let result = self.fresh_symbolic("undef", ty);
                        self.bind_first_result(node, result);
                    }
                }
                false
            }
            Inst::Call { callee, args } => {
                self.translate_call(
                    *callee,
                    args,
                    node,
                    block,
                    instruction_index,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::Alloca { ty, count, .. } => {
                self.translate_alloca(ty, count, node);
                false
            }
            Inst::HeapAlloc { .. } => {
                let ptr = self.fresh_symbolic("heap_alloc_ptr", &Ty::Ptr);
                self.bind_first_result(node, ptr);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::HeapAllocation,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::Load { ty, ptr, volatile, .. } => {
                if *volatile || !self.translate_stack_load(ty, *ptr, node) {
                    let result = self.fresh_symbolic("load_result", ty);
                    self.bind_first_result(node, result);
                    // A load of an aggregate (struct/enum) also registers a tracked
                    // aggregate of fresh-symbolic fields, so a subsequent
                    // `ExtractField` projects a CONSISTENT field symbol instead of
                    // failing to AggregateProjection-unsupported. This is what an
                    // enum discriminant read behind a `&self`/`&E` match compiles to
                    // (`ExtractField(Load(ptr), 0)`); without the tracked aggregate
                    // the discriminant the exhaustive-switch `Assume` constrains and
                    // the one the `Switch` selects were DIFFERENT fresh symbols, so
                    // the otherwise→`Unreachable` obligation got a spurious
                    // counterexample (by-value matches, with no load, already proved).
                    // Sound: every field is a fresh unconstrained value.
                    if let Some(result_id) = node.results.first().copied() {
                        self.resolve_aggregate(result_id, ty);
                    }
                    // A load annotated `ValidBorrow` is through a SAFE reference
                    // (`&T`/`&mut T`): the borrow checker guarantees the access is
                    // valid, so an unknown-address reference load is soundly modeled
                    // by the fresh-symbolic result above (the VALUE is unknown, the
                    // access is sound) — do NOT fail closed. This is what lets a
                    // slice iterator's yielded `&x` deref verify. A raw-pointer load
                    // (no annotation) carries no such guarantee and stays fail-closed.
                    let valid_reference = node.proofs.contains(&ProofAnnotation::ValidBorrow);
                    let known_stack = self.stack_ptrs.contains(ptr);
                    if self.options.check_memory_bounds && !valid_reference && !known_stack {
                        self.add_unsupported_error(
                            block,
                            instruction_index,
                            node,
                            TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel,
                            from,
                            path_constraints,
                        );
                    }
                }
                false
            }
            Inst::Store { ty, ptr, value, volatile, .. } => {
                if *volatile || !self.translate_stack_store(ty, *ptr, *value) {
                    // The direct (alloca-keyed) update did not apply. Before any
                    // suppression is considered, the write must still be MODELED:
                    // a store through an interior pointer (`&mut local.field`, a
                    // `GEP` off the alloca, a borrow of either) targets a tracked
                    // cell that `translate_stack_store` cannot see, and dropping it
                    // leaves the following `Load` returning the PRE-store value.
                    let outcome = self.model_indirect_store(*volatile, ty, *ptr, *value);

                    // A store annotated `ValidBorrow` is through a SAFE `&mut`
                    // reference: the borrow checker guarantees the access is valid,
                    // so an unknown-address reference store is sound to leave
                    // unmodeled (the written location is untracked — a later read
                    // through an unknown pointer is already fresh-symbolic) rather
                    // than fail closing. The stored value's own obligations are
                    // checked at its defining instruction. This is what lets
                    // `for x in s.iter_mut() { *x = … }` verify. A raw-pointer store
                    // (no annotation) stays fail-closed.
                    //
                    // `ValidBorrow` asserts the BORROW is valid; it is NOT an
                    // assertion that the WRITE was modeled, and it may not suppress
                    // the fail-close on that second question. `stale_cell` is the
                    // enforcement: `NoTrackedTarget` claims no precise cell could
                    // have been changed, so if one reachable from this pointer is
                    // nonetheless still standing (holding its PRE-store value), the
                    // claim is wrong — report unsupported no matter what annotations
                    // say. `Exact`/`Invalidated` already rewrote the cell.
                    let stale_cell = outcome == IndirectStoreOutcome::NoTrackedTarget
                        && self.store_target_cell_survives(*ptr);
                    let valid_reference = node.proofs.contains(&ProofAnnotation::ValidBorrow);
                    // Owned stack memory: the alloca itself, or an interior pointer
                    // whose whole offset is a constant field-lane chain rooted at an
                    // alloca (in-bounds by construction — the producer derives each
                    // lane from a type-directed field walk). Recognizing the latter
                    // is what makes the fail-close depend on whether the WRITE WAS
                    // MODELED rather than on whether a `ValidBorrow` annotation
                    // happens to be present. An unknown offset keeps `lanes: None`
                    // and still fails closed.
                    let known_stack = self.stack_ptrs.contains(ptr)
                        || self
                            .ptr_provenance
                            .get(ptr)
                            .is_some_and(|provenance| provenance.lanes.is_some());
                    if self.options.check_memory_bounds
                        && (stale_cell || (!valid_reference && !known_stack))
                    {
                        self.add_unsupported_error(
                            block,
                            instruction_index,
                            node,
                            TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel,
                            from,
                            path_constraints,
                        );
                    }
                }
                false
            }
            Inst::AtomicLoad { ty, .. } => {
                let result = self.fresh_symbolic("load_result", ty);
                self.bind_first_result(node, result);
                if self.options.check_memory_bounds {
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::AtomicStore { .. } | Inst::GEP { .. } => {
                // A `GEP` off a SAFE reference base (a `&T`/`&mut T` parameter, a
                // known-stack place, or another safe-ref-derived GEP) is a
                // borrow-checker-guaranteed in-bounds field/element address; do NOT
                // fail-close it. (The access THROUGH the result is still independently
                // checked at the Load/Store.) Without this, a spurious
                // `PointerArithmetic` error on the pervasive `&x.field` projection
                // poisons the function's single shared `ERROR` relation and
                // false-counterexamples EVERY obligation — e.g. the otherwise→
                // Unreachable of a field-carrying enum match (derived `Debug::fmt`).
                // An atomic store writes memory like any other store. Its value is
                // never modeled, but it must still not leave a tracked cell holding
                // its PRE-store value. The fail-close below is gated on
                // `check_memory_bounds`; cell invalidation is not, because turning
                // off a DIAGNOSTIC must never turn on a stale read.
                if let Inst::AtomicStore { ptr, .. } = &node.inst {
                    self.invalidate_store_targets(*ptr);
                }
                let gep_safe = if let Inst::GEP { base, indices, pointee_ty, .. } = &node.inst {
                    let ptr = self.fresh_symbolic("gep_ptr", &Ty::Ptr);
                    self.bind_first_result(node, ptr);
                    // Extend the interior-pointer provenance chain. TrustIR GEP is
                    // `base + sum(indices) * size_of(pointee_ty)`, so a constant
                    // index names an aggregate lane ONLY when declared layout proves
                    // its byte offset is exactly one non-overlapping field start (or
                    // the current aggregate is an array with the matching element
                    // stride). A missing/mismatched layout, symbolic, multi-index, or
                    // out-of-range step keeps the base but drops to "unknown offset",
                    // making a later store havoc the whole cell rather than silently
                    // update the wrong lane.
                    if let Some(base_provenance) = self.ptr_provenance.get(base).cloned()
                        && let Some(result) = node.results.first()
                    {
                        let lanes = base_provenance.lanes.and_then(|lanes| {
                            let [index] = indices[..] else { return None };
                            let field = self.constant_lane_index(index)?;
                            self.extend_exact_gep_lanes(
                                base_provenance.base,
                                lanes,
                                field,
                                pointee_ty,
                            )
                        });
                        self.ptr_provenance
                            .insert(*result, PtrProvenance { base: base_provenance.base, lanes });
                    }
                    let safe = self.valid_ref_ptrs.contains(base) || self.stack_ptrs.contains(base);
                    if safe && let Some(result) = node.results.first() {
                        // Propagate safe provenance so nested projections (`&self.a.b`)
                        // and a later Load/Store base stay recognized as safe.
                        self.valid_ref_ptrs.insert(*result);
                    }
                    safe
                } else {
                    false
                };
                if self.options.check_memory_bounds && !gep_safe {
                    let reason = if matches!(&node.inst, Inst::GEP { .. }) {
                        TrustIrChcUnsupportedReason::PointerArithmetic
                    } else {
                        TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel
                    };
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        reason,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::PtrData { ptr_ty, ptr } => {
                let data = self
                    .ptr_parts
                    .get(ptr)
                    .map(|(data, _)| data.clone())
                    .unwrap_or_else(|| self.resolve(*ptr, ptr_ty));
                self.bind_first_result(node, data);
                false
            }
            Inst::PtrMetadata { ptr_ty: _, metadata_ty, ptr } => {
                let metadata = if let Some((_, metadata)) = self.ptr_parts.get(ptr) {
                    metadata.clone()
                } else if matches!(metadata_ty, Ty::Unit) {
                    Expr::true_()
                } else if matches!(metadata_ty, Ty::U64) {
                    // A slice/str fat-pointer's metadata is its element/byte LENGTH
                    // (usize == U64), which the language guarantees lies in
                    // [0, isize::MAX] (total byte size <= isize::MAX, each element
                    // >= 1 byte). Model it as a fresh symbolic bounded by isize::MAX
                    // instead of an opaque unsupported value, so the CHC/PDR lane can
                    // prove obligations over `s.len()` — e.g. `s.len() + 1` no-overflow
                    // and `while i < s.len() { i += 1 }`. SOUND for proofs AND cex: the
                    // length is a genuine free value and EVERY value in [0, isize::MAX]
                    // is a realizable length, so this neither over- nor under-approximates.
                    // Gated to `U64` so a `dyn Trait` vtable pointer (Ty::Ptr) is NOT
                    // mis-bounded — it keeps the opaque-unsupported path below.
                    //
                    // DETERMINISTIC per SSA value (`ptr_metadata_syms`): the real
                    // metadata is a function of the fat value, so repeated reads
                    // of the SAME `ValueId` reuse one symbol. This is what lets a
                    // producer-asserted exact length (`Assume(PtrMetadata(v) ==
                    // len)`, the faithful `&str`-constant lowering) bind every
                    // later `s.len()` read of the same value in the same clause
                    // scope, instead of evaporating against a fresh symbol. The
                    // isize::MAX bound is (re-)pushed at EVERY read site because
                    // path constraints are per-clause, not per-symbol.
                    let metadata = match self.ptr_metadata_syms.get(ptr) {
                        Some(existing) => existing.clone(),
                        None => {
                            let fresh = self.fresh_symbolic("slice_len", metadata_ty);
                            self.ptr_metadata_syms.insert(*ptr, fresh.clone());
                            fresh
                        }
                    };
                    let isize_max = Expr::bitvec_const(i64::MAX as i128, 64);
                    path_constraints.push(metadata.clone().bvule(isize_max));
                    metadata
                } else {
                    let result = self.fresh_symbolic("ptr_metadata", metadata_ty);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::PointerMetadata,
                        from,
                        path_constraints,
                    );
                    result
                };
                self.bind_first_result(node, metadata);
                false
            }
            Inst::PtrFromParts { ptr_ty: _, metadata_ty, data, metadata } => {
                let data_expr = self.resolve(*data, &Ty::Ptr);
                let metadata_expr = if matches!(metadata_ty, Ty::Unit) {
                    Expr::true_()
                } else {
                    self.resolve(*metadata, metadata_ty)
                };
                if let Some(result) = node.results.first() {
                    self.values.insert(*result, data_expr.clone());
                    self.ptr_parts.insert(*result, (data_expr, metadata_expr));
                }
                false
            }
            Inst::Unreachable => {
                // Reaching an `Unreachable` is a safety violation, not an
                // unsupported construct. Emit a proof obligation that this program
                // point is infeasible — `Reachable ∧ path_constraints → ERROR` —
                // exactly as `Assert(false)` is encoded. The CHC then PROVES the
                // point unreachable when the path makes it infeasible (e.g. an
                // exhaustive enum match's otherwise arm under a discriminant-validity
                // `Assume(tag == 0 || tag == 1)`), and fails closed (derives ERROR →
                // counterexample) when it is genuinely reachable. Previously this
                // declared the whole translation unsupported, so *every* function
                // with an exhaustive match (the desugar of `match`/`if let`/`for`)
                // fell out of native CHC verification.
                self.add_error_rule(from, path_constraints, Expr::true_());
                // `Unreachable` is a terminator: stop translating this block.
                true
            }
            Inst::Cast { op, src_ty, dst_ty, operand } => {
                // The `vec!`/`Box` machinery transmutes a raw pointer through
                // single-pointer NEWTYPE structs: `*mut u8 -> Box<MaybeUninit<T>>`
                // (WRAP) and `NonNull -> *const MaybeUninit<T>` (UNWRAP). trust-ir
                // lowers Box/Unique/NonNull to `Struct(id)`; thread the pointer
                // value through these (value-preserving — the changed pointee type
                // is a SEPARATE deref-validity obligation). Both directions are
                // gated on `pointer_newtype_field_path` (fail-closed for any
                // non-newtype / fat-pointer shape), so no value transmute is
                // mismodeled as a pointer thread.
                if is_thin_pointer_ty(dst_ty) && !is_thin_pointer_ty(src_ty) {
                    if let Some(path) =
                        pointer_newtype_field_path(src_ty, self.module, POINTER_NEWTYPE_FUEL)
                        && let Some(ptr) = self.unwrap_pointer_newtype(*operand, src_ty, &path)
                    {
                        self.bind_first_result(node, ptr);
                        return false;
                    }
                } else if is_thin_pointer_ty(src_ty) && !is_thin_pointer_ty(dst_ty) {
                    if let Some(path) =
                        pointer_newtype_field_path(dst_ty, self.module, POINTER_NEWTYPE_FUEL)
                    {
                        let ptr = self.resolve(*operand, src_ty);
                        if let Some(agg) = self.wrap_pointer_newtype(ptr, dst_ty, &path) {
                            self.bind_aggregate_result(node, agg, dst_ty);
                            return false;
                        }
                    }
                } else if matches!(op, CastOp::Bitcast)
                    && is_pointer_width_unsigned_ty(src_ty)
                    && !is_thin_pointer_ty(dst_ty)
                {
                    // usize -> NonNull<T> (the `fmt::Arguments` bit-packing): at the
                    // pinned 64-bit target both sides are the SAME BV64 bits, so wrap
                    // the integer as the newtype's address leaf. No validity or
                    // provenance is asserted — a later deref carries its own
                    // obligation; only the round-trip bit identity is modeled.
                    if let Some(path) =
                        pointer_newtype_field_path(dst_ty, self.module, POINTER_NEWTYPE_FUEL)
                        && !path.is_empty()
                    {
                        let bits = self.resolve(*operand, src_ty);
                        if let Some(agg) = self.wrap_pointer_newtype(bits, dst_ty, &path) {
                            self.bind_aggregate_result(node, agg, dst_ty);
                            return false;
                        }
                    }
                } else if matches!(op, CastOp::Bitcast)
                    && is_pointer_width_unsigned_ty(dst_ty)
                    && !is_thin_pointer_ty(src_ty)
                {
                    // NonNull<T> -> usize (the unpack): the address leaf IS the
                    // integer's bits. `!path.is_empty()` keeps a bare thin-pointer
                    // source out of this leg — its honest spelling stays `PtrToInt`.
                    if let Some(path) =
                        pointer_newtype_field_path(src_ty, self.module, POINTER_NEWTYPE_FUEL)
                        && !path.is_empty()
                        && let Some(bits) = self.unwrap_pointer_newtype(*operand, src_ty, &path)
                    {
                        self.bind_first_result(node, bits);
                        return false;
                    }
                }
                // Same-type fat->fat reinterpret (`&str -> &[u8]` — identical
                // trust-ir spelling): identity on the BV64 data value. The
                // (data, metadata) parts and the deterministic `slice_len`
                // symbol are FORWARDED so a metadata read through the cast is
                // the same length as through the original value (true of the
                // real fat pointer: the cast does not change it). Forwarding
                // only copies an EXISTING binding — if the operand has none,
                // both values independently havoc (weaker, still sound).
                if matches!(op, CastOp::Bitcast | CastOp::PtrToPtr)
                    && src_ty == dst_ty
                    && matches!(src_ty, Ty::FatPtr(_))
                {
                    let value = self.resolve(*operand, src_ty);
                    self.bind_first_result(node, value);
                    if let Some(result) = node.results.first().copied() {
                        if let Some(parts) = self.ptr_parts.get(operand).cloned() {
                            self.ptr_parts.insert(result, parts);
                        }
                        if let Some(sym) = self.ptr_metadata_syms.get(operand).cloned() {
                            self.ptr_metadata_syms.insert(result, sym);
                        }
                    }
                    return false;
                }
                // Fat -> thin (`*const [u8] -> *const u8`, the `as_ptr` leg): a
                // fat value's SSA expression IS its data lane (the
                // `PtrFromParts` convention), so the thin result is exactly
                // that data pointer. Metadata is dropped, never transferred.
                if matches!(op, CastOp::Bitcast | CastOp::PtrToPtr)
                    && matches!(src_ty, Ty::FatPtr(_))
                    && is_thin_pointer_ty(dst_ty)
                {
                    let data = self
                        .ptr_parts
                        .get(operand)
                        .map(|(data, _)| data.clone())
                        .unwrap_or_else(|| self.resolve(*operand, src_ty));
                    self.bind_first_result(node, data);
                    return false;
                }
                if let Some(result) = self.eval_cast(*op, src_ty, dst_ty, *operand) {
                    self.bind_first_result(node, result);
                    // A1 SOUNDNESS: a NARROWING integer cast (`CastOp::Trunc`, src wider than
                    // dst) loses bits unless the value already fits the destination. Emit the
                    // lossless-narrowing-cast L0 obligation as a reachable `error` edge —
                    // mirroring the div-by-zero error rule — so the violation is REACHABLE
                    // exactly when the cast can lose information. Without this edge the
                    // narrowing cast carried NO obligation: its violation predicate was
                    // unreachable, so the acyclic search reported ExhaustivelyNone -> Safe and
                    // a lossy `(h % n) as u32` (n:u64 unbounded) FALSELY PROVED on -full.
                    // FAITHFUL: re-extending the kept low `dst` bits back to `src` width equals
                    // the operand EXACTLY when the dropped high bits are the type-correct
                    // extension (0 for an unsigned dst, sign-copies for a signed dst) — i.e.
                    // the value fits. So `error` fires iff the truncation is genuinely lossy;
                    // a bounded value (e.g. `h % n` with `n <= u32::MAX`) keeps it UNSAT and
                    // still proves.
                    if *op == CastOp::Trunc
                        && src_ty.is_integer()
                        && dst_ty.is_integer()
                        && let (Some(src_w), Some(dst_w)) = (
                            src_ty.bit_width_with(HOST_POINTER_BITS),
                            dst_ty.bit_width_with(HOST_POINTER_BITS),
                        )
                        && src_w > dst_w
                    {
                        let src_val = self.resolve(*operand, src_ty);
                        let kept = src_val.clone().extract(dst_w - 1, 0);
                        let reext = if dst_ty.is_signed() {
                            kept.sign_extend(src_w - dst_w)
                        } else {
                            kept.zero_extend(src_w - dst_w)
                        };
                        let lossy = src_val.eq(reext).not();
                        self.add_error_rule(from, path_constraints, lossy);
                    }
                } else {
                    let result = self.fresh_symbolic("unsupported_result", dst_ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::Cast,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::ExtractField { ty, aggregate, field } => {
                if let Some(binding) = self.eval_extract_field(*aggregate, *field) {
                    // Trust (#46): the extracted field may itself be a nested
                    // aggregate (e.g. the tuple payload of `Some((a,b))`) — bind it as
                    // an aggregate so a SUBSEQUENT ExtractField on this result resolves.
                    match binding {
                        ValueBinding::Scalar(expr) => self.bind_first_result(node, expr),
                        ValueBinding::Aggregate(aggregate) => {
                            self.bind_aggregate_result(node, aggregate, ty)
                        }
                    }
                } else {
                    let result = self.fresh_symbolic("unsupported_result", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::AggregateProjection,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::InsertField { ty, aggregate, field, value } => {
                if let Some(result) = self.eval_insert_field(ty, *aggregate, *field, *value) {
                    self.bind_aggregate_result(node, result, ty);
                } else {
                    let result = self.fresh_symbolic("unsupported_result", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::AggregateUpdate,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::ExtractElement { ty: dst_ty, .. } => {
                // An array/vector element READ. Model the element as a fresh
                // unconstrained value and do NOT fail closed: an unknown read value
                // can never make a dependent obligation falsely provable, and the
                // access's bounds safety is carried by the separately-emitted bounds
                // `Assert` — exactly as a `ValidBorrow` load is modeled above (see
                // `Inst::Load`). Failing closed here instead poisons the whole
                // function CHC and blocks that bounds obligation from ever being
                // proved (e.g. `arr[idx]` under a proven `idx < len` guard).
                let result = self.fresh_symbolic("element_read", dst_ty);
                self.bind_first_result(node, result);
                false
            }
            Inst::UnOp { op, ty, operand } => {
                // Logical / bitwise NOT is a TOTAL function whose value must be
                // BOUND, not havocked. An inlined `acc = !acc` (and `acc ^ true`,
                // which trustc const-folds to `UnOp::Not`) otherwise fell through
                // to the fail-closed fresh-symbolic path below, leaving `acc'`
                // free — so a loop-carried boolean accumulator was HAVOC'd and the
                // loop invariant (e.g. count-parity `acc <=> count[0]`) became
                // unprovable. Model `Not` PRECISELY (bool -> logical not, integer
                // -> bitwise complement), mirroring the direct-call summary
                // interpreter's `UnOp::Not` arm. The remaining unary ops — the
                // IEEE float ops and `CtPop` — keep the fail-closed
                // fresh-symbolic modeling below (unchanged behavior).
                if matches!(op, UnOp::Not) && (matches!(ty, Ty::Bool) || ty.is_integer()) {
                    let operand_expr = self.resolve(*operand, ty);
                    let result = if matches!(ty, Ty::Bool) {
                        operand_expr.not()
                    } else {
                        operand_expr.bvnot()
                    };
                    self.bind_first_result(node, result);
                    return false;
                }
                // Integer negation is likewise TOTAL over the two's-complement
                // carrier (`bvneg`) and must be BOUND: the previous
                // fresh-symbolic fall-through paired a HAVOCKED result with an
                // UNCONDITIONALLY REACHABLE error rule, so every function
                // containing `-x` had a vacuously satisfiable transport CHC —
                // an admission failure masquerading as a refutation. Bind the
                // wrapped value and carry the PRECISE trap obligation instead,
                // mirroring the direct-call summary interpreter's `Neg` arm:
                // signed negation traps exactly at `INT_MIN`
                // (`bvneg_no_overflow`), a defensive unsigned negation traps
                // unless the operand is zero, and a `Wrapping`-annotated node
                // carries no obligation at all (wrap-around is defined).
                if matches!(op, UnOp::Neg) && ty.is_integer() {
                    let operand_expr = normalize_expr_to_ty(&self.resolve(*operand, ty), ty);
                    if !node.proofs.contains(&ProofAnnotation::Wrapping) {
                        let no_overflow = if ty.is_signed() {
                            self.options
                                .check_signed_overflow
                                .then(|| operand_expr.clone().bvneg_no_overflow())
                        } else {
                            self.options.check_unsigned_overflow.then(|| {
                                let width =
                                    operand_expr.sort().bitvec_width().unwrap_or(HOST_POINTER_BITS);
                                operand_expr.clone().eq(Expr::bitvec_const(0, width))
                            })
                        };
                        if let Some(no_overflow) = no_overflow {
                            self.add_error_rule(from, path_constraints, no_overflow.not());
                        }
                    }
                    self.bind_first_result(node, operand_expr.bvneg());
                    return false;
                }
                let result = self.fresh_symbolic("unsupported_result", ty);
                self.bind_first_result(node, result);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    unsupported_value_reason(&node.inst),
                    from,
                    path_constraints,
                );
                false
            }
            Inst::InsertElement { ty: dst_ty, .. }
            | Inst::FCmp { ty: dst_ty, .. }
            | Inst::LoadSlot { ty: dst_ty, .. } => {
                let result_ty =
                    if matches!(&node.inst, Inst::FCmp { .. }) { &Ty::Bool } else { dst_ty };
                let result = self.fresh_symbolic("unsupported_result", result_ty);
                self.bind_first_result(node, result);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    unsupported_value_reason(&node.inst),
                    from,
                    path_constraints,
                );
                false
            }
            // CheckedBinaryOp: (wrapped_result, overflow_flag). The result is the
            // two's-complement wrapped op; the flag is the negation of the
            // no-overflow predicate, so the following `Assert{Overflow}`
            // obligation referencing this flag becomes provable under the
            // inductive CHC encoding instead of failing closed.
            Inst::Overflow { op, ty, lhs, rhs } => {
                let binop = overflow_op_to_binop(*op);
                let lhs_expr = self.resolve(*lhs, ty);
                let rhs_expr = self.resolve(*rhs, ty);
                let result_val = self.eval_binop(binop, ty, &lhs_expr, &rhs_expr);
                let no_overflow = integer_binop_no_overflow_condition(
                    binop,
                    ty,
                    &lhs_expr,
                    &rhs_expr,
                    self.options,
                );
                let mut results = node.results.iter();
                if let Some(result) = results.next() {
                    self.values.insert(*result, result_val);
                }
                if let Some(result) = results.next() {
                    let flag = match &no_overflow {
                        Some(nov) => nov.clone().not(),
                        None => self.fresh_symbolic("ovf_flag", &Ty::Bool),
                    };
                    self.values.insert(*result, flag);
                }
                if no_overflow.is_none() {
                    // Could not give the overflow flag real semantics
                    // (non-integer operand or overflow checks disabled).
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::OverflowIntrinsic,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::AtomicRMW { ty, .. } | Inst::CmpXchg { ty, .. } => {
                let result_val = self.fresh_symbolic("atomic_result", ty);
                self.bind_first_result(node, result_val);
                if let Some(success) = node.results.get(1) {
                    let success_expr = self.fresh_symbolic("atomic_success", &Ty::Bool);
                    self.values.insert(*success, success_expr);
                }
                let reason = if matches!(&node.inst, Inst::CmpXchg { .. }) {
                    TrustIrChcUnsupportedReason::CompareExchange
                } else {
                    TrustIrChcUnsupportedReason::AtomicReadModifyWrite
                };
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    reason,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                // A `&`/`&mut` borrow of a place is a transparent pointer to that
                // place: bind the result to the SAME pointer, so a later load/store
                // through the borrow hits the same stack cell (the cell model
                // already tracks mutation-through-reference). Borrow PERMISSION
                // (aliasing/uniqueness) is the borrow checker's job, already
                // discharged at compile time, and is irrelevant to the L0 safety
                // obligations (panic/overflow/bounds/unreachable) the CHC proves —
                // so this is NOT an unsupported construct. Marking it unsupported
                // previously poisoned every function that takes the address of a
                // local (e.g. `&mut iter` in a `for` loop's `next()`).
                let result = self.resolve(*ptr, &Ty::Ptr);
                self.bind_first_result(node, result);
                if let Some(parts) = self.ptr_parts.get(ptr).cloned() {
                    if let Some(result_id) = node.results.first() {
                        self.ptr_parts.insert(*result_id, parts);
                    }
                }
                // A borrow is a transparent alias, so it inherits the referent's
                // interior-pointer provenance verbatim. Without this, `*(&mut local)`
                // and `*(&mut local.field)` lose their base and the write is dropped.
                if let Some(provenance) = self.ptr_provenance.get(ptr).cloned()
                    && let Some(result_id) = node.results.first()
                {
                    self.ptr_provenance.insert(*result_id, provenance);
                }
                false
            }
            Inst::IsUnique { .. } => {
                let result = self.fresh_symbolic("is_unique_result", &Ty::Bool);
                self.bind_first_result(node, result);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::ReferenceCountUniqueness,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::OpenFrame { .. } | Inst::BindSlot { .. } => {
                let result = self.fresh_symbolic("binding_frame", &Ty::Ptr);
                self.bind_first_result(node, result);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::BindingFrame,
                    from,
                    path_constraints,
                );
                false
            }
            // Structural element-wise sequence maps: no precise CHC encoding of
            // whole-sequence transformation yet — bind the result symbolically
            // and fail closed.
            Inst::SeqMapAddK { ty, .. } | Inst::SeqMapNot { ty, .. } | Inst::SeqMap { ty, .. } => {
                let result = self.fresh_symbolic("seq_map", ty);
                self.bind_first_result(node, result);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::SequenceMap,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::CallIndirect { .. }
            | Inst::Fence { .. }
            | Inst::EndBorrow { .. }
            | Inst::Retain { .. }
            | Inst::Release { .. }
            | Inst::Dealloc { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::Invoke { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            | Inst::DialectOp(_) => {
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    unsupported_unit_reason(&node.inst),
                    from,
                    path_constraints,
                );
                node.inst.is_terminator()
            }
        }
    }

    fn translate_alloca(&mut self, ty: &Ty, count: &Option<ValueId>, node: &InstrNode) {
        let ptr = self.fresh_symbolic("alloca_ptr", &Ty::Ptr);
        self.bind_first_result(node, ptr);

        let Some(result) = node.results.first().copied() else {
            return;
        };
        // Record the alloca result as owned stack memory so a later store/load
        // through it is a SAFE access even when the value cannot be precisely
        // modeled below (a non-scalar struct gets no `stack_cell`). This is what
        // lets the opaque iterator-adapter structs (`Rev<Iter>`, …) — stored to a
        // stack slot to take the `&mut` for `next()` — not fail closed.
        self.stack_ptrs.insert(result);
        // Root of the interior-pointer provenance chain: the alloca points at
        // itself, at the empty lane path (the whole cell).
        self.ptr_provenance.insert(result, PtrProvenance { base: result, lanes: Some(Vec::new()) });
        if count.is_some() {
            return;
        }

        let Some(value) = self.fresh_stack_cell_value(ty) else {
            return;
        };
        self.stack_cells.insert(result, StackCell { ty: ty.clone(), value });
    }

    fn translate_stack_load(&mut self, ty: &Ty, ptr: ValueId, node: &InstrNode) -> bool {
        let Some(cell) = self.stack_cells.get(&ptr).cloned() else {
            return false;
        };
        if cell.ty != *ty {
            return false;
        }

        match cell.value {
            ValueBinding::Scalar(expr) => self.bind_first_result(node, expr),
            ValueBinding::Aggregate(aggregate) => self.bind_aggregate_result(node, aggregate, ty),
        }
        true
    }

    fn translate_stack_store(&mut self, ty: &Ty, ptr: ValueId, value: ValueId) -> bool {
        let Some(cell_ty) = self.stack_cells.get(&ptr).map(|cell| cell.ty.clone()) else {
            return false;
        };
        if cell_ty != *ty {
            return false;
        }

        let value_binding = if self.aggregate_field_tys(ty).is_some() {
            let Some(aggregate) = self.resolve_aggregate(value, ty) else {
                return false;
            };
            ValueBinding::Aggregate(aggregate)
        } else if is_precise_stack_scalar_ty(ty) {
            ValueBinding::Scalar(self.resolve(value, ty))
        } else {
            return false;
        };
        let Some(cell) = self.stack_cells.get_mut(&ptr) else {
            return false;
        };
        cell.value = value_binding;
        true
    }

    /// The constant field/element lane a `GEP` index denotes, or `None` when the
    /// index is symbolic (or too large to be a lane).
    fn constant_lane_index(&self, index: ValueId) -> Option<usize> {
        match self.values.get(&index)?.value() {
            ay_bindings::ExprValue::BitVecConst { value, .. } => {
                value.to_string().parse::<usize>().ok()
            }
            _ => None,
        }
    }

    /// Extend an exact aggregate-lane path by one TrustIR GEP step.
    ///
    /// TrustIR GEP is byte arithmetic with one repeated scale, not LLVM-style
    /// structural field walking. Re-walk the retained path defensively and require
    /// exact layout evidence at every step; otherwise the caller records an unknown
    /// offset and a later store havocs the whole cell.
    fn extend_exact_gep_lanes(
        &self,
        base: ValueId,
        mut lanes: Vec<(usize, Ty)>,
        field: usize,
        pointee_ty: &Ty,
    ) -> Option<Vec<(usize, Ty)>> {
        let mut lane_ty = self.stack_cells.get(&base)?.ty.clone();
        for (prior_field, prior_pointee_ty) in &lanes {
            lane_ty = self.exact_gep_lane_ty(&lane_ty, *prior_field, prior_pointee_ty)?;
        }
        self.exact_gep_lane_ty(&lane_ty, field, pointee_ty)?;
        lanes.push((field, pointee_ty.clone()));
        Some(lanes)
    }

    /// Aggregate lane selected exactly by one single-scale GEP step.
    ///
    /// Struct precision requires complete declared byte layout: every field must
    /// have an offset and a layout, every range must fit the struct, no starts may
    /// alias, and no byte ranges may overlap. The selected field's declared start
    /// must equal `field * size_of(pointee_ty)`. Missing metadata is not evidence
    /// and therefore returns `None`. Arrays carry their own exact element stride
    /// and remain precise when it agrees with the pointee layout.
    fn exact_gep_lane_ty(&self, aggregate_ty: &Ty, field: usize, pointee_ty: &Ty) -> Option<Ty> {
        let field_tys = self.aggregate_field_tys(aggregate_ty)?;
        let field_ty = field_tys.get(field)?;
        if field_ty != pointee_ty {
            return None;
        }

        let pointee_layout = self.module.ty_layout_shape(pointee_ty).ok()?;
        if pointee_layout.size_bits == 0 || pointee_layout.size_bits % 8 != 0 {
            return None;
        }
        let gep_offset_bits = pointee_layout.size_bits.checked_mul(u64::try_from(field).ok()?)?;

        match aggregate_ty {
            Ty::Struct(id) => {
                let aggregate_layout = self.module.ty_layout_shape(aggregate_ty).ok()?;
                let definition =
                    self.module.structs.iter().find(|definition| definition.id == *id)?;
                if definition.fields.len() != field_tys.len() {
                    return None;
                }

                let mut ranges = Vec::with_capacity(definition.fields.len());
                for (index, definition_field) in definition.fields.iter().enumerate() {
                    if definition_field.ty != field_tys[index] {
                        return None;
                    }
                    let start = definition_field.offset?.checked_mul(8)?;
                    let size = self.module.ty_layout_shape(&definition_field.ty).ok()?.size_bits;
                    let end = start.checked_add(size)?;
                    if end > aggregate_layout.size_bits {
                        return None;
                    }
                    ranges.push((start, end));
                }

                // The logical field identity must be unique at the selected byte
                // address and the aggregate binding must not hide byte aliases.
                for left in 0..ranges.len() {
                    for right in (left + 1)..ranges.len() {
                        let (left_start, left_end) = ranges[left];
                        let (right_start, right_end) = ranges[right];
                        if left_start == right_start
                            || (left_start < right_end && right_start < left_end)
                        {
                            return None;
                        }
                    }
                }

                if ranges[field].0 != gep_offset_bits {
                    return None;
                }
                Some(field_ty.clone())
            }
            Ty::Array(element, len) => {
                if u64::try_from(field).ok()? >= *len {
                    return None;
                }
                let element_ty = self.module.types.get(element.as_usize())?;
                if element_ty != pointee_ty {
                    return None;
                }
                let aggregate_layout = self.module.ty_layout_shape(aggregate_ty).ok()?;
                let trust_ir::TyLayoutKind::Array { stride_bits, .. } = aggregate_layout.kind
                else {
                    return None;
                };
                if stride_bits != pointee_layout.size_bits {
                    return None;
                }
                Some(field_ty.clone())
            }
            _ => None,
        }
    }

    /// Model a `Store` that `translate_stack_store` could not apply directly.
    ///
    /// SOUNDNESS CONTRACT — this is the fix for the fail-open that let a write
    /// through `&mut local.field` be silently dropped while the alloca's precise
    /// `stack_cell` survived, so the next `Load` of that alloca returned the
    /// PRE-store aggregate and any obligation over it was discharged against a
    /// stale value (a false PROVE, emitted with no diagnostic at all).
    ///
    /// Every reachable path either writes the cell exactly, resets to fresh
    /// unconstrained every cell the store could possibly target, or establishes
    /// that no tracked cell is reachable from the store's pointer. There is no
    /// path that leaves a tracked cell holding a pre-store value.
    fn model_indirect_store(
        &mut self,
        volatile: bool,
        ty: &Ty,
        ptr: ValueId,
        value: ValueId,
    ) -> IndirectStoreOutcome {
        // A volatile store's written value is not the modeled one, so it can only
        // ever havoc; otherwise try the exact field lane first.
        if !volatile
            && let Some(provenance) = self.ptr_provenance.get(&ptr).cloned()
            && let Some(lanes) = provenance.lanes
            && self.stack_cells.contains_key(&provenance.base)
            && self.store_cell_lane(provenance.base, &lanes, ty, value)
        {
            return IndirectStoreOutcome::Exact;
        }
        self.invalidate_store_targets(ptr)
    }

    /// Reset every precise cell a store through `ptr` could target. Used when the
    /// written value cannot be placed exactly — an unknown offset, a mismatched
    /// type, a volatile or atomic store — and as the fallback of
    /// `model_indirect_store`.
    fn invalidate_store_targets(&mut self, ptr: ValueId) -> IndirectStoreOutcome {
        if let Some(provenance) = self.ptr_provenance.get(&ptr).cloned() {
            // The referent is known exactly, so nothing else can be affected.
            if !self.stack_cells.contains_key(&provenance.base) {
                // Stack memory carrying no precise cell (an opaque aggregate):
                // there is no tracked value to go stale.
                return IndirectStoreOutcome::NoTrackedTarget;
            }
            self.invalidate_stack_cell(provenance.base);
            return IndirectStoreOutcome::Invalidated;
        }

        // The referent is unknown, so the store may alias any cell whose interior
        // address escaped this translator's model. Reset exactly those. When
        // nothing escaped, no tracked cell is reachable and leaving the write
        // unmodeled is sound.
        let targets: Vec<ValueId> = self
            .escaped_cell_bases
            .iter()
            .copied()
            .filter(|base| self.stack_cells.contains_key(base))
            .collect();
        if targets.is_empty() {
            return IndirectStoreOutcome::NoTrackedTarget;
        }
        for base in targets {
            self.invalidate_stack_cell(base);
        }
        IndirectStoreOutcome::Invalidated
    }

    /// Write `value` into the constant field lane `lanes` of `base`'s cell.
    ///
    /// The lane mapping is revalidated here. It is cross-checked three ways, and
    /// any disagreement returns `false` so the caller falls back to havoc:
    ///   1. every GEP step must carry exact declared layout evidence making
    ///      TrustIR's byte stride coincide with a unique, non-overlapping aggregate
    ///      lane (or an exact array element stride);
    ///   2. the cell's type is walked with `aggregate_field_tys` — the SAME table
    ///      `fresh_stack_cell_value` built the binding from and the `Load`/
    ///      `ExtractField` path reads it back through;
    ///   3. the stored type must equal the final lane type, and the binding tree
    ///      must actually have an aggregate node at every step.
    fn store_cell_lane(
        &mut self,
        base: ValueId,
        lanes: &[(usize, Ty)],
        ty: &Ty,
        value: ValueId,
    ) -> bool {
        let Some(cell_ty) = self.stack_cells.get(&base).map(|cell| cell.ty.clone()) else {
            return false;
        };

        let mut lane_ty = cell_ty;
        for (field, pointee_ty) in lanes {
            let Some(next) = self.exact_gep_lane_ty(&lane_ty, *field, pointee_ty) else {
                return false;
            };
            lane_ty = next;
        }
        if lane_ty != *ty {
            return false;
        }

        let new_binding = if self.aggregate_field_tys(ty).is_some() {
            let Some(aggregate) = self.resolve_aggregate(value, ty) else {
                return false;
            };
            ValueBinding::Aggregate(aggregate)
        } else if is_precise_stack_scalar_ty(ty) {
            ValueBinding::Scalar(self.resolve(value, ty))
        } else {
            return false;
        };

        let Some(cell) = self.stack_cells.get_mut(&base) else {
            return false;
        };
        let mut slot = &mut cell.value;
        for (field, _) in lanes {
            let ValueBinding::Aggregate(aggregate) = slot else {
                return false;
            };
            let Some(next) = aggregate.fields.get_mut(*field) else {
                return false;
            };
            slot = next;
        }
        *slot = new_binding;
        true
    }

    /// Reset a cell to a fresh unconstrained value (havoc). Keeps the cell PRESENT
    /// with the same shape when possible, because a promoted cell's binding is part
    /// of its block relation's signature; only a cell whose type can no longer be
    /// given a fresh binding is dropped (a later `Load` then havocs anyway).
    fn invalidate_stack_cell(&mut self, base: ValueId) {
        let Some(cell_ty) = self.stack_cells.get(&base).map(|cell| cell.ty.clone()) else {
            return;
        };
        match self.fresh_stack_cell_value(&cell_ty) {
            Some(value) => {
                if let Some(cell) = self.stack_cells.get_mut(&base) {
                    cell.value = value;
                }
            }
            None => {
                self.stack_cells.remove(&base);
            }
        }
    }

    /// Does a store through `ptr` still have a precise cell it could have changed?
    ///
    /// This is the enforcement half of the invariant "no store is silently dropped
    /// while a precise cell for its base survives": `model_indirect_store` is
    /// supposed to make this false, and the `Store` arm fails CLOSED whenever it is
    /// still true. A future edit that reintroduces a drop therefore produces a loud
    /// `MemoryAccessWithoutPreciseModel`, never a quiet stale read.
    fn store_target_cell_survives(&self, ptr: ValueId) -> bool {
        match self.ptr_provenance.get(&ptr) {
            Some(provenance) => self.stack_cells.contains_key(&provenance.base),
            None => self.escaped_cell_bases.iter().any(|base| self.stack_cells.contains_key(base)),
        }
    }

    /// Mark the base of every interior pointer this instruction uses in a position
    /// the cell model does not follow. Such a pointer may resurface as an unknown
    /// store target later in the block, so its cell must then be invalidated.
    ///
    /// Mirrors `compute_promotable_cells`' alias rule: the `ptr` of a memory op, the
    /// base of a `GEP`, and the referent of a borrow are TRACKED positions (their
    /// provenance is propagated); a `Store`'s *value*, a call argument, a `Select`
    /// operand, a block argument, and every use inside an instruction whose reads
    /// are not statically enumerable are escapes.
    fn record_interior_pointer_escapes(&mut self, inst: &Inst) {
        if self.ptr_provenance.is_empty() {
            return;
        }
        let mut uses = Vec::new();
        if collect_inst_value_uses(inst, &mut uses) {
            // Reads not statically enumerable: assume every interior pointer escaped.
            let all: Vec<ValueId> = self.ptr_provenance.values().map(|p| p.base).collect();
            self.escaped_cell_bases.extend(all);
            return;
        }
        // Selected POSITIONALLY, not by membership: `store p, p` must still count
        // the value position as an escape even though the same id is the tracked
        // pointer operand.
        let escaping = match inst {
            // The sole operand is the tracked pointer.
            Inst::Load { .. }
            | Inst::AtomicLoad { .. }
            | Inst::Borrow { .. }
            | Inst::BorrowMut { .. }
            | Inst::EndBorrow { .. }
            | Inst::Dealloc { .. } => Vec::new(),
            // `ptr` is tracked; the written VALUE puts a pointer into memory.
            Inst::Store { value, .. } | Inst::AtomicStore { value, .. } => vec![*value],
            // `base` is tracked; an index is an ordinary operand.
            Inst::GEP { indices, .. } => indices.clone(),
            _ => uses,
        };
        for used in escaping {
            if let Some(provenance) = self.ptr_provenance.get(&used) {
                self.escaped_cell_bases.insert(provenance.base);
            }
        }
    }

    fn fresh_stack_cell_value(&mut self, ty: &Ty) -> Option<ValueBinding> {
        if let Some(field_tys) = self.aggregate_field_tys(ty) {
            let mut fields = Vec::with_capacity(field_tys.len());
            for (field_index, field_ty) in field_tys.iter().enumerate() {
                // Trust (#46): recurse for nested-aggregate fields.
                fields.push(
                    self.resolve_field_binding(
                        &format!("stack_init_field{field_index}"),
                        field_ty,
                    )?,
                );
            }
            return Some(ValueBinding::Aggregate(AggregateValue { fields }));
        }

        is_precise_stack_scalar_ty(ty)
            .then(|| ValueBinding::Scalar(self.fresh_symbolic("stack_init", ty)))
    }

    fn translate_switch(
        &mut self,
        value: ValueId,
        default: BlockId,
        default_args: &[ValueId],
        cases: &[SwitchCase],
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) {
        let selector = self.resolve_switch_selector(value);
        let mut case_guards = Vec::with_capacity(cases.len());

        for case in cases {
            let Some(case_expr) = switch_case_expr(&case.value, &selector) else {
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::Switch,
                    from,
                    path_constraints,
                );
                return;
            };
            let guard = selector.clone().eq(case_expr);
            case_guards.push(guard.clone());
            self.add_transition_rule(
                case.target,
                &case.args,
                Some(guard),
                block,
                instruction_index,
                node,
                from,
                path_constraints,
            );
        }

        let default_guard = match case_guards.len() {
            0 => None,
            1 => Some(case_guards[0].clone().not()),
            _ => Some(Expr::and_many(case_guards.into_iter().map(Expr::not).collect())),
        };
        self.add_transition_rule(
            default,
            default_args,
            default_guard,
            block,
            instruction_index,
            node,
            from,
            path_constraints,
        );
    }

    fn translate_integer_binop(
        &mut self,
        op: BinOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) {
        let lhs_expr = normalize_expr_to_ty(&self.resolve(lhs, ty), ty);
        let rhs_expr = normalize_expr_to_ty(&self.resolve(rhs, ty), ty);

        // Trust Gap 3: a `Wrapping`-tagged op (e.g. `wrapping_add`) is intentionally
        // modular — wrap-around is defined, not UB — so it carries no no-overflow
        // obligation. (Div-by-zero still applies; wrapping never affects it.)
        if !node.proofs.contains(&ProofAnnotation::Wrapping) {
            if let Some(no_overflow) =
                integer_binop_no_overflow_condition(op, ty, &lhs_expr, &rhs_expr, self.options)
            {
                self.add_error_rule(from, path_constraints, no_overflow.not());
            }
        }

        if let Some(is_zero) = integer_binop_div_by_zero_condition(op, ty, &rhs_expr, self.options)
        {
            self.add_error_rule(from, path_constraints, is_zero);
        }

        let result = self.eval_binop(op, ty, &lhs_expr, &rhs_expr);
        self.bind_first_result(node, result);
    }

    fn translate_return(
        &mut self,
        values: &[ValueId],
        node: &InstrNode,
        block: BlockId,
        instruction_index: usize,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) {
        if let Some(func_ty) = self.module.func_types.get(self.func.ty.as_usize())
            && values.len() != func_ty.returns.len()
        {
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::ReturnArityMismatch,
                from,
                path_constraints,
            );
            return;
        }

        let ret_exprs: Vec<Expr> =
            if let Some(func_ty) = self.module.func_types.get(self.func.ty.as_usize()) {
                values
                    .iter()
                    .zip(func_ty.returns.iter())
                    .map(|(value, ty)| self.resolve(*value, ty))
                    .collect()
            } else {
                values.iter().map(|value| self.resolve(*value, &Ty::I64)).collect()
            };

        for proof in &self.func.proofs {
            if let ProofAnnotation::BoundedOutput { lo, hi } = proof {
                for (i, ret_expr) in ret_exprs.iter().enumerate() {
                    let ret_ty = self
                        .module
                        .func_types
                        .get(self.func.ty.as_usize())
                        .and_then(|func_ty| func_ty.returns.get(i));
                    match ret_ty
                        .and_then(|ret_ty| bounded_output_out_of_range(ret_ty, ret_expr, *lo, *hi))
                    {
                        Some(out_of_range) => {
                            self.add_error_rule(from, path_constraints, out_of_range);
                        }
                        // No exact integer encoding for the annotated bounds
                        // against this return type (float-typed return,
                        // fractional/out-of-range f64 bound, untyped return).
                        // The old encoding compared raw IEEE bits with signed
                        // bitvector order (wrong semantics — false proofs or
                        // false refutations) or silently skipped the
                        // obligation. Fail closed instead.
                        None => {
                            self.add_unsupported_error(
                                block,
                                instruction_index,
                                node,
                                TrustIrChcUnsupportedReason::UnsupportedBoundedOutput,
                                from,
                                path_constraints,
                            );
                        }
                    }
                }
            }
        }

        if node.results.is_empty() {
            return;
        }
        self.add_unsupported_error(
            block,
            instruction_index,
            node,
            TrustIrChcUnsupportedReason::ReturnInstructionWithResults,
            from,
            path_constraints,
        );
    }

    fn translate_call(
        &mut self,
        callee: FuncId,
        args: &[ValueId],
        node: &InstrNode,
        block: BlockId,
        instruction_index: usize,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) {
        let Some(callee_func) = self.module.function_by_id(callee).cloned() else {
            let result = self.fresh_symbolic("unknown_call_result", &Ty::I64);
            self.bind_first_result(node, result);
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::UnknownDirectCall,
                from,
                path_constraints,
            );
            return;
        };

        let callee_func_ty = self.module.func_types.get(callee_func.ty.as_usize()).cloned();
        let callee_return_tys = callee_func_ty.as_ref().map(|func_ty| func_ty.returns.as_slice());

        if self.is_recursive_direct_call(callee, &callee_func) {
            self.bind_symbolic_call_results(&callee_func.name, callee_return_tys, node);
            for (i, arg) in args.iter().enumerate() {
                let arg_ty = callee_func_ty
                    .as_ref()
                    .and_then(|func_ty| func_ty.params.get(i))
                    .unwrap_or(&Ty::I64);
                let _ = self.resolve(*arg, arg_ty);
            }
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::RecursiveDirectCall,
                from,
                path_constraints,
            );
            return;
        }

        // A WRAPPING arithmetic intrinsic (`u64::wrapping_add`, `i32::wrapping_sub`,
        // `wrapping_mul`, …) reaches the trust-ir as a direct `Call` to a numeric
        // method whose body the bounded summary interpreter does not model, so it
        // otherwise falls through to the fresh-symbolic havoc below — leaving the
        // result unbound and HAVOCKING any loop-carried cell it updates (e.g.
        // `count = count.wrapping_add(1)` left `count'` free, so the count-parity loop
        // invariant was unprovable). Model it PRECISELY as the corresponding MODULAR
        // bitvector op (`bvadd`/`bvsub`/`bvmul`): wrap-around is DEFINED, so there is
        // NO overflow obligation — mirroring `translate_integer_binop`'s `Wrapping`
        // path and the compiler MIR path's `inline_wrapping_arith_expr`, which likewise
        // resolve these directly to BV operations. Recognized by the callee's method
        // name plus an integer-typed 2-in / 1-out signature of a single common width
        // (the strong signal it is the numeric intrinsic, not an unrelated same-named
        // user function of a different shape).
        if let Some(op) = wrapping_arith_binop(&callee_func.name)
            && args.len() == 2
            && let Some(func_ty) = &callee_func_ty
            && func_ty.params.len() == 2
            && func_ty.returns.len() == 1
        {
            let lhs_ty = func_ty.params[0].clone();
            let rhs_ty = func_ty.params[1].clone();
            let ret_ty = func_ty.returns[0].clone();
            let width = ret_ty.bit_width_with(HOST_POINTER_BITS);
            if ret_ty.is_integer()
                && lhs_ty.is_integer()
                && rhs_ty.is_integer()
                && width.is_some()
                && lhs_ty.bit_width_with(HOST_POINTER_BITS) == width
                && rhs_ty.bit_width_with(HOST_POINTER_BITS) == width
            {
                let lhs = self.resolve(args[0], &lhs_ty);
                let rhs = self.resolve(args[1], &rhs_ty);
                let result = self.eval_binop(op, &ret_ty, &lhs, &rhs);
                self.bind_first_result(node, result);
                return;
            }
        }

        if let Some(summary) = self.try_direct_call_summary(&callee_func, args) {
            for condition in summary.error_conditions {
                self.add_error_rule(from, path_constraints, condition);
            }
            if let Some(callee_func_ty) = &callee_func_ty
                && summary.returns.len() == node.results.len()
                && summary.returns.len() == callee_func_ty.returns.len()
            {
                for ((result, ty), binding) in
                    node.results.iter().zip(callee_func_ty.returns.iter()).zip(summary.returns)
                {
                    self.bind_call_result(*result, binding, ty);
                }
                return;
            }
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::MalformedControlFlow,
                from,
                path_constraints,
            );
            return;
        }

        let ret_ty = self
            .module
            .func_types
            .get(callee_func.ty.as_usize())
            .and_then(|func_ty| func_ty.returns.first())
            .unwrap_or(&Ty::I64);
        let result =
            self.fresh_symbolic(&format!("call_{}", sanitize_name(&callee_func.name)), ret_ty);
        self.bind_first_result(node, result);

        for (i, arg) in args.iter().enumerate() {
            let arg_ty = callee_func_ty
                .as_ref()
                .and_then(|func_ty| func_ty.params.get(i))
                .unwrap_or(&Ty::I64);
            let _ = self.resolve(*arg, arg_ty);
        }
        self.add_unsupported_error(
            block,
            instruction_index,
            node,
            TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary,
            from,
            path_constraints,
        );
    }

    fn is_recursive_direct_call(&self, callee: FuncId, callee_func: &Function) -> bool {
        callee == self.func.id
            || callee_func.blocks.iter().flat_map(|block| &block.body).any(
                |node| matches!(&node.inst, Inst::Call { callee, .. } if *callee == self.func.id),
            )
    }

    fn try_direct_call_summary(
        &mut self,
        callee_func: &Function,
        args: &[ValueId],
    ) -> Option<DirectCallSummary> {
        let callee_func_ty = self.module.func_types.get(callee_func.ty.as_usize())?.clone();
        if callee_func_ty.params.len() != args.len()
            || !callee_func_ty.params.iter().all(|ty| self.is_call_summary_value_ty(ty))
            || !callee_func_ty.returns.iter().all(|ty| self.is_call_summary_value_ty(ty))
        {
            return None;
        }

        let entry_block = callee_func.block(callee_func.entry)?;
        if entry_block.params.len() != args.len() {
            return None;
        }

        let mut locals = BTreeMap::new();
        for ((param, param_ty), arg) in entry_block.params.iter().zip(args.iter()) {
            if !self.is_call_summary_value_ty(param_ty) {
                return None;
            }
            locals.insert(*param, self.resolve_call_summary_argument(*arg, param_ty)?);
        }

        let mut pending = vec![CallSummaryState {
            block: callee_func.entry,
            locals,
            path_conditions: Vec::new(),
            visited_blocks: Vec::new(),
        }];
        let mut returns = Vec::new();
        let mut error_conditions = Vec::new();
        // Rung-2 recursion fixpoint: set when the callee calls ITSELF. A self-recursive callee's
        // single-invocation summary proves panic-freedom for ALL recursion depths ONLY if it
        // carries no per-level obligation (checked after the loop) — see the `Inst::Call` arm.
        let mut self_recursion_seen = false;

        let mut processed_states = 0;
        while let Some(mut state) = pending.pop() {
            processed_states += 1;
            if processed_states > DIRECT_CALL_SUMMARY_MAX_STATES
                || state.visited_blocks.contains(&state.block)
            {
                return None;
            }
            state.visited_blocks.push(state.block);

            let block = callee_func.block(state.block)?;
            let mut terminated = false;
            for node in &block.body {
                match &node.inst {
                    Inst::Const { ty, value } if is_call_summary_scalar_ty(ty) => {
                        // A constant without an exact bit-level encoding
                        // declines the whole summary (fail closed), like every
                        // other unmodeled construct in this interpreter.
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(const_to_expr(ty, value)?),
                        )?;
                    }
                    Inst::Copy { ty, operand } if self.is_call_summary_value_ty(ty) => {
                        let binding = call_summary_value(&state.locals, *operand, ty)?;
                        bind_call_summary_result(&mut state.locals, node, binding)?;
                    }
                    Inst::BinOp { op, ty, lhs, rhs } if ty.is_integer() => {
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs)?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs)?;
                        // Trust Gap 3: `Wrapping`-tagged ops carry no overflow obligation.
                        if !node.proofs.contains(&ProofAnnotation::Wrapping) {
                            if let Some(no_overflow) = integer_binop_no_overflow_condition(
                                *op,
                                ty,
                                &lhs_expr,
                                &rhs_expr,
                                self.options,
                            ) {
                                error_conditions.push(call_summary_guarded_condition(
                                    &state.path_conditions,
                                    no_overflow.not(),
                                ));
                            }
                        }
                        if let Some(is_zero) =
                            integer_binop_div_by_zero_condition(*op, ty, &rhs_expr, self.options)
                        {
                            error_conditions.push(call_summary_guarded_condition(
                                &state.path_conditions,
                                is_zero,
                            ));
                        }
                        let result = self.eval_binop(*op, ty, &lhs_expr, &rhs_expr);
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(result),
                        )?;
                    }
                    Inst::BinOp { op, ty, lhs, rhs } if matches!(ty, Ty::Bool) => {
                        // Logical And/Or/Xor on `Bool` carry no overflow/div-by-zero
                        // obligation; `eval_binop` models the connective precisely (as
                        // the main translate does), so a guard conjunction such as
                        // `x == i32::MIN && y == -1` (the signed-division overflow guard)
                        // threads through the summary instead of falling past the
                        // integer-only arm above to `_ => return None`.
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs)?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs)?;
                        let result = self.eval_binop(*op, ty, &lhs_expr, &rhs_expr);
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(result),
                        )?;
                    }
                    Inst::ICmp { op, ty, lhs, rhs } => {
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs)?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs)?;
                        let result = self.eval_icmp(*op, ty, &lhs_expr, &rhs_expr)?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(result),
                        )?;
                    }
                    Inst::Cast { op, src_ty, dst_ty, operand }
                        if is_call_summary_scalar_ty(src_ty)
                            && is_call_summary_scalar_ty(dst_ty) =>
                    {
                        let operand = call_summary_scalar(&state.locals, *operand)?;
                        let result = eval_cast_expr(*op, src_ty, dst_ty, operand)?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(result),
                        )?;
                    }
                    Inst::Select { ty, cond, then_val, else_val }
                        if is_call_summary_scalar_ty(ty) =>
                    {
                        let cond_expr = call_summary_bool(&state.locals, *cond)?;
                        let then_expr = call_summary_scalar(&state.locals, *then_val)?;
                        let else_expr = call_summary_scalar(&state.locals, *else_val)?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(Expr::ite(cond_expr, then_expr, else_expr)),
                        )?;
                    }
                    Inst::NullPtr => {
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(Expr::bitvec_const(0u64, 64)),
                        )?;
                    }
                    Inst::Undef { ty } if self.is_call_summary_value_ty(ty) => {
                        let result = self.fresh_call_summary_value("call_undef", ty)?;
                        bind_call_summary_result(&mut state.locals, node, result)?;
                    }
                    Inst::DialectOp(op) if node.results.len() == 1 && is_thread_local_addr(op) => {
                        let result =
                            self.fresh_call_summary_value("call_thread_local_addr", &Ty::Ptr)?;
                        bind_call_summary_result(&mut state.locals, node, result)?;
                    }
                    Inst::ExtractField { ty, aggregate, field }
                        if is_call_summary_scalar_ty(ty) =>
                    {
                        // Trust (#46): this arm is guarded scalar-result; the call-
                        // summary path stays scalar-only, so a nested-aggregate field
                        // here bails (fail closed).
                        let ValueBinding::Scalar(result) =
                            call_summary_aggregate(&state.locals, *aggregate)?
                                .fields
                                .get(*field as usize)?
                                .clone()
                        else {
                            return None;
                        };
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(result),
                        )?;
                    }
                    Inst::ExtractElement { ty, .. } if is_call_summary_scalar_ty(ty) => {
                        // Array/vector element read: model the element as a fresh
                        // unconstrained value (sound — an unknown read value cannot
                        // make a dependent obligation falsely provable, and bounds are
                        // carried by the separately-emitted Assert), mirroring
                        // translate_block's ExtractElement arm. Scalar element results
                        // only; an aggregate-element read falls through to fail closed.
                        let result = self.fresh_call_summary_value("call_element_read", ty)?;
                        bind_call_summary_result(&mut state.locals, node, result)?;
                    }
                    Inst::InsertField { ty, aggregate, field, value }
                        if self.aggregate_field_tys(ty).is_some() =>
                    {
                        let field_tys = self.aggregate_field_tys(ty)?;
                        let field_index = *field as usize;
                        let value_ty = field_tys.get(field_index)?;
                        if !is_call_summary_scalar_ty(value_ty) {
                            return None;
                        }
                        let mut result = call_summary_aggregate(&state.locals, *aggregate)?;
                        if result.fields.len() != field_tys.len() {
                            return None;
                        }
                        // Trust (#46): guarded scalar value_ty (above) — wrap as Scalar.
                        result.fields[field_index] =
                            ValueBinding::Scalar(call_summary_scalar(&state.locals, *value)?);
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Aggregate(result),
                        )?;
                    }
                    Inst::Assert { cond } => {
                        error_conditions.push(call_summary_guarded_condition(
                            &state.path_conditions,
                            call_summary_bool(&state.locals, *cond)?.not(),
                        ));
                    }
                    Inst::Br { target, args } => {
                        pending.push(self.call_summary_successor_state(
                            callee_func,
                            &state,
                            *target,
                            args,
                            None,
                        )?);
                        terminated = true;
                        break;
                    }
                    Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                        let cond_expr = call_summary_bool(&state.locals, *cond)?;
                        pending.push(self.call_summary_successor_state(
                            callee_func,
                            &state,
                            *else_target,
                            else_args,
                            Some(cond_expr.clone().not()),
                        )?);
                        pending.push(self.call_summary_successor_state(
                            callee_func,
                            &state,
                            *then_target,
                            then_args,
                            Some(cond_expr),
                        )?);
                        terminated = true;
                        break;
                    }
                    Inst::Return { values } => {
                        if values.len() != callee_func_ty.returns.len() {
                            return None;
                        }
                        // Resolve each returned value; if one is NOT in scope on this path
                        // (the trust-ir lowering can leave a shared return block referencing
                        // a value defined only on one predecessor — `signed_min`'s block 9
                        // returns `v45`, defined only on the saturate path), fall back to a
                        // HAVOC value. SOUNDNESS: a return value is never a panic site, so
                        // havocing it only LOSES precision on the call's result (a caller
                        // cannot then rely on a specific value — conservative), and NEVER
                        // masks a panic; the alternative `return None` would conservatively
                        // model the whole call as may-panic and block the caller's proof.
                        let mut resolved = Vec::with_capacity(values.len());
                        for (value, ty) in values.iter().zip(callee_func_ty.returns.iter()) {
                            let binding = match call_summary_value(&state.locals, *value, ty) {
                                Some(binding) => binding,
                                None => self.fresh_call_summary_value("call_ret_havoc", ty)?,
                            };
                            resolved.push(binding);
                        }
                        returns.push(CallSummaryReturn {
                            values: resolved,
                            path_conditions: state.path_conditions.clone(),
                        });
                        terminated = true;
                        break;
                    }
                    // SIGNED integer negation `-x` (e.g. `signed_min`'s
                    // `-(1i128 << (width-1))`). The main translate leaves `Inst::UnOp`
                    // UNSUPPORTED (havoc + error rule); the call-summary interpreter models
                    // it precisely: result = `bvneg(x)`, and the OverflowNeg obligation
                    // (`-x` overflows iff `x == INT_MIN`) is recorded as a guarded error —
                    // redundant if the lowering also emits a separate neg-overflow `Assert`,
                    // sound if it does not (it never masks a real neg overflow; an unguarded
                    // `-(i128::MIN)` stays SAT/refutable). For a guarded operand
                    // (`1 << (width-1)` under `width <= 127`, always `< 2^(w-1)`) it is UNSAT,
                    // so the inlined negation discharges and the caller proves panic-free.
                    // A `Wrapping` negation carries no obligation (matches the `BinOp` arm).
                    Inst::UnOp { op: UnOp::Neg, ty, operand } if ty.is_integer() => {
                        let operand_expr = normalize_expr_to_ty(
                            &call_summary_scalar(&state.locals, *operand)?,
                            ty,
                        );
                        if !node.proofs.contains(&ProofAnnotation::Wrapping) {
                            // Per-signedness exactness (aligned with the main
                            // translator's `Neg` arm): signed negation traps
                            // exactly at `INT_MIN`; a defensive unsigned
                            // negation traps unless the operand is zero — the
                            // signed `bvneg_no_overflow` predicate is
                            // meaningless on an unsigned carrier.
                            let no_overflow = if ty.is_signed() {
                                operand_expr.clone().bvneg_no_overflow()
                            } else {
                                let width =
                                    operand_expr.sort().bitvec_width().unwrap_or(HOST_POINTER_BITS);
                                operand_expr.clone().eq(Expr::bitvec_const(0, width))
                            };
                            error_conditions.push(call_summary_guarded_condition(
                                &state.path_conditions,
                                no_overflow.not(),
                            ));
                        }
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(operand_expr.bvneg()),
                        )?;
                    }
                    // Bitwise / logical NOT (`!x`) is TOTAL and modeled PRECISELY — a
                    // Bool operand negates (`not`), a BitVec operand bit-complements
                    // (`bvnot`), matching the main translate's precise `eval_binop`
                    // handling of the other connectives. Precision here is load-bearing:
                    // `xor_accumulate_parity`'s body lowers `a ^ true` to
                    // `Select(true, !a, a)`, so a HAVOCED `!a` (the old fresh-symbolic
                    // total-unop model) made the summarized result — and every loop cell
                    // it updates — unconstrained, blocking the count-parity loop invariant
                    // (`acc' = !acc` collapsed to a free variable). `not`/`bvnot` never
                    // panic, so NO error condition is pushed. A non-scalar operand (never
                    // produced under the `is_call_summary_scalar_ty` guard) fails closed.
                    Inst::UnOp { op: UnOp::Not, ty, operand } if is_call_summary_scalar_ty(ty) => {
                        let operand_expr = call_summary_scalar(&state.locals, *operand)?;
                        let result = if operand_expr.sort().is_bool() {
                            operand_expr.not()
                        } else if operand_expr.sort().is_bitvec() {
                            operand_expr.bvnot()
                        } else {
                            return None;
                        };
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(result),
                        )?;
                    }
                    // The remaining UNARY ops are TOTAL — population count `CtPop` and the
                    // IEEE float unary ops (`FNeg`/`FAbs`/`FSqrt`/`FFloor`/`FCeil`/`FTrunc`)
                    // — and NEVER panic (no overflow obligation, unlike the signed `Neg`
                    // matched above, which carries the `x == INT_MIN` obligation), but have
                    // no precise scalar model here. Model the result as a fresh-symbolic
                    // value (sound over-approximation: the value is left unconstrained, so a
                    // downstream use stays `unknown`, never falsely proved) and push NO error
                    // condition, so the summary CONTINUES instead of declining the whole
                    // callee. Without this arm a callee using `x.count_ones()` / `f.abs()`
                    // hit the `_ => return None` fail-close and its caller was conservatively
                    // modeled as may-panic (UNKNOWN) — a precision loss with no soundness
                    // justification, since these ops cannot panic.
                    Inst::UnOp {
                        op:
                            UnOp::CtPop
                            | UnOp::FNeg
                            | UnOp::FAbs
                            | UnOp::FSqrt
                            | UnOp::FFloor
                            | UnOp::FCeil
                            | UnOp::FTrunc,
                        ty,
                        operand,
                    } if is_call_summary_scalar_ty(ty) => {
                        // Resolve the operand to confirm it is in scope on this path (a missing
                        // operand means a malformed CFG — decline, like the arms above). The
                        // resolved value is unused: the result is havoc, never panics.
                        let _ = call_summary_scalar(&state.locals, *operand)?;
                        let result = self.fresh_call_summary_value("call_unop_total", ty)?;
                        bind_call_summary_result(&mut state.locals, node, result)?;
                    }
                    // A checked-arithmetic intrinsic (`a.overflowing_sub(b)` etc. — the
                    // lowering of a Rust `CheckedBinaryOp`, INCLUDING i128 negation as
                    // `0 - x`). Mirrors the main translate's `Inst::Overflow` arm: bind
                    // result[0] = the WRAPPED value, result[1] = the overflow FLAG
                    // (`¬no_overflow`). It pushes NO error condition itself — the panic is
                    // the subsequent `Assert(!flag)` (handled above) or the panic block's
                    // `Unreachable` (handled below), guarded by the dominating path. Without
                    // this arm the interpreter bailed on `signed_min`'s `width - 1` (a
                    // `SubOverflow` over `u32`), so its caller (`type_min`) could not be
                    // proved panic-free. Fails closed (`?` on `integer_binop_no_overflow_
                    // condition`) when the op has no integer no-overflow semantics — exactly
                    // the main translate's `OverflowIntrinsic` unsupported path.
                    Inst::Overflow { op, ty, lhs, rhs } if ty.is_integer() => {
                        let binop = overflow_op_to_binop(*op);
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs)?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs)?;
                        let no_overflow = integer_binop_no_overflow_condition(
                            binop,
                            ty,
                            &lhs_expr,
                            &rhs_expr,
                            self.options,
                        )?;
                        let value = self.eval_binop(binop, ty, &lhs_expr, &rhs_expr);
                        let flag = no_overflow.not();
                        let mut results = node.results.iter();
                        if let Some(value_result) = results.next() {
                            state.locals.insert(*value_result, ValueBinding::Scalar(value));
                        }
                        if let Some(flag_result) = results.next() {
                            state.locals.insert(*flag_result, ValueBinding::Scalar(flag));
                        }
                    }
                    // A panic block (the FALSE side of an overflow / bounds / explicit
                    // `panic!` assert) lowers to `Assert(false)` then `Unreachable`. The
                    // preceding `Inst::Assert` (handled above) already pushed the guarded
                    // panic condition; this `Unreachable` is the path's dead end. We also
                    // record "reaching this Unreachable on a feasible path is an error"
                    // (redundant with the Assert when one precedes it, and sound for a
                    // bare `Unreachable` that has none), then terminate the path with NO
                    // return value. SOUNDNESS / adversarial guardrail: a genuinely
                    // panicking callee makes this error condition SATISFIABLE (its path
                    // guard is reachable), so a caller of it STILL refutes; a guarded /
                    // total callee (e.g. `signed_min`, whose shift/sub/neg panics are all
                    // dominated by `width` guards) makes it UNSAT, so the call proves
                    // panic-free. Without this arm the block was not `terminated`, the
                    // whole summary returned `None`, and `translate_call` fell back to an
                    // unconditional may-panic error rule — which is exactly why a caller
                    // of a proven-total i128 fn (`type_min` -> `signed_min`) stayed UNKNOWN.
                    Inst::Unreachable => {
                        error_conditions.push(call_summary_guarded_condition(
                            &state.path_conditions,
                            Expr::true_(),
                        ));
                        terminated = true;
                        break;
                    }
                    // A SELF-recursive call (the callee invokes the very function being
                    // summarized). Model it by the INDUCTIVE HYPOTHESIS of the fixpoint: assume
                    // the recursive call is panic-free (contribute NO error condition) and HAVOC
                    // its results (a sound over-approximation of the returned values). This is
                    // sound for ALL recursion depths ONLY when the callee carries no OTHER
                    // per-level obligation — enforced by the post-loop check below: then the
                    // callee is obligation-free modulo recursion, so it is panic-free at every
                    // depth by induction (the inductive-invariant argument machine-checked in
                    // clean's recursive_summary.lean). The arguments' own panic obligations (e.g.
                    // computing `n-1`) were already emitted by the instructions that produced
                    // them, so they are NOT lost. The self-call is NOT inlined/followed, so there
                    // is no unbounded unfolding. (A call to a DIFFERENT function still declines —
                    // that needs the callee's own summary, handled elsewhere.)
                    Inst::Call { callee, .. } if *callee == callee_func.id => {
                        self_recursion_seen = true;
                        if node.results.len() != callee_func_ty.returns.len() {
                            return None;
                        }
                        for (result, ty) in node.results.iter().zip(callee_func_ty.returns.iter()) {
                            if !self.is_call_summary_value_ty(ty) {
                                return None;
                            }
                            let havoc = self.fresh_call_summary_value("call_self_rec", ty)?;
                            state.locals.insert(*result, havoc);
                        }
                    }
                    Inst::Load { ty, volatile, .. }
                        if !*volatile
                            && node.proofs.contains(&ProofAnnotation::ValidBorrow)
                            && self.is_call_summary_value_ty(ty) =>
                    {
                        // A load through a SAFE reference (`ValidBorrow`): the access is
                        // borrow-checker-valid, so the loaded VALUE is modeled as a fresh
                        // unconstrained value (mirroring the main translate's ValidBorrow
                        // load). The access's bounds safety is carried by the
                        // separately-emitted bounds Assert. A raw-pointer load (no
                        // `ValidBorrow`) or a volatile load falls through to fail closed.
                        let result = self.fresh_call_summary_value("call_load", ty)?;
                        bind_call_summary_result(&mut state.locals, node, result)?;
                    }
                    // Any other instruction in the callee body is not modeled by the
                    // bounded summary interpreter — decline (fail closed / conservative).
                    _ => return None,
                }
            }

            if !terminated {
                // The block fell off the end of its body without a recognized
                // terminator. FAIL CLOSED (decline the summary → the caller conservatively
                // models this call as may-panic / UNKNOWN).
                //
                // SOUNDNESS (this is load-bearing — do NOT relax it to a havoc return):
                // a well-formed trust-ir block ALWAYS ends in a terminator — the bridge's
                // own validator rejects a missing terminator as a hard error
                // (`ValidationError::BlockMissingTerminator`, trust-ir-build validate.rs).
                // So reaching this arm means the lowering produced a MALFORMED CFG in which
                // a successor EDGE was dropped. A dropped edge is structurally
                // indistinguishable from a genuine dead-end, so we CANNOT conclude "no
                // successor exists ⇒ no further panic reachable": the dropped edge may lead
                // to a block that panics. The unsound predecessor of this code (commit
                // 7e5a2e345) pushed a `call_falloff` HAVOC return and `continue`d here,
                // which silently deleted that reachable panic's disjunct from `P_f` and
                // produced a FALSE PROOF — e.g. `let x = r?; assert!(x == 0); Ok(x)` over an
                // unconstrained `Result` proved panic-free (the post-`?` assert lives past
                // the dropped Try::branch edge). See trust falsification mutant
                // `tests/trust-falsification/mutant/try_result_unit.rs`.
                //
                // The completeness win this used to chase (`type_min` → `signed_min`) does
                // NOT depend on this arm: signed_min's imprecise leaves are genuine
                // `Inst::Return`s with an out-of-scope value, handled soundly by the
                // `Inst::Return` arm above (havoc the VALUE on a path that DID terminate).
                // Recovering precision for the `?` shape is the bridge's job (emit a
                // well-formed terminated CFG that models Try::branch), not this interpreter's
                // — it must never paper over a malformed lowering.
                return None;
            }
        }

        // SOUNDNESS of the recursion fixpoint: a self-recursive callee's single-invocation
        // summary establishes panic-freedom at EVERY depth ONLY when it carries NO per-level
        // obligation. The recursive call was assumed safe (the inductive hypothesis); discharging
        // that assumption requires the callee's own body to be obligation-free (so the base case
        // and every step are panic-free). If ANY obligation remains, we cannot prove it holds at
        // all recursion depths from this single invocation (it would have to be checked at every
        // reachable argument, not just the call site's), so we fail closed — sound, conservative.
        if self_recursion_seen && !error_conditions.is_empty() {
            return None;
        }
        let returns = combine_call_summary_returns(&returns, callee_func_ty.returns.len())?;
        Some(DirectCallSummary { returns, error_conditions })
    }

    fn call_summary_successor_state(
        &self,
        callee_func: &Function,
        state: &CallSummaryState,
        target: BlockId,
        args: &[ValueId],
        guard: Option<Expr>,
    ) -> Option<CallSummaryState> {
        if state.visited_blocks.contains(&target) {
            return None;
        }

        let target_block = callee_func.block(target)?;
        if target_block.params.len() != args.len() {
            return None;
        }

        let mut locals = state.locals.clone();
        for (arg, (param, ty)) in args.iter().zip(target_block.params.iter()) {
            if !self.is_call_summary_value_ty(ty) {
                return None;
            }
            locals.insert(*param, call_summary_value(&state.locals, *arg, ty)?);
        }

        let mut path_conditions = state.path_conditions.clone();
        if let Some(guard) = guard {
            path_conditions.push(guard);
        }
        Some(CallSummaryState {
            block: target,
            locals,
            path_conditions,
            visited_blocks: state.visited_blocks.clone(),
        })
    }

    fn add_transition_rule(
        &mut self,
        target: BlockId,
        args: &[ValueId],
        guard: Option<Expr>,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) {
        let Some(target_block) = self.func.block(target) else {
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::MalformedControlFlow,
                from,
                path_constraints,
            );
            return;
        };
        if target_block.params.len() != args.len() {
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::MalformedControlFlow,
                from,
                path_constraints,
            );
            return;
        }

        // Prepend the target block's threaded immutable-parameter prefix,
        // evaluated in the *source* block's context: SSA params are in scope by
        // dominance, so forwarding the source's current binding is sound.
        let target_threaded = self.block_threaded_params.get(&target).cloned().unwrap_or_default();
        let mut head_args = Vec::new();
        for (value, ty) in &target_threaded {
            head_args.extend(self.flatten_value_for_relation(*value, ty));
        }
        // mem2reg: forward the CURRENT (post-store) value of each cell the target
        // relation carries, evaluated in THIS (source) block's context. The source
        // block's `stack_cells` reflects every store executed on this path (seeded
        // from the incoming cell args in `translate_block`, updated by
        // `translate_stack_store`), so this is exactly the loop-carried update.
        // Order: target threaded -> target cells -> target own params, matching the
        // relation signature. A cell absent from `stack_cells` (a source path that
        // neither created nor stored it — defensive only) forwards a fresh
        // unconstrained value, the same fail-open default a Load would mint.
        let target_cells = self.block_promoted_cells.get(&target).cloned().unwrap_or_default();
        for (cell, ty) in &target_cells {
            let binding = match self.stack_cells.get(cell).map(|c| c.value.clone()) {
                Some(value) => value,
                None => {
                    let fresh = self.fresh_stack_cell_value(ty);
                    fresh.unwrap_or_else(|| {
                        ValueBinding::Scalar(self.fresh_symbolic("cell_undef", ty))
                    })
                }
            };
            let flat = binding.flat_args();
            head_args.extend(flat);
        }
        for (arg, (_, ty)) in args.iter().zip(target_block.params.iter()) {
            head_args.extend(self.flatten_value_for_relation(*arg, ty));
        }

        let mut constraints = path_constraints.to_vec();
        if let Some(guard) = guard {
            constraints.push(guard);
        }
        self.vc.add_rule(Rule::new(
            RuleBody::new(Some(from.clone()), constraints),
            RelationApp::new(block_relation_name(target), head_args),
        ));
    }

    fn add_error_rule(&mut self, from: &RelationApp, path_constraints: &[Expr], condition: Expr) {
        let mut constraints = path_constraints.to_vec();
        constraints.push(condition);
        self.vc.add_rule(Rule::new(
            RuleBody::new(Some(from.clone()), constraints),
            RelationApp::nullary(ERROR_REL),
        ));
    }

    fn add_unsupported_error(
        &mut self,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        reason: TrustIrChcUnsupportedReason,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) {
        self.diagnostics.push(TrustIrChcDiagnostic {
            function: self.func.name.clone(),
            block,
            instruction_index,
            family: family_for_inst(&node.inst),
            reason,
            result_values: node.results.clone(),
        });
        // PER-OBLIGATION NARROWING. In whole-function mode (narrow_to_target_block
        // = None, the default everywhere today) this rule is always added, so a
        // single unmodeled construct makes `error` reachable and sinks EVERY
        // obligation of the function. When the caller is asking about ONE
        // obligation whose assertion lives in `target`, an unsupported construct
        // that cannot lie on an entry ->* site ->* target path cannot influence
        // the states reaching that assertion — so its error rule would only
        // poison a sibling obligation, never this one.
        //
        // SOUNDNESS: the exclusion fires ONLY when the site is provably OFF every
        // entry->target path. Any uncertainty (unknown terminator, absent block,
        // the site IS the target) leaves `site_can_precede_target` = true and the
        // rule is added — over-approximate, never under. It can only DROP a rule
        // that is irrelevant to this obligation; it can never mask a real
        // violation, so it cannot produce a false PROVE.
        if let Some(target) = self.options.narrow_to_target_block
            && !self.site_can_precede_target(block, target)
        {
            return;
        }
        self.add_error_rule(from, path_constraints, Expr::true_());
    }

    /// Can an unsupported construct in `site` lie on an entry ->* site ->* target
    /// path? True (include the rule) on ANY uncertainty. Only a site provably
    /// unreachable-to-target OR unreachable-from-entry returns false.
    fn site_can_precede_target(&self, site: BlockId, target: BlockId) -> bool {
        let entry = self.func.entry;
        // The site is irrelevant when EITHER half of
        // `entry ->* site ->* target` is proven impossible. Unknown is not a
        // proof: malformed or incomplete CFG information always keeps the rule.
        !matches!(
            (Self::cfg_reaches(self.func, entry, site), Self::cfg_reaches(self.func, site, target),),
            (CfgReachability::ProvenUnreachable, _) | (_, CfgReachability::ProvenUnreachable)
        )
    }

    /// Exact-or-unknown forward reachability over the TrustIR CFG.
    ///
    /// `ProvenUnreachable` requires a complete traversal of every block
    /// reachable from `from`, with exactly one known terminator at the end of
    /// each block and every successor resolving to exactly one block. Any
    /// malformed or unsupported shape encountered on that reachable frontier
    /// yields `Unknown`. Finding `to` is conclusive even if another frontier is
    /// malformed, because narrowing keeps rules for `Reachable` and `Unknown`
    /// alike.
    fn cfg_reaches(func: &Function, from: BlockId, to: BlockId) -> CfgReachability {
        let mut blocks = BTreeMap::new();
        for block in &func.blocks {
            if blocks.insert(block.id, block).is_some() {
                return CfgReachability::Unknown;
            }
        }
        if !blocks.contains_key(&from) || !blocks.contains_key(&to) {
            return CfgReachability::Unknown;
        }
        if from == to {
            return CfgReachability::Reachable;
        }

        let mut stack = vec![from];
        let mut seen = BTreeSet::new();
        let mut incomplete = false;
        while let Some(b) = stack.pop() {
            if !seen.insert(b) {
                continue;
            }
            let Some(block) = blocks.get(&b) else {
                incomplete = true;
                continue;
            };

            let Some((terminator, prefix)) = block.body.split_last() else {
                incomplete = true;
                continue;
            };
            if prefix.iter().any(|node| node.inst.is_terminator()) {
                incomplete = true;
                continue;
            }
            let successors = match &terminator.inst {
                Inst::Br { target, .. } => vec![*target],
                Inst::CondBr { then_target, else_target, .. } => {
                    vec![*then_target, *else_target]
                }
                Inst::Switch { default, cases, .. } => {
                    let mut successors = vec![*default];
                    successors.extend(cases.iter().map(|case| case.target));
                    successors
                }
                Inst::Invoke { normal_dest, unwind_dest, .. } => {
                    vec![*normal_dest, *unwind_dest]
                }
                Inst::Return { .. }
                | Inst::CoroSuspend { .. }
                | Inst::Resume { .. }
                | Inst::Unreachable => Vec::new(),
                _ => {
                    incomplete = true;
                    continue;
                }
            };
            for successor in successors {
                if successor == to {
                    return CfgReachability::Reachable;
                }
                if blocks.contains_key(&successor) {
                    stack.push(successor);
                } else {
                    incomplete = true;
                }
            }
        }
        if incomplete { CfgReachability::Unknown } else { CfgReachability::ProvenUnreachable }
    }

    fn add_global_unsupported_error(&mut self, reason: TrustIrChcUnsupportedReason) {
        self.diagnostics.push(TrustIrChcDiagnostic {
            function: self.func.name.clone(),
            block: self.func.entry,
            instruction_index: 0,
            family: SemanticsFamily::ControlFlow,
            reason,
            result_values: Vec::new(),
        });
        self.vc.add_rule(Rule::new(RuleBody::empty(), RelationApp::nullary(ERROR_REL)));
    }

    fn block_app(&self, block: BlockId) -> Option<RelationApp> {
        self.block_param_bindings.get(&block).map(|bindings| {
            // Match the formal-argument order from declare_block_relations:
            // threaded immutable-parameter prefix, then the mem2reg promoted-cell
            // prefix, then the block's own params.
            let mut args: Vec<Expr> = Vec::new();
            if let Some(threaded) = self.block_threaded_bindings.get(&block) {
                args.extend(threaded.iter().flat_map(ValueBinding::flat_args));
            }
            if let Some(cells) = self.block_cell_bindings.get(&block) {
                args.extend(cells.iter().flat_map(ValueBinding::flat_args));
            }
            args.extend(bindings.iter().flat_map(ValueBinding::flat_args));
            RelationApp::new(block_relation_name(block), args)
        })
    }

    fn resolve(&mut self, value: ValueId, ty: &Ty) -> Expr {
        if let Some(expr) = self.values.get(&value) {
            return expr.clone();
        }
        let expr = self.fresh_symbolic(&format!("v{}", value.index()), ty);
        self.values.insert(value, expr.clone());
        expr
    }

    fn resolve_bool_condition(
        &mut self,
        value: ValueId,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) -> Option<Expr> {
        let expr = self.resolve(value, &Ty::Bool);
        if expr.sort().is_bool() {
            Some(expr)
        } else {
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::NonBooleanCondition,
                from,
                path_constraints,
            );
            None
        }
    }

    fn resolve_switch_selector(&mut self, value: ValueId) -> Expr {
        if let Some(expr) = self.values.get(&value) {
            return expr.clone();
        }
        self.resolve(value, &Ty::I64)
    }

    fn bind_first_result(&mut self, node: &InstrNode, expr: Expr) {
        if let Some(result) = node.results.first() {
            self.values.insert(*result, expr);
        }
    }

    fn bind_aggregate_result(&mut self, node: &InstrNode, aggregate: AggregateValue, ty: &Ty) {
        if let Some(result) = node.results.first() {
            let opaque = self.fresh_symbolic("aggregate", ty);
            self.values.insert(*result, opaque);
            self.aggregates.insert(*result, aggregate);
        }
    }

    fn bind_call_result(&mut self, result: ValueId, binding: ValueBinding, ty: &Ty) {
        match binding {
            ValueBinding::Scalar(expr) => {
                self.values.insert(result, expr);
            }
            ValueBinding::Aggregate(aggregate) => {
                let opaque = self.fresh_symbolic("call_aggregate", ty);
                self.values.insert(result, opaque);
                self.aggregates.insert(result, aggregate);
            }
        }
    }

    fn bind_symbolic_call_results(
        &mut self,
        callee_name: &str,
        return_tys: Option<&[Ty]>,
        node: &InstrNode,
    ) {
        for (index, result) in node.results.iter().enumerate() {
            let ty = return_tys.and_then(|tys| tys.get(index)).unwrap_or(&Ty::I64);
            let prefix = format!("call_{}", sanitize_name(callee_name));
            match self.fresh_call_summary_value(&prefix, ty) {
                Some(binding) => self.bind_call_result(*result, binding, ty),
                None => {
                    let result_expr = self.fresh_symbolic(&prefix, ty);
                    self.values.insert(*result, result_expr);
                }
            }
        }
    }

    fn fresh_symbolic(&mut self, prefix: &str, ty: &Ty) -> Expr {
        let name = format!("{}_{}_{}", sanitize_name(&self.func.name), prefix, self.next_sym_id);
        self.next_sym_id += 1;
        self.vc.declare_var(name, ty_to_sort(ty))
    }

    fn fresh_call_summary_value(&mut self, prefix: &str, ty: &Ty) -> Option<ValueBinding> {
        if is_call_summary_scalar_ty(ty) {
            return Some(ValueBinding::Scalar(self.fresh_symbolic(prefix, ty)));
        }

        let field_tys = self.aggregate_field_tys(ty)?;
        let mut fields = Vec::with_capacity(field_tys.len());
        for (field_index, field_ty) in field_tys.iter().enumerate() {
            // Trust (#46): recurse for nested-aggregate fields.
            fields.push(
                self.resolve_field_binding(&format!("{prefix}_field{field_index}"), field_ty)?,
            );
        }
        Some(ValueBinding::Aggregate(AggregateValue { fields }))
    }

    fn aggregate_field_tys(&self, ty: &Ty) -> Option<Vec<Ty>> {
        aggregate_field_tys_of(self.module, ty)
    }

    /// Trust (#46): build a fresh `ValueBinding` for a field of type `ty` — a scalar
    /// gets a fresh symbol; a (possibly nested) aggregate is recursively built with
    /// fresh leaves. Returns `None` if `ty` is neither scalar nor a trackable
    /// aggregate (fail closed).
    fn resolve_field_binding(&mut self, prefix: &str, ty: &Ty) -> Option<ValueBinding> {
        if is_scalar_field_ty(ty) {
            return Some(ValueBinding::Scalar(self.fresh_symbolic(prefix, ty)));
        }
        let field_tys = self.aggregate_field_tys(ty)?;
        let mut fields = Vec::with_capacity(field_tys.len());
        for (index, field_ty) in field_tys.iter().enumerate() {
            fields.push(self.resolve_field_binding(&format!("{prefix}_f{index}"), field_ty)?);
        }
        Some(ValueBinding::Aggregate(AggregateValue { fields }))
    }

    fn is_call_summary_value_ty(&self, ty: &Ty) -> bool {
        is_call_summary_scalar_ty(ty) || self.aggregate_field_tys(ty).is_some()
    }

    fn resolve_call_summary_argument(&mut self, value: ValueId, ty: &Ty) -> Option<ValueBinding> {
        if is_call_summary_scalar_ty(ty) {
            return Some(ValueBinding::Scalar(self.resolve(value, ty)));
        }

        self.aggregate_field_tys(ty)?;
        Some(ValueBinding::Aggregate(self.resolve_aggregate(value, ty)?))
    }

    fn resolve_aggregate(&mut self, value: ValueId, ty: &Ty) -> Option<AggregateValue> {
        if let Some(aggregate) = self.aggregates.get(&value) {
            return Some(aggregate.clone());
        }

        let field_tys = self.aggregate_field_tys(ty)?;
        let mut fields = Vec::with_capacity(field_tys.len());
        for (field_index, field_ty) in field_tys.iter().enumerate() {
            // Trust (#46): recurse so a nested-aggregate field gets a nested binding
            // (fresh leaves), not a single scalar symbol.
            fields.push(self.resolve_field_binding(
                &format!("v{}_field{}", value.index(), field_index),
                field_ty,
            )?);
        }
        let aggregate = AggregateValue { fields };
        self.aggregates.insert(value, aggregate.clone());
        Some(aggregate)
    }

    fn flatten_value_for_relation(&mut self, value: ValueId, ty: &Ty) -> Vec<Expr> {
        self.resolve_aggregate(value, ty)
            .map(|aggregate| ValueBinding::Aggregate(aggregate).flat_args())
            .unwrap_or_else(|| vec![self.resolve(value, ty)])
    }

    fn eval_extract_field(&mut self, aggregate: ValueId, field: u32) -> Option<ValueBinding> {
        self.aggregates.get(&aggregate)?.fields.get(field as usize).cloned()
    }

    fn eval_insert_field(
        &mut self,
        ty: &Ty,
        aggregate: ValueId,
        field: u32,
        value: ValueId,
    ) -> Option<AggregateValue> {
        let field_tys = self.aggregate_field_tys(ty)?;
        let field_index = field as usize;
        let value_ty = field_tys.get(field_index)?;
        let value_ty = value_ty.clone();
        let mut result = self.resolve_aggregate(aggregate, ty)?;
        if result.fields.len() != field_tys.len() {
            return None;
        }
        // Trust (#46): the inserted field may itself be a nested aggregate.
        result.fields[field_index] = if is_scalar_field_ty(&value_ty) {
            ValueBinding::Scalar(self.resolve(value, &value_ty))
        } else {
            ValueBinding::Aggregate(self.resolve_aggregate(value, &value_ty)?)
        };
        Some(result)
    }

    fn eval_binop(&mut self, op: BinOp, ty: &Ty, lhs: &Expr, rhs: &Expr) -> Expr {
        let lhs = &normalize_expr_to_ty(lhs, ty);
        let rhs = &normalize_expr_to_ty(rhs, ty);
        if ty.is_integer() {
            match op {
                BinOp::Add => lhs.clone().bvadd(rhs.clone()),
                BinOp::Sub => lhs.clone().bvsub(rhs.clone()),
                BinOp::Mul => lhs.clone().bvmul(rhs.clone()),
                BinOp::UDiv => lhs.clone().bvudiv(rhs.clone()),
                BinOp::SDiv => lhs.clone().bvsdiv(rhs.clone()),
                BinOp::URem => lhs.clone().bvurem(rhs.clone()),
                BinOp::SRem => lhs.clone().bvsrem(rhs.clone()),
                BinOp::And => lhs.clone().bvand(rhs.clone()),
                BinOp::Or => lhs.clone().bvor(rhs.clone()),
                BinOp::Xor => lhs.clone().bvxor(rhs.clone()),
                BinOp::Shl => lhs.clone().bvshl(rhs.clone()),
                BinOp::LShr => lhs.clone().bvlshr(rhs.clone()),
                BinOp::AShr => lhs.clone().bvashr(rhs.clone()),
                BinOp::FAdd
                | BinOp::FSub
                | BinOp::FMul
                | BinOp::FDiv
                | BinOp::FRem
                | BinOp::FMin
                | BinOp::FMax => self.fresh_symbolic("float_on_int", ty),
                // Trust: the BOOLEAN connectives (trust-ir 4b06918) on an INTEGER
                // type are ill-typed IR -- trust-ir's validator admits them on Bool
                // (or bool-vector) only. Same fail-closed treatment as float-on-int:
                // a fresh, unconstrained symbolic, never a plausible bit-level
                // reading of a program that should have been rejected. Mirrors
                // `translate::eval_binop`.
                BinOp::BAnd | BinOp::BOr | BinOp::BXor => {
                    self.fresh_symbolic("bool_connective_on_int", ty)
                }
            }
        } else if matches!(ty, Ty::Bool) {
            // `And`/`Or`/`Xor` on a `Bool`-typed value are LOGICAL connectives, not
            // bitvector ops. Modeling them precisely (rather than havocing to a
            // fresh symbolic) lets the CHC reason through boolean structure — e.g.
            // a discriminant-validity `Assume(tag == 0 || tag == 1)` that discharges
            // an exhaustive enum match's otherwise→unreachable obligation. Xor over
            // booleans is inequality. Falls back to a fresh symbolic only on a sort
            // mismatch (never silently unsound: a fresh bool is unconstrained).
            match op {
                BinOp::And => lhs
                    .clone()
                    .try_and(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                BinOp::Or => lhs
                    .clone()
                    .try_or(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                BinOp::Xor => lhs
                    .clone()
                    .try_ne(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
// Trust: the DEDICATED boolean connectives (trust-ir 4b06918) -- the same
                // logical semantics as the `And`/`Or`/`Xor` arms above, which MIR
                // reaches only through opcode overloading. Explicit arms, not the
                // catch-all: havocing them to a fresh symbolic would discard exactly
                // the boolean structure this branch exists to preserve for the CHC.
                BinOp::BAnd => lhs
                    .clone()
                    .try_and(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                BinOp::BOr => lhs
                    .clone()
                    .try_or(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                BinOp::BXor => lhs
                    .clone()
                    .try_ne(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                                _ => self.fresh_symbolic("binop_result", ty),
            }
        } else {
            self.fresh_symbolic("binop_result", ty)
        }
    }

    fn eval_icmp(&self, op: ICmpOp, ty: &Ty, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
        let lhs = &normalize_expr_to_ty(lhs, ty);
        let rhs = &normalize_expr_to_ty(rhs, ty);

        if ty.is_float() || lhs.sort() != rhs.sort() {
            return None;
        }

        match op {
            ICmpOp::Eq if is_eq_comparable_ty(ty) => Some(lhs.clone().eq(rhs.clone())),
            ICmpOp::Ne if is_eq_comparable_ty(ty) => Some(lhs.clone().eq(rhs.clone()).not()),
            ICmpOp::Ult if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvult(rhs.clone()))
            }
            ICmpOp::Ule if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvule(rhs.clone()))
            }
            ICmpOp::Ugt if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvugt(rhs.clone()))
            }
            ICmpOp::Uge if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvuge(rhs.clone()))
            }
            ICmpOp::Slt if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvslt(rhs.clone()))
            }
            ICmpOp::Sle if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvsle(rhs.clone()))
            }
            ICmpOp::Sgt if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvsgt(rhs.clone()))
            }
            ICmpOp::Sge if is_order_comparable_ty(ty, lhs, rhs) => {
                Some(lhs.clone().bvsge(rhs.clone()))
            }
            _ => None,
        }
    }

    fn eval_cast(
        &mut self,
        op: CastOp,
        src_ty: &Ty,
        dst_ty: &Ty,
        operand: ValueId,
    ) -> Option<Expr> {
        let operand = self.resolve(operand, src_ty);
        eval_cast_expr(op, src_ty, dst_ty, operand)
    }

    /// UNWRAP a single-pointer-newtype struct value (`NonNull`/`Box`/…) to its
    /// inner thin pointer by navigating the resolved aggregate down `path` to the
    /// leaf scalar. The pointer value is preserved exactly (the transmute reads
    /// the same address bits); the changed pointee TYPE is a separate
    /// deref-validity obligation.
    fn unwrap_pointer_newtype(
        &mut self,
        operand: ValueId,
        src_ty: &Ty,
        path: &[u32],
    ) -> Option<Expr> {
        let mut binding = ValueBinding::Aggregate(self.resolve_aggregate(operand, src_ty)?);
        for &idx in path {
            binding = match binding {
                ValueBinding::Aggregate(agg) => agg.fields.get(idx as usize)?.clone(),
                ValueBinding::Scalar(_) => return None,
            };
        }
        match binding {
            ValueBinding::Scalar(expr) => Some(expr),
            ValueBinding::Aggregate(_) => None,
        }
    }

    /// WRAP a thin pointer into a single-pointer-newtype struct (`*mut u8 ->
    /// Box<…>`): build the nested aggregate with the pointer at the leaf (down
    /// `path`) and fresh zero-sized pad fields elsewhere (`PhantomData`). The
    /// pointer value is preserved; a later projection + unwrap recovers it.
    fn wrap_pointer_newtype(
        &mut self,
        ptr: Expr,
        dst_ty: &Ty,
        path: &[u32],
    ) -> Option<AggregateValue> {
        let field_tys = self.aggregate_field_tys(dst_ty)?;
        let target = *path.first()? as usize;
        let mut fields = Vec::with_capacity(field_tys.len());
        for (i, field_ty) in field_tys.iter().enumerate() {
            if i == target {
                if path.len() == 1 {
                    fields.push(ValueBinding::Scalar(ptr.clone()));
                } else {
                    let nested = self.wrap_pointer_newtype(ptr.clone(), field_ty, &path[1..])?;
                    fields.push(ValueBinding::Aggregate(nested));
                }
            } else {
                fields.push(self.fresh_call_summary_value(&format!("newtype_pad{i}"), field_ty)?);
            }
        }
        Some(AggregateValue { fields })
    }
}

fn translate_function(
    func: &Function,
    module: &Module,
    options: &TranslateOptions,
) -> ChcTranslationOutput {
    ChcFuncTranslator::new(func, module, options).translate()
}

const POINTER_WIDTH: u32 = 64;

fn resize_bitvec_unsigned(expr: Expr, src_width: u32, dst_width: u32) -> Expr {
    match src_width.cmp(&dst_width) {
        std::cmp::Ordering::Equal => expr,
        std::cmp::Ordering::Less => expr.zero_extend(dst_width - src_width),
        std::cmp::Ordering::Greater => expr.extract(dst_width - 1, 0),
    }
}

fn resize_bitvec_for_int_to_ptr(expr: Expr, src_ty: &Ty, src_width: u32) -> Expr {
    match src_width.cmp(&POINTER_WIDTH) {
        std::cmp::Ordering::Equal => expr,
        std::cmp::Ordering::Less if src_ty.is_signed() => {
            expr.sign_extend(POINTER_WIDTH - src_width)
        }
        std::cmp::Ordering::Less => expr.zero_extend(POINTER_WIDTH - src_width),
        std::cmp::Ordering::Greater => expr.extract(POINTER_WIDTH - 1, 0),
    }
}

fn eval_cast_expr(op: CastOp, src_ty: &Ty, dst_ty: &Ty, operand: Expr) -> Option<Expr> {
    match op {
        CastOp::ZExt | CastOp::SExt | CastOp::Trunc
            if src_ty.is_integer() && dst_ty.is_integer() =>
        {
            let src_width = src_ty.bit_width_with(HOST_POINTER_BITS)?;
            let dst_width = dst_ty.bit_width_with(HOST_POINTER_BITS)?;
            match op {
                CastOp::ZExt | CastOp::SExt | CastOp::Trunc if src_width == dst_width => {
                    Some(operand)
                }
                CastOp::ZExt if src_width < dst_width => {
                    Some(operand.zero_extend(dst_width - src_width))
                }
                CastOp::SExt if src_width < dst_width => {
                    Some(operand.sign_extend(dst_width - src_width))
                }
                CastOp::Trunc if src_width > dst_width => Some(operand.extract(dst_width - 1, 0)),
                _ => None,
            }
        }
        // A `bool -> <int>` cast is `ite(b, 1, 0)` — a bool is 0 or 1, so the result
        // is in {0, 1} — for WHATEVER `CastOp` the bridge cast-op selector assigned
        // it, not only `ZExt`. A bool source that reached here with any other op
        // previously fell through to the `_ => None` fail-closed path (fresh
        // UNCONSTRAINED symbolic result), so a SUM of such casts — flag/edge counts
        // like `(a != b) as u32 + (b != c) as u32 + ...` — could not bound its
        // operands and spuriously REFUTED its arithmetic-overflow VC. Matching any
        // op for a bool source is SOUND and exact: the {0,1} semantics is the same
        // regardless of the op label. (over-refutation audit: body cast semantics.)
        _ if matches!(src_ty, Ty::Bool) && dst_ty.is_integer() => {
            let dst_width = dst_ty.bit_width_with(HOST_POINTER_BITS)?;
            Some(Expr::ite(
                operand,
                Expr::bitvec_const(1u64, dst_width),
                Expr::bitvec_const(0u64, dst_width),
            ))
        }
        CastOp::Bitcast if src_ty.is_integer() && dst_ty.is_integer() => {
            let src_width = src_ty.bit_width_with(HOST_POINTER_BITS)?;
            let dst_width = dst_ty.bit_width_with(HOST_POINTER_BITS)?;
            (src_width == dst_width).then_some(operand)
        }
        CastOp::PtrToInt if is_thin_pointer_ty(src_ty) && dst_ty.is_integer() => {
            let dst_width = dst_ty.bit_width_with(HOST_POINTER_BITS)?;
            Some(resize_bitvec_unsigned(operand, POINTER_WIDTH, dst_width))
        }
        CastOp::IntToPtr if src_ty.is_integer() && is_thin_pointer_ty(dst_ty) => {
            let src_width = src_ty.bit_width_with(HOST_POINTER_BITS)?;
            Some(resize_bitvec_for_int_to_ptr(operand, src_ty, src_width))
        }
        CastOp::PtrToPtr | CastOp::Bitcast
            if is_thin_pointer_ty(src_ty) && is_thin_pointer_ty(dst_ty) =>
        {
            Some(operand)
        }
        _ => None,
    }
}

fn block_relation_name(block: BlockId) -> String {
    format!("bb{}", block.index())
}

/// Append every `ValueId` read (used as an operand) by `inst` into `uses`.
///
/// Block-argument lists on terminators (`Br` / `CondBr` / `Switch`) *are* reads:
/// the value is consumed to populate the successor's block parameter.
///
/// Returns `true` when `inst` is a variant whose operands this collector does
/// not statically enumerate (e.g. a future / dialect instruction). Callers must
/// treat an unknown instruction as *potentially reading any in-scope value* so
/// liveness stays a sound over-approximation: under-counting a use would let a
/// downstream `resolve` mint an unconstrained fresh symbolic for an immutable
/// parameter, which a model checker could then pick adversarially and mask a
/// real violation. Over-counting only threads a dead parameter (sound, verbose).
fn collect_inst_value_uses(inst: &Inst, uses: &mut Vec<ValueId>) -> bool {
    match inst {
        Inst::BinOp { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. } => {
            uses.push(*lhs);
            uses.push(*rhs);
            false
        }
        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } => {
            uses.push(*operand);
            false
        }
        Inst::Load { ptr, .. }
        | Inst::PtrData { ptr, .. }
        | Inst::PtrMetadata { ptr, .. }
        | Inst::AtomicLoad { ptr, .. }
        | Inst::Borrow { ptr }
        | Inst::BorrowMut { ptr }
        | Inst::Retain { ptr }
        | Inst::Release { ptr }
        | Inst::IsUnique { ptr }
        | Inst::Dealloc { ptr } => {
            uses.push(*ptr);
            false
        }
        Inst::EndBorrow { borrow_ptr } => {
            uses.push(*borrow_ptr);
            false
        }
        Inst::Store { ptr, value, .. }
        | Inst::AtomicStore { ptr, value, .. }
        | Inst::AtomicRMW { ptr, value, .. } => {
            uses.push(*ptr);
            uses.push(*value);
            false
        }
        Inst::Alloca { count, .. } | Inst::HeapAlloc { count, .. } => {
            if let Some(count) = count {
                uses.push(*count);
            }
            false
        }
        Inst::GEP { base, indices, .. } => {
            uses.push(*base);
            uses.extend(indices.iter().copied());
            false
        }
        Inst::PtrFromParts { data, metadata, .. } => {
            uses.push(*data);
            uses.push(*metadata);
            false
        }
        Inst::CmpXchg { ptr, expected, desired, .. } => {
            uses.push(*ptr);
            uses.push(*expected);
            uses.push(*desired);
            false
        }
        Inst::Br { args, .. } => {
            uses.extend(args.iter().copied());
            false
        }
        Inst::CondBr { cond, then_args, else_args, .. } => {
            uses.push(*cond);
            uses.extend(then_args.iter().copied());
            uses.extend(else_args.iter().copied());
            false
        }
        Inst::Switch { value, default_args, cases, .. } => {
            uses.push(*value);
            uses.extend(default_args.iter().copied());
            for case in cases {
                uses.extend(case.args.iter().copied());
            }
            false
        }
        Inst::Call { args, .. } => {
            uses.extend(args.iter().copied());
            false
        }
        Inst::CallIndirect { callee, args, .. } => {
            uses.push(*callee);
            uses.extend(args.iter().copied());
            false
        }
        Inst::Return { values } => {
            uses.extend(values.iter().copied());
            false
        }
        Inst::ExtractField { aggregate, .. } => {
            uses.push(*aggregate);
            false
        }
        Inst::InsertField { aggregate, value, .. } => {
            uses.push(*aggregate);
            uses.push(*value);
            false
        }
        Inst::ExtractElement { array, index, .. } => {
            uses.push(*array);
            uses.push(*index);
            false
        }
        Inst::InsertElement { array, index, value, .. } => {
            uses.push(*array);
            uses.push(*index);
            uses.push(*value);
            false
        }
        Inst::Assume { cond } | Inst::Assert { cond } => {
            uses.push(*cond);
            false
        }
        Inst::Copy { operand, .. } => {
            uses.push(*operand);
            false
        }
        Inst::Select { cond, then_val, else_val, .. } => {
            uses.push(*cond);
            uses.push(*then_val);
            uses.push(*else_val);
            false
        }
        Inst::BindSlot { frame, value, .. } => {
            uses.push(*frame);
            uses.push(*value);
            false
        }
        Inst::LoadSlot { frame, .. } => {
            uses.push(*frame);
            false
        }
        Inst::CloseFrame { frame } => {
            uses.push(*frame);
            false
        }
        // The general SeqMap's `fwd` is a FuncId (function reference, not a
        // value read); `seq` is the sole value use for all three forms.
        Inst::SeqMapAddK { seq, .. } | Inst::SeqMapNot { seq, .. } | Inst::SeqMap { seq, .. } => {
            uses.push(*seq);
            false
        }
        // Operand-free instructions: no value reads.
        Inst::DialectOp(op) if is_thread_local_addr(op) => false,
        Inst::Const { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Unreachable
        | Inst::Fence { .. }
        | Inst::OpenFrame { .. } => false,
        // Unknown / opaque (e.g. `DialectOp`, or any future variant): we cannot
        // enumerate its reads, so report it conservatively.
        _ => true,
    }
}

/// Successor blocks of a terminator. An unrecognized terminator is reported via
/// the boolean flag so liveness can stay conservative.
fn collect_terminator_successors(inst: &Inst, successors: &mut Vec<BlockId>) -> bool {
    match inst {
        Inst::Br { target, .. } => {
            successors.push(*target);
            false
        }
        Inst::CondBr { then_target, else_target, .. } => {
            successors.push(*then_target);
            successors.push(*else_target);
            false
        }
        Inst::Switch { default, cases, .. } => {
            successors.push(*default);
            successors.extend(cases.iter().map(|case| case.target));
            false
        }
        Inst::Return { .. } | Inst::Unreachable => false,
        // A non-terminator (block falls through to nothing modeled) or an
        // unknown terminator: report conservatively.
        _ => true,
    }
}

fn sanitize_name(name: &str) -> String {
    name.chars().map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' }).collect()
}

/// Map a callee method name to the MODULAR `BinOp` a wrapping arithmetic intrinsic
/// computes, matching on the final `::` path segment (`core::num::<impl u64>::
/// wrapping_add` → `Add`). Mirrors the compiler MIR path's
/// `inline_wrapping_arith_expr`; the caller (`translate_call`) additionally checks
/// the callee's signature shape before modeling the call as this BV op.
fn wrapping_arith_binop(callee_name: &str) -> Option<BinOp> {
    match callee_name.rsplit("::").next()? {
        "wrapping_add" => Some(BinOp::Add),
        "wrapping_sub" => Some(BinOp::Sub),
        "wrapping_mul" => Some(BinOp::Mul),
        _ => None,
    }
}

/// Trust: host target thin-pointer width in bits. trust-ir `Ty::bit_width()`
/// returns `None` for pointer-like types (`Ptr`/`Ref`/`RefMut`/`Rc`/`FatPtr`) as
/// of trust-ir 6ed4bf0, which made pointer width target-dependent (a real wasm32
/// correctness fix). Trust verifies host-target (64-bit aarch64/x86-64) code, so
/// resolve those types at 64 via `bit_width_with` — exactly restoring the
/// pre-6ed4bf0 behavior where pointers reported `Some(64)`. Without this, a `&T` /
/// `&mut Iter` field reads as non-scalar and the for-each / reference-payload CHC
/// loses its invariant (`ay-chc returned unknown`), regressing the slice-iterator
/// proof lane. (Threading the real per-target pointer width is a future
/// enhancement; the host is 64-bit.)
const HOST_POINTER_BITS: u32 = 64;

fn is_scalar_field_ty(ty: &Ty) -> bool {
    ty.bit_width_with(HOST_POINTER_BITS).is_some()
}

/// Trust (#46): free version of `aggregate_field_tys` (so the recursive block-
/// relation declaration can borrow `&Module` + `&mut vc` as disjoint fields while a
/// `&self.func` block iteration is live). A struct/tuple is trackable when every
/// field is a scalar OR itself a trackable (possibly nested) aggregate.
fn aggregate_field_tys_of(module: &Module, ty: &Ty) -> Option<Vec<Ty>> {
    // Bound the TOTAL flattened scalar-leaf count before declaring this aggregate
    // trackable. `aggregate_leaf_count_within` subsumes the old field-by-field
    // trackability check (it returns `None` unless every leaf bottoms out in a
    // scalar) AND caps the leaf count at `MAX_AGGREGATE_LEAVES`, so a trackable-but-
    // huge nested array (`bd37bce4a`) can no longer explode the block-relation
    // signature into millions of CHC variables. Over budget ⇒ `None` ⇒ every caller
    // that gates expansion on this function (`declare_relation_binding_rec`,
    // `resolve_field_binding`, `fresh_call_summary_value`, the pad/newtype helpers)
    // uniformly treats the value as a single opaque scalar (fail closed).
    aggregate_leaf_count_within(module, ty, MAX_AGGREGATE_LEAVES)?;
    immediate_aggregate_field_tys(module, ty)
}

/// Whether proof-grade native ingestion may admit a metadata-less, single-cell
/// `Alloca` without importing source authority.
///
/// This deliberately mirrors the CHC translator's tracked-versus-opaque split.
/// A precise scalar or trackable aggregate is admitted only when its pointer is
/// used exclusively in its defining block as the direct operand of same-type,
/// non-volatile loads and stores with no caller-asserted alignment, and every
/// load follows a store. That prevents an uninitialized read, alias, volatile
/// access, unsupported alignment claim, or type-punning write from entering the
/// proof lane. The same structural restriction is deliberately
/// retained for opaque aggregates even though their loads are already fresh
/// havoc: proof-grade ingestion does not silently widen the allocation-lifetime
/// surface merely because the value model is imprecise. The translator's
/// independent indirect-store invalidation remains a second line of defense
/// rather than an admission premise.
pub fn single_cell_alloca_is_admissible(
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> bool {
    let aggregate = matches!(
        ty,
        Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, _) | Ty::Unit | Ty::Closure(_) | Ty::Enum(_)
    );
    if !is_precise_stack_scalar_ty(ty) && !aggregate {
        return false;
    }

    let result = alloca_result.index();
    let Some(definition_block) = function.blocks.iter().find_map(|block| {
        block
            .body
            .iter()
            .any(|node| {
                node.results.iter().any(|value| value.index() == result)
                    && matches!(
                        &node.inst,
                        Inst::Alloca { ty: cell_ty, count: None, align: None } if cell_ty == ty
                    )
            })
            .then_some(block.id)
    }) else {
        return false;
    };

    let mut initialized = false;
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ty: access_ty, ptr, volatile, align } => {
                    if ptr.index() == result
                        && (block.id != definition_block
                            || !initialized
                            || *volatile
                            || align.is_some()
                            || access_ty != ty)
                    {
                        return false;
                    }
                }
                Inst::Store { ty: access_ty, ptr, value, volatile, align } => {
                    if ptr.index() == result
                        && (block.id != definition_block
                            || *volatile
                            || align.is_some()
                            || access_ty != ty)
                    {
                        return false;
                    }
                    if value.index() == result {
                        return false;
                    }
                    if ptr.index() == result {
                        initialized = true;
                    }
                }
                other => {
                    let mut uses = Vec::new();
                    if collect_inst_value_uses(other, &mut uses) {
                        // An opaque instruction may read any in-scope pointer.
                        return false;
                    }
                    if uses.iter().any(|value| value.index() == result) {
                        return false;
                    }
                }
            }
        }
    }
    true
}

/// The immediate field types of `ty` viewed as an aggregate, WITHOUT the trackability
/// or leaf-budget checks. `None` for a non-aggregate (scalar / pointer / enum) leaf.
fn immediate_aggregate_field_tys(module: &Module, ty: &Ty) -> Option<Vec<Ty>> {
    match ty {
        Ty::Struct(id) => Some(
            module
                .structs
                .get(id.as_usize())?
                .fields
                .iter()
                .map(|field| field.ty.clone())
                .collect(),
        ),
        Ty::Tuple(fields) => Some(fields.clone()),
        // Trust (#46): `()` (unit / zero-size) is a ZERO-FIELD aggregate — it carries
        // no data and contributes no CHC leaf. Without this, a unit field (e.g. the
        // `Err(())` payload of `Result<T, ()>`, the shape `r?` desugars over) is
        // neither scalar nor a trackable aggregate, so it POISONS the whole enclosing
        // aggregate and `r?` fails closed. An empty tuple already takes the
        // `Ty::Tuple` arm; `Ty::Unit` is the distinct variant.
        Ty::Unit => Some(Vec::new()),
        // A fixed-size array `[T; N]` is modeled as an N-field aggregate of the
        // element type, so it is trackable as a call-summary value (param/return)
        // and an `ExtractElement` at a constant index projects a consistent field.
        // Capped per-dimension; larger arrays fail closed.
        Ty::Array(elem_id, len) if *len <= 256 => {
            Some(vec![module.types.get(elem_id.as_usize())?.clone(); *len as usize])
        }
        _ => None,
    }
}

/// Total flattened scalar-leaf count of `ty`, expanded EXACTLY as
/// `declare_relation_binding_rec` would, or `None` if `ty` is not a trackable
/// aggregate (some leaf is neither a scalar nor a trackable aggregate) OR its leaf
/// count would exceed `budget`. Saturating and short-circuiting: it stops as soon as
/// the running total passes `budget`, so an over-budget type costs `O(budget)` rather
/// than `O(leaves)` and is never materialized.
fn aggregate_leaf_count_within(module: &Module, ty: &Ty, budget: usize) -> Option<usize> {
    let fields = immediate_aggregate_field_tys(module, ty)?;
    let mut total = 0usize;
    for field in &fields {
        // Mirror `declare_relation_binding_rec`'s precedence: a field that is itself a
        // trackable (within-budget) aggregate is expanded; otherwise it is one scalar
        // leaf — but only if it is a valid scalar, else the parent is not trackable.
        let leaves = match aggregate_leaf_count_within(module, field, budget) {
            Some(count) => count,
            None if is_scalar_field_ty(field) => 1,
            None => return None,
        };
        total = total.saturating_add(leaves);
        if total > budget {
            return None;
        }
    }
    Some(total)
}

/// Trust (#46): declare the CHC block-relation formal arguments and the matching
/// `ValueBinding` for a value of type `ty`, recursing through nested aggregates so
/// `arg_sorts` gets ONE sort per leaf in the SAME depth-first, left-to-right order
/// `ValueBinding::flat_args` produces — keeping the relation's formal signature and
/// its application args leaf-aligned (a mismatch would be a malformed CHC).
fn declare_relation_binding_rec(
    module: &Module,
    vc: &mut ChcVc,
    prefix: &str,
    ty: &Ty,
    arg_sorts: &mut Vec<ay_bindings::Sort>,
) -> ValueBinding {
    if let Some(field_tys) = aggregate_field_tys_of(module, ty) {
        let mut fields = Vec::with_capacity(field_tys.len());
        for (field_index, field_ty) in field_tys.iter().enumerate() {
            fields.push(declare_relation_binding_rec(
                module,
                vc,
                &format!("{prefix}_field{field_index}"),
                field_ty,
                arg_sorts,
            ));
        }
        ValueBinding::Aggregate(AggregateValue { fields })
    } else {
        arg_sorts.push(ty_to_sort(ty));
        ValueBinding::Scalar(vc.declare_var(prefix.to_string(), ty_to_sort(ty)))
    }
}

fn is_precise_stack_scalar_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool) || is_ordered_scalar_ty(ty)
}

fn is_call_summary_scalar_ty(ty: &Ty) -> bool {
    // A pointer is modeled opaquely (it is never dereferenced precisely in the
    // summary — a `ValidBorrow` Load havocs the loaded value), so a reference
    // parameter such as `&[u32; N]` is a trackable call-summary value.
    is_precise_stack_scalar_ty(ty) || matches!(ty, Ty::Ptr)
}

fn call_summary_value(
    values: &BTreeMap<ValueId, ValueBinding>,
    value: ValueId,
    ty: &Ty,
) -> Option<ValueBinding> {
    if is_call_summary_scalar_ty(ty) {
        return Some(ValueBinding::Scalar(call_summary_scalar(values, value)?));
    }

    Some(ValueBinding::Aggregate(call_summary_aggregate(values, value)?))
}

fn call_summary_scalar(values: &BTreeMap<ValueId, ValueBinding>, value: ValueId) -> Option<Expr> {
    match values.get(&value)? {
        ValueBinding::Scalar(expr) => Some(expr.clone()),
        ValueBinding::Aggregate(_) => None,
    }
}

fn call_summary_aggregate(
    values: &BTreeMap<ValueId, ValueBinding>,
    value: ValueId,
) -> Option<AggregateValue> {
    match values.get(&value)? {
        ValueBinding::Scalar(_) => None,
        ValueBinding::Aggregate(aggregate) => Some(aggregate.clone()),
    }
}

fn call_summary_bool(values: &BTreeMap<ValueId, ValueBinding>, value: ValueId) -> Option<Expr> {
    let expr = call_summary_scalar(values, value)?;
    expr.sort().is_bool().then_some(expr)
}

fn call_summary_path_condition(path_conditions: &[Expr]) -> Expr {
    match path_conditions {
        [] => Expr::true_(),
        [condition] => condition.clone(),
        _ => Expr::and_many(path_conditions.to_vec()),
    }
}

fn call_summary_guarded_condition(path_conditions: &[Expr], condition: Expr) -> Expr {
    if path_conditions.is_empty() {
        condition
    } else {
        let mut conditions = path_conditions.to_vec();
        conditions.push(condition);
        Expr::and_many(conditions)
    }
}

fn combine_call_summary_returns(
    return_paths: &[CallSummaryReturn],
    return_count: usize,
) -> Option<Vec<ValueBinding>> {
    if return_paths.is_empty() {
        return None;
    }

    (0..return_count)
        .map(|return_index| {
            let mut paths = return_paths.iter().rev();
            let mut combined = paths.next()?.values.get(return_index)?.clone();
            for return_path in paths {
                combined = combine_call_summary_binding(
                    call_summary_path_condition(&return_path.path_conditions),
                    return_path.values.get(return_index)?,
                    combined,
                )?;
            }
            Some(combined)
        })
        .collect()
}

fn combine_call_summary_binding(
    guard: Expr,
    then_value: &ValueBinding,
    else_value: ValueBinding,
) -> Option<ValueBinding> {
    match (then_value, else_value) {
        (ValueBinding::Scalar(then_expr), ValueBinding::Scalar(else_expr)) => {
            // Fail closed (never `ite`-panic / ICE) when the two return paths carry
            // INCOMPATIBLE sorts — a malformed trust-ir lowering can give one path an
            // `i64`-typed constant and another an `i128` value (the transport lowering
            // mis-types `signed_min`'s `i128::MIN` literal), or a nested aggregate field
            // pair that is BV64 on one path and BV128 on the other. Delegate to ay's OWN
            // ite-compatibility predicate via `try_ite` (Bool cond + branch sorts
            // identical INCLUDING bitvec width) and decline the summary on any mismatch:
            // `Expr::sort()`'s `PartialEq` does NOT always distinguish bitvec widths, so a
            // manual `then_expr.sort() != else_expr.sort()` pre-check let a BV64-vs-BV128
            // pair reach `Expr::ite`, whose internal `.expect("… matching branch sorts")`
            // then ICE'd. `try_ite(...).ok()?` is the authoritative, panic-proof guard;
            // declining (havoc) is the sound conservative fallback.
            Expr::try_ite(guard, then_expr.clone(), else_expr).ok().map(ValueBinding::Scalar)
        }
        (ValueBinding::Aggregate(then_aggregate), ValueBinding::Aggregate(else_aggregate))
            if then_aggregate.fields.len() == else_aggregate.fields.len() =>
        {
            // Trust (#46): recurse so nested-aggregate fields are merged field-by-
            // field (not `ite`'d as if they were scalars).
            let mut fields = Vec::with_capacity(then_aggregate.fields.len());
            for (then_field, else_field) in then_aggregate.fields.iter().zip(else_aggregate.fields)
            {
                fields.push(combine_call_summary_binding(guard.clone(), then_field, else_field)?);
            }
            Some(ValueBinding::Aggregate(AggregateValue { fields }))
        }
        _ => None,
    }
}

fn bind_call_summary_result(
    values: &mut BTreeMap<ValueId, ValueBinding>,
    node: &InstrNode,
    binding: ValueBinding,
) -> Option<()> {
    values.insert(*node.results.first()?, binding);
    Some(())
}

#[cfg(test)]
mod narrowing_reachability_tests {
    use super::*;
    use trust_ir::value::FuncTyId;

    fn block(id: u32, terminator: Inst) -> Block {
        let mut block = Block::new(BlockId::new(id));
        block.body.push(InstrNode::new(terminator));
        block
    }

    fn function(entry: u32, blocks: Vec<Block>) -> Function {
        let mut function = Function::new(
            FuncId::new(0),
            "cfg_reachability",
            FuncTyId::new(0),
            BlockId::new(entry),
        );
        function.blocks = blocks;
        function
    }

    fn return_block(id: u32) -> Block {
        block(id, Inst::Return { values: Vec::new() })
    }

    #[test]
    fn invalid_source_and_target_are_unknown() {
        let function = function(0, vec![return_block(0)]);
        let missing = BlockId::new(99);
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, missing, BlockId::new(0)),
            CfgReachability::Unknown
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(0), missing),
            CfgReachability::Unknown
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, missing, missing),
            CfgReachability::Unknown,
            "from == to is not reachable authority when the block does not exist"
        );
    }

    #[test]
    fn dangling_successor_is_unknown() {
        let function = function(
            0,
            vec![
                block(0, Inst::Br { target: BlockId::new(99), args: Vec::new() }),
                return_block(1),
            ],
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(0), BlockId::new(1)),
            CfgReachability::Unknown
        );
    }

    #[test]
    fn missing_or_unsupported_terminator_is_unknown() {
        let empty = function(0, vec![Block::new(BlockId::new(0)), return_block(1)]);
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&empty, BlockId::new(0), BlockId::new(1)),
            CfgReachability::Unknown
        );

        let unterminated = function(
            0,
            vec![block(0, Inst::Const { ty: Ty::Bool, value: Constant::Int(1) }), return_block(1)],
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&unterminated, BlockId::new(0), BlockId::new(1)),
            CfgReachability::Unknown
        );
    }

    #[test]
    fn terminator_before_the_end_is_unknown() {
        let mut malformed = block(0, Inst::Br { target: BlockId::new(1), args: Vec::new() });
        malformed.body.push(InstrNode::new(Inst::Return { values: Vec::new() }));
        let function = function(0, vec![malformed, return_block(1)]);
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(0), BlockId::new(1)),
            CfgReachability::Unknown
        );
    }

    #[test]
    fn duplicate_block_identity_is_unknown() {
        let function = function(0, vec![return_block(0), return_block(0), return_block(1)]);
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(0), BlockId::new(1)),
            CfgReachability::Unknown
        );
    }

    #[test]
    fn cycles_terminate_and_can_still_prove_unreachable() {
        let function = function(
            0,
            vec![
                block(0, Inst::Br { target: BlockId::new(1), args: Vec::new() }),
                block(1, Inst::Br { target: BlockId::new(0), args: Vec::new() }),
                return_block(2),
            ],
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(0), BlockId::new(1)),
            CfgReachability::Reachable
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(0), BlockId::new(2)),
            CfgReachability::ProvenUnreachable
        );
    }

    #[test]
    fn complete_diamond_proves_sibling_unreachable() {
        let function = function(
            0,
            vec![
                block(
                    0,
                    Inst::CondBr {
                        cond: ValueId::new(0),
                        then_target: BlockId::new(1),
                        then_args: Vec::new(),
                        else_target: BlockId::new(2),
                        else_args: Vec::new(),
                    },
                ),
                return_block(1),
                return_block(2),
            ],
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(0), BlockId::new(2)),
            CfgReachability::Reachable
        );
        assert_eq!(
            ChcFuncTranslator::cfg_reaches(&function, BlockId::new(1), BlockId::new(2)),
            CfgReachability::ProvenUnreachable
        );
    }
}

// `is_eq_comparable_ty` / `is_ordered_scalar_ty` moved to `crate::translate`
// so the BMC lane's `eval_icmp` applies the SAME type gates as this lane.

fn is_order_comparable_ty(ty: &Ty, lhs: &Expr, rhs: &Expr) -> bool {
    is_ordered_scalar_ty(ty)
        && lhs
            .sort()
            .bitvec_width()
            .zip(rhs.sort().bitvec_width())
            .is_some_and(|(lhs_width, rhs_width)| lhs_width == rhs_width)
}

fn is_thin_pointer_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Ptr | Ty::PtrConst(_) | Ty::PtrMut(_) | Ty::Ref(_) | Ty::RefMut(_) | Ty::Rc(_))
}

/// Pointer-width unsigned integer at the pinned 64-bit target — the ONLY
/// integer spellings the usize<->pointer-newtype bit-identity legs admit.
fn is_pointer_width_unsigned_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::U64 | Ty::Usize)
}

/// Does the proof-grade lane have EXACT (bit-identity) semantics for this cast?
///
/// KEPT IN LOCKSTEP with the `Inst::Cast` legs in `translate_instruction` and
/// `eval_cast_expr`: every shape admitted here is translated value-preservingly
/// (never havoc, never an unconditional error rule). Consumed by the
/// trust-mc-driver proof-authority preflight, which refuses every other cast.
///
/// The admitted set beyond integer Trunc/ZExt/SExt (checked by the caller):
/// * `Bitcast`/`PtrToPtr` thin -> thin — identity on the BV64 address.
/// * `Bitcast` thin <-> single-pointer-NEWTYPE struct (`NonNull`/`Box`
///   wrap/unwrap) — the address leaf threads through unchanged.
/// * `Bitcast` usize/u64 <-> single-pointer-NEWTYPE struct (the
///   `fmt::Arguments` bit-packing) — same 64 bits, no validity asserted.
/// * `Bitcast`/`PtrToPtr` same-type fat -> fat — identity, metadata forwarded.
/// * `PtrToInt` thin -> usize/u64 — the address bits as an integer.
///
/// Deliberately NOT admitted: `IntToPtr` (a bare integer-to-`Ty::Ptr` forge has
/// no newtype structure to key on and stays on the refusal pin), fat-source
/// `PtrToInt`, width-changing `Bitcast` — including fat -> thin, whose honest
/// spelling is `Inst::PtrData` (the translator's fat->thin leg stays for the
/// diagnostic lane only; the module validator refuses the cast spelling) —
/// every float cast, and `Transmute`.
pub fn proof_grade_cast_is_admissible(
    module: &Module,
    op: CastOp,
    src_ty: &Ty,
    dst_ty: &Ty,
) -> bool {
    let newtype_path_of =
        |ty: &Ty| pointer_newtype_field_path(ty, module, POINTER_NEWTYPE_FUEL);
    let is_newtype_struct =
        |ty: &Ty| !is_thin_pointer_ty(ty) && newtype_path_of(ty).is_some_and(|p| !p.is_empty());
    match op {
        CastOp::Bitcast | CastOp::PtrToPtr => {
            let thin_thin = is_thin_pointer_ty(src_ty) && is_thin_pointer_ty(dst_ty);
            let fat_same = src_ty == dst_ty && matches!(src_ty, Ty::FatPtr(_));
            if matches!(op, CastOp::PtrToPtr) {
                return thin_thin || fat_same;
            }
            let thin_wrap = is_thin_pointer_ty(src_ty) && is_newtype_struct(dst_ty);
            let thin_unwrap = is_newtype_struct(src_ty) && is_thin_pointer_ty(dst_ty);
            let int_pack = is_pointer_width_unsigned_ty(src_ty) && is_newtype_struct(dst_ty);
            let int_unpack = is_newtype_struct(src_ty) && is_pointer_width_unsigned_ty(dst_ty);
            thin_thin || fat_same || thin_wrap || thin_unwrap || int_pack || int_unpack
        }
        CastOp::PtrToInt => {
            is_thin_pointer_ty(src_ty) && is_pointer_width_unsigned_ty(dst_ty)
        }
        _ => false,
    }
}

const POINTER_NEWTYPE_FUEL: u32 = 8;

/// A zero-sized marker field (`PhantomData`, `Unit`) — skipped when deciding
/// whether a struct is a single-pointer NEWTYPE. `PhantomData` lowers to an
/// empty-field `Struct`; `Unit` is `Ty::Unit`.
fn is_zero_sized_newtype_pad(ty: &Ty, module: &Module, fuel: u32) -> bool {
    if fuel == 0 {
        return false;
    }
    if matches!(ty, Ty::Unit) {
        return true;
    }
    match aggregate_field_tys_of(module, ty) {
        // an empty struct (PhantomData) or a struct whose every field is itself
        // zero-sized is a pad; a scalar/pointer leaf (`aggregate_field_tys_of`
        // returns None) is NOT a pad.
        Some(fields) => fields.iter().all(|f| is_zero_sized_newtype_pad(f, module, fuel - 1)),
        None => false,
    }
}

/// If `ty` is a single-pointer NEWTYPE struct (`Box`/`Unique`/`NonNull` and the
/// like — after stripping zero-sized pad fields, exactly one non-pad field that
/// recursively resolves to a thin pointer), return the chain of field indices
/// from `ty` down to the inner thin pointer (e.g. `Box -> [0,0,0]`,
/// `NonNull -> [0]`). Returns `None` (fail-closed) for anything else — a multi-
/// field struct, an enum, or a fat-pointer leaf — so a non-newtype transmute is
/// never modeled as a value-preserving pointer thread.
fn pointer_newtype_field_path(ty: &Ty, module: &Module, fuel: u32) -> Option<Vec<u32>> {
    if fuel == 0 {
        return None;
    }
    if is_thin_pointer_ty(ty) {
        return Some(Vec::new());
    }
    let field_tys = aggregate_field_tys_of(module, ty)?;
    let mut non_pad =
        field_tys.iter().enumerate().filter(|(_, f)| !is_zero_sized_newtype_pad(f, module, fuel));
    let (idx, inner) = non_pad.next()?;
    if non_pad.next().is_some() {
        return None; // more than one non-pad field — not a newtype
    }
    let mut path = pointer_newtype_field_path(inner, module, fuel - 1)?;
    path.insert(0, idx as u32);
    Some(path)
}

fn unsupported_value_reason(inst: &Inst) -> TrustIrChcUnsupportedReason {
    match inst {
        Inst::Cast { .. } => TrustIrChcUnsupportedReason::Cast,
        Inst::UnOp { .. } => TrustIrChcUnsupportedReason::UnaryOperation,
        Inst::ExtractField { .. } | Inst::ExtractElement { .. } => {
            TrustIrChcUnsupportedReason::AggregateProjection
        }
        Inst::InsertField { .. } | Inst::InsertElement { .. } => {
            TrustIrChcUnsupportedReason::AggregateUpdate
        }
        Inst::FCmp { .. } => TrustIrChcUnsupportedReason::FloatingPointComparison,
        Inst::LoadSlot { .. } => TrustIrChcUnsupportedReason::BindingFrameSlotLoad,
        _ => TrustIrChcUnsupportedReason::MalformedControlFlow,
    }
}

fn unsupported_unit_reason(inst: &Inst) -> TrustIrChcUnsupportedReason {
    match inst {
        Inst::Switch { .. } => TrustIrChcUnsupportedReason::Switch,
        Inst::CallIndirect { .. } => TrustIrChcUnsupportedReason::IndirectCall,
        Inst::Fence { .. } => TrustIrChcUnsupportedReason::Fence,
        Inst::EndBorrow { .. } => TrustIrChcUnsupportedReason::EndBorrow,
        Inst::Retain { .. } | Inst::Release { .. } => {
            TrustIrChcUnsupportedReason::ReferenceCounting
        }
        Inst::Dealloc { .. } => TrustIrChcUnsupportedReason::HeapDeallocation,
        Inst::CloseFrame { .. } => TrustIrChcUnsupportedReason::BindingFrameClose,
        Inst::DialectOp(_) => TrustIrChcUnsupportedReason::DialectOperation,
        _ => TrustIrChcUnsupportedReason::MalformedControlFlow,
    }
}

#[cfg(test)]
mod aggregate_leaf_budget_tests {
    //! Regression guard for the nested-array aggregate OOM introduced in `bd37bce4a`
    //! ("model array ExtractElement"). A trackable-but-deeply-nested fixed-size array
    //! was flattened into one CHC leaf per scalar with NO total-leaf cap (only a
    //! per-dimension `len <= 256` guard), so a value like `[[[u8; 256]; 256]; 256]`
    //! declared `256^3 ~= 16.7M` permanently-live CHC variables (`declare_var` per leaf,
    //! re-cloned at every relation application), exhausting RAM + swap — a kernel
    //! watchdog OOM panic. `MAX_AGGREGATE_LEAVES` now bounds the flattened leaf count;
    //! an over-budget aggregate is reported non-trackable and falls back to a single
    //! opaque scalar (fail closed — spurious-unverified, never a false proof).
    //!
    //! NOTE: this could not be executed in-session — the pinned `nightly-2025-12-03`
    //! toolchain ICEs while compiling `serde_derive v1.0.228`, which blocks every build
    //! of this crate. Re-run once that toolchain blocker is cleared.
    use super::*;
    use trust_ir_build::ModuleBuilder;

    /// `[[u8; 128]; 128]` = 16_384 leaves, over `MAX_AGGREGATE_LEAVES` (4096): the
    /// aggregate must be reported NON-trackable so it collapses to one opaque scalar
    /// rather than exploding the block-relation signature into 16_384 CHC variables.
    /// Pre-fix this returned `Some(..)` (and the full expansion is what OOM'd).
    #[test]
    fn nested_array_over_leaf_budget_is_not_trackable() {
        let mut mb = ModuleBuilder::new("agg_leaf_budget_over");
        let u8_ty = mb.add_type(Ty::U8);
        let row_ty = mb.add_type(Ty::Array(u8_ty, 128)); // [u8; 128]
        let module = mb.build();
        let matrix = Ty::Array(row_ty, 128); // [[u8; 128]; 128] = 16_384 leaves

        assert!(
            aggregate_field_tys_of(&module, &matrix).is_none(),
            "a 16_384-leaf nested array must fail closed via the leaf-count budget, \
             not expand into 16_384 permanently-declared CHC variables"
        );
    }

    /// A small nested array (`[[u8; 8]; 8]` = 64 leaves) is within budget: it must
    /// stay trackable and still expand into its immediate rows — the guard must not
    /// over-restrict ordinary small aggregates.
    #[test]
    fn small_nested_array_within_budget_stays_trackable() {
        let mut mb = ModuleBuilder::new("agg_leaf_budget_under");
        let u8_ty = mb.add_type(Ty::U8);
        let row_ty = mb.add_type(Ty::Array(u8_ty, 8)); // [u8; 8]
        let module = mb.build();
        let matrix = Ty::Array(row_ty, 8); // [[u8; 8]; 8] = 64 leaves

        let fields = aggregate_field_tys_of(&module, &matrix)
            .expect("a 64-leaf nested array stays trackable");
        assert_eq!(fields.len(), 8, "the outer array expands into its 8 immediate rows");
    }

    /// The flattened-leaf counter is inclusive at the cap and short-circuits without
    /// materializing the leaves: `[[u8; 64]; 64]` = exactly 4096 leaves stays trackable.
    #[test]
    fn leaf_budget_boundary_is_inclusive() {
        let mut mb = ModuleBuilder::new("agg_leaf_budget_boundary");
        let u8_ty = mb.add_type(Ty::U8);
        let row_ty = mb.add_type(Ty::Array(u8_ty, 64)); // [u8; 64]
        let module = mb.build();
        let at_cap = Ty::Array(row_ty, 64); // [[u8; 64]; 64] = 4096 == MAX_AGGREGATE_LEAVES

        assert_eq!(
            aggregate_leaf_count_within(&module, &at_cap, MAX_AGGREGATE_LEAVES),
            Some(MAX_AGGREGATE_LEAVES),
            "a 4096-leaf aggregate sits exactly at the inclusive cap (the guard rejects only `> cap`)"
        );
        assert!(
            aggregate_field_tys_of(&module, &at_cap).is_some(),
            "an at-cap aggregate is still trackable"
        );
    }
}

#[cfg(test)]
mod mem2reg_tests {
    //! mem2reg promotion: a loop-carried mutable scalar stack alloca used ONLY via
    //! direct Load/Store must become threaded block-relation state (so a loop
    //! predicate is no longer nullary), while any aliased alloca must be left
    //! un-promoted (soundness).
    use super::*;
    use trust_ir_build::ModuleBuilder;

    /// `fn count_to_ten() { let mut acc = 0; loop { if acc >= 10 break; acc += 1 }
    /// assert(acc >= 0) }` — a `let mut acc` mutated across a loop back-edge. The
    /// alloca's pointer is used only as Load/Store `ptr`, so it must be promoted
    /// and threaded through the loop-header relation, which the per-block stack
    /// reset would otherwise leave nullary.
    fn build_count_to_ten() -> (Module, ValueId, BlockId, BlockId, BlockId, BlockId) {
        let mut mb = ModuleBuilder::new("mem2reg_count_to_ten");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("count_to_ten", ft);

        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.set_entry(entry);

        // entry: acc = alloca; acc = 0; -> header
        fb.switch_to_block(entry);
        let acc = fb.alloca(Ty::I64);
        let zero = fb.iconst(Ty::I64, 0);
        fb.store(Ty::I64, acc, zero);
        fb.br(header, vec![]);

        // header: cur = load acc; if cur < 10 -> body else -> exit
        fb.switch_to_block(header);
        let cur = fb.load(Ty::I64, acc);
        let ten = fb.iconst(Ty::I64, 10);
        let cmp = fb.icmp(ICmpOp::Slt, Ty::I64, cur, ten);
        fb.condbr(cmp, body, vec![], exit, vec![]);

        // body: acc = load acc + 1; -> header (back edge)
        fb.switch_to_block(body);
        let cur2 = fb.load(Ty::I64, acc);
        let one = fb.iconst(Ty::I64, 1);
        let next = fb.add(Ty::I64, cur2, one);
        fb.store(Ty::I64, acc, next);
        fb.br(header, vec![]);

        // exit: assert(load acc >= 0); ret
        fb.switch_to_block(exit);
        let final_v = fb.load(Ty::I64, acc);
        let z2 = fb.iconst(Ty::I64, 0);
        let ge = fb.icmp(ICmpOp::Sge, Ty::I64, final_v, z2);
        fb.assert(ge);
        fb.ret(vec![]);
        fb.build();

        (mb.build(), acc, entry, header, body, exit)
    }

    #[test]
    fn promotes_loop_carried_scalar_alloca() {
        let (module, acc, entry, ..) = build_count_to_ten();
        let func = &module.functions[0];
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(func, &module, &options);

        let (promoted, def_block) = translator.compute_promotable_cells();

        assert_eq!(
            promoted.iter().map(|(v, _)| *v).collect::<Vec<_>>(),
            vec![acc],
            "the un-aliased `let mut acc` scalar cell must be the sole promoted alloca"
        );
        assert_eq!(
            def_block.get(&acc.index()),
            Some(&entry),
            "the promoted cell's def block is the entry block that alloca'd it"
        );
    }

    #[test]
    fn loop_header_relation_is_no_longer_nullary() {
        let (module, _acc, _entry, header, body, exit) = build_count_to_ten();
        let func = &module.functions[0];
        let options = TranslateOptions::default();
        let output = translate_function(func, &module, &options);

        // The function takes no parameters, so NOTHING is threaded except the
        // promoted cell. Pre-mem2reg every loop block relation was nullary; now the
        // header/body/exit relations each carry exactly the one promoted cell leaf.
        let arity = |name: &str| {
            output
                .vc
                .relations
                .iter()
                .find(|rel| rel.name == name)
                .unwrap_or_else(|| panic!("relation {name} must be declared"))
                .arity()
        };
        assert_eq!(
            arity(&block_relation_name(header)),
            1,
            "the loop-header relation must carry the promoted cell (was nullary)"
        );
        assert_eq!(arity(&block_relation_name(body)), 1, "the loop body carries the cell");
        assert_eq!(arity(&block_relation_name(exit)), 1, "the exit block reads the cell");
        assert_eq!(
            arity(&block_relation_name(func.entry)),
            0,
            "the def (entry) block does NOT receive the cell — it alloca's it fresh"
        );
        assert!(
            output.diagnostics.is_empty(),
            "the promoted-cell loop lowers with no unsupported diagnostics"
        );
    }

    /// An alloca whose pointer escapes is NOT promotable. This exercises every
    /// disqualification path from `compute_promotable_cells`: a GEP base, a compare
    /// operand, and a Store *value*. A control alloca used only via Load/Store in
    /// the same function must still be promoted, proving the analysis is a precise
    /// per-cell filter rather than an all-or-nothing bail-out.
    #[test]
    fn rejects_aliased_allocas() {
        let mut mb = ModuleBuilder::new("mem2reg_aliased");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("aliased", ft);

        let entry = fb.create_block();
        fb.set_entry(entry);
        fb.switch_to_block(entry);

        let promotable = fb.alloca(Ty::I64); // clean: only Load/Store below
        let gepd = fb.alloca(Ty::I64); // used as a GEP base
        let compared = fb.alloca(Ty::I64); // used as an ICmp operand
        let escaped = fb.alloca(Ty::I64); // its pointer stored as a Store value
        let sink = fb.alloca(Ty::Ptr); // receives the escaped pointer

        let zero = fb.iconst(Ty::I64, 0);
        fb.store(Ty::I64, promotable, zero);
        let _loaded = fb.load(Ty::I64, promotable);

        let idx = fb.iconst(Ty::I64, 0);
        let _addr = fb.gep(Ty::I64, gepd, vec![idx]); // gepd aliased
        let _eq = fb.icmp(ICmpOp::Eq, Ty::Ptr, compared, gepd); // compared aliased
        fb.store(Ty::Ptr, sink, escaped); // escaped aliased (stored as value)
        fb.ret(vec![]);
        fb.build();

        let module = mb.build();
        let func = &module.functions[0];
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(func, &module, &options);
        let (promoted, _def) = translator.compute_promotable_cells();
        let promoted_ids: std::collections::BTreeSet<u32> =
            promoted.iter().map(|(v, _)| v.index()).collect();

        assert!(
            promoted_ids.contains(&promotable.index()),
            "an alloca used only via Load/Store must still be promoted"
        );
        assert!(
            !promoted_ids.contains(&gepd.index()),
            "an alloca used as a GEP base is aliased — must NOT be promoted"
        );
        assert!(
            !promoted_ids.contains(&compared.index()),
            "an alloca used as a compare operand is aliased — must NOT be promoted"
        );
        assert!(
            !promoted_ids.contains(&escaped.index()),
            "an alloca whose pointer is stored as a Store value escaped — must NOT be promoted"
        );
    }
}
