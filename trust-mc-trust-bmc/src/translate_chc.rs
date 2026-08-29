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
use trust_ir::ty::{FatPtrKind, Ty};
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

impl TrustIrChcUnsupportedReason {
    /// Stable short label for this reason, for DIAGNOSTIC text only.
    ///
    /// The demotion message a demoted obligation carries says only "N
    /// unsupported trust_ir construct(s)"; the count reaches the transport but
    /// the typed reason did not, so there was no way to learn WHICH of these
    /// ~50 constructs blocked a given obligation without re-running the
    /// translator. This is the label the producer records alongside the count.
    ///
    /// Derived from the variant name via `Debug` deliberately: a hand-written
    /// match would silently start returning a wrong/placeholder label for a
    /// variant added later, whereas this cannot drift. NOTHING parses these
    /// strings — no verdict, gate or acceptance check reads them — so the only
    /// contract they carry is legibility.
    #[must_use]
    pub fn label(self) -> String {
        format!("{self:?}")
    }
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
    // R3 (cross-block owned-stack consistency): every `Alloca` RESULT id in the
    // WHOLE function, precomputed before block translation. SSA result ids are
    // function-unique and immutable, so "this id is the function's own stack
    // slot" is a block-independent fact — but `stack_ptrs`/`ptr_provenance` are
    // (correctly) per-block VALUE state and are cleared at each block entry,
    // which made an access through an alloca pointer from a LATER block (the
    // pervasive `let r = if c { … } else { … }` result-slot shape main's bridge
    // emits across blocks) fail closed as an unknown pointer. Seeding each
    // block's `stack_ptrs` + provenance ROOT from this set restores exactly the
    // same-block treatment: the ACCESS is a safe owned-slot access (never a
    // wild pointer), while the VALUE stays untracked across blocks — a
    // cross-block store is dropped and a cross-block load stays fresh-symbolic
    // (havoc ⊇ real: obligations depending on it can only become unknown /
    // refuted-under-abstraction, never falsely proved). The stale-cell guard is
    // untouched: precise cells still exist only in their defining block.
    func_alloca_ptrs: BTreeSet<ValueId>,
    // The declared type of each single-cell (`count: None`) alloca, so a
    // constant-lane `GEP` walk rooted at an alloca resolves in EVERY block
    // (`extend_exact_gep_lanes` sourced its root type from the per-block
    // `stack_cells`, which does not exist outside the defining block). Static
    // type information only — never a value fact.
    func_alloca_tys: BTreeMap<ValueId, Ty>,
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
    // invalidates them. The per-block discoveries are supplemented by
    // `function_escaped_bases`, which keeps promotion of a transparently derived
    // or call-escaping cell sound across block resets.
    escaped_cell_bases: BTreeSet<ValueId>,
    /// WHOLE-FUNCTION escape baseline, computed once and NEVER cleared per block.
    ///
    /// `escaped_cell_bases` above is per-block: it is cleared at every block boundary and
    /// repopulated as instructions are walked. That is exact while a tracked cell cannot
    /// outlive its def block — which is true only because
    /// `compute_promotable_cells` step 2 disqualifies every cell whose pointer is used by
    /// a `GEP` or a `Call`, so no ESCAPING cell is ever promoted and threaded.
    ///
    /// The moment promotion is widened to admit GEP-derived cells, that stops holding: a
    /// base that escaped into a call in block B1 is absent from the per-block set when B2
    /// is translated, so neither `invalidate_cells_escaping_into_call` nor
    /// `invalidate_store_targets` would fire in B2 — while the promoted value IS threaded
    /// into B2 via `block_promoted_cells`. That is a stale read across a block boundary,
    /// i.e. a false proof.
    ///
    /// So this baseline is the SOUNDNESS PREREQUISITE for widening promotion, and it is
    /// landed first and separately for exactly that reason. It is re-seeded into
    /// `escaped_cell_bases` at every block reset, which makes all three consumers
    /// function-aware through ONE change point rather than three.
    ///
    /// Strictly MORE invalidation than before ⇒ strictly weaker ⇒ sound. It can only turn
    /// a precise tracked value into a havoc, never the reverse.
    function_escaped_bases: BTreeSet<ValueId>,
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

/// R63 LANE TRACE (diagnostic only, env-gated, no verdict effect).
/// Set TRUST_LANE_TRACE=1 to learn WHICH fail-closed exit the interior-pointer lane read
/// takes on a real crate. R62 proved the cell is admitted AND promoted with the widening
/// on, yet the projected read still did not resolve -- so exactly one of these exits fires
/// and nothing in the log says which.
fn lane_trace(exit: &str) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *ON.get_or_init(|| std::env::var_os("TRUST_LANE_TRACE").is_some()) {
        eprintln!("R63_LANE_TRACE {exit}");
    }
}

/// R66: the same trace, but GATED to loads whose pointer is actually GEP-DERIVED, and
/// carrying the function name. R65's trace fired on EVERY `stack_cells` miss, so ordinary
/// provenance-free loads swamped the signal (2120 exit1 / 113 exit3) and neither survivor
/// could be quoted as a cause. This one only speaks about the case it was built for.
fn lane_trace_gep(exit: &str, is_gep_derived: bool, function: &str) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if is_gep_derived && *ON.get_or_init(|| std::env::var_os("TRUST_LANE_TRACE").is_some()) {
        eprintln!("R66_GEP_LANE {exit} fn={function}");
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
            func_alloca_ptrs: BTreeSet::new(),
            func_alloca_tys: BTreeMap::new(),
            valid_ref_ptrs: BTreeSet::new(),
            ptr_provenance: BTreeMap::new(),
            escaped_cell_bases: BTreeSet::new(),
            function_escaped_bases: BTreeSet::new(),
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
        // R3: precompute the function-scoped owned-stack-slot facts (see the
        // `func_alloca_ptrs` field doc). Pure instruction-syntax scan — result
        // ids and declared types only, no value state.
        for block in &self.func.blocks {
            for node in &block.body {
                if let Inst::Alloca { ty, count, .. } = &node.inst
                    && let Some(result) = node.results.first()
                {
                    self.func_alloca_ptrs.insert(*result);
                    if count.is_none() {
                        self.func_alloca_tys.insert(*result, ty.clone());
                    }
                }
            }
        }
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

        // mem2reg: promote single-cell allocas used through direct Load/Store and
        // narrowly guarded transparent derivations into a THREADED prefix of every
        // block relation, whose value is UPDATED by stores. This recovers loop-carried
        // mutable state
        // (`let mut acc`/`let mut count`) that the per-block `stack_cells` reset drops,
        // turning otherwise-nullary loop-block predicates into real threaded state.
        // A cell may be a precise scalar (one leaf) or a TRACKABLE AGGREGATE (one leaf
        // per flattened scalar leaf) — `promotable_cell_ty` decides, and it is exactly
        // the set `fresh_stack_cell_value` builds a tracked binding for.
        // `compute_live_params` is reused verbatim: a cell's Load/Store `ptr` operand
        // is collected exactly like a value use, so a cell is threaded into precisely
        // the blocks whose reachable code can Load/Store it (and never its def block,
        // which is excluded via `cell_def`). Threading it is exact — not an
        // over-approximation — because promotion rejects unbounded aliases and admits
        // only direct accesses plus explicitly modeled transparent derivations, whose
        // threaded binding remains the cell's complete modeled value.
        // Whole-function escape baseline — computed BEFORE any block is translated, so it
        // is available in every block including ones translated before the escape's own
        // block. Any alloca whose classification is not `Contained` has its address reach
        // something we do not model away, so it is permanently invalidation-eligible.
        // `Unbounded` cells are never tracked at all, so in practice this carries the
        // `IntoCallsOnly` ones; including both keeps the predicate conservative and means
        // a future change to the admission rules cannot silently un-invalidate a cell.
        self.function_escaped_bases = self
            .func
            .blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .filter(|node| matches!(&node.inst, Inst::Alloca { .. }))
            .filter_map(|node| node.results.first().copied())
            .filter(|result| {
                stack_alloca_escape_classification(self.func, *result) != StackCellEscape::Contained
            })
            .collect();

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
            // dead cells (no reachable Load/Store) are dropped. A promoted cell
            // flattens to ONE relation leaf when it is a precise scalar and to one
            // leaf per flattened scalar leaf when it is a trackable aggregate —
            // `declare_relation_binding_rec` recurses, and `ValueBinding::flat_args`
            // (used by `block_app` and `add_transition_rule`) walks the identical
            // depth-first order, so the formal signature and every application stay
            // leaf-aligned.
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

    /// mem2reg candidate analysis: find single-cell allocas whose result pointer is
    /// NEVER aliased, so their current value can be threaded through block relations
    /// (like an SSA param, but updated by stores) exactly.
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
    ///
    /// The candidate's cell TYPE is restricted only by `promotable_cell_ty` — a
    /// precise scalar or a trackable aggregate, one relation leaf per flattened
    /// scalar leaf. The argument above never inspects the cell's shape: because the
    /// pointer is un-aliased and every access is a WHOLE-CELL, exact-type Load/Store
    /// (a field projection needs a `GEP`, whose `base` use disqualifies the
    /// candidate), the cell's value is a pure function of the Store sequence for an
    /// aggregate exactly as it is for a scalar. Enums are excluded by
    /// `promotable_cell_ty` — see its doc.
    fn compute_promotable_cells(
        &self,
    ) -> (Vec<(ValueId, Ty)>, std::collections::BTreeMap<u32, BlockId>) {
        compute_promotable_cells_of(self.module, self.func)
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
        // Re-seed, do NOT clear to empty: the whole-function baseline must survive
        // every block boundary or invalidation cannot fire for a threaded cell.
        self.escaped_cell_bases = self.function_escaped_bases.clone();
        // R3 (cross-block owned-stack consistency): re-seed every block with the
        // block-independent fact "these SSA ids are the function's own stack
        // slots" — exactly what `translate_alloca` records in the defining
        // block. This restores the same-block treatment for an access reaching
        // the alloca from a later block: the ACCESS is safe (owned slot, so no
        // fail-closed memory/pointer-arithmetic error), while the VALUE stays
        // untracked (`stack_cells` is not seeded — a cross-block store is
        // dropped and a cross-block load havocs to fresh-symbolic; havoc ⊇ real,
        // never a false proof). Runs AFTER the clears and BEFORE the mem2reg
        // seeding below, whose promoted cells overwrite compatibly.
        //
        // DELIBERATELY NOT seeded: `ptr_provenance`. Pre-populating provenance
        // roots would make `record_interior_pointer_escapes`' conservative
        // "reads not statically enumerable ⇒ every interior pointer escaped"
        // arm fire from the first instruction of every block (provenance would
        // never be empty), demoting precisely-tracked same-block cells that the
        // baseline kept exact. Cross-block GEP chains instead recover their
        // root at the GEP itself (see the alloca-root fallback there), which
        // enters provenance only when a derivation actually occurs — the same
        // point the defining block enters it.
        for alloca in self.func_alloca_ptrs.clone() {
            self.stack_ptrs.insert(alloca);
        }
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
                // R60: re-seed the PROVENANCE ROOT too, not just the value and the
                // owned-slot fact.
                //
                // `ptr_provenance` is cleared at every block boundary and re-established
                // only by `translate_alloca`, which runs in the DEF BLOCK. So a threaded
                // cell arrives here with its value and its `stack_ptrs` membership intact
                // but with NO provenance — and a `GEP` on it in this block therefore
                // resolves to nothing, the interior-pointer read cannot find the cell, and
                // it havocs. That is the mechanical reason a cross-block field projection
                // cannot be modelled today, and it is why the cross-block bucket
                // (`store_/load_in_other_block`, 221 rows at R59, 181 of them
                // aggregate-typed) is unreachable rather than merely unattempted.
                //
                // SOUNDNESS. This asserts exactly what `translate_alloca` asserts in the
                // def block: the cell is its own provenance root at the empty lane path.
                // It is a TRUE fact about a cell that `compute_promotable_cells` has
                // already proved un-aliased — promotion is granted only to cells with no
                // escaping use, so no other pointer can be a provenance root for it. It
                // adds no admission and no discharge; it only lets a read that the model
                // already threads resolve to the value it already carries.
                //
                // Count-inert on its own: promotion still disqualifies any cell with a
                // `GEP` use, so no projected cell is threaded yet. This lands FIRST and
                // ALONE as the prerequisite, exactly as `invalidate_cells_escaping_into_call`
                // and `function_escaped_bases` did — the widening that consumes it is a
                // separate change with its own soundness argument.
                self.ptr_provenance
                    .insert(*cell, PtrProvenance { base: *cell, lanes: Some(Vec::new()) });
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
        self.invalidate_cells_escaping_into_call(&node.inst);
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
                // `resolve` is not type-checked: malformed TrustIR can bind an arm to a
                // different carrier (Bool vs BV, or incompatible float widths). Width
                // normalization repairs valid integer width drift, but deliberately
                // leaves incompatible carriers unchanged. Check both arms exactly and
                // use AY's panic-proof constructor before accepting the Select.
                let then_expr =
                    normalize_expr_to_exact_ty(&self.resolve(*then_val, ty), ty);
                let else_expr =
                    normalize_expr_to_exact_ty(&self.resolve(*else_val, ty), ty);
                let selected = match (then_expr, else_expr) {
                    (Some(then_expr), Some(else_expr)) => {
                        Expr::try_ite(cond_expr, then_expr, else_expr).ok()
                    }
                    _ => None,
                };
                let Some(selected) = selected else {
                    let result = self.fresh_symbolic("unsupported_result", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::MalformedControlFlow,
                        from,
                        path_constraints,
                    );
                    return false;
                };
                self.bind_first_result(node, selected);
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
                    // R3 (cross-block owned-stack consistency): a GEP whose base
                    // is one of the FUNCTION's own alloca results but has no
                    // per-block provenance entry (the alloca lives in an earlier
                    // block) roots a fresh provenance chain here — exactly the
                    // {base, whole-cell} root `translate_alloca` records in the
                    // defining block. Static SSA-identity fact only; entering
                    // provenance at the derivation site (not block entry) keeps
                    // `record_interior_pointer_escapes`' emptiness fast-path and
                    // its conservative escape accounting byte-identical for
                    // blocks that never touch an alloca interior.
                    let base_provenance = self.ptr_provenance.get(base).cloned().or_else(|| {
                        self.func_alloca_ptrs
                            .contains(base)
                            .then(|| PtrProvenance { base: *base, lanes: Some(Vec::new()) })
                    });
                    if let Some(base_provenance) = base_provenance
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
            Inst::PtrMetadata { ptr_ty, metadata_ty, ptr } => {
                let metadata = if let Some((_, metadata)) = self.ptr_parts.get(ptr) {
                    metadata.clone()
                } else if matches!(metadata_ty, Ty::Unit) {
                    Expr::true_()
                } else if matches!(metadata_ty, Ty::U64) {
                    // A slice/str fat-pointer's metadata is its element/byte LENGTH
                    // (usize == U64). Model it as a symbolic instead of an opaque
                    // unsupported value, so the CHC/PDR lane can prove obligations over
                    // `s.len()` — e.g. `s.len() + 1` no-overflow and
                    // `while i < s.len() { i += 1 }`. Gated to `U64` so a `dyn Trait`
                    // vtable pointer (Ty::Ptr) is NOT mis-bounded — it keeps the
                    // opaque-unsupported path below.
                    //
                    // Trust (P0 ZST-slice-length FALSE PROOF): the `len <= isize::MAX`
                    // upper bound is a theorem ONLY when the element is provably NON-ZST.
                    // `isize::MAX` caps the total BYTE size, so it caps the ELEMENT count
                    // only via `size_of::<T>() >= 1`. A ZERO-sized element breaks that
                    // step: `[(); usize::MAX]` occupies 0 bytes, so a `&[()]` length may
                    // legally reach `usize::MAX`. The bound used to be pushed for EVERY
                    // U64 metadata, which false-PROVED
                    //
                    //     pub fn f(z: &[()]) -> usize { z.len() + 1 }
                    //
                    // no-overflow (`len <= isize::MAX` ⟹ `len + 1` fits), while
                    // `let v: Vec<()> = vec![(); usize::MAX]; f(&v)` really overflows.
                    // `fat_ptr_metadata_len_is_isize_bounded` therefore admits the bound
                    // only for `str` (a BYTE length — every byte is 1 byte) and for a
                    // slice whose element type is PROVABLY non-ZST, mirroring the three
                    // sibling gates (`trust_vcgen::build_len_call_bound_facts` /
                    // `nonzst_slice_len_vars`, the bridge's
                    // `conjoin_native_slice_len_bounds`, and the `str`-vs-slice split in
                    // `trust_types::total_call_summaries`). Every other shape keeps an
                    // UNCONSTRAINED symbolic — a sound over-approximation (the free value
                    // ranges over all of `u64` ⊇ the realizable lengths), so an
                    // obligation over a ZST length stays unknown/refuted, never proved.
                    //
                    // With the bound present the modeling is still exact in both
                    // directions: the length is a genuine free value and EVERY value in
                    // [0, isize::MAX] is a realizable length for a non-ZST element.
                    //
                    // DETERMINISTIC per SSA value (`ptr_metadata_syms`): metadata is a
                    // function of the fat value, so repeated reads of the SAME `ValueId`
                    // reuse one symbol. A producer-asserted exact length therefore binds
                    // every later read of that value. The conditional bound is pushed at
                    // EVERY read site because path constraints are per-clause, not
                    // per-symbol.
                    let metadata = match self.ptr_metadata_syms.get(ptr) {
                        Some(existing) => existing.clone(),
                        None => {
                            let fresh = self.fresh_symbolic("slice_len", metadata_ty);
                            self.ptr_metadata_syms.insert(*ptr, fresh.clone());
                            fresh
                        }
                    };
                    if fat_ptr_metadata_len_is_isize_bounded(self.module, ptr_ty) {
                        let isize_max = Expr::bitvec_const(i64::MAX as i128, 64);
                        path_constraints.push(metadata.clone().bvule(isize_max));
                    }
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
                if let Some((src_val, result)) = self.eval_cast(*op, src_ty, dst_ty, *operand) {
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
                        // `src_val` is the operand already coerced to `src_ty`'s carrier
                        // by `eval_cast`, so it is EXACTLY `src_w` bits and `reext` below
                        // — `dst_w` kept bits re-extended by `src_w - dst_w` — matches it
                        // by construction. Re-resolving the raw binding here instead
                        // compared a `BitVec 128` against a `BitVec 64` and tripped
                        // `Expr::eq`'s same-sort contract.
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
            // An array/vector element WRITE. The symmetric counterpart of the
            // `InsertField` arm above (struct/tuple field write): TrustIR
            // `InsertElement` is a PURE functional update — it READS `array` and
            // BINDS A NEW SSA result; the source value's binding is never mutated
            // (`trust_ir::interpret::eval_insert_element` clones before assigning).
            // So there is no in-place location whose tracked value a model could
            // leave stale; the only thing that must be right is the RESULT binding.
            //
            // Before this arm existed, EVERY `InsertElement` fell into the
            // fail-closed bucket below and emitted an UNCONDITIONALLY REACHABLE
            // error rule, which makes every obligation in the enclosing function
            // unprovable by construction — even though the READ side
            // (`ExtractElement`) has long been modeled without failing closed and
            // a `[T; N <= 256]` is already a fully trackable N-field aggregate
            // (`immediate_aggregate_field_tys`). The pervasive shape this blocks is
            // the `[core::fmt::rt::Argument; N]` array every `format!`/`write!`
            // builds: one `InsertElement` at a CONSTANT index per format argument.
            Inst::InsertElement { ty, array, index, value } => {
                if let Some(result) = self.eval_insert_element(ty, *array, *index, *value) {
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
            Inst::FCmp { ty: dst_ty, .. } | Inst::LoadSlot { ty: dst_ty, .. } => {
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
                // R3: a borrow of one of the FUNCTION's own allocas from a block
                // other than the defining one roots the same {base, whole-cell}
                // provenance the defining block would have inherited (see the GEP
                // arm's alloca-root fallback for the rationale and scope).
                let provenance = self.ptr_provenance.get(ptr).cloned().or_else(|| {
                    self.func_alloca_ptrs
                        .contains(ptr)
                        .then(|| PtrProvenance { base: *ptr, lanes: Some(Vec::new()) })
                });
                if let Some(provenance) = provenance
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
        // Trust (Fix a): DEMOTE a precisely-trackable cell to OPAQUE — leave the
        // pointer in `stack_ptrs` (inserted above) but record NO `stack_cell` — when
        // its pointer ESCAPES or its direct Load/Store accesses are type-inconsistent.
        // Either condition would let a hidden write through an ALIAS, or a
        // silently-dropped mismatched-type Store, leave the tracked value STALE, so a
        // later same-type Load would read a fabricated value (a FALSE PROOF). With no
        // `stack_cell`, every later Load misses (`translate_stack_load` returns `false`)
        // and havocs to a fresh symbolic while `known_stack` suppresses the memory
        // error, and every later Store misses and is dropped (havoc ⊇ real) — an
        // UNCONDITIONAL sound over-approximation. A promoted cell is type-consistent and
        // never `Unbounded` by construction. `Contained` cells stay precise;
        // `IntoCallsOnly` cells stay tracked but are havoced at every call. Thus the
        // guard does not demote a threaded cell without its promotion analysis already
        // refusing it. Removes facts only — a previously-lenient proof that relied on
        // tracking an escaping cell now becomes UNKNOWN (sound), never a false proof.
        //
        // NARROWED (half 2 of the provenance model). The escape half of this guard is
        // now `stack_alloca_escape_classification`, which walks the GEP/Borrow
        // derivation closure instead of testing the alloca id alone. `Unbounded` still
        // demotes exactly as before. `IntoCallsOnly` is admitted, and is sound ONLY
        // because `invalidate_cells_escaping_into_call` havocs the cell at every call
        // its pointer reaches — precise before the call, havoc after. The two halves
        // must never be separated; admitting this without that invalidation is a
        // completed false proof.
        //
        // The strictly-conservative `stack_alloca_pointer_is_non_escaping` is left
        // untouched and still exported, because the driver gate's contract text names
        // it. `Contained` implies it; the added coverage is precisely the GEP/Borrow
        // derivations it counted as escapes despite
        // `record_interior_pointer_escapes` treating those same positions as TRACKED.
        // The type-match half is unchanged: it guards a different false proof (a
        // silently-dropped mismatched-type Store leaving a stale value).
        if matches!(
            stack_alloca_escape_classification(self.func, result),
            StackCellEscape::Unbounded
        ) || !stack_alloca_cell_accesses_match_type(self.func, result, ty)
        {
            return;
        }
        self.stack_cells.insert(result, StackCell { ty: ty.clone(), value });
    }

    /// R66: is `ptr` the RESULT of a `GEP`? Used only to gate the diagnostic trace so
    /// ordinary provenance-free loads stop swamping the signal. No verdict effect.
    fn ptr_is_gep_derived(&self, ptr: ValueId) -> bool {
        self.func.blocks.iter().flat_map(|b| b.body.iter()).any(|n| {
            matches!(&n.inst, Inst::GEP { .. }) && n.results.iter().any(|r| *r == ptr)
        })
    }

    fn translate_stack_load(&mut self, ty: &Ty, ptr: ValueId, node: &InstrNode) -> bool {
        let Some(cell) = self.stack_cells.get(&ptr).cloned() else {
            // R63: INTERIOR-POINTER LANE READ — the mirror of the store side.
            //
            // This lookup is keyed by the LOAD's `ptr` operand, which for a GEP-derived
            // pointer is the GEP RESULT, not the cell base. So a field read through
            // `&s.a` missed here and havoced, even for a cell that is tracked and (once
            // promoted) threaded. Stores through interior pointers have had a precise
            // lane since the provenance work (`model_indirect_store` / `store_cell_lane`,
            // pinned by `field_store_through_borrow_is_modeled_precisely`); LOADS had
            // none. That asymmetry — not the admission gate, not the promotion candidate
            // set (R62 proved both fine) — is what blocked the cross-block projected read.
            //
            // SOUNDNESS. This is an ADDITION on the exactly-resolving path only; every
            // other case still falls through to `return false`, which havocs, exactly as
            // before. `lanes` is `Some` only when `extend_exact_gep_lanes` resolved every
            // step to a CONSTANT field index with a matching type — `None` means an
            // unknown offset and is refused here. The extracted leaf's type must equal the
            // load type, so a mismatched-width or wrong-field read cannot borrow a leaf it
            // does not name. It reads a value the model already carries; it cannot
            // manufacture one.
            let Some(provenance) = self.ptr_provenance.get(&ptr).cloned() else {
                lane_trace("exit1_no_provenance");
                lane_trace_gep("exit1_no_provenance", self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            };
            let Some(lanes) = provenance.lanes else {
                lane_trace("exit2_lanes_none");
                lane_trace_gep("exit2_lanes_none", self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            };
            // Exactly one constant lane: a nested path is not modelled here, and the
            // empty path is the whole cell, which the direct lookup above already covers.
            let [(field, field_ty)] = lanes.as_slice() else {
                let e3 = if lanes.is_empty() { "exit3a_empty_path" } else { "exit3b_nested_chain" };
                lane_trace(e3);
                lane_trace_gep(e3, self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            };
            if field_ty != ty {
                lane_trace("exit4_field_ty_mismatch");
                lane_trace_gep("exit4_field_ty_mismatch", self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            }
            let Some(base_cell) = self.stack_cells.get(&provenance.base).cloned() else {
                lane_trace("exit5_base_not_tracked");
                lane_trace_gep("exit5_base_not_tracked", self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            };
            let ValueBinding::Aggregate(aggregate) = base_cell.value else {
                lane_trace("exit6_base_not_aggregate");
                lane_trace_gep("exit6_base_not_aggregate", self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            };
            let Some(leaf) = aggregate.fields.get(*field).cloned() else {
                return false;
            };
            match leaf {
                ValueBinding::Scalar(expr) => self.bind_first_result(node, expr),
                ValueBinding::Aggregate(nested) => {
                    self.bind_aggregate_result(node, nested, ty)
                }
            }
            return true;
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
    ///
    /// SIGNEDNESS: a `BitVecConst` carries the RAW UNSIGNED bitvector, so a
    /// negative signed constant reads back WRAPPED — `-1i8` arrives as `255`.
    /// Taking that at face value names a DIFFERENT lane than the program does,
    /// and a negative lane index is undefined behaviour in the reference
    /// semantics anyway (`trust-ir :: interpret.rs :: runtime_index` rejects
    /// `int.signed && int.as_signed() < 0`). Worse, a wrapped index can land back
    /// IN BOUNDS — `-1i8` -> lane 255 of a `[T; 256]` — so the caller's
    /// bounds check is not a backstop for it.
    ///
    /// Requiring the TOP BIT to be CLEAR makes the signed and unsigned readings
    /// provably agree, so this stays correct without consulting the index's
    /// declared type (which this layer does not have). Declining is FAIL-CLOSED at
    /// both call sites: the element-write path keeps its unconditional
    /// `AggregateUpdate` error rule and the GEP path records an unknown offset.
    fn constant_lane_index(&self, index: ValueId) -> Option<usize> {
        match self.values.get(&index)?.value() {
            ay_bindings::ExprValue::BitVecConst { value, width } => {
                if value.bits() >= u64::from(*width) {
                    return None;
                }
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
        // R3: the lane walk's ROOT type is static declaration information. Source
        // it from the per-block cell when one exists (byte-identical to before),
        // else from the function-scoped alloca type map so a constant-lane chain
        // rooted at an alloca resolves in EVERY block, not only the defining one.
        // The walk itself is unchanged: every step still demands exact layout
        // evidence, and any uncertainty keeps `lanes: None` (fail-closed).
        let mut lane_ty = match self.stack_cells.get(&base) {
            Some(cell) => cell.ty.clone(),
            None => self.func_alloca_tys.get(&base)?.clone(),
        };
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
    /// CALL-INVALIDATION. A tracked cell whose interior pointer reaches a CALL must be
    /// havoc'd at that call, because the callee may write through it.
    ///
    /// THE HOLE THIS CLOSES. `record_interior_pointer_escapes` already records call
    /// arguments — `Inst::Call` takes its `_ => uses` arm, so the escaped base lands in
    /// `escaped_cell_bases`. But that set had only TWO consumers,
    /// `invalidate_store_targets` and `store_target_cell_survives`, and BOTH are reached
    /// solely from the `Store`/`AtomicStore` path. So the escape was recorded and then
    /// acted on only if an unrelated indirect store happened to follow. For
    /// `f(&mut local)` with no intervening unknown store, the next `Load` returned the
    /// tracked PRE-CALL value: a stale read of memory the callee may have overwritten.
    /// That is a completed false proof, and it is why the coarse whole-function escape
    /// guard in `translate_alloca` could not simply be narrowed — that guard was the only
    /// thing covering this.
    ///
    /// SOUNDNESS. Invalidation is `fresh_stack_cell_value` — an unconstrained havoc, or
    /// removal of the cell when the type has no trackable value. It only ever REMOVES
    /// facts, so a proof that previously relied on a stale post-call value now becomes
    /// UNKNOWN. It cannot manufacture one. This is deliberately independent of whether the
    /// callee is bundled, proven, or absent: an unproven or absent callee is exactly the
    /// case where we know least about what it wrote.
    ///
    /// `CallIndirect` is included: an unresolved target is strictly less known than a
    /// resolved one.
    fn invalidate_cells_escaping_into_call(&mut self, inst: &Inst) {
        if !matches!(inst, Inst::Call { .. } | Inst::CallIndirect { .. }) {
            return;
        }
        if self.escaped_cell_bases.is_empty() || self.stack_cells.is_empty() {
            return;
        }
        // Collect first: `invalidate_stack_cell` takes `&mut self`.
        let escaped: Vec<ValueId> = self
            .escaped_cell_bases
            .iter()
            .copied()
            .filter(|base| self.stack_cells.contains_key(base))
            .collect();
        for base in escaped {
            self.invalidate_stack_cell(base);
        }
    }

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
                        // Decline the summary when malformed TrustIR gives either arm
                        // an incompatible carrier. The caller then takes the existing
                        // fail-closed UnsupportedDirectCallSummary path.
                        let then_expr = normalize_expr_to_exact_ty(
                            &call_summary_scalar(&state.locals, *then_val)?,
                            ty,
                        )?;
                        let else_expr = normalize_expr_to_exact_ty(
                            &call_summary_scalar(&state.locals, *else_val)?,
                            ty,
                        )?;
                        let selected = Expr::try_ite(cond_expr, then_expr, else_expr).ok()?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            ValueBinding::Scalar(selected),
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

    /// EXACT model of an array/vector element WRITE, the element-index analogue of
    /// [`Self::eval_insert_field`]. `Some` is returned ONLY when the update can be
    /// expressed exactly; the caller keeps the pre-existing FAIL-CLOSED path
    /// (an unconditionally reachable error rule) for `None` — deliberately NOT a
    /// havoc that would forget the write.
    ///
    /// Exactness requires ALL of:
    /// * `ty` — which TrustIR fixes to be the ARRAY's own type, not the element's
    ///   (`trust_ir::interpret::eval_insert_element` starts with
    ///   `expect_ty(array, result_ty)`) — is a trackable aggregate. For `[T; N]`
    ///   with `N <= 256` `immediate_aggregate_field_tys` already yields N copies of
    ///   `T`, and `aggregate_field_tys` additionally enforces the flattened-leaf
    ///   budget.
    /// * the index is a COMPILE-TIME CONSTANT. A symbolic index names an unknown
    ///   lane, for which "copy the aggregate and replace field i" is simply the
    ///   WRONG model (it would leave every other lane readable as its old value
    ///   while the real write could have landed on any of them), so it fails closed.
    /// * that constant is IN BOUNDS. An out-of-bounds element write is TrustIR
    ///   undefined behaviour (the interpreter raises `UndefinedBehavior`); there is
    ///   no defined result to model, so it fails closed.
    /// * the source array resolves to an aggregate binding of matching arity.
    ///
    /// Soundness of the exact arm rests on TrustIR `InsertElement` being a PURE
    /// functional update — the result is a fresh SSA value and the source array
    /// value keeps its own (still correct) binding — so modeling it cannot leave a
    /// stale value readable through any surviving name.
    fn eval_insert_element(
        &mut self,
        ty: &Ty,
        array: ValueId,
        index: ValueId,
        value: ValueId,
    ) -> Option<AggregateValue> {
        let field_tys = self.aggregate_field_tys(ty)?;
        let element_index = self.constant_lane_index(index)?;
        let element_ty = field_tys.get(element_index)?.clone();
        let mut result = self.resolve_aggregate(array, ty)?;
        if result.fields.len() != field_tys.len() {
            return None;
        }
        result.fields[element_index] = if is_scalar_field_ty(&element_ty) {
            ValueBinding::Scalar(self.resolve(value, &element_ty))
        } else {
            ValueBinding::Aggregate(self.resolve_aggregate(value, &element_ty)?)
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

    /// Resolve `operand` into the carrier its DECLARED `src_ty` names (see
    /// [`cast_operand_in_src_carrier`]) and apply the cast.
    ///
    /// Returns `(src_in_declared_carrier, result)`. Handing the coerced source back is
    /// load-bearing: the caller's lossless-narrowing obligation MUST be built from the
    /// same expression the result was derived from. Re-`resolve`-ing the operand there
    /// re-introduced the raw, possibly wrong-width binding — which is exactly how the
    /// `EQ requires same sort` abort happened.
    fn eval_cast(
        &mut self,
        op: CastOp,
        src_ty: &Ty,
        dst_ty: &Ty,
        operand: ValueId,
    ) -> Option<(Expr, Expr)> {
        let operand = self.resolve(operand, src_ty);
        let operand = cast_operand_in_src_carrier(src_ty, operand)?;
        let result = eval_cast_expr(op, src_ty, dst_ty, operand.clone())?;
        Some((operand, result))
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

/// Coerce a cast operand into the carrier its DECLARED `src_ty` names.
///
/// `ChcFuncTranslator::resolve` returns whatever expression is currently BOUND to a
/// value id; it is not width-typed, so the binding can carry a different bitvector
/// width than the type the consuming instruction declares for that operand (a u64
/// limb read out of a u128 intermediate is the shape `num-bigint`/`num-traits`
/// exercises). Every other operand consumer in this file already re-establishes the
/// declared carrier with `normalize_expr_to_ty` before use — `translate_integer_binop`,
/// `eval_binop`, `eval_icmp`, `integer_binop_no_overflow_condition` and the `UnOp::Neg`
/// arms all do. `Inst::Cast` was the sole omission, with two consequences:
///
///   * the lossless-narrowing obligation compared the RAW binding against a
///     re-extension built at `src_ty`'s width, violating `Expr::eq`'s
///     `REQUIRES: identical sorts` and aborting trustc with
///     `EQ requires same sort: ... (_ BitVec 128) and (_ BitVec 64)`; and
///   * a widening `ZExt`/`SExt` off an over-wide binding silently produced an
///     OVER-WIDE result (`zero_extend` of a 128-bit carrier by `dst - src = 64`
///     bits yields 192 bits) that was then bound to a `dst_ty`-typed value.
///
/// The extension direction is taken from `src_ty`'s SIGNEDNESS (`normalize_expr_to_ty`
/// picks `sign_extend` for a signed type and `zero_extend` otherwise) — the one place
/// that information exists. `Expr::eq` must never be "fixed" by widening inside the
/// binding layer: it cannot know the signedness, and guessing changes the meaning of
/// the comparison.
///
/// Narrowing an OVER-wide binding takes the low `width(src_ty)` bits. That is the only
/// reinterpretation consistent with the operand's declared MIR type — a value of type
/// `src_ty` has its meaning in those bits under both extension conventions — and it is
/// already the semantics the cast RESULT commits to (`eval_cast_expr`'s `Trunc` arm
/// extracts `dst_ty`'s low bits from whatever carrier it is handed). Unifying here only
/// makes the obligation agree with the value the same call already produces.
///
/// Returns `None` — an honest UNKNOWN via the caller's `TrustIrChcUnsupportedReason::Cast`
/// fail-closed path — when width normalization CANNOT reconcile the sorts, i.e. when
/// the disagreement is not a bitvector-width disagreement at all: a Bool-sorted binding
/// under an integer `src_ty`, an integer-sorted binding under `Ty::Bool`, or a float
/// `src_ty` (where `normalize_expr_to_ty` deliberately refuses to fabricate bits,
/// because f32<->f64 re-biases the exponent and is NOT zero-extension or truncation of
/// the bit pattern). Each of those previously panicked inside the `Expr` contract or
/// bound a wrong-sorted result; a lost proof is the correct trade.
fn cast_operand_in_src_carrier(src_ty: &Ty, operand: Expr) -> Option<Expr> {
    let coerced = normalize_expr_to_ty(&operand, src_ty);
    (*coerced.sort() == ty_to_sort(src_ty)).then_some(coerced)
}

fn eval_cast_expr(op: CastOp, src_ty: &Ty, dst_ty: &Ty, operand: Expr) -> Option<Expr> {
    // Re-establish `src_ty`'s carrier before ANY width arithmetic below: every arm
    // derives its widths from the TYPES, so an operand whose binding disagrees would
    // otherwise be extended/extracted against the wrong base width. Idempotent when the
    // operand already matches, so a well-formed cast is unaffected.
    let operand = cast_operand_in_src_carrier(src_ty, operand)?;
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

/// Proof-authority admission class for a single-cell (`count: None`) stack `Alloca`,
/// mirroring `translate_alloca`'s (translate_chc.rs) tracked-vs-opaque decision EXACTLY.
///
/// - `OpaqueSafe`: the translator leaves the cell opaque — `fresh_stack_cell_value`
///   returns `None`, so `translate_alloca` records the pointer in `stack_ptrs` but NOT
///   `stack_cells`. A later Load then misses `stack_cells` (`translate_stack_load`
///   returns `false`) and havocs to a fresh symbolic while `known_stack` suppresses the
///   memory-access error; a later Store likewise misses and is dropped. This is an
///   UNCONDITIONAL sound over-approximation (havoc ⊇ real), so no escape/volatile
///   reasoning is required.
/// - `RequiresNonEscape`: the translator tracks the cell's fields precisely
///   (`aggregate_field_tys_of` is `Some`, so `fresh_stack_cell_value` builds a
///   `ValueBinding::Aggregate` and `translate_alloca` inserts a `stack_cell`). A later
///   Load returns the precisely tracked last-stored value. This is sound ONLY if BOTH
///   (a) the cell pointer never escapes ([`stack_alloca_pointer_is_non_escaping`]) — else
///   a write through an alias leaves the tracked value stale — AND (b) every direct
///   Load/Store of it uses the cell type ([`stack_alloca_cell_accesses_match_type`]) —
///   else a silently-dropped mismatched-type store leaves the tracked value stale. Either
///   staleness lets a dependent Load read a fabricated value (a FALSE PROOF).
/// - `NotAggregate`: `ty` is a scalar/other shape this classifier does not own (the
///   scalar-cell arm or an unconditional reject handles those).
///
/// The classification is EXACT because for every cell shape below,
/// `is_precise_stack_scalar_ty` is `false` (`is_ordered_scalar_ty`/`Ty::Bool` never match
/// Struct/Tuple/Array/Unit/Closure/Enum), so `fresh_stack_cell_value(ty)` is `Some`
/// (tracked) iff `aggregate_field_tys_of(module, ty).is_some()` and `None` (opaque)
/// otherwise — the same predicate this function branches on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackCellAdmission {
    /// Translator models the cell opaquely (havoc-on-read) — unconditionally sound.
    OpaqueSafe,
    /// Translator tracks the cell precisely — sound only if the pointer never escapes.
    RequiresNonEscape,
    /// Not an aggregate/enum cell shape this arm owns.
    NotAggregate,
}

/// Classify an `Alloca` cell type for proof-authority admission, MATCHING
/// `translate_alloca`'s tracked-vs-opaque decision EXACTLY. Both this function and the
/// translator route through `aggregate_field_tys_of` — the translator via the
/// `self.aggregate_field_tys` method, which is literally
/// `aggregate_field_tys_of(self.module, ty)` — so the tracked/opaque split cannot drift.
/// See [`StackCellAdmission`] for the per-variant soundness argument.
pub fn classify_aggregate_stack_cell(module: &Module, ty: &Ty) -> StackCellAdmission {
    let is_cell_shape = matches!(
        ty,
        Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, _) | Ty::Unit | Ty::Closure(_) | Ty::Enum(_)
    );
    if !is_cell_shape {
        return StackCellAdmission::NotAggregate;
    }
    if aggregate_field_tys_of(module, ty).is_some() {
        StackCellAdmission::RequiresNonEscape
    } else {
        StackCellAdmission::OpaqueSafe
    }
}

/// `true` iff `translate_alloca` would model a `count: None` stack `Alloca` of `ty`
/// OPAQUELY — i.e. `fresh_stack_cell_value(ty)` returns `None`, so `translate_alloca`
/// records the pointer in `stack_ptrs` but NOT `stack_cells`. Every later Load then
/// misses `stack_cells` (`translate_stack_load` returns `false`) and havocs to a fresh
/// symbolic (with `known_stack` suppressing the memory-access error); every later Store
/// likewise misses and is dropped. This is an UNCONDITIONAL sound over-approximation
/// (havoc ⊇ real): there is NO tracked value that an aliased write or a mismatched-type
/// store could leave stale, so no escape / type / volatile guard is required.
///
/// This is EXACTLY `fresh_stack_cell_value`'s `None` predicate: `ty` is neither a precise
/// stack scalar (`is_precise_stack_scalar_ty`) nor a trackable aggregate
/// (`aggregate_field_tys_of` is `Some`). `aggregate_field_tys_of == None` also guarantees
/// `fresh_stack_cell_value`'s aggregate branch cannot even be reached, so the equivalence
/// is exact — this function is `true` iff the translator leaves the cell opaque. Covers
/// `FatPtr` (`&str`/`&[T]`/`&Path`), floats (`F16`/`F32`/`F64`), `Char`, `Set`/`Seq`/
/// `Record`, and any opaque/over-budget aggregate that `classify_aggregate_stack_cell`
/// reports as `NotAggregate` (a non-cell shape) or `OpaqueSafe`.
pub fn stack_cell_is_translator_opaque(module: &Module, ty: &Ty) -> bool {
    !is_precise_stack_scalar_ty(ty) && aggregate_field_tys_of(module, ty).is_none()
}

/// The cell types mem2reg promotion may thread through the block relations: EXACTLY
/// the types the translator gives a TRACKED binding to, i.e. the logical negation of
/// [`stack_cell_is_translator_opaque`] and — by construction — exactly
/// `fresh_stack_cell_value(ty).is_some()`.
///
/// A precise stack scalar flattens to ONE relation leaf; a trackable aggregate
/// (`aggregate_field_tys_of` is `Some`) flattens to one leaf per FLATTENED SCALAR LEAF,
/// in the depth-first order `declare_relation_binding_rec` declares and
/// `ValueBinding::flat_args` applies — the same leaf threading the entry-parameter and
/// call-summary lanes already use. Nothing else is required: the whole promotion
/// soundness argument (see `compute_promotable_cells_of`) is about the cell POINTER's
/// use set, not about the cell's shape.
///
/// EXCLUDED, and each falls out of `aggregate_field_tys_of` returning `None` rather
/// than from a special case here:
/// - `Ty::Enum` — `immediate_aggregate_field_tys` has no enum arm, because an enum
///   value is a DISCRIMINANT plus a variant-dependent payload and this translator has
///   no per-variant leaf model for it. A leaf vector that ignored the discriminant
///   would let a merge forward one variant's payload onto a path carrying another.
/// - `Ty::FatPtr` / floats / `Char` / `Set` / `Seq` / `Record` — not aggregates and not
///   `is_precise_stack_scalar_ty`; the translator havocs these cells.
/// - an aggregate with a non-trackable leaf, an array longer than 256, or any type over
///   `MAX_AGGREGATE_LEAVES` — `aggregate_leaf_count_within` declines, so the translator
///   would model the cell opaquely and there is no binding to thread.
fn promotable_cell_ty(module: &Module, ty: &Ty) -> bool {
    is_precise_stack_scalar_ty(ty) || aggregate_field_tys_of(module, ty).is_some()
}

/// `true` iff `alloca_result` is used ONLY as the `ptr` operand of `Load`/`Store` —
/// never as a value operand (a `Store`'s `value`, a call arg, a `Return`, or any operand
/// of an opaque instruction). Mirrors the ESCAPE half of `compute_promotable_cells`
/// step 2 for a single result and STRICTLY conservative: any ambiguity (an
/// unrecognized/opaque instruction, or the result appearing in any non-`ptr` position)
/// reports escaping (`false`).
///
/// This is HALF of the guard that keeps a precisely-tracked
/// ([`StackCellAdmission::RequiresNonEscape`]) stack cell sound: if the pointer never
/// escapes, no write through an alias can make the tracked value stale. `Inst::Load` has
/// exactly one value operand — `ptr` (see `Inst::Load { ty, ptr, volatile, align }`), so
/// a Load can only use the pointer as `ptr`; a `Store`'s `ptr` use is the legitimate
/// write INTO the cell, while its `value` use is the pointer escaping into memory.
///
/// The OTHER half — [`stack_alloca_cell_accesses_match_type`] — is REQUIRED alongside
/// this one: a DIRECT (`ptr`-operand) Store of a DIFFERENT type than the cell is silently
/// dropped by `translate_stack_store` (it `return`s `false` on `cell_ty != *ty` without
/// updating the cell, and `known_stack` then suppresses the memory error), so a later
/// same-type Load reads the STALE precise value — a false proof. `compute_promotable_cells`
/// step 2 disqualifies exactly that mismatch (lines ~799-814); this pair reproduces the
/// full disqualification.
/// How an alloca's address — and every pointer DERIVED from it by `GEP`/`Borrow`/
/// `BorrowMut` — is used across the function.
///
/// This is the provenance-aware refinement of [`stack_alloca_pointer_is_non_escaping`],
/// which is deliberately left BYTE-IDENTICAL: the driver's proof-authority gate
/// (`native.rs`) documents its unconditional admission of `RequiresNonEscape` cells as
/// resting on that exact predicate, so it is not edited in place.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum StackCellEscape {
    /// No use lets the address reach code we cannot see: only `Load`s, `Store`s
    /// THROUGH it, and the `GEP`/`Borrow` derivations feeding those.
    Contained,
    /// The address, or an interior pointer derived from it, reaches a `Call`/
    /// `CallIndirect` argument — and is otherwise contained. Each such call is an
    /// invalidation point (`invalidate_cells_escaping_into_call`), so the cell may
    /// still be tracked: precise before the call, havoc after it.
    IntoCallsOnly,
    /// The address reaches memory (a `Store`'s VALUE), an indirect call's callee
    /// slot, a block argument, a return, or an instruction whose uses are not
    /// statically enumerable. There is no single program point at which to
    /// invalidate, so the cell must not be tracked at all.
    Unbounded,
}

/// OPT-IN (default OFF): admit a def-block-local field projection into the promotion lane.
///
/// SOUND as far as the pins can tell — all three
/// (`aggregate_cell_hazards_stay_fail_closed`,
/// `promotion_widens_only_on_trackable_aggregate_cells`,
/// `a_field_projected_aggregate_cell_is_refused_for_escaping`) stay GREEN with it on,
/// which the earlier escape-only attempt could not manage. But it is UNMEASURED, and on
/// real lowered IR it admits EVERY previously-rejected cell in the
/// `alloca_rejection_taxonomy_on_lowered_modules` fixtures — enough that the coverage
/// canary "has rejected allocas" no longer holds. That is plausibly the lever working, and
/// it is equally plausibly over-admission; only a gate run separates those.
///
/// So it ships default-OFF rather than weakening that canary to make my own change pass.
/// Flag-off is byte-identical to the historical predicate. Read once per process.
fn promote_def_block_projections() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TRUST_PROMOTE_DEF_BLOCK_PROJECTIONS").is_some())
}

/// Admit a TRANSPARENT BORROW of a promotion candidate (`&local` / `&mut local`).
///
/// MEASURED, not guessed (R67). Driving the already-shipped
/// `TRUST_ALLOCA_REJECT_TRACE` over ny-cert and histogramming the promoted-lane
/// `pointer_used_by_instruction` records by the instruction they name gives:
///
/// ```text
///   42  inst=Borrow
///   27  inst=BorrowMut
///    3  inst=GEP
/// ```
///
/// So THIS is the arm that refuses ny-cert, and field projection never was: the
/// Alloca gate owns 159 of 399 obligations and one promoted-lane reason owns 147
/// of those. The sibling [`promote_def_block_projections`] lever addresses the
/// 3, which is why R59 lane C and R66 both measured inert — the def-block-locality
/// clause was never why they were inert.
///
/// Ships default-OFF for the same reason as its sibling: flag-off is byte-identical
/// to the historical predicate, so one gate run can A/B it. Read once per process.
fn promote_cell_borrows() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("TRUST_PROMOTE_CELL_BORROWS").is_some())
}

/// Whether `inst` is a TRANSPARENT BORROW of promotion candidate `cell` which the
/// translator models exactly and whose derived pointers all stay inside the model.
///
/// SPLIT OUT FROM THE STEP-2 ARM ON PURPOSE. [`promote_cell_borrows`] is a
/// process-global `OnceLock`, so a test cannot toggle the flag in-process; a
/// tripwire that could only run under an env var is a tripwire that does not run.
/// Keeping the decision here lets `a_borrow_stored_as_a_value_is_still_refused`
/// exercise the real predicate in the DEFAULT lane.
///
/// The escape classification is the load-bearing half — see the call site.
fn borrow_use_is_transparently_promotable(func: &Function, inst: &Inst, cell: ValueId) -> bool {
    matches!(
        inst,
        Inst::Borrow { ptr } | Inst::BorrowMut { ptr } if ptr.index() == cell.index()
    ) && stack_alloca_escape_classification(func, cell) != StackCellEscape::Unbounded
}

/// Classify how `alloca_result` and its derived interior pointers escape.
///
/// WHY A DERIVED-POINTER CLOSURE. [`stack_alloca_pointer_is_non_escaping`] tests uses of
/// the alloca id ALONE, and treats every non-`Load`/`Store`-`ptr` use as an escape. A
/// `GEP` on the alloca is such a use, so `&mut s.a` — the pervasive field-access shape —
/// disqualifies the whole cell. That is why the precise interior-pointer store lane
/// (`store_cell_lane` / `model_indirect_store`) was unreachable: a coarse guard in front
/// of a precise model. But a `GEP` base and a borrow referent are exactly the positions
/// `record_interior_pointer_escapes` calls TRACKED — it propagates provenance through
/// them rather than treating them as escapes. This function applies that same
/// classification to the admission decision, so the two agree.
///
/// SOUNDNESS OBLIGATION FOR `IntoCallsOnly`. Admitting it is sound only because every
/// `Call`/`CallIndirect` invalidates every tracked cell whose pointer reached it. The two
/// must ship together and must not be separated: without the invalidation, a callee's
/// write through `&mut local` would leave the pre-call value readable, which is a
/// completed false proof. The store-side hazard is already covered independently —
/// `invalidate_store_targets` havocs on an unknown store once the base is in
/// `escaped_cell_bases`.
///
/// Anything not positively recognized is [`StackCellEscape::Unbounded`]: this fails
/// closed, matching the conservative-`true` contract of `collect_inst_value_uses`. Note
/// the failure mode for an UNMODELLED DERIVATION is also closed rather than open: if some
/// instruction outside the {GEP, Borrow, BorrowMut} closure produces a new pointer from
/// one of ours, that instruction still USES a derived pointer, so it lands on the `_` arm
/// and the whole cell becomes `Unbounded`. A derivation we do not understand costs
/// precision, never soundness.
///
/// THE CROSS-BLOCK COUPLING. Promotion may opt into a narrowly recognized GEP or
/// transparent Borrow/BorrowMut use. Such a promoted cell survives block resets, so its
/// soundness depends on the whole-function machinery installed with this classifier:
/// `function_escaped_bases` is re-seeded into every block, promoted cells regain a
/// provenance root, and every direct or indirect call invalidates call-escaping cells.
/// `Unbounded` cells remain unpromotable. Treat the classification, whole-function escape
/// baseline, provenance re-seed, call invalidation, and promotion guards as one unit.
pub(crate) fn stack_alloca_escape_classification(
    func: &Function,
    alloca_result: ValueId,
) -> StackCellEscape {
    // Fixpoint over GEP/Borrow derivations. The IR is SSA, but a derivation may be
    // written before the block that defines its base is visited, so iterate to
    // stability rather than assuming a single ordered pass suffices.
    let mut derived: BTreeSet<ValueId> = BTreeSet::new();
    derived.insert(alloca_result);
    loop {
        let mut grew = false;
        for block in &func.blocks {
            for node in &block.body {
                let base = match &node.inst {
                    Inst::GEP { base, .. } => *base,
                    Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => *ptr,
                    _ => continue,
                };
                if !derived.contains(&base) {
                    continue;
                }
                for result in &node.results {
                    grew |= derived.insert(*result);
                }
            }
        }
        if !grew {
            break;
        }
    }

    let mut escape = StackCellEscape::Contained;
    for block in &func.blocks {
        // Terminators live in `block.body` (hence `translate_node`'s `is_terminator()`
        // check), so a `Ret` or a branch handing a derived pointer to a successor as a
        // block argument is caught by the fail-closed `_` arm below — a derived pointer
        // that outlives this block's tracking state is never admitted.
        for node in &block.body {
            let mut uses = Vec::new();
            if collect_inst_value_uses(&node.inst, &mut uses) {
                // Uses not statically enumerable. Only decisive if this instruction
                // could touch one of our pointers at all, which we cannot rule out.
                if !derived.is_empty() {
                    return StackCellEscape::Unbounded;
                }
                continue;
            }
            if !uses.iter().any(|u| derived.contains(u)) {
                continue;
            }
            // Positional, never by membership: `store p, p` must count the VALUE
            // position even though the same id is also the tracked pointer operand.
            match &node.inst {
                // The sole pointer operand is the tracked position.
                Inst::Load { .. }
                | Inst::AtomicLoad { .. }
                | Inst::Borrow { .. }
                | Inst::BorrowMut { .. }
                | Inst::EndBorrow { .. } => {}
                // `ptr` is tracked; a derived pointer in the VALUE position puts the
                // address INTO memory, where no invalidation point exists.
                Inst::Store { value, .. } | Inst::AtomicStore { value, .. } => {
                    if derived.contains(value) {
                        return StackCellEscape::Unbounded;
                    }
                }
                // `base` is tracked; a derived pointer used as an INDEX is not a
                // pointer use we model.
                Inst::GEP { indices, .. } => {
                    if indices.iter().any(|i| derived.contains(i)) {
                        return StackCellEscape::Unbounded;
                    }
                }
                // Every argument position is an escape, but a recoverable one: the
                // call is itself the invalidation point.
                Inst::Call { .. } => escape = StackCellEscape::IntoCallsOnly,
                Inst::CallIndirect { callee, .. } => {
                    // The callee SLOT is not an argument — a derived pointer there is
                    // being executed, not passed.
                    if derived.contains(callee) {
                        return StackCellEscape::Unbounded;
                    }
                    escape = StackCellEscape::IntoCallsOnly;
                }
                // Deliberately not enumerated: anything else that reads one of our
                // pointers is outside the model.
                _ => return StackCellEscape::Unbounded,
            }
        }
    }
    escape
}

pub fn stack_alloca_pointer_is_non_escaping(func: &Function, alloca_result: ValueId) -> bool {
    let id = alloca_result.index();
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                // A Load reads only through `ptr`; that use does not let the pointer
                // escape.
                Inst::Load { .. } => {}
                // A Store's `ptr` use writes INTO the cell (allowed); the pointer
                // appearing as the stored `value` means it escaped into memory.
                Inst::Store { value, .. } => {
                    if value.index() == id {
                        return false;
                    }
                }
                // Every other instruction: any value use of the pointer is an escape.
                // `collect_inst_value_uses` returns `true` (conservative) for opaque /
                // unrecognized instructions, which we treat as escaping.
                other => {
                    let mut uses = Vec::new();
                    let conservative = collect_inst_value_uses(other, &mut uses);
                    if conservative {
                        return false;
                    }
                    if uses.iter().any(|u| u.index() == id) {
                        return false;
                    }
                }
            }
        }
    }
    true
}

/// `true` iff every DIRECT (`ptr`-operand) `Load`/`Store` of `alloca_result` reads/writes
/// the SAME type as the cell (`cell_ty`, the `Alloca`'s pointee type). This is the second
/// half of the [`StackCellAdmission::RequiresNonEscape`] guard and is REQUIRED for
/// soundness, NOT precision: `translate_stack_store` silently DROPS a Store whose type
/// differs from the tracked cell (`cell_ty != *ty` ⇒ early `return false`, cell value
/// left UNCHANGED), and the `Store` caller then suppresses the memory error because the
/// pointer is `known_stack`. A subsequent same-type `Load` therefore returns the STALE
/// precise value that the mismatched store should have overwritten — a FALSE PROOF.
/// Pointers are untyped in TrustIr (`Ty::Ptr`), so `validate_module` does NOT tie a
/// Store's type to the alloca's pointee; only this check does. Reproduces the type-match
/// disqualification of `compute_promotable_cells` step 2 (the `cell_ty != ty` arms). A
/// mismatched-type Load alone is sound (it havocs), but is rejected here too to mirror
/// step 2 exactly — harmless, since the admissible whole-aggregate return slot reads and
/// writes a single consistent type.
pub fn stack_alloca_cell_accesses_match_type(
    func: &Function,
    alloca_result: ValueId,
    cell_ty: &Ty,
) -> bool {
    let id = alloca_result.index();
    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ty, ptr, .. } | Inst::Store { ty, ptr, .. } => {
                    if ptr.index() == id && ty != cell_ty {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }
    true
}

/// mem2reg candidate analysis, free of `&self` so the proof-grade ADMISSION
/// predicate and the translator run the SAME analysis rather than two prose-
/// synchronized copies. See `ChcTranslator::compute_promotable_cells` for the
/// soundness argument; this is that function's whole body, moved verbatim.
fn compute_promotable_cells_of(
    module: &Module,
    func: &Function,
) -> (Vec<(ValueId, Ty)>, std::collections::BTreeMap<u32, BlockId>) {
    use std::collections::{BTreeMap, BTreeSet};

    // 1. Candidates: every `Alloca { count: None }` whose cell type the translator
    //    tracks precisely (`promotable_cell_ty` — a precise scalar OR a trackable
    //    aggregate, i.e. exactly `fresh_stack_cell_value(ty).is_some()`) with a first
    //    result. Keyed by result index for cheap membership tests.
    let mut candidate_ty: BTreeMap<u32, Ty> = BTreeMap::new();
    let mut candidate_val: BTreeMap<u32, ValueId> = BTreeMap::new();
    let mut def_block: BTreeMap<u32, BlockId> = BTreeMap::new();
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::Alloca { ty, count: None, .. } = &node.inst
                && promotable_cell_ty(module, ty)
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
    for block in &func.blocks {
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
                                // R58 half 2: DEF-BLOCK-LOCAL FIELD PROJECTION.
                                //
                                // This arm is what stops a `&mut s.a` cell from ever being
                                // promoted, which is why its cross-block accesses then fail
                                // the block-local lane as `store_/load_in_other_block` —
                                // 209 + 12 rows at R56, the largest remaining bucket.
                                //
                                // A `GEP` on the cell is admitted ONLY when it sits in the
                                // cell's own DEF BLOCK. That is what keeps the
                                // `FieldProjected` hazard fail-closed for the same reason
                                // and via the same guard as before: that fixture's `GEP` is
                                // in the JOIN block — a block that CONSUMES the threaded
                                // value — so it still lands on `disqualified` below and
                                // `aggregate_cell_hazards_stay_fail_closed` keeps passing
                                // untouched. The pin is preserved, not flipped.
                                //
                                // SOUNDNESS. With every projection confined to the def
                                // block, each one happens while the cell is locally tracked
                                // in `stack_cells`, where the precise interior-pointer store
                                // lane applies — updating the exact leaf on a constant lane,
                                // or havocing the cell on a symbolic/mismatched one. Both
                                // are sound. `add_transition_rule` then forwards whatever
                                // the cell holds at end of block, so the value threaded into
                                // successors is either precise or havoc, never stale. Blocks
                                // that RECEIVE the threaded value perform only whole-cell
                                // Load/Store by construction of this very check, so no
                                // projection can read a leaf the threading did not carry.
                                // That is why the exactness of any individual lane does not
                                // need re-deciding here — the translator already fails
                                // closed on it via `store_target_cell_survives`.
                                //
                                // The escape condition is REQUIRED, and it is what R58
                                // half 1 made checkable across blocks: an `Unbounded` cell
                                // stays disqualified, and an `IntoCallsOnly` cell is
                                // invalidated at every call in EVERY block because
                                // `function_escaped_bases` is re-seeded at each block reset.
                                // Without half 1 this admission would be a cross-block stale
                                // read.
                                // The cell must be an AGGREGATE. A `GEP` on a scalar cell is
                                // not a field projection, there is no leaf for it to select,
                                // and the threaded value has no structure to keep in step —
                                // `promotion_widens_only_on_trackable_aggregate_cells` pins
                                // exactly that, and caught this arm admitting an `i64`.
                                let projectable_aggregate = candidate_ty
                                    .get(&used.index())
                                    .is_some_and(|ty| {
                                        matches!(
                                            ty,
                                            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, _)
                                        )
                                    });
                                let def_block_local_projection = promote_def_block_projections()
                                    && projectable_aggregate
                                    && matches!(
                                        other,
                                        Inst::GEP { base, .. } if base.index() == used.index()
                                    )
                                    && def_block.get(&used.index()) == Some(&block.id)
                                    && candidate_val.get(&used.index()).is_some_and(|cell| {
                                        stack_alloca_escape_classification(func, *cell)
                                            != StackCellEscape::Unbounded
                                    });
                                // R68: TRANSPARENT BORROW OF THE CELL (`&local`, `&mut local`).
                                //
                                // MEASURED (R67), and it inverts the previous plan: of the
                                // promoted-lane `pointer_used_by_instruction` records on
                                // ny-cert, 42 name `Borrow`, 27 `BorrowMut`, and 3 `GEP`.
                                // The sibling projection arm above addresses the 3. That is
                                // why R59 lane C and R66 both measured inert — not the
                                // def-block-locality clause, which was never the reason.
                                //
                                // SOUNDNESS, and why this is EXACT rather than merely
                                // havoc-tolerant. `translate_node`'s Borrow arm binds the
                                // borrow result to the SAME resolved pointer as its referent
                                // and inherits the referent's provenance verbatim (with the
                                // R3 alloca-root fallback for a borrow taken outside the def
                                // block). So a Load/Store through the borrow is
                                // indistinguishable from one through the cell pointer and
                                // lands on the same `stack_cells` entry. The model already
                                // handles this shape; only this analysis refused it.
                                //
                                // THE ESCAPE GUARD IS LOAD-BEARING HERE, NOT A PRECISION
                                // FILTER — this is the one condition that must never be
                                // dropped. Step 2's alias check tests whether the CANDIDATE's
                                // id appears as a `Store` value. A borrow binds a NEW SSA id,
                                // so storing the BORROW RESULT into another cell would slip
                                // past that check. Today that hole is unreachable because the
                                // borrow itself disqualifies the cell; admitting borrows makes
                                // it reachable, and the only thing that closes it is
                                // `stack_alloca_escape_classification`, whose derivation
                                // closure includes GEP/Borrow/BorrowMut RESULTS and whose
                                // fail-closed `_` arm classifies any use of a derived pointer
                                // outside {Load ptr, Store ptr, GEP base, borrow referent} as
                                // `Unbounded`. `a_borrow_stored_as_a_value_is_still_refused`
                                // pins exactly that, and is the false-proof tripwire for this
                                // arm: if it ever goes green, this widening is unsound.
                                //
                                // An `IntoCallsOnly` cell is admitted because every
                                // Call/CallIndirect invalidates it via
                                // `invalidate_cells_escaping_into_call`, in EVERY block —
                                // `function_escaped_bases` is re-seeded at each block reset
                                // (R58 half 1), which is precisely the cross-block
                                // re-establishment the note on
                                // `stack_alloca_escape_classification` demands before
                                // promotion may be loosened.
                                //
                                // DELIBERATELY NO `projectable_aggregate` REQUIREMENT — the
                                // one place this arm is WIDER than the projection arm. A GEP
                                // on a scalar selects no leaf (and
                                // `promotion_widens_only_on_trackable_aggregate_cells` rightly
                                // pins it out), but a borrow of a scalar selects the WHOLE
                                // cell: lane path `[]`, exactly what the block-entry re-seed
                                // installs. R67 observes `ty=u64` borrows.
                                let transparent_borrow = promote_cell_borrows()
                                    && borrow_use_is_transparently_promotable(func, other, used);
                                if def_block_local_projection || transparent_borrow {
                                    continue;
                                }
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

/// The SECOND exact stack-cell lane: a cell the translator's mem2reg pass
/// PROMOTES, i.e. threads through every block relation as an SSA-like value that
/// stores update.
///
/// `single_cell_alloca_is_admissible`'s original clause mirrors only the
/// translator's per-block `stack_cells` lane, so it rejects the ordinary
/// `let k = if c { a } else { b };` shape rustc lowers as *alloca in the entry
/// block, store in each arm, load in the join* — even though `translate_chc`
/// models exactly that shape precisely. This clause admits it, and admits it by
/// calling the translator's own promotion analysis
/// (`compute_promotable_cells_of`) rather than restating it, so the admission
/// predicate cannot drift from the model it is asserting about.
///
/// Promotion alone is NOT sufficient for proof grade; four further conditions
/// are required here, each closing a lane where the translator's model is not
/// the exact cell semantics:
///
///  * `align: None` on the Alloca AND on every access. The translator ignores
///    `align` entirely, so a caller-asserted alignment is an unmodeled claim.
///  * `volatile: false` on every access. A volatile Load is fresh havoc (sound,
///    merely imprecise), but a volatile *Store* takes the `model_indirect_store`
///    path, and in a NON-def block the cell has no `ptr_provenance` entry and
///    nothing has escaped, so the store is classified `NoTrackedTarget` and the
///    promoted cell KEEPS ITS PRE-STORE VALUE while `stack_ptrs` suppresses the
///    fail-closed error. Reading that stale value back is a false-prove
///    generator; excluding volatile accesses keeps it out of the proof lane.
///  * the Alloca that defines the cell must itself carry `count: None` and the
///    exact `ty` being admitted (the promotion analysis keys on the result id,
///    this pins the instruction the driver is admitting).
///  * DEFINITE INITIALIZATION: every `Load` of the cell must be preceded, on
///    EVERY path from the function entry, by a `Store` to it. `translate_alloca`
///    seeds an uninitialized cell with ONE stable fresh symbol, so the CHC reads
///    an arbitrary but *self-consistent* value — which is strictly weaker than
///    the `undef` an uninitialized Rust read actually has (two reads of one
///    uninit cell need not agree, so `a = load c; b = load c; assert(a == b)`
///    would PROVE against a program that is UB). That is a false-prove shape,
///    not an over-approximation, so the block-local clause's "every load follows
///    a store" requirement is kept here in its across-blocks form rather than
///    dropped.
///
/// Everything else the block-local clause guards against is already discharged
/// by promotion itself: aliasing (any non-`ptr` use disqualifies) and type
/// punning (a mismatched access type disqualifies).
///
/// AGGREGATE CELLS. The cell need not be a scalar: `promotable_cell_ty` admits any
/// type the translator tracks precisely, which threads one relation leaf per
/// FLATTENED SCALAR LEAF. The four conditions above and the promotion argument are
/// unchanged and type-agnostic; what needs saying is why the CFG MERGE stays exact
/// per leaf.
///
/// There is no join FUNCTION to get wrong. A block relation's least fixpoint is the
/// UNION of its incoming transition rules, and `add_transition_rule` emits one rule
/// per edge whose head arguments are `binding.flat_args()` of the SOURCE block's
/// current cell value — the whole binding, atomically, from ONE predecessor. So a
/// merge block's cell columns are always some single predecessor's leaves, never a
/// leaf-wise mixture and never a predecessor-independent default. A cell written in
/// one predecessor and not another therefore reads, on the unwritten path, exactly
/// what that predecessor carried in (its own incoming relation argument, or the
/// `Alloca`'s fresh symbol if that predecessor is the def block) — never the other
/// path's stored value. Leaf ALIGNMENT is structural: `declare_relation_binding_rec`
/// pushes sorts and `ValueBinding::flat_args` pushes arguments in the same
/// depth-first, left-to-right expansion of `aggregate_field_tys_of`, and every
/// binding the cell can hold is built from that same table
/// (`fresh_stack_cell_value` at the `Alloca` and at `invalidate_stack_cell`,
/// `resolve_aggregate` at a `Store`), so the arity cannot drift.
///
/// DEFINITE INITIALIZATION still does the work it does for scalars. The
/// fresh-symbol-per-cell seeding is self-consistent rather than `undef` for an
/// aggregate exactly as for a scalar, so the same false-prove shape exists and the
/// same across-blocks MUST dataflow excludes it. Note the dataflow is whole-cell:
/// it has no notion of a partly-initialized aggregate — which is sound here only
/// because a partial write needs a `GEP` on the cell pointer, and a `GEP` base use
/// disqualifies the candidate at promotion step 2. Every admitted access is a
/// whole-cell, exact-type `Load`/`Store`.
#[cfg(test)]
fn promoted_cell_alloca_is_admissible(
    module: &Module,
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> bool {
    promoted_cell_alloca_reject(module, function, alloca_result, ty).is_none()
}

/// The reason form of `promoted_cell_alloca_is_admissible`; `None` = admitted.
/// Behavior unchanged — each `return false` became a `return Some(..)` in place.
fn promoted_cell_alloca_reject(
    module: &Module,
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> Option<PromotedAllocaReject> {
    let result = alloca_result.index();

    // The instruction being admitted must be the metadata-less, exact-typed
    // single-cell Alloca that defines this value.
    let defines_exact_cell = function.blocks.iter().any(|block| {
        block.body.iter().any(|node| {
            node.results.iter().any(|value| value.index() == result)
                && matches!(
                    &node.inst,
                    Inst::Alloca { ty: cell_ty, count: None, align: None } if cell_ty == ty
                )
        })
    });
    if !defines_exact_cell {
        return Some(PromotedAllocaReject::NoExactDefiningAlloca);
    }

    // The translator's own promotion verdict — not a restatement of it.
    let (promoted, _) = compute_promotable_cells_of(module, function);
    if !promoted.iter().any(|(cell, cell_ty)| cell.index() == result && cell_ty == ty) {
        return Some(PromotedAllocaReject::NotPromotable(promotion_blocker_of(
            module, function, result, ty,
        )));
    }

    // No unmodeled access qualifier anywhere on this cell.
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ptr, volatile, align, .. }
                | Inst::Store { ptr, volatile, align, .. } => {
                    if ptr.index() == result && (*volatile || align.is_some()) {
                        return Some(if *volatile {
                            PromotedAllocaReject::AccessVolatile
                        } else {
                            PromotedAllocaReject::AccessAligned
                        });
                    }
                }
                _ => {}
            }
        }
    }

    if promoted_cell_is_definitely_initialized(function, result) {
        None
    } else {
        Some(PromotedAllocaReject::NotDefinitelyInitialized)
    }
}

/// DIAGNOSTIC-ONLY refinement of "the translator would not promote this cell":
/// a single-candidate mirror of `compute_promotable_cells_of` steps 1 and 2.
///
/// It is deliberately NOT the admission authority — `promoted_cell_alloca_reject`
/// has already consulted `compute_promotable_cells_of` and decided to reject by
/// the time this runs. If this mirror ever drifts from the real analysis the only
/// consequence is a mislabeled histogram bucket (or `Unclassified`), never an
/// admitted cell.
fn promotion_blocker_of(
    module: &Module,
    function: &Function,
    result: u32,
    ty: &Ty,
) -> PromotionBlocker {
    // Step 1: only a cell the translator tracks precisely is ever a candidate.
    if !promotable_cell_ty(module, ty) {
        return PromotionBlocker::PointeeNotPreciseScalar { ty: ty.to_string() };
    }

    // Step 2, restricted to this candidate.
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ty: access_ty, ptr, .. } => {
                    if ptr.index() == result && access_ty != ty {
                        return PromotionBlocker::AccessTypeMismatch {
                            access: "load",
                            access_ty: access_ty.to_string(),
                            cell_ty: ty.to_string(),
                        };
                    }
                }
                Inst::Store { ty: access_ty, ptr, value, .. } => {
                    if ptr.index() == result && access_ty != ty {
                        return PromotionBlocker::AccessTypeMismatch {
                            access: "store",
                            access_ty: access_ty.to_string(),
                            cell_ty: ty.to_string(),
                        };
                    }
                    if value.index() == result {
                        return PromotionBlocker::PointerStoredAsValue;
                    }
                }
                other => {
                    let mut uses = Vec::new();
                    if collect_inst_value_uses(other, &mut uses) {
                        return PromotionBlocker::OpaqueInstruction {
                            inst: inst_variant_name(other),
                        };
                    }
                    if uses.iter().any(|value| value.index() == result) {
                        return PromotionBlocker::PointerUsedByInstruction {
                            inst: inst_variant_name(other),
                        };
                    }
                }
            }
        }
    }

    PromotionBlocker::Unclassified
}

/// The pre-taxonomy boolean body of `promoted_cell_alloca_reject`, kept VERBATIM
/// for `alloca_reject_parity_tests`. Never compiled outside tests.
#[cfg(test)]
fn promoted_cell_alloca_is_admissible_reference(
    module: &Module,
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> bool {
    let result = alloca_result.index();

    let defines_exact_cell = function.blocks.iter().any(|block| {
        block.body.iter().any(|node| {
            node.results.iter().any(|value| value.index() == result)
                && matches!(
                    &node.inst,
                    Inst::Alloca { ty: cell_ty, count: None, align: None } if cell_ty == ty
                )
        })
    });
    if !defines_exact_cell {
        return false;
    }

    let (promoted, _) = compute_promotable_cells_of(module, function);
    if !promoted.iter().any(|(cell, cell_ty)| cell.index() == result && cell_ty == ty) {
        return false;
    }

    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ptr, volatile, align, .. }
                | Inst::Store { ptr, volatile, align, .. } => {
                    if ptr.index() == result && (*volatile || align.is_some()) {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }

    promoted_cell_is_definitely_initialized(function, result)
}

/// The lane-2 predicate AS IT STOOD BEFORE the aggregate-cell widening: candidate
/// collection restricted to `is_precise_stack_scalar_ty`, everything else identical.
/// Never compiled outside tests.
///
/// This is the DIRECTIONAL parity control. `promoted_cell_alloca_is_admissible_reference`
/// above tracks the live predicate, so it can only prove the taxonomy rewrite is
/// verdict-inert; it cannot notice the widening itself. This one is frozen at the
/// scalar-only behaviour, and `promotion_widens_only_on_trackable_aggregate_cells`
/// asserts the live predicate differs from it ONLY by ADMITTING a cell whose type is a
/// trackable non-scalar aggregate. Any other divergence — a narrowing, or a widening on
/// a scalar / enum / fat-pointer / over-budget cell — is a parity FAILURE.
#[cfg(test)]
fn promoted_cell_alloca_is_admissible_scalar_reference(
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> bool {
    use std::collections::{BTreeMap, BTreeSet};

    let result = alloca_result.index();

    let defines_exact_cell = function.blocks.iter().any(|block| {
        block.body.iter().any(|node| {
            node.results.iter().any(|value| value.index() == result)
                && matches!(
                    &node.inst,
                    Inst::Alloca { ty: cell_ty, count: None, align: None } if cell_ty == ty
                )
        })
    });
    if !defines_exact_cell {
        return false;
    }

    // `compute_promotable_cells_of`, frozen at the pre-widening step 1.
    let mut candidate_ty: BTreeMap<u32, Ty> = BTreeMap::new();
    for block in &function.blocks {
        for node in &block.body {
            if let Inst::Alloca { ty, count: None, .. } = &node.inst
                && is_precise_stack_scalar_ty(ty)
                && let Some(candidate) = node.results.first()
            {
                candidate_ty.insert(candidate.index(), ty.clone());
            }
        }
    }
    let mut disqualified: BTreeSet<u32> = BTreeSet::new();
    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ty: access_ty, ptr, .. } => {
                    if let Some(cell_ty) = candidate_ty.get(&ptr.index())
                        && cell_ty != access_ty
                    {
                        disqualified.insert(ptr.index());
                    }
                }
                Inst::Store { ty: access_ty, ptr, value, .. } => {
                    if let Some(cell_ty) = candidate_ty.get(&ptr.index())
                        && cell_ty != access_ty
                    {
                        disqualified.insert(ptr.index());
                    }
                    if candidate_ty.contains_key(&value.index()) {
                        disqualified.insert(value.index());
                    }
                }
                other => {
                    let mut uses = Vec::new();
                    if collect_inst_value_uses(other, &mut uses) {
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
    if candidate_ty.get(&result) != Some(ty) || disqualified.contains(&result) {
        return false;
    }

    for block in &function.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Load { ptr, volatile, align, .. }
                | Inst::Store { ptr, volatile, align, .. } => {
                    if ptr.index() == result && (*volatile || align.is_some()) {
                        return false;
                    }
                }
                _ => {}
            }
        }
    }

    promoted_cell_is_definitely_initialized(function, result)
}

/// Whether every `Load` of the promoted cell `cell` is preceded on EVERY path
/// from the function entry by a `Store` to it — the across-blocks form of the
/// block-local clause's `initialized` flag.
///
/// A forward MUST dataflow (meet = AND) over the block CFG: the entry starts
/// uninitialized, an `Alloca` of the cell RESETS it (matching `translate_alloca`,
/// which mints a new fresh cell each time the defining block executes — a cell
/// alloca'd inside a loop is a new local per iteration), a `Store` sets it, and a
/// `Load` while unset rejects. Interior blocks start optimistically initialized
/// and the fixpoint only ever moves them to uninitialized, which is the standard
/// greatest-fixpoint formulation of definite assignment; a loop header whose only
/// store is inside the loop still meets with the entry's `false` and is rejected.
///
/// Every ambiguity fails CLOSED: a duplicate block id, a block with no
/// terminator, an unrecognized terminator, a successor naming a missing block, a
/// non-entry block with no predecessor (not reachable from the entry, so its
/// incoming state is not derivable here), or a fixpoint that has not settled
/// within its monotone bound all return `false`.
fn promoted_cell_is_definitely_initialized(function: &Function, cell: u32) -> bool {
    use std::collections::BTreeMap;

    let count = function.blocks.len();
    if count == 0 {
        return false;
    }

    let mut index_of: BTreeMap<u32, usize> = BTreeMap::new();
    for (index, block) in function.blocks.iter().enumerate() {
        if index_of.insert(block.id.index(), index).is_some() {
            return false;
        }
    }
    let Some(&entry) = index_of.get(&function.entry.index()) else {
        return false;
    };

    let mut successors: Vec<Vec<usize>> = Vec::with_capacity(count);
    for block in &function.blocks {
        let mut targets = Vec::new();
        let mut terminated = false;
        for node in &block.body {
            if !node.inst.is_terminator() {
                continue;
            }
            if collect_terminator_successors(&node.inst, &mut targets) {
                return false;
            }
            terminated = true;
            break;
        }
        if !terminated {
            return false;
        }
        let mut resolved = Vec::with_capacity(targets.len());
        for target in targets {
            let Some(&index) = index_of.get(&target.index()) else {
                return false;
            };
            resolved.push(index);
        }
        successors.push(resolved);
    }

    let mut predecessors: Vec<Vec<usize>> = vec![Vec::new(); count];
    for (from, targets) in successors.iter().enumerate() {
        for &target in targets {
            predecessors[target].push(from);
        }
    }

    let mut incoming = vec![true; count];
    let mut outgoing = vec![true; count];
    incoming[entry] = false;

    // Knock every block that is NOT REACHABLE FROM ENTRY off the optimistic top.
    //
    // An earlier version tested `predecessors[block].is_empty()` instead. That fails
    // OPEN, and adversarial review measured it: a non-entry block that is unreachable
    // from `entry` but lies in a MUTUALLY-REFERENTIAL region has predecessors (each
    // other), so it kept `incoming = true` forever — the AND over its own cycle never
    // introduces a `false`. A Load of a never-stored cell inside such a region would
    // then be treated as definitely initialized, which is the exact fail-open this
    // predicate exists to prevent. Pred-count is not reachability; compute reachability.
    //
    // Unreachable code cannot initialize anything on any real execution, so `false`
    // ("not definitely initialized") is both the sound and the honest value: a Load
    // there declines admission rather than being waved through.
    let mut reachable = vec![false; count];
    reachable[entry] = true;
    let mut stack = vec![entry];
    while let Some(block) = stack.pop() {
        for &next in &successors[block] {
            if next < count && !reachable[next] {
                reachable[next] = true;
                stack.push(next);
            }
        }
    }
    for block in 0..count {
        if block != entry && !reachable[block] {
            incoming[block] = false;
        }
    }

    // Monotone descent from the optimistic top: each of the 2*count lattice
    // slots can flip true -> false at most once, so 2*count + 1 rounds is a hard
    // bound on convergence. Not converging is a contradiction, not a verdict.
    let mut settled = false;
    for _ in 0..(2 * count + 1) {
        let mut changed = false;
        for block in 0..count {
            let (out, _) =
                promoted_cell_block_transfer(&function.blocks[block], cell, incoming[block]);
            if outgoing[block] != out {
                outgoing[block] = out;
                changed = true;
            }
        }
        for block in 0..count {
            if block == entry || predecessors[block].is_empty() {
                continue;
            }
            let next = predecessors[block].iter().all(|&pred| outgoing[pred]);
            if incoming[block] != next {
                incoming[block] = next;
                changed = true;
            }
        }
        if !changed {
            settled = true;
            break;
        }
    }
    if !settled {
        return false;
    }

    (0..count)
        .all(|block| promoted_cell_block_transfer(&function.blocks[block], cell, incoming[block]).1)
}

/// One block's contribution to [`promoted_cell_is_definitely_initialized`]:
/// `(state at the terminator, no load of an uninitialized cell in this block)`.
///
/// An `Alloca` of the cell RESETS the state, matching `translate_alloca`, which
/// mints a fresh unconstrained cell every time the defining block executes.
fn promoted_cell_block_transfer(block: &Block, cell: u32, mut state: bool) -> (bool, bool) {
    for node in &block.body {
        match &node.inst {
            Inst::Alloca { .. } if node.results.iter().any(|value| value.index() == cell) => {
                state = false;
            }
            Inst::Store { ptr, .. } if ptr.index() == cell => state = true,
            Inst::Load { ptr, .. } if ptr.index() == cell && !state => return (state, false),
            _ => {}
        }
        if node.inst.is_terminator() {
            break;
        }
    }
    (state, true)
}

/// Why lane 1 (`block_local_alloca_reject`) declined a cell.
///
/// DIAGNOSTIC ONLY. Every variant corresponds one-to-one with a `return false`
/// in the historical boolean predicate, in the same order, so constructing a
/// reason cannot change which cells are admitted — the admission verdict is
/// exactly `reason.is_none()`. `block_local_alloca_is_admissible_reference`
/// (test-only) keeps the original boolean body verbatim and
/// `alloca_reject_parity_tests` asserts the two agree on every fixture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockLocalAllocaReject {
    /// The pointee is neither a precise stack scalar nor a (possibly opaque)
    /// aggregate — e.g. a fat pointer or a bare `Ty::Ptr`.
    PointeeNotScalarOrAggregate { ty: String },
    /// No `Alloca { count: None, align: None, ty: <exactly this ty> }` in the
    /// function defines this value.
    NoExactDefiningAlloca,
    /// A `Load` through the cell pointer outside the defining block. This is
    /// the clause a cross-block escape analysis would have to replace.
    LoadInOtherBlock { block: u32, definition_block: u32 },
    /// A `Load` in the defining block not preceded there by a `Store`.
    LoadBeforeStore { block: u32 },
    LoadVolatile { block: u32 },
    LoadAligned { block: u32 },
    LoadTypeMismatch { block: u32, access_ty: String, cell_ty: String },
    StoreInOtherBlock { block: u32, definition_block: u32 },
    StoreVolatile { block: u32 },
    StoreAligned { block: u32 },
    StoreTypeMismatch { block: u32, access_ty: String, cell_ty: String },
    /// The cell POINTER itself is the stored value — it escaped into memory.
    PointerStoredAsValue { block: u32 },
    /// An instruction whose operands `collect_inst_value_uses` does not
    /// enumerate appears anywhere in the function; it could read any pointer.
    OpaqueInstruction { block: u32, inst: String },
    /// The cell pointer is an operand of some instruction other than a direct
    /// `Load`/`Store` through it (a `GEP` base, a `Call` argument, a `Borrow`).
    PointerUsedByInstruction { block: u32, inst: String },
}

impl BlockLocalAllocaReject {
    /// Short, stable, greppable token — the histogram bucket name.
    pub fn kind(&self) -> &'static str {
        match self {
            Self::PointeeNotScalarOrAggregate { .. } => "pointee_not_scalar_or_aggregate",
            Self::NoExactDefiningAlloca => "no_exact_defining_alloca",
            Self::LoadInOtherBlock { .. } => "load_in_other_block",
            Self::LoadBeforeStore { .. } => "load_before_store",
            Self::LoadVolatile { .. } => "load_volatile",
            Self::LoadAligned { .. } => "load_aligned",
            Self::LoadTypeMismatch { .. } => "load_type_mismatch",
            Self::StoreInOtherBlock { .. } => "store_in_other_block",
            Self::StoreVolatile { .. } => "store_volatile",
            Self::StoreAligned { .. } => "store_aligned",
            Self::StoreTypeMismatch { .. } => "store_type_mismatch",
            Self::PointerStoredAsValue { .. } => "pointer_stored_as_value",
            Self::OpaqueInstruction { .. } => "opaque_instruction",
            Self::PointerUsedByInstruction { .. } => "pointer_used_by_instruction",
        }
    }
}

impl std::fmt::Display for BlockLocalAllocaReject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind())?;
        match self {
            Self::PointeeNotScalarOrAggregate { ty } => write!(f, "(ty={ty})"),
            Self::NoExactDefiningAlloca => Ok(()),
            Self::LoadInOtherBlock { block, definition_block }
            | Self::StoreInOtherBlock { block, definition_block } => {
                write!(f, "(at=#{block},def=#{definition_block})")
            }
            Self::LoadBeforeStore { block }
            | Self::LoadVolatile { block }
            | Self::LoadAligned { block }
            | Self::StoreVolatile { block }
            | Self::StoreAligned { block }
            | Self::PointerStoredAsValue { block } => write!(f, "(at=#{block})"),
            Self::LoadTypeMismatch { block, access_ty, cell_ty }
            | Self::StoreTypeMismatch { block, access_ty, cell_ty } => {
                write!(f, "(at=#{block},access={access_ty},cell={cell_ty})")
            }
            Self::OpaqueInstruction { block, inst }
            | Self::PointerUsedByInstruction { block, inst } => {
                write!(f, "(at=#{block},inst={inst})")
            }
        }
    }
}

/// Why the translator's mem2reg pass would not PROMOTE the cell — the refinement
/// of [`PromotedAllocaReject::NotPromotable`].
///
/// DIAGNOSTIC ONLY, and unlike the two lane predicates this one is a *mirror* of
/// `compute_promotable_cells_of` step 1/2 restricted to a single candidate, not
/// the analysis itself. The authority for "was it promoted" remains
/// `compute_promotable_cells_of`; drift here can only mislabel a histogram
/// bucket, never admit a cell.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PromotionBlocker {
    /// Never even a promotion CANDIDATE: the translator does not track this cell
    /// type precisely, so there is no binding to thread (`promotable_cell_ty` is
    /// `false` — see its doc for the exact set).
    ///
    /// The bucket TOKEN is deliberately unchanged (`not_promotable.
    /// pointee_not_precise_scalar`) so gate-log histograms stay comparable across
    /// the R49 boundary, but the CONDITION is now wider than its name: promotion
    /// covers precise scalars AND trackable aggregates, so a `struct`/`tuple`/
    /// `array`/`closure`/`unit` cell no longer lands here. What still does:
    /// `enum` (no per-variant leaf model), fat pointers, floats, `char`, and any
    /// aggregate with a non-trackable leaf or over `MAX_AGGREGATE_LEAVES`.
    PointeeNotPreciseScalar { ty: String },
    AccessTypeMismatch { access: &'static str, access_ty: String, cell_ty: String },
    PointerStoredAsValue,
    OpaqueInstruction { inst: String },
    PointerUsedByInstruction { inst: String },
    /// The mirror found no blocker although the authority says not promoted —
    /// report it rather than guessing.
    Unclassified,
}

impl PromotionBlocker {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::PointeeNotPreciseScalar { .. } => "not_promotable.pointee_not_precise_scalar",
            Self::AccessTypeMismatch { .. } => "not_promotable.access_type_mismatch",
            Self::PointerStoredAsValue => "not_promotable.pointer_stored_as_value",
            Self::OpaqueInstruction { .. } => "not_promotable.opaque_instruction",
            Self::PointerUsedByInstruction { .. } => "not_promotable.pointer_used_by_instruction",
            Self::Unclassified => "not_promotable.unclassified",
        }
    }
}

impl std::fmt::Display for PromotionBlocker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind())?;
        match self {
            Self::PointeeNotPreciseScalar { ty } => write!(f, "(ty={ty})"),
            Self::AccessTypeMismatch { access, access_ty, cell_ty } => {
                write!(f, "({access},access={access_ty},cell={cell_ty})")
            }
            Self::OpaqueInstruction { inst } | Self::PointerUsedByInstruction { inst } => {
                write!(f, "(inst={inst})")
            }
            Self::PointerStoredAsValue | Self::Unclassified => Ok(()),
        }
    }
}

/// Why lane 2 (`promoted_cell_alloca_reject`) declined a cell. Same one-to-one
/// correspondence with the historical boolean's `return false`s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PromotedAllocaReject {
    NoExactDefiningAlloca,
    NotPromotable(PromotionBlocker),
    AccessVolatile,
    AccessAligned,
    NotDefinitelyInitialized,
}

impl PromotedAllocaReject {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::NoExactDefiningAlloca => "no_exact_defining_alloca",
            Self::NotPromotable(blocker) => blocker.kind(),
            Self::AccessVolatile => "access_volatile",
            Self::AccessAligned => "access_aligned",
            Self::NotDefinitelyInitialized => "not_definitely_initialized",
        }
    }
}

impl std::fmt::Display for PromotedAllocaReject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotPromotable(blocker) => write!(f, "{blocker}"),
            other => write!(f, "{}", other.kind()),
        }
    }
}

/// Both lanes' reasons for one declined `Alloca`. Produced only when
/// [`single_cell_alloca_is_admissible`] is `false`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SingleCellAllocaRejection {
    pub block_local: BlockLocalAllocaReject,
    pub promoted: PromotedAllocaReject,
}

impl SingleCellAllocaRejection {
    /// `<lane1>/<lane2>` — the pair of bucket tokens, for a grep-only histogram
    /// over an ordinary gate log.
    pub fn kind(&self) -> String {
        format!("{}/{}", self.block_local.kind(), self.promoted.kind())
    }
}

impl std::fmt::Display for SingleCellAllocaRejection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "block-local={} promoted={}", self.block_local, self.promoted)
    }
}

/// The variant name of `inst`, taken from its derived `Debug` rendering so this
/// cannot drift as `Inst` grows variants. Reject path only.
fn inst_variant_name(inst: &Inst) -> String {
    let rendered = format!("{inst:?}");
    let end = rendered
        .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
        .unwrap_or(rendered.len());
    rendered[..end].to_string()
}

/// Whether proof-grade native ingestion may admit a metadata-less, single-cell
/// `Alloca` without importing source authority.
///
/// This deliberately mirrors the CHC translator's tracked-versus-opaque split,
/// which has TWO exact lanes. The first (below) is the per-block `stack_cells`
/// lane: a precise scalar or trackable aggregate is admitted when its pointer is
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
///
/// The second lane is `promoted_cell_alloca_is_admissible` — the mem2reg
/// promotion the translator already performs, which models an un-aliased cell
/// exactly ACROSS blocks. Neither lane subsumes the other: the block-local one also
/// covers cells the translator models OPAQUELY (enums, fat pointers, over-budget
/// aggregates — never promoted), the promoted one also covers cross-block cells.
pub fn single_cell_alloca_is_admissible(
    module: &Module,
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> bool {
    single_cell_alloca_rejection(module, function, alloca_result, ty).is_none()
}

/// The reason form of [`single_cell_alloca_is_admissible`]: `None` iff the cell
/// is admitted, otherwise BOTH lanes' first blocking condition.
///
/// This is the sole implementation — the boolean above is defined as
/// `.is_none()` — so a verdict cannot differ between the measured and unmeasured
/// paths. The `?` keeps the original `||` short-circuit exactly: lane 2 runs only
/// when lane 1 declined.
pub fn single_cell_alloca_rejection(
    module: &Module,
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> Option<SingleCellAllocaRejection> {
    let block_local = block_local_alloca_reject(function, alloca_result, ty)?;
    let promoted = promoted_cell_alloca_reject(module, function, alloca_result, ty)?;
    Some(SingleCellAllocaRejection { block_local, promoted })
}

/// Lane 1 of [`single_cell_alloca_is_admissible`]: the per-block `stack_cells`
/// model. `None` = admitted.
///
/// Behavior is UNCHANGED from the boolean original: each `return false` became a
/// `return Some(..)` in place, and the disjunctive access guard was expanded into
/// the same conditions tested in the same order, so the first one that held is
/// named. `block_local_alloca_is_admissible_reference` holds the original body
/// and the parity test pins them together.
fn block_local_alloca_reject(
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> Option<BlockLocalAllocaReject> {
    let aggregate = matches!(
        ty,
        Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, _) | Ty::Unit | Ty::Closure(_) | Ty::Enum(_)
    );
    if !is_precise_stack_scalar_ty(ty) && !aggregate {
        return Some(BlockLocalAllocaReject::PointeeNotScalarOrAggregate { ty: ty.to_string() });
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
        return Some(BlockLocalAllocaReject::NoExactDefiningAlloca);
    };

    // Whole-function, so computed ONCE: the derivation closure is a fixpoint and
    // evaluating it per instruction would make this gate quadratic in body size.
    //
    // OPT-IN (default OFF). Widening this gate is SOUND — the translator models both
    // admitted classes precisely, `IntoCallsOnly` via `invalidate_cells_escaping_into_call`
    // — but R54 + the R53 solver census say it is not yet USEFUL, and may be harmful:
    // of the 47 ny-cert obligations that already reach the solver, 43 come back REFUTED
    // (`counterexample evidence is not a proof` is emitted only for
    // `FullVerificationVerdict::Failed`), because unmodelled calls contribute an
    // unconditionally reachable error rule and inlined callee panic paths are guarded
    // only by caller path constraints. Freeing ~90 more Alloca rows would move them into
    // a bucket with a measured 0/47 proof rate, and a refutation is routed to FAILED —
    // so defaulting this ON risks moving ny-cert's `failed` off 0 with spurious
    // havoc-induced counterexamples.
    //
    // So it ships flag-gated rather than silently on: flag-off is byte-identical to the
    // historical predicate, and one gate run can A/B it. Turn it on once the CHC
    // encoding can actually discharge a panic-freedom obligation for this crate.
    //
    // THE FLAG IS PROVEN ON THE LIVE PATH, which is precisely what R54 could not show for
    // the translator-only change. Running the suite with the flag set turns R49's
    // inertness pins RED — `parity_with_the_original_boolean_predicates` and
    // `parity_on_the_mem2reg_fixtures` report "verdict changed on
    // `pointer_used_by_instruction` probed at i64: left true, right false". Those tests
    // exist to detect exactly this, and their failure under the flag is them WORKING:
    // the gate now admits a cell it used to refuse. They pin the DEFAULT lane, so they
    // are green in every normal run and must NOT be weakened to accommodate the flag —
    // a future reader who "fixes" them deletes the only evidence that this lever bites.
    //
    // Read once per process, not per alloca.
    static WIDEN: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let widen = *WIDEN
        .get_or_init(|| std::env::var_os("TRUST_ALLOCA_ESCAPE_GATE_WIDEN").is_some());
    let escape = if widen {
        stack_alloca_escape_classification(function, alloca_result)
    } else {
        StackCellEscape::Unbounded
    };

    let mut initialized = false;
    for block in &function.blocks {
        let at = block.id.index();
        for node in &block.body {
            match &node.inst {
                Inst::Load { ty: access_ty, ptr, volatile, align } => {
                    if ptr.index() == result {
                        if block.id != definition_block {
                            return Some(BlockLocalAllocaReject::LoadInOtherBlock {
                                block: at,
                                definition_block: definition_block.index(),
                            });
                        }
                        if !initialized {
                            return Some(BlockLocalAllocaReject::LoadBeforeStore { block: at });
                        }
                        if *volatile {
                            return Some(BlockLocalAllocaReject::LoadVolatile { block: at });
                        }
                        if align.is_some() {
                            return Some(BlockLocalAllocaReject::LoadAligned { block: at });
                        }
                        if access_ty != ty {
                            return Some(BlockLocalAllocaReject::LoadTypeMismatch {
                                block: at,
                                access_ty: access_ty.to_string(),
                                cell_ty: ty.to_string(),
                            });
                        }
                    }
                }
                Inst::Store { ty: access_ty, ptr, value, volatile, align } => {
                    if ptr.index() == result {
                        if block.id != definition_block {
                            return Some(BlockLocalAllocaReject::StoreInOtherBlock {
                                block: at,
                                definition_block: definition_block.index(),
                            });
                        }
                        if *volatile {
                            return Some(BlockLocalAllocaReject::StoreVolatile { block: at });
                        }
                        if align.is_some() {
                            return Some(BlockLocalAllocaReject::StoreAligned { block: at });
                        }
                        if access_ty != ty {
                            return Some(BlockLocalAllocaReject::StoreTypeMismatch {
                                block: at,
                                access_ty: access_ty.to_string(),
                                cell_ty: ty.to_string(),
                            });
                        }
                    }
                    if value.index() == result {
                        return Some(BlockLocalAllocaReject::PointerStoredAsValue { block: at });
                    }
                    if ptr.index() == result {
                        initialized = true;
                    }
                }
                other => {
                    // R55 — THE CONSUMER HALF. These two arms are the ADMISSION gate; the
                    // provenance model landed in `translate_alloca` is the TRACKING
                    // decision. They were independent, and that is why the provenance
                    // model measured FLAT on ny-cert (R54: escape bucket 92 -> 90): the
                    // driver refused the input here before the translator's improved
                    // tracking was ever exercised. Producer without consumer.
                    //
                    // `escape` is the SAME whole-function classification `translate_alloca`
                    // now uses, so gate and translator move in LOCKSTEP. That lockstep is
                    // the soundness condition, and it is directional:
                    //   gate admits + translator demotes  -> harmless (havoc, imprecise)
                    //   gate admits + translator UNSOUND  -> FALSE PROOF
                    // Admitting `Contained`/`IntoCallsOnly` is legal ONLY because the
                    // translator models exactly those two soundly — `IntoCallsOnly` via
                    // `invalidate_cells_escaping_into_call` (precise before the call,
                    // havoc after). Widening this gate BEFORE that landed would have been
                    // the false proof; that is why it is a separate, later commit.
                    //
                    // `Unbounded` still rejects with the identical reason, so the
                    // fail-closed default is unchanged: a pointer reaching memory, a
                    // return, a block argument, an indirect call's callee slot, or any
                    // instruction whose uses are not statically enumerable is refused
                    // exactly as before.
                    //
                    // The classifier subsumes the opaque case: it returns `Unbounded`
                    // whenever `collect_inst_value_uses` is conservative, so a non-
                    // `Unbounded` verdict already proves no opaque instruction is present.
                    // Both arms are nevertheless kept and merely guarded, so this stays a
                    // pure narrowing of when they fire rather than a deletion.
                    let mut uses = Vec::new();
                    if collect_inst_value_uses(other, &mut uses) {
                        if escape == StackCellEscape::Unbounded {
                            // An opaque instruction may read any in-scope pointer.
                            return Some(BlockLocalAllocaReject::OpaqueInstruction {
                                block: at,
                                inst: inst_variant_name(other),
                            });
                        }
                        continue;
                    }
                    if uses.iter().any(|value| value.index() == result)
                        && escape == StackCellEscape::Unbounded
                    {
                        return Some(BlockLocalAllocaReject::PointerUsedByInstruction {
                            block: at,
                            inst: inst_variant_name(other),
                        });
                    }
                }
            }
        }
    }
    None
}

/// Boolean view of lane 1, for the existing lane-level tests.
#[cfg(test)]
fn block_local_alloca_is_admissible(function: &Function, alloca_result: ValueId, ty: &Ty) -> bool {
    block_local_alloca_reject(function, alloca_result, ty).is_none()
}

/// The pre-taxonomy boolean body of `block_local_alloca_reject`, kept VERBATIM so
/// `alloca_reject_parity_tests` can prove the reason-returning rewrite admits
/// exactly the same cells. Never compiled outside tests.
#[cfg(test)]
fn block_local_alloca_is_admissible_reference(
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

/// Normalize valid integer width drift, then require the expression to inhabit
/// the exact carrier declared by `ty`. `Sort` equality is not sufficient for
/// this boundary because AY's equality historically did not always distinguish
/// bitvector widths; compare the carrier kind and width explicitly.
fn normalize_expr_to_exact_ty(expr: &Expr, ty: &Ty) -> Option<Expr> {
    let normalized = normalize_expr_to_ty(expr, ty);
    let expected = ty_to_sort(ty);
    if expected.is_bool() {
        return normalized.sort().is_bool().then_some(normalized);
    }
    let expected_width = expected.bitvec_width()?;
    (normalized.sort().bitvec_width() == Some(expected_width)).then_some(normalized)
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
            // SAME-WIDTH INTEGER BITCAST — gate/translator lockstep restoration, not a
            // new model. `translate_cast` already lowers this arm EXACTLY, as the
            // identity on the bit-vector carrier:
            //     CastOp::Bitcast if src_ty.is_integer() && dst_ty.is_integer() => {
            //         let src_width = src_ty.bit_width_with(HOST_POINTER_BITS)?;
            //         let dst_width = dst_ty.bit_width_with(HOST_POINTER_BITS)?;
            //         (src_width == dst_width).then_some(operand)
            //     }
            // Only THIS admission predicate omitted it, so `i128 -> u128` and
            // `i64 -> u64` were refused at the gate despite being modelled precisely —
            // the same producer-without-consumer split that made the provenance model
            // measure flat in R54. native.rs's merge note (2026-08-22) records that this
            // branch retired its own same-width Bitcast admit arm in favour of upstream's
            // stricter set; this restores it on the translator's terms.
            //
            // SOUNDNESS. A bitcast between two integer types of EQUAL bit width is the
            // identity on the bits: no truncation, no extension, no reinterpretation of
            // a sign bit that the BV carrier does not already represent. Signedness is
            // not part of the carrier, so `i128 -> u128` changes nothing the model can
            // observe. Widths are matched via `bit_width_with(HOST_POINTER_BITS)`, the
            // same call the translator uses, so `usize`/`isize` resolve identically on
            // both sides and cannot disagree.
            //
            // FAIL-CLOSED ON UNKNOWN WIDTH: the translator's `?` makes an unknown width
            // fall through to unsupported, so an admitted-but-unmodelled cast must be
            // impossible here. Both widths must be `Some` AND equal; a `None == None`
            // comparison would admit exactly the pair the translator refuses, which is
            // why this is written as an explicit match rather than `==` on the Options.
            let int_identity = src_ty.is_integer()
                && dst_ty.is_integer()
                && matches!(
                    (
                        src_ty.bit_width_with(HOST_POINTER_BITS),
                        dst_ty.bit_width_with(HOST_POINTER_BITS),
                    ),
                    (Some(src_width), Some(dst_width)) if src_width == dst_width
                );
            thin_thin
                || fat_same
                || thin_wrap
                || thin_unwrap
                || int_pack
                || int_unpack
                || int_identity
        }
        CastOp::PtrToInt => {
            is_thin_pointer_ty(src_ty) && is_pointer_width_unsigned_ty(dst_ty)
        }
        _ => false,
    }
}

const POINTER_NEWTYPE_FUEL: u32 = 8;

/// Recursion budget for [`ty_is_definitely_non_zst`] — a self-referential type table
/// entry must terminate at `false` (no bound) rather than spin.
const NON_ZST_FUEL: u32 = 8;

/// Trust (P0 ZST-slice-length FALSE PROOF): whether a value of `ty` is PROVABLY at
/// least one byte wide.
///
/// Conservative and FAIL-CLOSED — `true` only for shapes proved `>= 1` byte: a scalar
/// or pointer (`bit_width_with` reports a nonzero width), a NON-EMPTY array/vector of
/// a non-ZST element, and a tuple/struct with at least one non-ZST field. Everything
/// else — `Ty::Unit`, an empty or all-ZST aggregate, `[T; 0]`, an enum, a closure, an
/// unresolvable table id, or an unknown variant — answers `false`, i.e. NOT bounded,
/// which is the sound direction (a missed proof, never a false one).
///
/// Faithful port of `trust_vcgen::ty_is_definitely_non_zst` and the bridge's
/// `native_ty_is_definitely_non_zst`, which gate the SAME `len <= isize::MAX` bound in
/// the two other lanes; the recursion needs `module` here because trust-ir puts
/// array-element and struct-field types behind table ids.
fn ty_is_definitely_non_zst(module: &Module, ty: &Ty, fuel: u32) -> bool {
    if fuel == 0 {
        return false;
    }
    // Scalars, floats, thin/fat pointers, references, `Rc`, vectors: a nonzero bit
    // width IS the non-ZST proof. `Ty::Unit` and every aggregate report `None` here
    // and fall through to the structural arms below.
    if ty.bit_width_with(HOST_POINTER_BITS).is_some_and(|bits| bits > 0) {
        return true;
    }
    match ty {
        Ty::Array(elem, len) => {
            *len > 0
                && module
                    .ty(*elem)
                    .is_some_and(|elem| ty_is_definitely_non_zst(module, elem, fuel - 1))
        }
        Ty::Tuple(tys) => tys.iter().any(|t| ty_is_definitely_non_zst(module, t, fuel - 1)),
        Ty::Struct(id) => module.struct_def(*id).is_some_and(|def| {
            def.fields.iter().any(|f| ty_is_definitely_non_zst(module, &f.ty, fuel - 1))
        }),
        _ => false,
    }
}

/// Trust (P0 ZST-slice-length FALSE PROOF): whether the METADATA of a fat pointer of
/// type `ptr_ty` is a length provably confined to `[0, isize::MAX]`.
///
/// * `FatPtr(Str)` — the metadata is a BYTE length and every byte is one byte, so the
///   allocation-size limit bounds it UNCONDITIONALLY (the same `str`-vs-slice split
///   `trust_types::total_call_summaries::total_summary_len_bound` already draws).
/// * `FatPtr(Slice(elem))` — bounded ONLY when `elem` is provably non-ZST; a `&[()]`
///   length may legally reach `usize::MAX`.
/// * anything else — a `dyn Trait` vtable pointer, an element the module's type table
///   cannot resolve, or a non-fat `ptr_ty` spelling — is NOT bounded (fail-closed).
fn fat_ptr_metadata_len_is_isize_bounded(module: &Module, ptr_ty: &Ty) -> bool {
    match ptr_ty {
        Ty::FatPtr(FatPtrKind::Str) => true,
        Ty::FatPtr(FatPtrKind::Slice(elem)) => module
            .ty(*elem)
            .is_some_and(|elem| ty_is_definitely_non_zst(module, elem, NON_ZST_FUEL)),
        _ => false,
    }
}

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
    //! mem2reg promotion: a loop-carried mutable stack alloca used ONLY via direct
    //! Load/Store must become threaded block-relation state (so a loop predicate is
    //! no longer nullary), while any aliased alloca must be left un-promoted
    //! (soundness). The cell may be a precise scalar or a trackable AGGREGATE; the
    //! `build_aggregate_clamp_join` fixtures below carry the aggregate half,
    //! including the CFG-merge and definite-initialization hazards.
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

    /// The `let k = if i < 8 { i } else { 7 };` shape, exactly as rustc's MIR and
    /// `trust-ir-bridge::promote_local_to_memory` lower a local written in more
    /// than one block: ALLOCA in the entry block, a STORE in each arm, a LOAD in
    /// the join. Returns `(module, cell, join_block)`.
    fn build_clamp_join(
        volatile_join_store: bool,
        aligned_join_store: bool,
        alias_the_cell: bool,
    ) -> (Module, ValueId, BlockId) {
        let mut mb = ModuleBuilder::new("mem2reg_clamp_join");
        let ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut fb = mb.function("slot_index", ft);

        let entry = fb.create_block();
        let then_block = fb.create_block();
        let else_block = fb.create_block();
        let join = fb.create_block();
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let i = fb.add_block_param(entry, Ty::U64);
        let cell = fb.alloca(Ty::U64);
        let eight = fb.iconst(Ty::U64, 8);
        let lt = fb.icmp(ICmpOp::Ult, Ty::U64, i, eight);
        fb.condbr(lt, then_block, vec![], else_block, vec![]);

        // then: k = i
        fb.switch_to_block(then_block);
        fb.store(Ty::U64, cell, i);
        fb.br(join, vec![]);

        // else: k = 7
        fb.switch_to_block(else_block);
        let seven = fb.iconst(Ty::U64, 7);
        if volatile_join_store {
            fb.store_volatile(Ty::U64, cell, seven);
        } else if aligned_join_store {
            fb.store_aligned(Ty::U64, cell, seven, 8);
        } else {
            fb.store(Ty::U64, cell, seven);
        }
        fb.br(join, vec![]);

        // join: return k  (optionally leaking the cell pointer first)
        fb.switch_to_block(join);
        if alias_the_cell {
            let sink = fb.alloca(Ty::Ptr);
            fb.store(Ty::Ptr, sink, cell);
        }
        let k = fb.load(Ty::U64, cell);
        fb.ret(vec![k]);
        fb.build();

        (mb.build(), cell, join)
    }

    /// THE gap this lane closes: the cross-block clamp/join cell is modeled
    /// EXACTLY by mem2reg, but the block-local admission clause rejects it
    /// because its accesses are not in the defining block. Both halves are
    /// asserted so the differential — not just the final verdict — is pinned.
    #[test]
    fn admits_cross_block_promoted_cell_the_block_local_clause_rejects() {
        let (module, cell, _join) = build_clamp_join(false, false, false);
        let func = &module.functions[0];

        assert!(
            !block_local_alloca_is_admissible(func, cell, &Ty::U64),
            "the store/load are outside the defining block, so lane 1 must still reject"
        );
        assert!(
            promoted_cell_alloca_is_admissible(&module, func, cell, &Ty::U64),
            "an un-aliased scalar cell the translator promotes is exactly modeled across blocks"
        );
        assert!(single_cell_alloca_is_admissible(&module, func, cell, &Ty::U64));

        // The admission premise must be the translator's OWN verdict.
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(func, &module, &options);
        let (promoted, _def) = translator.compute_promotable_cells();
        assert!(
            promoted.iter().any(|(value, _)| value.index() == cell.index()),
            "admission is granted only for a cell the translator actually promotes"
        );
    }

    /// A volatile STORE to a promoted cell in a non-def block is classified
    /// `NoTrackedTarget` (no `ptr_provenance` outside the def block, nothing
    /// escaped), so the cell keeps its PRE-store value while `stack_ptrs`
    /// suppresses the fail-closed error — a stale read, i.e. a false-prove
    /// generator. It must never reach the proof lane.
    #[test]
    fn rejects_volatile_access_on_a_promoted_cell() {
        let (module, cell, _join) = build_clamp_join(true, false, false);
        let func = &module.functions[0];
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(func, &module, &options);
        let (promoted, _def) = translator.compute_promotable_cells();
        assert!(
            promoted.iter().any(|(value, _)| value.index() == cell.index()),
            "the promotion analysis itself ignores `volatile` — which is exactly why \
             admission must not"
        );
        assert!(!single_cell_alloca_is_admissible(&module, func, cell, &Ty::U64));
    }

    /// The translator ignores `align` entirely, so a caller-asserted alignment is
    /// an unmodeled claim and must stay out of the proof lane.
    #[test]
    fn rejects_caller_asserted_alignment_on_a_promoted_cell() {
        let (module, cell, _join) = build_clamp_join(false, true, false);
        let func = &module.functions[0];
        assert!(!single_cell_alloca_is_admissible(&module, func, cell, &Ty::U64));
    }

    /// An aliased cell is not promoted, so neither lane may admit it.
    #[test]
    fn rejects_aliased_cross_block_cell() {
        let (module, cell, _join) = build_clamp_join(false, false, true);
        let func = &module.functions[0];
        assert!(!single_cell_alloca_is_admissible(&module, func, cell, &Ty::U64));
    }

    /// An uninitialized read must stay fail-closed. The translator seeds an
    /// un-stored cell with ONE stable fresh symbol, which is self-consistent
    /// across reads — strictly weaker than `undef`, hence a false-prove shape
    /// rather than an over-approximation.
    #[test]
    fn rejects_a_cross_block_load_of_an_unstored_cell() {
        let mut mb = ModuleBuilder::new("mem2reg_uninit_join");
        let ft = mb.add_func_type(vec![Ty::Bool], vec![Ty::U64]);
        let mut fb = mb.function("uninit_join", ft);

        let entry = fb.create_block();
        let stores = fb.create_block();
        let skips = fb.create_block();
        let join = fb.create_block();
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        let cell = fb.alloca(Ty::U64);
        fb.condbr(cond, stores, vec![], skips, vec![]);

        // Only ONE arm writes the cell.
        fb.switch_to_block(stores);
        let seven = fb.iconst(Ty::U64, 7);
        fb.store(Ty::U64, cell, seven);
        fb.br(join, vec![]);

        fb.switch_to_block(skips);
        fb.br(join, vec![]);

        fb.switch_to_block(join);
        let k = fb.load(Ty::U64, cell);
        fb.ret(vec![k]);
        fb.build();

        let module = mb.build();
        let func = &module.functions[0];
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(func, &module, &options);
        let (promoted, _def) = translator.compute_promotable_cells();
        assert!(
            promoted.iter().any(|(value, _)| value.index() == cell.index()),
            "the cell is still un-aliased, so promotion alone would admit it — which is \
             exactly why admission also demands definite initialization"
        );
        assert!(!promoted_cell_is_definitely_initialized(func, cell.index()));
        assert!(!single_cell_alloca_is_admissible(&module, func, cell, &Ty::U64));
    }

    /// A loop whose only store is inside the body does NOT initialize the header's
    /// load: the header's meet includes the entry's uninitialized state. Pins that
    /// the optimistic-top fixpoint does not fabricate initialization around a back
    /// edge.
    #[test]
    fn rejects_a_loop_header_load_initialized_only_inside_the_loop() {
        let mut mb = ModuleBuilder::new("mem2reg_loop_uninit");
        let ft = mb.add_func_type(vec![], vec![]);
        let mut fb = mb.function("loop_uninit", ft);

        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let cell = fb.alloca(Ty::I64);
        fb.br(header, vec![]);

        fb.switch_to_block(header);
        let cur = fb.load(Ty::I64, cell); // reads before any store on the first pass
        let ten = fb.iconst(Ty::I64, 10);
        let cmp = fb.icmp(ICmpOp::Slt, Ty::I64, cur, ten);
        fb.condbr(cmp, body, vec![], exit, vec![]);

        fb.switch_to_block(body);
        let one = fb.iconst(Ty::I64, 1);
        fb.store(Ty::I64, cell, one);
        fb.br(header, vec![]);

        fb.switch_to_block(exit);
        fb.ret(vec![]);
        fb.build();

        let module = mb.build();
        let func = &module.functions[0];
        assert!(!promoted_cell_is_definitely_initialized(func, cell.index()));
        assert!(!single_cell_alloca_is_admissible(&module, func, cell, &Ty::I64));
    }

    /// The counterpart: `build_count_to_ten` stores in the entry block before the
    /// loop, so the same header load IS definitely initialized.
    #[test]
    fn admits_a_loop_carried_cell_initialized_before_the_loop() {
        let (module, acc, ..) = build_count_to_ten();
        let func = &module.functions[0];
        assert!(promoted_cell_is_definitely_initialized(func, acc.index()));
        assert!(single_cell_alloca_is_admissible(&module, func, acc, &Ty::I64));
    }

    /// Which hazard the aggregate clamp/join fixture carries.
    #[derive(Clone, Copy, Debug)]
    enum AggregateJoinShape {
        /// Both arms store the whole cell; the join loads it. The control.
        Clean,
        /// Only the `then` arm stores — the join's load is uninitialized on the
        /// `else` path, so promotion alone would fabricate a value.
        OneArmOnly,
        /// The `else` arm's store is `volatile`.
        VolatileStore,
        /// The `else` arm's store carries a caller-asserted alignment.
        AlignedStore,
        /// The `else` arm stores a DIFFERENT type through the cell pointer.
        MismatchedStore,
        /// The join takes a `GEP` on the cell pointer — a FIELD PROJECTION.
        FieldProjected,
        /// The join leaks the cell pointer into another cell.
        Aliased,
    }

    /// The aggregate twin of `build_clamp_join`, in the shape the bridge lowers a
    /// multi-block aggregate local into: ALLOCA in the entry block, a whole-cell
    /// STORE in each arm, a whole-cell LOAD in the join. Returns
    /// `(module, cell, cell ty, join block)`.
    fn build_aggregate_clamp_join(shape: AggregateJoinShape) -> (Module, ValueId, Ty, BlockId) {
        let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
        let mut mb = ModuleBuilder::new("mem2reg_aggregate_join");
        let ft = mb.add_func_type(vec![Ty::Bool, pair.clone()], vec![pair.clone()]);
        let mut fb = mb.function("pair_join", ft);

        let entry = fb.create_block();
        let then_block = fb.create_block();
        let else_block = fb.create_block();
        let join = fb.create_block();
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        let p = fb.add_block_param(entry, pair.clone());
        let cell = fb.alloca(pair.clone());
        fb.condbr(cond, then_block, vec![], else_block, vec![]);

        fb.switch_to_block(then_block);
        fb.store(pair.clone(), cell, p);
        fb.br(join, vec![]);

        fb.switch_to_block(else_block);
        let seven = fb.iconst(Ty::U64, 7);
        let q = fb.insert_field(pair.clone(), p, 0, seven);
        match shape {
            AggregateJoinShape::OneArmOnly => {}
            AggregateJoinShape::VolatileStore => fb.store_volatile(pair.clone(), cell, q),
            AggregateJoinShape::AlignedStore => fb.store_aligned(pair.clone(), cell, q, 8),
            AggregateJoinShape::MismatchedStore => fb.store(Ty::U64, cell, seven),
            _ => fb.store(pair.clone(), cell, q),
        }
        fb.br(join, vec![]);

        fb.switch_to_block(join);
        match shape {
            AggregateJoinShape::FieldProjected => {
                let zero = fb.iconst(Ty::U64, 0);
                let _addr = fb.gep(Ty::U64, cell, vec![zero]);
            }
            AggregateJoinShape::Aliased => {
                let sink = fb.alloca(Ty::Ptr);
                fb.store(Ty::Ptr, sink, cell);
            }
            _ => {}
        }
        let k = fb.load(pair.clone(), cell);
        fb.ret(vec![k]);
        fb.build();

        (mb.build(), cell, pair, join)
    }

    fn relation_arity(output: &ChcTranslationOutput, block: BlockId) -> usize {
        output
            .vc
            .relations
            .iter()
            .find(|rel| rel.name == block_relation_name(block))
            .expect("the block relation is declared")
            .arity()
    }

    /// END TO END: a cross-block AGGREGATE cell is promoted and its leaves are
    /// threaded through the join relation, exactly as a scalar cell's single leaf
    /// is. The arity DIFFERENTIAL against the aliased build is what pins "two
    /// leaves, one per tuple field" without hard-coding the (liveness-dependent)
    /// threaded-parameter prefix.
    #[test]
    fn promotes_and_threads_a_cross_block_aggregate_cell() {
        let (module, cell, pair, join) = build_aggregate_clamp_join(AggregateJoinShape::Clean);
        let func = &module.functions[0];
        let options = TranslateOptions::default();

        let translator = ChcFuncTranslator::new(func, &module, &options);
        let (promoted, def_block) = translator.compute_promotable_cells();
        assert!(
            promoted.iter().any(|(value, ty)| *value == cell && *ty == pair),
            "the un-aliased whole-cell tuple must be promoted"
        );
        assert_eq!(def_block.get(&cell.index()), Some(&func.entry));

        assert!(
            block_local_alloca_reject(func, cell, &pair).is_some(),
            "lane 1 is block-local, so it still rejects the cross-block accesses"
        );
        assert!(single_cell_alloca_is_admissible(&module, func, cell, &pair));

        let output = translate_function(func, &module, &options);
        assert!(output.diagnostics.is_empty(), "the promoted aggregate lowers with no diagnostics");

        let (aliased_module, ..) = build_aggregate_clamp_join(AggregateJoinShape::Aliased);
        let aliased = translate_function(&aliased_module.functions[0], &aliased_module, &options);
        assert_eq!(
            relation_arity(&output, join) - relation_arity(&aliased, join),
            2,
            "promotion adds exactly one relation leaf per flattened tuple field"
        );
    }

    /// LEAF-ARITY AGREEMENT, the one thing a malformed CHC could come from. In the
    /// block-local lane an aggregate cell binding never crosses a relation boundary;
    /// in the promotion lane it does, so the declaration
    /// (`declare_relation_binding_rec`) and every application (`flat_args` of the
    /// binding built by `fresh_stack_cell_value` at the `Alloca` and by
    /// `resolve_aggregate` at each `Store`) must expand the type identically.
    /// A NESTED cell exercises the recursion; the two expansions differ in field
    /// precedence (`resolve_field_binding` tests `is_scalar_field_ty` first,
    /// `declare_relation_binding_rec` tests `aggregate_field_tys_of` first), which is
    /// only benign because those two predicates are disjoint — this pins that.
    #[test]
    fn a_nested_aggregate_cell_threads_one_relation_leaf_per_scalar_leaf() {
        let inner = Ty::Tuple(vec![Ty::U64, Ty::Bool]);
        let outer = Ty::Tuple(vec![Ty::U64, inner, Ty::Unit]);

        let build = |alias: bool| {
            let mut mb = ModuleBuilder::new("mem2reg_nested_join");
            let ft = mb.add_func_type(vec![Ty::Bool, outer.clone()], vec![outer.clone()]);
            let mut fb = mb.function("nested_join", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let else_block = fb.create_block();
            let join = fb.create_block();
            fb.set_entry(entry);

            fb.switch_to_block(entry);
            let cond = fb.add_block_param(entry, Ty::Bool);
            let p = fb.add_block_param(entry, outer.clone());
            let cell = fb.alloca(outer.clone());
            fb.condbr(cond, then_block, vec![], else_block, vec![]);

            fb.switch_to_block(then_block);
            fb.store(outer.clone(), cell, p);
            fb.br(join, vec![]);

            fb.switch_to_block(else_block);
            let seven = fb.iconst(Ty::U64, 7);
            let q = fb.insert_field(outer.clone(), p, 0, seven);
            fb.store(outer.clone(), cell, q);
            fb.br(join, vec![]);

            fb.switch_to_block(join);
            if alias {
                let sink = fb.alloca(Ty::Ptr);
                fb.store(Ty::Ptr, sink, cell);
            }
            let k = fb.load(outer.clone(), cell);
            fb.ret(vec![k]);
            fb.build();
            (mb.build(), cell, join)
        };

        let (module, cell, join) = build(false);
        let (aliased_module, ..) = build(true);
        let options = TranslateOptions::default();

        assert!(single_cell_alloca_is_admissible(&module, &module.functions[0], cell, &outer));
        let output = translate_function(&module.functions[0], &module, &options);
        let aliased = translate_function(&aliased_module.functions[0], &aliased_module, &options);
        assert!(output.diagnostics.is_empty());
        assert_eq!(
            relation_arity(&output, join) - relation_arity(&aliased, join),
            3,
            "(u64, (u64, bool), ()) is three scalar leaves — the unit field contributes none"
        );
    }

    /// THE JOIN. Each incoming edge of the join carries the SOURCE block's own cell
    /// leaves — there is no leaf-wise merge function and no shared default — so the
    /// two arms' rules must reach the join relation with DIFFERENT arguments. A
    /// single rule, or two identical ones, would mean one arm's stored value is
    /// readable on the other arm's path (a false proof).
    #[test]
    fn each_join_edge_carries_its_own_predecessors_aggregate_leaves() {
        let (module, .., join) = build_aggregate_clamp_join(AggregateJoinShape::Clean);
        let options = TranslateOptions::default();
        let output = translate_function(&module.functions[0], &module, &options);

        let name = block_relation_name(join);
        let heads: Vec<&Vec<Expr>> = output
            .vc
            .rules
            .iter()
            .filter(|rule| *rule.head.name == *name)
            .map(|rule| rule.head.args.as_ref())
            .collect();
        assert_eq!(heads.len(), 2, "one transition rule per predecessor arm");
        assert_ne!(
            format!("{:?}", heads[0]),
            format!("{:?}", heads[1]),
            "the two arms must reach the join with different cell leaves"
        );
    }

    /// A cell stored on ONE branch only is uninitialized on the other path. The
    /// translator seeds an un-stored cell with ONE stable fresh binding, which is
    /// self-consistent across reads rather than `undef` — a false-prove shape — so
    /// definite initialization must refuse it for an aggregate exactly as it does
    /// for a scalar.
    #[test]
    fn rejects_an_aggregate_cell_stored_on_one_branch_only() {
        let (module, cell, pair, _join) =
            build_aggregate_clamp_join(AggregateJoinShape::OneArmOnly);
        let func = &module.functions[0];
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(func, &module, &options);
        let (promoted, _def) = translator.compute_promotable_cells();
        assert!(
            promoted.iter().any(|(value, _)| *value == cell),
            "the cell is still un-aliased, so promotion alone would admit it — which is \
             exactly why admission also demands definite initialization"
        );
        assert!(!promoted_cell_is_definitely_initialized(func, cell.index()));
        assert!(!single_cell_alloca_is_admissible(&module, func, cell, &pair));
    }

    /// The four remaining hazards, unchanged by the widening: a volatile store (kept
    /// as a promoted cell by the analysis, which ignores `volatile`, and therefore
    /// refused by admission), an unmodeled alignment claim, a type-punned store, and
    /// a field projection. None may reach the proof lane for an aggregate cell any
    /// more than for a scalar one.
    #[test]
    fn aggregate_cell_hazards_stay_fail_closed() {
        // The lane-2 bucket is pinned, not just the verdict: a hazard that were
        // rejected for the WRONG reason (e.g. the field projection passing the
        // escape check and being caught only by definite initialization) would be a
        // guard that stops working the moment the fixture changes shape.
        for (shape, expected) in [
            (AggregateJoinShape::VolatileStore, "access_volatile"),
            (AggregateJoinShape::AlignedStore, "access_aligned"),
            (AggregateJoinShape::MismatchedStore, "not_promotable.access_type_mismatch"),
            (AggregateJoinShape::FieldProjected, "not_promotable.pointer_used_by_instruction"),
            (AggregateJoinShape::Aliased, "not_promotable.pointer_stored_as_value"),
        ] {
            let (module, cell, pair, _join) = build_aggregate_clamp_join(shape);
            let func = &module.functions[0];
            let rejection = single_cell_alloca_rejection(&module, func, cell, &pair)
                .unwrap_or_else(|| panic!("{shape:?} must stay fail-closed"));
            assert_eq!(rejection.promoted.kind(), expected, "{shape:?} refused for the wrong reason");
        }
    }

    #[test]
    fn def_block_projection_gate_obeys_the_explicit_opt_in() {
        let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
        let mut mb = ModuleBuilder::new("mem2reg_def_block_projection");
        let ft = mb.add_func_type(vec![pair.clone()], vec![pair.clone()]);
        let mut fb = mb.function("projected", ft);
        let entry = fb.create_block();
        let join = fb.create_block();
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let seed = fb.add_block_param(entry, pair.clone());
        let cell = fb.alloca(pair.clone());
        fb.store(pair.clone(), cell, seed);
        let zero = fb.iconst(Ty::U64, 0);
        let field = fb.gep(Ty::U64, cell, vec![zero]);
        let seven = fb.iconst(Ty::U64, 7);
        fb.store(Ty::U64, field, seven);
        fb.br(join, vec![]);

        fb.switch_to_block(join);
        let value = fb.load(pair.clone(), cell);
        fb.ret(vec![value]);
        fb.build();

        let module = mb.build();
        let admitted =
            single_cell_alloca_rejection(&module, &module.functions[0], cell, &pair).is_none();
        assert_eq!(
            admitted,
            promote_def_block_projections(),
            "only TRUST_PROMOTE_DEF_BLOCK_PROJECTIONS may admit this exact projection"
        );
    }

    /// R68 fixtures, and the shape R67 MEASURED as ny-cert's dominant Alloca
    /// refusal: a local that is BORROWED, with its store and load straddling block
    /// boundaries. The promoted-lane `pointer_used_by_instruction` records name
    /// `Borrow` 42 times and `BorrowMut` 27 against `GEP` 3 — so the
    /// `build_aggregate_clamp_join` fixtures above model the RARE case. This models
    /// the common one.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum BorrowShape {
        /// `&mut local`, stored through in a LATER block and loaded in a third —
        /// the transparent alias `translate_node`'s Borrow arm models exactly.
        Transparent,
        /// The same, on a SCALAR cell. Pins that this arm deliberately does not
        /// require a projectable aggregate: unlike a GEP, a borrow selects the
        /// WHOLE cell, so there is no leaf for it to miss. R67 sees `ty=u64`.
        ScalarTransparent,
        /// THE HAZARD: the borrow RESULT is written into memory. A borrow binds a
        /// NEW SSA id, so step 2's candidate-id alias check is structurally blind
        /// to it; only the escape classifier's derivation closure sees it.
        StoredAsValue,
    }

    fn build_borrowed_cross_block(shape: BorrowShape) -> (Module, ValueId, Ty) {
        let cell_ty = if shape == BorrowShape::ScalarTransparent {
            Ty::U64
        } else {
            Ty::Tuple(vec![Ty::U64, Ty::U64])
        };
        let mut mb = ModuleBuilder::new("mem2reg_borrow_cross_block");
        let ft = mb.add_func_type(vec![Ty::Bool, cell_ty.clone()], vec![cell_ty.clone()]);
        let mut fb = mb.function("borrowed", ft);

        let entry = fb.create_block();
        let arm = fb.create_block();
        let join = fb.create_block();
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        let seed = fb.add_block_param(entry, cell_ty.clone());
        let cell = fb.alloca(cell_ty.clone());
        fb.store(cell_ty.clone(), cell, seed); // definite initialization in the def block
        let borrowed = fb.borrow_mut(cell); // THE BORROW
        if shape == BorrowShape::StoredAsValue {
            let sink = fb.alloca(Ty::Ptr);
            fb.store(Ty::Ptr, sink, borrowed); // the ADDRESS goes into memory
        }
        fb.condbr(cond, arm, vec![], join, vec![]);

        // Cross-block, and THROUGH the borrow — the exact shape that lands in the
        // `store_in_other_block` bucket (109 of ny-cert's 159 Alloca rows).
        fb.switch_to_block(arm);
        fb.store(cell_ty.clone(), borrowed, seed);
        fb.br(join, vec![]);

        fb.switch_to_block(join);
        let out = fb.load(cell_ty.clone(), cell);
        fb.ret(vec![out]);
        fb.build();

        (mb.build(), cell, cell_ty)
    }

    /// Run the real step-2 predicate on the fixture's borrow. Called directly
    /// because `promote_cell_borrows()` is a process-global `OnceLock` — a pin that
    /// could only run under an env var is a pin that does not run.
    fn borrow_is_transparently_promotable(module: &Module, cell: ValueId) -> bool {
        let func = &module.functions[0];
        func.blocks
            .iter()
            .flat_map(|block| block.body.iter())
            .find(|node| {
                matches!(
                    &node.inst,
                    Inst::Borrow { ptr } | Inst::BorrowMut { ptr } if ptr.index() == cell.index()
                )
            })
            .map(|node| borrow_use_is_transparently_promotable(func, &node.inst, cell))
            .expect("the fixture borrows the cell")
    }

    /// THE FALSE-PROOF TRIPWIRE for the R68 borrow arm. If this ever goes green the
    /// widening is UNSOUND: the cell's address is in memory, an unknown store can
    /// reach it, and promoting it would thread a value that a later write through
    /// the leaked pointer silently invalidates.
    ///
    /// Step 2's own alias check cannot catch this — it tests whether the CANDIDATE's
    /// id appears as a `Store` value, and a borrow binds a new id. The escape
    /// classification is the only thing standing here, which is why the arm requires
    /// it rather than treating it as a precision filter.
    #[test]
    fn a_borrow_stored_as_a_value_is_still_refused() {
        let (module, cell, _) = build_borrowed_cross_block(BorrowShape::StoredAsValue);
        assert!(
            !borrow_is_transparently_promotable(&module, cell),
            "a borrow whose RESULT is written into memory must never be promotable",
        );
        assert_eq!(
            stack_alloca_escape_classification(&module.functions[0], cell),
            StackCellEscape::Unbounded,
            "and it must be refused for the ESCAPE reason, not incidentally",
        );
    }

    /// The positive half: the transparent cross-block borrow the arm exists to
    /// admit, on both an aggregate and a scalar cell.
    #[test]
    fn a_transparent_cross_block_borrow_is_promotable() {
        for shape in [BorrowShape::Transparent, BorrowShape::ScalarTransparent] {
            let (module, cell, _) = build_borrowed_cross_block(shape);
            assert!(borrow_is_transparently_promotable(&module, cell), "{shape:?}");
            assert_ne!(
                stack_alloca_escape_classification(&module.functions[0], cell),
                StackCellEscape::Unbounded,
                "{shape:?} must not be Unbounded",
            );
        }
    }

    /// DEFAULT-LANE INERTNESS, and bucket preservation. With the flag off every
    /// shape stays refused, in the SAME histogram bucket as before the change, so
    /// gate logs remain comparable across it.
    ///
    /// Like the R49 inertness pins, this test is EXPECTED to fail when the suite is
    /// run with `TRUST_PROMOTE_CELL_BORROWS` set — that failure is the pin working,
    /// and is the evidence the lever actually bites. It must not be weakened to
    /// accommodate the flag.
    #[test]
    fn the_borrow_arm_is_default_off_and_bucket_preserving() {
        for shape in [
            BorrowShape::Transparent,
            BorrowShape::ScalarTransparent,
            BorrowShape::StoredAsValue,
        ] {
            let (module, cell, ty) = build_borrowed_cross_block(shape);
            let func = &module.functions[0];
            let rejection = single_cell_alloca_rejection(&module, func, cell, &ty)
                .unwrap_or_else(|| panic!("{shape:?} must stay refused in the default lane"));
            assert_eq!(
                rejection.promoted.kind(),
                "not_promotable.pointer_used_by_instruction",
                "{shape:?} refused for the wrong reason",
            );
        }
    }

    #[test]
    fn transparent_borrow_gate_obeys_the_explicit_opt_in() {
        for shape in [BorrowShape::Transparent, BorrowShape::ScalarTransparent] {
            let (module, cell, ty) = build_borrowed_cross_block(shape);
            let admitted =
                single_cell_alloca_rejection(&module, &module.functions[0], cell, &ty).is_none();
            assert_eq!(
                admitted,
                promote_cell_borrows(),
                "only TRUST_PROMOTE_CELL_BORROWS may admit {shape:?}"
            );
        }

        let (module, cell, ty) = build_borrowed_cross_block(BorrowShape::StoredAsValue);
        assert!(
            single_cell_alloca_rejection(&module, &module.functions[0], cell, &ty).is_some(),
            "a borrow stored as a value must remain fail-closed in both modes"
        );
    }

    #[test]
    fn call_escape_admission_gate_obeys_the_explicit_opt_in() {
        let mut mb = ModuleBuilder::new("alloca_call_escape_gate");
        let caller_ty = mb.add_func_type(vec![], vec![]);
        let callee_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);

        let mut caller = mb.function("caller", caller_ty);
        let entry = caller.create_block();
        caller.set_entry(entry);
        caller.switch_to_block(entry);
        let cell = caller.alloca(Ty::I64);
        let one = caller.iconst(Ty::I64, 1);
        caller.store(Ty::I64, cell, one);
        let borrowed = caller.borrow_mut(cell);
        let _call = caller.call(FuncId::new(1), vec![borrowed]);
        let _value = caller.load(Ty::I64, cell);
        caller.ret(vec![]);
        caller.build();

        let mut callee = mb.function("sink", callee_ty);
        let entry = callee.create_block();
        callee.set_entry(entry);
        callee.switch_to_block(entry);
        let _pointer = callee.add_block_param(entry, Ty::Ptr);
        callee.ret(vec![]);
        callee.build();

        let module = mb.build();
        assert_eq!(
            stack_alloca_escape_classification(&module.functions[0], cell),
            StackCellEscape::IntoCallsOnly
        );
        let admitted =
            single_cell_alloca_rejection(&module, &module.functions[0], cell, &Ty::I64).is_none();
        assert_eq!(
            admitted,
            std::env::var_os("TRUST_ALLOCA_ESCAPE_GATE_WIDEN").is_some(),
            "only TRUST_ALLOCA_ESCAPE_GATE_WIDEN may admit this call-escaping cell"
        );
    }

    /// The refactor that made the admission predicate call the translator's
    /// promotion analysis must be behavior-identical for the translator.
    #[test]
    fn free_and_method_promotion_analyses_agree() {
        let (module, ..) = build_count_to_ten();
        let func = &module.functions[0];
        let options = TranslateOptions::default();
        let translator = ChcFuncTranslator::new(func, &module, &options);
        assert_eq!(
            translator.compute_promotable_cells().0.len(),
            compute_promotable_cells_of(&module, func).0.len()
        );
        assert_eq!(
            translator.compute_promotable_cells().1,
            compute_promotable_cells_of(&module, func).1
        );
    }
}

#[cfg(test)]
mod unsupported_reason_label_tests {
    //! The typed fail-closed reason must reach the transport as a legible label.
    //! Before this, only the COUNT crossed the boundary, so a demoted obligation
    //! reported "N unsupported trust_ir construct(s)" with no way to learn which
    //! of the ~50 constructs blocked it.
    use super::TrustIrChcUnsupportedReason;

    /// The label is the variant name, verbatim — pinned for the families that
    /// actually show up on the ny-cert frontier.
    #[test]
    fn label_is_the_variant_name() {
        assert_eq!(TrustIrChcUnsupportedReason::Cast.label(), "Cast");
        assert_eq!(TrustIrChcUnsupportedReason::IndirectCall.label(), "IndirectCall");
        assert_eq!(TrustIrChcUnsupportedReason::HeapAllocation.label(), "HeapAllocation");
        assert_eq!(
            TrustIrChcUnsupportedReason::FloatingPointArithmetic.label(),
            "FloatingPointArithmetic"
        );
        assert_eq!(
            TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel.label(),
            "MemoryAccessWithoutPreciseModel"
        );
    }

    /// Distinct reasons must not collide onto one label, or the surfaced list
    /// would silently under-report the blocking families.
    #[test]
    fn labels_are_distinct_across_the_families_we_surface() {
        let reasons = [
            TrustIrChcUnsupportedReason::Cast,
            TrustIrChcUnsupportedReason::UnaryOperation,
            TrustIrChcUnsupportedReason::AggregateProjection,
            TrustIrChcUnsupportedReason::AggregateUpdate,
            TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel,
            TrustIrChcUnsupportedReason::HeapAllocation,
            TrustIrChcUnsupportedReason::PointerArithmetic,
            TrustIrChcUnsupportedReason::Switch,
            TrustIrChcUnsupportedReason::IndirectCall,
            TrustIrChcUnsupportedReason::UnknownDirectCall,
            TrustIrChcUnsupportedReason::RecursiveDirectCall,
            TrustIrChcUnsupportedReason::FloatingPointArithmetic,
            TrustIrChcUnsupportedReason::FloatingPointComparison,
        ];
        let mut labels: Vec<String> = reasons.iter().map(|r| r.label()).collect();
        let total = labels.len();
        labels.sort();
        labels.dedup();
        assert_eq!(labels.len(), total, "reason labels must be injective: {labels:?}");
    }
}

#[cfg(test)]
mod alloca_reject_taxonomy_tests {
    //! The `Alloca` admission gate holds the largest block of unknown rows on the
    //! ny-cert strict lane, and "411 rejections" says nothing about WHY. These
    //! tests pin one synthetic function per rejection reason so the histogram the
    //! driver prints is trustworthy, and — more importantly — prove the
    //! reason-returning rewrite is VERDICT-INERT: `*_reference` holds the original
    //! boolean bodies verbatim and `parity_with_the_original_boolean_predicates`
    //! runs every fixture through both.
    use super::*;
    use trust_ir::dialect::DialectInst;
    use trust_ir::ty::{EnumDef, EnumVariant};
    use trust_ir::value::{EnumId, FuncTyId, TyId};

    /// The fixtures are hand-built `Function`s, so the module only has to answer
    /// `aggregate_field_tys_of` for the types they use. `Ty::Tuple` carries its own
    /// field types, so the only entry that matters is the ENUM definition — and even
    /// that is present for honesty rather than necessity: `immediate_aggregate_field_tys`
    /// has no `Ty::Enum` arm at all, so a defined and an undefined enum are equally
    /// non-trackable.
    fn taxonomy_module() -> Module {
        let mut module = Module::new("alloca_taxonomy");
        module.enums.push(EnumDef::new(
            EnumId::new(0),
            "Choice",
            vec![
                EnumVariant {
                    name: "A".to_string(),
                    fields: Vec::new(),
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "B".to_string(),
                    fields: vec![Ty::I64],
                    field_names: Vec::new(),
                },
            ],
        ));
        module
    }

    fn func(entry: u32, blocks: Vec<Block>) -> Function {
        let mut function =
            Function::new(FuncId::new(0), "alloca_taxonomy", FuncTyId::new(0), BlockId::new(entry));
        function.blocks = blocks;
        function
    }

    fn block(id: u32, body: Vec<InstrNode>) -> Block {
        let mut block = Block::new(BlockId::new(id));
        block.body = body;
        block
    }

    fn alloca(result: u32, ty: Ty) -> InstrNode {
        InstrNode::new(Inst::Alloca { ty, count: None, align: None })
            .with_result(ValueId::new(result))
    }

    fn store(ptr: u32, value: u32, ty: Ty) -> InstrNode {
        InstrNode::new(Inst::Store {
            ty,
            ptr: ValueId::new(ptr),
            value: ValueId::new(value),
            volatile: false,
            align: None,
        })
    }

    fn load(result: u32, ptr: u32, ty: Ty) -> InstrNode {
        InstrNode::new(Inst::Load {
            ty,
            ptr: ValueId::new(ptr),
            volatile: false,
            align: None,
        })
        .with_result(ValueId::new(result))
    }

    fn ret() -> InstrNode {
        InstrNode::new(Inst::Return { values: Vec::new() })
    }

    fn br(target: u32) -> InstrNode {
        InstrNode::new(Inst::Br { target: BlockId::new(target), args: Vec::new() })
    }

    /// Every fixture below, as `(label, function, cell, cell ty)`.
    fn fixtures() -> Vec<(&'static str, Function, ValueId, Ty)> {
        let cell = ValueId::new(0);
        let i64_ = Ty::I64;
        let mut all: Vec<(&'static str, Function, ValueId, Ty)> = Vec::new();

        // Admitted control: block-local scalar, store then load.
        all.push((
            "admissible_block_local",
            func(0, vec![block(0, vec![alloca(0, i64_.clone()), store(0, 1, i64_.clone()),
                load(2, 0, i64_.clone()), ret()])]),
            cell,
            i64_.clone(),
        ));

        // Lane 1: the pointee is neither a precise scalar nor an aggregate.
        let fat = Ty::FatPtr(FatPtrKind::Slice(TyId::new(0)));
        all.push((
            "pointee_not_scalar_or_aggregate",
            func(0, vec![block(0, vec![alloca(0, fat.clone()), ret()])]),
            cell,
            fat,
        ));

        // No `Alloca { count: None, align: None, ty }` defines the cell: here the
        // defining alloca carries a DIFFERENT type than the one being admitted.
        all.push((
            "no_exact_defining_alloca",
            func(0, vec![block(0, vec![alloca(0, Ty::I32), ret()])]),
            cell,
            i64_.clone(),
        ));

        // A load in a block other than the defining one. This is the shape
        // `trust-ir-bridge::promote_local_to_memory` emits for EVERY multi-block
        // local, which is the only reason it emits an `Alloca` at all.
        all.push((
            "load_in_other_block",
            func(
                0,
                vec![
                    block(0, vec![alloca(0, i64_.clone()), store(0, 1, i64_.clone()), br(1)]),
                    block(1, vec![load(2, 0, i64_.clone()), ret()]),
                ],
            ),
            cell,
            i64_.clone(),
        ));
        all.push((
            "store_in_other_block",
            func(
                0,
                vec![
                    block(0, vec![alloca(0, i64_.clone()), br(1)]),
                    block(1, vec![store(0, 1, i64_.clone()), ret()]),
                ],
            ),
            cell,
            i64_.clone(),
        ));

        all.push((
            "load_before_store",
            func(0, vec![block(0, vec![alloca(0, i64_.clone()), load(2, 0, i64_.clone()), ret()])]),
            cell,
            i64_.clone(),
        ));

        all.push((
            "load_volatile",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        store(0, 1, i64_.clone()),
                        InstrNode::new(Inst::Load {
                            ty: i64_.clone(),
                            ptr: cell,
                            volatile: true,
                            align: None,
                        })
                        .with_result(ValueId::new(2)),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));
        all.push((
            "load_aligned",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        store(0, 1, i64_.clone()),
                        InstrNode::new(Inst::Load {
                            ty: i64_.clone(),
                            ptr: cell,
                            volatile: false,
                            align: Some(8),
                        })
                        .with_result(ValueId::new(2)),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));
        all.push((
            "load_type_mismatch",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        store(0, 1, i64_.clone()),
                        load(2, 0, Ty::I32),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));

        all.push((
            "store_volatile",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        InstrNode::new(Inst::Store {
                            ty: i64_.clone(),
                            ptr: cell,
                            value: ValueId::new(1),
                            volatile: true,
                            align: None,
                        }),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));
        all.push((
            "store_aligned",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        InstrNode::new(Inst::Store {
                            ty: i64_.clone(),
                            ptr: cell,
                            value: ValueId::new(1),
                            volatile: false,
                            align: Some(8),
                        }),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));
        all.push((
            "store_type_mismatch",
            func(0, vec![block(0, vec![alloca(0, i64_.clone()), store(0, 1, Ty::I32), ret()])]),
            cell,
            i64_.clone(),
        ));

        // The cell POINTER is the stored value — it escaped into memory.
        all.push((
            "pointer_stored_as_value",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        alloca(3, Ty::Ptr),
                        store(3, 0, Ty::Ptr),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));

        // A `GEP` on the cell pointer: the shape a struct FIELD projection takes.
        all.push((
            "pointer_used_by_instruction",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        store(0, 1, i64_.clone()),
                        InstrNode::new(Inst::GEP {
                            pointee_ty: i64_.clone(),
                            base: cell,
                            indices: vec![ValueId::new(4)],
                            inbounds: false,
                        })
                        .with_result(ValueId::new(5)),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));

        // An instruction whose operands the use-collector cannot enumerate poisons
        // EVERY cell in the function, even one it never mentions.
        all.push((
            "opaque_instruction",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        store(0, 1, i64_.clone()),
                        InstrNode::new(Inst::DialectOp(Box::new(DialectInst::new(
                            "verif", "bfs_step",
                        )))),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));

        // A cross-block TRACKABLE AGGREGATE cell: lane 1 still rejects (the store is
        // not in the defining block) and lane 2 now ADMITS it — this is the whole
        // point of the aggregate widening, and it is the shape behind ny-cert's
        // `store_in_other_block/not_promotable.pointee_not_precise_scalar` bucket.
        // It is deliberately kept in `fixtures()` (rather than moved out) so the
        // parity tests below see it: `promotion_widens_only_on_trackable_aggregate_cells`
        // is what pins that this flip is the INTENDED one.
        all.push((
            "aggregate_cross_block",
            func(
                0,
                vec![
                    block(0, vec![alloca(0, Ty::Tuple(vec![Ty::I64, Ty::I64])), br(1)]),
                    block(
                        1,
                        vec![store(0, 1, Ty::Tuple(vec![Ty::I64, Ty::I64])), ret()],
                    ),
                ],
            ),
            cell,
            Ty::Tuple(vec![Ty::I64, Ty::I64]),
        ));

        // An ENUM cell in exactly the same shape. `immediate_aggregate_field_tys`
        // has no enum arm — an enum is a DISCRIMINANT plus a variant-dependent
        // payload and this translator has no per-variant leaf model — so the cell is
        // modeled OPAQUELY and promotion must never reach it. Both lanes reject.
        let choice = Ty::Enum(EnumId::new(0));
        all.push((
            "enum_cross_block",
            func(
                0,
                vec![
                    block(0, vec![alloca(0, choice.clone()), br(1)]),
                    block(1, vec![store(0, 1, choice.clone()), ret()]),
                ],
            ),
            cell,
            choice,
        ));

        // A cross-block aggregate whose cell pointer is a GEP base — the FIELD
        // PROJECTION shape. Promotion step 2 disqualifies a GEP base, so widening the
        // pointee type must NOT let a field-projected cell through.
        let pair = Ty::Tuple(vec![Ty::I64, Ty::I64]);
        all.push((
            "aggregate_field_projected",
            func(
                0,
                vec![
                    block(0, vec![alloca(0, pair.clone()), store(0, 1, pair.clone()), br(1)]),
                    block(
                        1,
                        vec![
                            InstrNode::new(Inst::GEP {
                                pointee_ty: Ty::I64,
                                base: cell,
                                indices: vec![ValueId::new(4)],
                                inbounds: false,
                            })
                            .with_result(ValueId::new(5)),
                            ret(),
                        ],
                    ),
                ],
            ),
            cell,
            pair,
        ));

        // An ARRAY alloca never reaches the predicate (the driver arm's pattern
        // requires `count: None`), but the predicate must still decline it.
        all.push((
            "array_alloca_count_some",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        InstrNode::new(Inst::Alloca {
                            ty: i64_.clone(),
                            count: Some(ValueId::new(9)),
                            align: None,
                        })
                        .with_result(cell),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));
        all.push((
            "aligned_alloca",
            func(
                0,
                vec![block(
                    0,
                    vec![
                        InstrNode::new(Inst::Alloca {
                            ty: i64_.clone(),
                            count: None,
                            align: Some(8),
                        })
                        .with_result(cell),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));

        all
    }

    /// Lane 1's verdict on a fixture. Probed directly, because a cross-block
    /// SCALAR cell that lane 1 rejects is legitimately ADMITTED by lane 2 — see
    /// `a_cross_block_scalar_is_admitted_by_the_promotion_lane`.
    fn block_local_reason_for(label: &str) -> BlockLocalAllocaReject {
        let all = fixtures();
        let (_, function, cell, ty) =
            all.iter().find(|(name, ..)| *name == label).expect("fixture exists");
        block_local_alloca_reject(function, *cell, ty)
            .unwrap_or_else(|| panic!("fixture `{label}` must be rejected by lane 1"))
    }

    fn reason_for(label: &str) -> SingleCellAllocaRejection {
        let all = fixtures();
        let (_, function, cell, ty) =
            all.iter().find(|(name, ..)| *name == label).expect("fixture exists");
        single_cell_alloca_rejection(&taxonomy_module(), function, *cell, ty)
            .unwrap_or_else(|| panic!("fixture `{label}` must be rejected"))
    }

    #[test]
    fn the_admissible_control_is_admitted_and_has_no_reason() {
        let all = fixtures();
        let (_, function, cell, ty) = all
            .iter()
            .find(|(name, ..)| *name == "admissible_block_local")
            .expect("control exists");
        let module = taxonomy_module();
        assert!(single_cell_alloca_is_admissible(&module, function, *cell, ty));
        assert_eq!(single_cell_alloca_rejection(&module, function, *cell, ty), None);
    }

    #[test]
    fn each_block_local_reason_is_named() {
        for label in [
            "pointee_not_scalar_or_aggregate",
            "no_exact_defining_alloca",
            "load_in_other_block",
            "store_in_other_block",
            "load_before_store",
            "load_volatile",
            "load_aligned",
            "load_type_mismatch",
            "store_volatile",
            "store_aligned",
            "store_type_mismatch",
            "pointer_stored_as_value",
            "pointer_used_by_instruction",
            "opaque_instruction",
        ] {
            assert_eq!(
                block_local_reason_for(label).kind(),
                label,
                "fixture `{label}` must classify as `{label}`"
            );
        }
    }

    #[test]
    fn a_cross_block_access_names_both_the_access_and_the_defining_block() {
        assert_eq!(
            block_local_reason_for("store_in_other_block"),
            BlockLocalAllocaReject::StoreInOtherBlock { block: 1, definition_block: 0 }
        );
        assert_eq!(
            block_local_reason_for("load_in_other_block"),
            BlockLocalAllocaReject::LoadInOtherBlock { block: 1, definition_block: 0 }
        );
    }

    /// Lane 1 is block-local by construction, but a cross-block SCALAR cell is
    /// exactly what lane 2 (mem2reg promotion) exists to admit — so a cross-block
    /// access is only fatal for cells promotion cannot reach, i.e. aggregates.
    /// This is the load-bearing asymmetry behind the ny-cert histogram.
    #[test]
    fn a_cross_block_scalar_is_admitted_by_the_promotion_lane() {
        for label in ["store_in_other_block", "load_in_other_block"] {
            let all = fixtures();
            let (_, function, cell, ty) =
                all.iter().find(|(name, ..)| *name == label).expect("fixture exists");
            assert!(
                block_local_alloca_reject(function, *cell, ty).is_some(),
                "lane 1 rejects the cross-block access in `{label}`"
            );
            assert!(
                single_cell_alloca_is_admissible(&taxonomy_module(), function, *cell, ty),
                "lane 2 still ADMITS the cross-block scalar in `{label}`"
            );
        }
    }

    #[test]
    fn a_type_mismatch_names_both_types() {
        assert_eq!(
            block_local_reason_for("store_type_mismatch"),
            BlockLocalAllocaReject::StoreTypeMismatch {
                block: 0,
                access_ty: "i32".to_string(),
                cell_ty: "i64".to_string(),
            }
        );
    }

    #[test]
    fn an_escaping_use_names_the_instruction_that_took_the_pointer() {
        assert_eq!(
            block_local_reason_for("pointer_used_by_instruction"),
            BlockLocalAllocaReject::PointerUsedByInstruction { block: 0, inst: "GEP".to_string() }
        );
        assert_eq!(
            block_local_reason_for("opaque_instruction"),
            BlockLocalAllocaReject::OpaqueInstruction { block: 0, inst: "DialectOp".to_string() }
        );
    }

    /// The R49 frontier, now cleared: a cross-block TRACKABLE aggregate — the shape
    /// behind ny-cert's dominant `store_in_other_block/…pointee_not_precise_scalar`
    /// bucket — is admitted by the promotion lane, exactly as the cross-block scalar
    /// already was. Lane 1 must still reject it, so the differential (not just the
    /// verdict) stays pinned.
    #[test]
    fn a_cross_block_trackable_aggregate_is_admitted_by_the_promotion_lane() {
        let all = fixtures();
        let (_, function, cell, ty) =
            all.iter().find(|(name, ..)| *name == "aggregate_cross_block").expect("fixture exists");
        let module = taxonomy_module();
        assert_eq!(
            block_local_alloca_reject(function, *cell, ty).map(|reason| reason.kind()),
            Some("store_in_other_block"),
            "lane 1 is block-local, so it still rejects"
        );
        assert!(
            promoted_cell_alloca_reject(&module, function, *cell, ty).is_none(),
            "lane 2 promotes the un-aliased, whole-cell, definitely-initialized tuple"
        );
        assert!(single_cell_alloca_is_admissible(&module, function, *cell, ty));
    }

    /// The bound on the widening. An ENUM cell in the identical shape stays rejected
    /// by BOTH lanes: the translator models it opaquely (no per-variant leaf model),
    /// so there is no binding to thread and promotion must not claim one. The bucket
    /// token is unchanged, which is why its doc says the condition — not the name —
    /// moved.
    #[test]
    fn an_enum_cell_is_still_never_a_promotion_candidate() {
        let module = taxonomy_module();
        assert!(
            !promotable_cell_ty(&module, &Ty::Enum(EnumId::new(0))),
            "an enum carries a discriminant this leaf model cannot represent"
        );
        let reason = reason_for("enum_cross_block");
        assert_eq!(reason.block_local.kind(), "store_in_other_block");
        assert_eq!(reason.promoted.kind(), "not_promotable.pointee_not_precise_scalar");
    }

    /// The other bound: widening the POINTEE type does not widen the ACCESS shape.
    /// A cell whose pointer is a `GEP` base is a field projection, and promotion
    /// step 2 disqualifies it — so it is refused for ESCAPING, not for its type.
    /// (Whole-cell access is what makes the whole-cell definite-initialization
    /// dataflow sufficient; a partly-initialized aggregate is unrepresentable here.)
    #[test]
    fn a_field_projected_aggregate_cell_is_refused_for_escaping() {
        let reason = reason_for("aggregate_field_projected");
        assert_eq!(reason.block_local.kind(), "pointer_used_by_instruction");
        assert_eq!(
            reason.promoted,
            PromotedAllocaReject::NotPromotable(PromotionBlocker::PointerUsedByInstruction {
                inst: "GEP".to_string()
            }),
            "the GEP base is what disqualifies it, not the pointee type"
        );
    }

    #[test]
    fn an_array_or_aligned_alloca_is_declined_by_both_lanes() {
        assert_eq!(reason_for("array_alloca_count_some").block_local.kind(), "no_exact_defining_alloca");
        assert_eq!(reason_for("array_alloca_count_some").promoted.kind(), "no_exact_defining_alloca");
        assert_eq!(reason_for("aligned_alloca").block_local.kind(), "no_exact_defining_alloca");
        assert_eq!(reason_for("aligned_alloca").promoted.kind(), "no_exact_defining_alloca");
    }

    #[test]
    fn reason_kinds_are_stable_grep_tokens() {
        // The gate log histogram is built by grepping `reason=<lane1>/<lane2>`, so
        // a bucket name must never contain a separator that breaks the split.
        for (_, function, cell, ty) in fixtures() {
            if let Some(reason) = single_cell_alloca_rejection(&taxonomy_module(), &function, cell, &ty)
            {
                let kind = reason.kind();
                assert_eq!(kind.matches('/').count(), 1, "exactly one lane separator: {kind}");
                assert!(
                    kind.chars().all(|c| c.is_ascii_lowercase() || "_./".contains(c)),
                    "bucket names stay grep-safe: {kind}"
                );
            }
        }
    }

    /// VERDICT INERTNESS. The reason-returning rewrite must admit exactly the
    /// cells the original booleans admitted — on every fixture, for BOTH lanes
    /// independently and for the combined predicate.
    #[test]
    fn parity_with_the_original_boolean_predicates() {
        let module = taxonomy_module();
        for (label, function, cell, ty) in fixtures() {
            assert_eq!(
                block_local_alloca_reject(&function, cell, &ty).is_none(),
                block_local_alloca_is_admissible_reference(&function, cell, &ty),
                "lane 1 verdict changed on `{label}`"
            );
            assert_eq!(
                promoted_cell_alloca_reject(&module, &function, cell, &ty).is_none(),
                promoted_cell_alloca_is_admissible_reference(&module, &function, cell, &ty),
                "lane 2 verdict changed on `{label}`"
            );
            assert_eq!(
                single_cell_alloca_is_admissible(&module, &function, cell, &ty),
                block_local_alloca_is_admissible_reference(&function, cell, &ty)
                    || promoted_cell_alloca_is_admissible_reference(&module, &function, cell, &ty),
                "combined verdict changed on `{label}`"
            );
        }
    }

    /// The same parity, over every cell of every function the OTHER test modules
    /// build — including the real cross-block promotion shapes.
    #[test]
    fn parity_on_the_mem2reg_fixtures() {
        let module = taxonomy_module();
        for (label, function, cell, ty) in fixtures() {
            for probe_ty in [ty.clone(), Ty::I64, Ty::I32, Ty::Ptr, Ty::Unit] {
                assert_eq!(
                    single_cell_alloca_is_admissible(&module, &function, cell, &probe_ty),
                    block_local_alloca_is_admissible_reference(&function, cell, &probe_ty)
                        || promoted_cell_alloca_is_admissible_reference(
                            &module, &function, cell, &probe_ty
                        ),
                    "verdict changed on `{label}` probed at {probe_ty}"
                );
            }
        }
    }

    /// DIRECTIONAL PARITY — the guard on the aggregate widening itself.
    ///
    /// `promoted_cell_alloca_is_admissible_scalar_reference` is frozen at the lane's
    /// PRE-widening behaviour (candidate collection restricted to
    /// `is_precise_stack_scalar_ty`, everything else identical). The live predicate
    /// may differ from it in exactly ONE way: it may ADMIT a cell whose type is a
    /// trackable NON-SCALAR aggregate. It may never narrow, and it may never widen on
    /// a scalar, an enum, a fat pointer, or an over-budget aggregate. Every fixture is
    /// probed at its own type and at a spread of others, including the two aggregate
    /// shapes and the enum.
    #[test]
    fn promotion_widens_only_on_trackable_aggregate_cells() {
        let module = taxonomy_module();
        let probes = [
            Ty::I64,
            Ty::I32,
            Ty::Ptr,
            Ty::Unit,
            Ty::Tuple(vec![Ty::I64, Ty::I64]),
            Ty::Enum(EnumId::new(0)),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        ];
        for (label, function, cell, ty) in fixtures() {
            for probe_ty in std::iter::once(ty.clone()).chain(probes.iter().cloned()) {
                let now = promoted_cell_alloca_reject(&module, &function, cell, &probe_ty).is_none();
                let before =
                    promoted_cell_alloca_is_admissible_scalar_reference(&function, cell, &probe_ty);
                if now == before {
                    continue;
                }
                assert!(now && !before, "the promotion lane NARROWED on `{label}` at {probe_ty}");
                assert!(
                    !is_precise_stack_scalar_ty(&probe_ty)
                        && aggregate_field_tys_of(&module, &probe_ty).is_some(),
                    "the promotion lane widened on `{label}` at {probe_ty}, which is not a \
                     trackable aggregate"
                );
            }
        }
    }
}
