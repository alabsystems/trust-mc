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

use std::cell::{Cell, RefCell};
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
use crate::input::ModuleInput;
use crate::signature_abi::first_typed_signature_abi;
use crate::translate::{
    TranslateOptions, binop_is_floating_point, bounded_output_out_of_range, bv_rotate,
    const_to_expr, integer_binop_div_by_zero_condition, integer_binop_no_overflow_condition,
    integer_binop_overflow_obligation, integer_rotate_is_unencodable, is_eq_comparable_ty,
    is_ordered_scalar_ty, normalize_expr_to_ty, overflow_op_to_binop, switch_case_expr, ty_to_sort,
};

const ERROR_REL: &str = "error";
const DIRECT_CALL_SUMMARY_MAX_STATES: usize = 64;

#[path = "translate_chc_large_block.rs"]
mod large_block;

pub use large_block::{LargeBlockEdge, LargeBlockErrorSite, LargeBlockMap, LargeBlockPath};

#[path = "translate_chc_bulk_memory.rs"]
mod bulk_memory;

#[path = "translate_chc_ty_facts.rs"]
mod ty_facts;

#[path = "translate_chc_dataless_enum.rs"]
mod dataless_enum;

#[path = "translate_chc_construction_definedness.rs"]
mod construction_definedness;

#[cfg(test)]
#[path = "translate_chc_bulk_memory_tests.rs"]
mod bulk_memory_tests;

#[cfg(test)]
#[path = "translate_chc_fat_pointer_cell_tests.rs"]
mod fat_pointer_cell_tests;

#[cfg(test)]
#[path = "translate_chc_liveness_tests.rs"]
pub(crate) mod liveness_tests;

#[cfg(test)]
#[path = "translate_chc_large_block_tests.rs"]
mod large_block_tests;

#[cfg(test)]
#[path = "translate_chc_opaque_fat_pointer_summary_tests.rs"]
mod opaque_fat_pointer_summary_tests;

#[cfg(test)]
#[path = "translate_chc_smt_array_tests.rs"]
mod smt_array_tests;

#[cfg(test)]
#[path = "translate_chc_source_reference_tests.rs"]
mod source_reference_tests;

#[cfg(test)]
#[path = "translate_chc_source_reference_product_tests.rs"]
mod source_reference_product_tests;

#[cfg(test)]
#[path = "translate_chc_source_initialized_value_tests.rs"]
mod source_initialized_value_tests;

#[cfg(test)]
#[path = "translate_chc_tensor_region_tests.rs"]
mod tensor_region_tests;

/// Trust: cap on the number of scalar CHC leaves a single trackable aggregate may
/// flatten into when its block-relation signature is declared.
///
/// ARRAYS ARE NOT COUNTED BY LENGTH. A fixed-size array `[e; n]` is one SMT array
/// per scalar leaf of `e` (`ArrayValue`), so it contributes `e`'s leaf count ONCE,
/// whatever `n` is: `[[[u8; 256]; 256]; 256]` is ONE leaf of sort
/// `(Array BV64 (Array BV64 (Array BV64 BV8)))`, not `256^3` variables.
///
/// What this still bounds is STRUCT-DAG expansion: `k` nested two-field structs
/// flatten to `2^k` leaves, exponential in the program text, because every
/// struct/tuple field is its own CHC column. Retiring this bound needs a
/// datatype-sort model for ALL aggregates (registers and array elements alike)
/// AND an engine whose cost for a datatype sort follows its type text. At the
/// pinned ay it follows the flattened leaf count instead: the proof identity
/// prints a datatype's whole definition at every variable occurrence, and its
/// sort hash recurses through it. A datatype column there costs more than these
/// columns, and it loses the verdict from 1024 leaves on. Deleting the bound
/// would turn this bounded refusal into allocation proportional to `2^k` inside
/// ay (measured: `docs/ay-asks/2026-10-01-datatype-sort-cost-follows-leaf-count`).
/// Beyond the bound the aggregate is treated as NON-trackable and falls back to a
/// single opaque scalar var — the same fail-closed handling an enum gets
/// (spurious-unverified, never a false proof).
const MAX_AGGREGATE_LEAVES: usize = 4096;

/// Typed result of lowering one trust_ir function to a CHC verification condition.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct ChcTranslationOutput {
    /// Generated typed CHC verification condition.
    pub vc: ChcVc,
    /// Canonical whole-module input refusal, before any function translation.
    /// Its VC contains an unconditional ownerless error fact. This is separate
    /// from instruction diagnostics, which require a real function/block/site.
    /// `None` for every canonically valid module, including unsupported semantics.
    pub module_input_refusal: Option<String>,
    /// Fail-closed diagnostics emitted while lowering unsupported trust_ir semantics.
    pub diagnostics: Vec<TrustIrChcDiagnostic>,
    /// Direct SELF-call sites modeled by the INDUCTIVE HYPOTHESIS (results
    /// havoc'd, entry preconditions re-asserted over the actuals, NO error
    /// rule). One row per admitted site. Demote-only transport: a refutation
    /// whose derivation may pass through a havoc'd self-call result is held at
    /// Unknown by the driver; a proof is a real proof (see
    /// `try_self_call_inductive_hypothesis`). Disjoint from `diagnostics`, which
    /// holds only the fail-closed error-rule sites.
    pub inductive_hypothesis_sites: Vec<TrustIrChcDiagnostic>,
    /// One row per direct-call site, recording whether the modular call summary
    /// succeeded and -- when it did not -- the exact labelled exit it declined at.
    ///
    /// EMPTY unless `TranslateOptions::collect_call_summary_census` is set.
    /// Diagnostic only: nothing in the verdict path reads it.
    pub call_summary_census: Vec<CallSummaryAttempt>,
    /// Deterministic work counters of this translation. Instrumentation only:
    /// nothing in the verdict path reads them.
    pub work: ChcTranslationWork,
    /// How `vc`'s one query rule maps back to the per-block encoding, when the
    /// function was translated with the large-block encoding
    /// (`translate_chc_large_block.rs`): its error sites and transitions, from
    /// which [`LargeBlockMap::counterexample_path`] recovers the block path of a
    /// counterexample. `None` for a per-block translation.
    pub large_block: Option<LargeBlockMap>,
}

/// Deterministic work counters of one function's CHC translation.
///
/// Pure instrumentation — nothing in the verdict path reads them. They exist so
/// tests can pin that translation cost follows the program's size and the values
/// that are actually live, not the product of blocks and threaded values nor the
/// number of obligations asked of the function.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct ChcTranslationWork {
    /// Instructions of the translated function handed to the per-instruction
    /// translator. Call-summary interpretation of callee bodies is not included.
    pub instructions_translated: u64,
    /// `(block, value)` pairs entered into a live-in set, over the threaded SSA
    /// values and the promoted cells together: the summed live-in sizes.
    pub live_in_insertions: u64,
    /// `(CFG edge, value)` pairs visited while propagating live-in sets to
    /// predecessors: `Σ_b |live_in(b)| · |preds(b)|`.
    pub live_in_edge_visits: u64,
    /// Relation arguments declared across all block relations, counting every
    /// flattened aggregate leaf.
    pub relation_arguments: u64,
    /// Reads of a relation-carried value (a threaded SSA value or a promoted
    /// cell) in a non-entry block that did not define it and whose relation does
    /// not carry it. Each such read becomes a fresh havoc — sound, but a lost
    /// precision the liveness analysis exists to prevent — so the corpus tests
    /// pin this at zero: the analysis must cover every read the translation
    /// actually makes, not only the reads a use enumerator lists.
    pub carried_value_misses: u64,
    /// Linear passes over a summarized callee's body to gather the declared types
    /// of its element operands (`callee_operand_tys_of`): at most one per distinct
    /// callee a summary reads an element in, however many call sites and nested
    /// summaries reach it.
    pub callee_operand_type_passes: u64,
    /// Blocks the large-block encoding merged into the function's one query
    /// rule instead of giving them a relation (`translate_chc_large_block.rs`).
    pub large_block_merged_blocks: u64,
    /// Variables the large-block encoding declared: reachability, prefix,
    /// selector and error-site Booleans, and column variables.
    pub large_block_variables: u64,
    /// Of those, definitional variables (`LargeBlockMap::columns`): a merged
    /// block's input whose emitted in-edges pass one compound term, each link
    /// of a column's selection chain (one per in-edge passing another term than
    /// the column's most frequent one), and each cross-block fat-pointer part
    /// variable.
    pub large_block_column_variables: u64,
    /// `(merged block, column)` pairs whose in-edge terms were compared: the
    /// merged blocks' summed relation widths in the per-block encoding.
    pub large_block_column_merges: u64,
    /// Translations that abandoned the large-block encoding for the per-block
    /// one because an emitted rule did not have the shape the encoding relies
    /// on. Pinned at zero by the corpus tests.
    pub large_block_fallbacks: u64,
}

impl ChcTranslationWork {
    /// Add `other`'s counters to these (summing over several translations).
    pub(crate) fn accumulate(&mut self, other: &Self) {
        let Self {
            instructions_translated,
            live_in_insertions,
            live_in_edge_visits,
            relation_arguments,
            carried_value_misses,
            callee_operand_type_passes,
            large_block_merged_blocks,
            large_block_variables,
            large_block_column_variables,
            large_block_column_merges,
            large_block_fallbacks,
        } = *other;
        self.instructions_translated += instructions_translated;
        self.live_in_insertions += live_in_insertions;
        self.live_in_edge_visits += live_in_edge_visits;
        self.relation_arguments += relation_arguments;
        self.carried_value_misses += carried_value_misses;
        self.callee_operand_type_passes += callee_operand_type_passes;
        self.large_block_merged_blocks += large_block_merged_blocks;
        self.large_block_variables += large_block_variables;
        self.large_block_column_variables += large_block_column_variables;
        self.large_block_column_merges += large_block_column_merges;
        self.large_block_fallbacks += large_block_fallbacks;
    }
}

/// Which liveness analysis sizes the block relations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LivenessOracle {
    /// Uses are every instruction's SSA operands; successors come only from a
    /// block's terminator. The production analysis.
    Precise,
    /// The analysis this crate shipped before the precise one: it asked every
    /// instruction for terminator successors, so any block holding an ordinary
    /// instruction read every carried value. Kept only as the differential
    /// oracle for the verdict-parity tests.
    #[cfg(any(test, feature = "legacy-liveness-oracle"))]
    Legacy,
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
    /// BoxDeref's site-scoped Box validity hypothesis has no CHC model.
    BoxDerefValidity,
    UnaryOperation,
    OverflowIntrinsic,
    AggregateProjection,
    AggregateUpdate,
    /// An array element index this lowering cannot place: not a bit-vector
    /// (malformed IR), or — for an index whose declared type is not a known
    /// integer type — a value with its top bit set below the array's length,
    /// which names a real lane if the index is unsigned and is a negative
    /// (undefined-behaviour) index if it is signed. Neither reading is assumed,
    /// so the access fails closed there.
    UnmodeledElementIndex,
    /// An element read of an operand whose length this lowering does not know: a
    /// sequence (no static length) or a value with no declared type. trust-ir makes
    /// the read undefined behaviour when it is out of bounds, and no bound can be
    /// stated without the length, so with memory bounds checked the read fails
    /// closed (its value is an unconstrained one either way).
    UnmodeledElementLength,
    /// Aggregate construction outside the precisely tracked composite model.
    AggregateConstruction,
    /// Runtime closure target/capture construction has no exact value model.
    ClosureConstruction,
    /// Initialization of a consumed constructor operand was not established.
    AggregateOperandDefinedness,
    /// A constructor would materialize opaque address/metadata value tokens.
    AggregateOpaqueValue,
    /// Canonical call argument transport was not established (poison/unknown).
    CallArgumentTransport,
    /// A supported content-inspecting operation has unproved operand transport.
    OperandConsumption,
    BindingFrame,
    BindingFrameSlotLoad,
    BindingFrameClose,
    SequenceMap,
    MemoryAccessWithoutPreciseModel,
    /// A trust-ir WS3.20 `MemCopy` (`memcpy`/`memmove`) or `MemSet` through a
    /// pointer with no exact place in a single-cell stack allocation (a pointer
    /// parameter, a symbolic offset, a heap block), or a copy FROM such a pointer.
    /// Its write is modeled soundly — every tracked cell the destination could
    /// reach is havocked — but the range's in-bounds / non-overlap undefined
    /// behaviour cannot be decided, so with memory bounds checked the instruction
    /// fails closed wherever its byte count is nonzero
    /// (`translate_chc_bulk_memory.rs`).
    BulkMemoryTransfer,
    /// A `MemCopy`/`MemSet` whose range is defined and in bounds of a TRACKED
    /// stack cell but is not one whole object starting at the destination: a run
    /// of `k` lanes of an array with `1 < k < len` (exact only as an array-range
    /// write, `lambda i. ite(lo <= i < hi, ..)`, which neither `ay_bindings::Expr`
    /// nor the CHC engine's `ay_chc::ChcExpr` can express in constant size), a
    /// copy between objects of different types, or a fill of a non-integer leaf.
    /// The cell is havocked and the error fires exactly where such a range is
    /// written (`translate_chc_bulk_memory.rs`).
    BulkMemoryUnplacedRange,
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
    /// A trust-ir v47 `Drop { ty, ptr }`: `ty`'s drop glue run on the place at
    /// `ptr`. The glue (user `Drop` impls, nested field drops, deallocation) is
    /// not part of the node, so it may read or write anything reachable from
    /// `ptr` and may panic; with no body to summarize it fails closed.
    DropGlue,
    PointerMetadata,
    Switch,
    IndirectCall,
    /// A trust-ir v53 `CallCannotUnwind` / `CallIndirectCannotUnwind`: a call
    /// whose normal return means what `Call` / `CallIndirect` means, but at
    /// which an unwind out of the callee must be stopped. Neither the boundary
    /// nor its callee is modeled, so it fails closed.
    NoUnwindCallBoundary,
    /// A trust-ir v54 `AssertInvoke`: a sited check whose failure may enter an
    /// in-frame landing pad. Its unwind edge has no model here (as `Invoke`'s
    /// has none), so the terminator fails closed and its successors are never
    /// reached through it.
    UnwindingCheck,
    UnknownDirectCall,
    UnsupportedDirectCallSummary,
    RecursiveDirectCall,
    /// NOT an unsupported construct: the LABEL of a direct self-call site the
    /// translator modeled by the inductive hypothesis (see
    /// `ChcTranslationOutput::inductive_hypothesis_sites`). Lives in this enum so
    /// the demotion message can name it beside the fail-closed constructs.
    RecursiveSelfCallInductiveHypothesis,
    Fence,
    EndBorrow,
    DialectOperation,
    MalformedControlFlow,
    ReturnArityMismatch,
    ReturnInstructionWithResults,
    UnreachableInstruction,
    NonBooleanCondition,
    /// The module records a typed signature ABI (trust-ir wire v60
    /// `FuncTy::abi`): transport (caller copies, argument extension, hidden
    /// results, source-to-carrier bindings) this lowering does not model. It
    /// is a property of the module, not of one instruction, so the function's
    /// encoding gets an unconditional `error` rule (`crate::signature_abi`).
    TypedSignatureAbiTransport,
    /// A trust-ir v67-v70 tensor-region construct, named: one of the six
    /// `Inst::Tensor*` instructions, or a `Const` that builds a
    /// `Constant::TensorBlob` or has a `Ty::Tensor` type. No tensor value has
    /// a sort here; the module input refuses every module storing one before
    /// translation, so this fires only for a caller that bypassed it
    /// (`crate::tensor_region`).
    TensorRegion(crate::TensorConstruct),
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

// ---------------------------------------------------------------------------
// Direct-call-summary census
//
// `try_direct_call_summary` is the modular mechanism: it interprets a callee's
// body into the caller's CHC encoding so the caller can be proved panic-free
// THROUGH the call. It declines through ~80 separate exits, and until this
// census existed there was NO counter of SUCCESSFUL summaries anywhere in
// tree and no way to learn WHICH exit a decline took -- the only downstream
// signal was one undifferentiated `UnsupportedDirectCallSummary` diagnostic.
//
// Attribution is reported BY THIS CODE, not reconstructed by an external
// probe replicating the ladder: every exit carries a hand-written tag, and
// `tests/call_summary_census_labels_every_exit.rs` fails when a new unlabelled
// `return None` or `?` appears in the instrumented region. A probe that
// mirrors the ladder drifts silently; a label cannot.
//
// The census is OFF by default (`TranslateOptions::collect_call_summary_census`)
// and is diagnostic only: it observes, never decides. No verdict, gate or
// acceptance check reads it.
// ---------------------------------------------------------------------------

/// The exact `try_direct_call_summary` exit a decline took.
///
/// `tag` is hand-written and unique across the interpreter; `line` is `line!()`
/// at that exit, so a tag stays locatable after the file moves around it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CallSummaryDeclineSite {
    /// Unique short name of the exit.
    pub tag: &'static str,
    /// Source line of the exit in `translate_chc.rs`.
    pub line: u32,
}

/// What the translator did with one direct-call site.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum CallSummaryOutcome {
    /// A summary was produced and its return arity matched: the callee's body
    /// is now interpreted into the caller's encoding. This is the SUCCESS count.
    Summarized,
    /// A summary was produced but its return arity disagreed with the callee
    /// signature, so the site still failed closed (`MalformedControlFlow`).
    SummarizedArityMismatch,
    /// The interpreter declined at exactly this exit.
    Declined {
        /// The labelled exit.
        site: CallSummaryDeclineSite,
        /// Discriminator for a catch-all exit -- the trust_ir opcode that hit
        /// it. `None` for every exit that already names one construct.
        ///
        /// Without this the `_ => return None` arm is an anonymous catch-all
        /// that would hide the whole wave behind it.
        detail: Option<String>,
    },
    /// A direct SELF-call modeled by the inductive hypothesis in the MAIN
    /// translate (results havoc'd, entry preconditions re-asserted over the
    /// actuals, no error rule); see `try_self_call_inductive_hypothesis`.
    InductiveHypothesis,
    /// The interpreter was never reached: an earlier arm of `translate_call`
    /// took the site first.
    NotAttempted {
        /// Which earlier arm.
        reason: &'static str,
    },
}

/// One direct-call site (`Inst::Call`) and what the translator did with it.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct CallSummaryAttempt {
    /// Function being translated.
    pub caller: String,
    /// Callee name, or `#<id>` when the module has no such function.
    pub callee: String,
    /// Block holding the call.
    pub block: BlockId,
    /// Zero-based instruction index within `block`.
    pub instruction_index: usize,
    /// Outcome for this site.
    pub outcome: CallSummaryOutcome,
}

/// Where the in-flight `try_direct_call_summary` records its decline.
///
/// A plain LOCAL passed by reference, deliberately not a translator field: the
/// exits sit inside expressions that already borrow `self` mutably, and a field
/// would make every label a borrow-checker negotiation. First writer wins, so
/// the innermost exit (e.g. inside `call_summary_successor_state`) is the one
/// reported -- never the outer `?` that merely propagated it.
#[derive(Debug, Default)]
struct DeclineSlot {
    site: Cell<Option<CallSummaryDeclineSite>>,
    detail: RefCell<Option<String>>,
}

impl DeclineSlot {
    fn note(&self, tag: &'static str, line: u32) {
        if self.site.get().is_none() {
            self.site.set(Some(CallSummaryDeclineSite { tag, line }));
        }
    }

    fn note_with_detail(&self, tag: &'static str, line: u32, detail: String) {
        if self.site.get().is_none() {
            self.site.set(Some(CallSummaryDeclineSite { tag, line }));
            *self.detail.borrow_mut() = Some(detail);
        }
    }

    fn into_outcome(self) -> CallSummaryOutcome {
        match self.site.get() {
            Some(site) => CallSummaryOutcome::Declined { site, detail: self.detail.into_inner() },
            // Unreachable while every exit is labelled; REPORTED rather than
            // hidden, so the census can never silently attribute a decline to
            // nothing. The label test is what keeps this at zero.
            None => CallSummaryOutcome::Declined {
                site: CallSummaryDeclineSite { tag: "__unlabelled__", line: 0 },
                detail: None,
            },
        }
    }
}

/// Record a decline at this exit and return `None`.
macro_rules! decline {
    ($slot:expr, $tag:literal) => {{
        $slot.note($tag, line!());
        return None;
    }};
}

/// `Option` extension that labels the exit a `?` is about to take.
///
/// Written as a SUFFIX combinator on purpose: it leaves the `?` in place, so
/// adding a label provably cannot change control flow.
trait OrDecline<T> {
    fn or_decline(self, slot: &DeclineSlot, tag: &'static str, line: u32) -> Option<T>;
}

impl<T> OrDecline<T> for Option<T> {
    #[inline]
    fn or_decline(self, slot: &DeclineSlot, tag: &'static str, line: u32) -> Option<T> {
        if self.is_none() {
            slot.note(tag, line);
        }
        self
    }
}

/// The leading identifier of `value`'s `Debug` rendering, or `"?"` if it has
/// none.
///
/// Census labels are derived from `Debug` deliberately, exactly like
/// `TrustIrChcUnsupportedReason::label`: a hand-written match would silently
/// return a stale name for a variant added later. The sink stops at the first
/// non-alphanumeric byte, so this never formats a whole `Ty` or `Inst` tree —
/// the write is abandoned by returning `Err`, which `write!` propagates.
fn debug_head(value: &dyn std::fmt::Debug) -> String {
    use std::fmt::Write as _;

    #[derive(Default)]
    struct Head(String);
    impl std::fmt::Write for Head {
        fn write_str(&mut self, s: &str) -> std::fmt::Result {
            for ch in s.chars() {
                if !ch.is_alphanumeric() || self.0.len() >= 40 {
                    return Err(std::fmt::Error);
                }
                self.0.push(ch);
            }
            Ok(())
        }
    }

    let mut head = Head::default();
    let _ = write!(head, "{value:?}");
    if head.0.is_empty() { "?".to_owned() } else { head.0 }
}

/// The trust_ir opcode name of `inst`, bounded to its leading identifier.
fn inst_opcode(inst: &Inst) -> String {
    debug_head(inst)
}

/// The CARRIER CLASS of `ty` — the census discriminator for a signature exit.
///
/// Derived from `Debug`'s leading identifier exactly like [`inst_opcode`], so a
/// `Ty` variant added later cannot be silently misreported by a stale hand-
/// written match. Two refinements, because the head alone would merge causes
/// that want different work:
///
/// * `FatPtr` keeps its kind (`FatPtr_Str`, `FatPtr_Slice`, `FatPtr_TraitObject`,
///   `FatPtr_ContainerLen`, `FatPtr_ContainerVtable`). `&str`, `&[T]` and
///   `&dyn Trait` are three separate carrier decisions — and the two container-
///   tail kinds (`Arc<str>`'s and `Arc<dyn Any>`'s inner pointers) are two more,
///   since their data pointer addresses a container HEADER rather than the
///   content or the dispatched object — and reporting them as one number would repeat the
///   `signature_not_summary_value` mistake at the next level down. The match is
///   EXHAUSTIVE on purpose — a `_` arm would fold a kind added later into an
///   anonymous `Other` bucket, which is the attribution failure this census
///   exists to remove, so a new kind must be a compile error and not a silent
///   merge. (`ContainerLen` was reported as `FatPtr_Other` until this was made
///   exhaustive, contradicting the list above; it is a measured zero in the
///   corpus swept so far, so no published split changes.)
/// * A named aggregate is NOT keyed by its id — `Struct(StructId(7))` would make
///   every struct in the corpus its own cause. The head `Struct`/`Array`/`Tuple`
///   is the actionable class.
fn ty_carrier(ty: &Ty) -> String {
    match ty {
        Ty::FatPtr(kind) => {
            let head = match kind {
                FatPtrKind::Slice(_) => "Slice",
                FatPtrKind::Str => "Str",
                FatPtrKind::TraitObject { .. } => "TraitObject",
                FatPtrKind::ContainerLen => "ContainerLen",
                // trust-ir v40: the `dyn`-tail container pointer (`*const
                // ArcInner<dyn Any>` inside `Arc<dyn Any>`). Its OWN class, not
                // `TraitObject`'s: the data pointer addresses the container
                // header, nothing dispatches through it, and giving it a carrier
                // is a separate decision from giving `&dyn Trait` one.
                FatPtrKind::ContainerVtable => "ContainerVtable",
            };
            format!("FatPtr_{head}")
        }
        other => debug_head(other),
    }
}

/// Translate canonically valid functions into typed CHC VCs. Invalid modules
/// yield one unconditional module-input error VC, even with no functions.
/// A valid empty library has no function obligations and grants no authority.
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
    ModuleInput::new(module).chc_all(options, ChcEncoding::Automatic)
}

/// [`trust_ir_to_chc_translation_outputs`] in the per-block encoding (see
/// [`trust_ir_function_to_chc_translation_output_per_block`]).
pub fn trust_ir_to_chc_translation_outputs_per_block(
    module: &Module,
    options: &TranslateOptions,
) -> Vec<ChcTranslationOutput> {
    ModuleInput::new(module).chc_all(options, ChcEncoding::PerBlock)
}

/// Translate one function from a `trust_ir::Module` into a typed CHC VC.
///
/// Returns `None` for an actually absent function (selection refusal, never
/// verification success). An existing selection in an invalid module gets an
/// unconditional module-input error VC, without invented instruction ownership.
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
/// Complete canonical module validation precedes translation. Returns `None`
/// only for an actually absent selection; invalidity of any function/table
/// refuses every existing selection through `module_input_refusal`.
pub fn trust_ir_function_to_chc_translation_output(
    module: &Module,
    function: FuncId,
    options: &TranslateOptions,
) -> Option<ChcTranslationOutput> {
    ModuleInput::new(module).chc_function(function, options)
}

pub(crate) fn trust_ir_function_to_chc_translation_output_with_source_references<'a>(
    module: &'a Module,
    function: FuncId,
    options: &'a TranslateOptions,
    facts: &'a crate::SourceReferenceFacts<'a>,
) -> Option<ChcTranslationOutput> {
    ModuleInput::new(module).chc_function_with_source_references(function, options, facts)
}

/// [`trust_ir_function_to_chc_translation_output`] with block relations sized by
/// the liveness analysis this crate shipped before the precise one, which
/// threads (almost) every carried value through every block. Exists only as the
/// differential oracle of the verdict-parity tests; never enabled in production
/// builds (`legacy-liveness-oracle` is a test-only feature).
#[cfg(any(test, feature = "legacy-liveness-oracle"))]
#[doc(hidden)]
pub fn trust_ir_function_to_chc_translation_output_with_legacy_liveness(
    module: &Module,
    function: FuncId,
    options: &TranslateOptions,
) -> Option<ChcTranslationOutput> {
    ModuleInput::new(module).chc_function_with_encoding(function, options, ChcEncoding::Legacy)
}

/// [`trust_ir_function_to_chc_translation_output`] in the PER-BLOCK encoding
/// whatever the function's shape: one relation per block, one rule per emitted
/// transition and error site, never the large-block query an acyclic function
/// otherwise becomes (`translate_chc_large_block.rs`). The two encodings are
/// equisatisfiable; this one is the reference the large-block tests compare
/// against, and the one whose relations name each block's live values.
///
/// Canonical validity and absent-selection handling match the default entry.
pub fn trust_ir_function_to_chc_translation_output_per_block(
    module: &Module,
    function: FuncId,
    options: &TranslateOptions,
) -> Option<ChcTranslationOutput> {
    ModuleInput::new(module).chc_function_with_encoding(function, options, ChcEncoding::PerBlock)
}

#[derive(Clone, Copy)]
enum ChcEncoding {
    Automatic,
    PerBlock,
    #[cfg(any(test, feature = "legacy-liveness-oracle"))]
    Legacy,
}

impl ModuleInput<'_> {
    /// This output is about module invalidity, not a fabricated function/site.
    fn chc_refusal(&self, options: &TranslateOptions) -> Option<ChcTranslationOutput> {
        let reason = self.refusal_reason()?;
        let mut vc = ChcVc::new();
        vc.add_relation(RelationDecl::nullary(ERROR_REL));
        vc.add_rule(Rule::new(RuleBody::empty(), RelationApp::nullary(ERROR_REL)));
        vc.query = ChcQuery::new().with_target(ERROR_REL);
        if let Some(timeout) = options.timeout_ms {
            vc.query = vc.query.with_timeout(timeout);
        }
        Some(ChcTranslationOutput {
            vc,
            module_input_refusal: Some(reason.to_owned()),
            diagnostics: Vec::new(),
            inductive_hypothesis_sites: Vec::new(),
            call_summary_census: Vec::new(),
            work: ChcTranslationWork::default(),
            large_block: None,
        })
    }

    fn chc_all(
        &self,
        options: &TranslateOptions,
        encoding: ChcEncoding,
    ) -> Vec<ChcTranslationOutput> {
        if let Some(refusal) = self.chc_refusal(options) {
            return vec![refusal];
        }
        self.module()
            .functions
            .iter()
            .map(|func| translate_function_with_encoding(func, self.module(), options, encoding))
            .collect()
    }

    pub(crate) fn chc_function(
        &self,
        function: FuncId,
        options: &TranslateOptions,
    ) -> Option<ChcTranslationOutput> {
        self.chc_function_with_encoding(function, options, ChcEncoding::Automatic)
    }

    fn chc_function_with_encoding(
        &self,
        function: FuncId,
        options: &TranslateOptions,
        encoding: ChcEncoding,
    ) -> Option<ChcTranslationOutput> {
        let func = self.module().function_by_id(function)?;
        Some(self.chc_refusal(options).unwrap_or_else(|| {
            translate_function_with_encoding(func, self.module(), options, encoding)
        }))
    }

    pub(crate) fn chc_function_with_source_references<'a>(
        &'a self,
        function: FuncId,
        options: &'a TranslateOptions,
        facts: &'a crate::SourceReferenceFacts<'a>,
    ) -> Option<ChcTranslationOutput> {
        let module = self.module();
        if !facts.matches_module(module) {
            return None;
        }
        let func = module.function_by_id(function)?;
        Some(self.chc_refusal(options).unwrap_or_else(|| {
            let mut translator = ChcFuncTranslator::new(func, module, options);
            translator.source_consumption =
                construction_definedness::Analysis::with_source_references(module, function, facts);
            translator.translate()
        }))
    }
}

struct ChcFuncTranslator<'a> {
    func: &'a Function,
    module: &'a Module,
    options: &'a TranslateOptions,
    source_consumption: construction_definedness::Analysis<'a>,
    vc: ChcVc,
    values: BTreeMap<ValueId, Expr>,
    aggregates: BTreeMap<ValueId, AggregateValue>,
    // SSA values of a non-empty fixed-size array type, in the SMT-array model
    // (`ArrayValue`). Cleared with `aggregates` at every block boundary.
    arrays: BTreeMap<ValueId, ArrayValue>,
    // Whether array CONTENT is modeled with SMT arrays in the block being
    // translated (or, while relations are declared, the block being declared):
    // `false` in a block reachable from a cycle of the CFG, where every array is
    // shape-only (see `ArrayValue`). Set per block from `array_content_blocks`.
    smt_arrays: bool,
    // The blocks in which array content is modeled: every block that no cycle of
    // the CFG reaches (`array_content_blocks`). Closed under predecessors, so a
    // transition INTO such a block always leaves one too, and a transition from
    // one into a cyclic region drops the array columns the target does not carry.
    array_content_blocks: BTreeSet<BlockId>,
    // The DECLARED type of every value used as the array or the index operand of
    // an `ExtractElement`/`InsertElement` (block parameters and instruction
    // results, `InstrNode::result_tys`), gathered once per function, linear in its
    // size. An element index's signedness decides what its bits mean (trust-ir
    // `runtime_index`), and an array operand with no binding in the block still
    // has a length.
    element_operand_tys: BTreeMap<ValueId, Ty>,
    // Names of the fresh lane variables a flat array literal pins lane by lane
    // (`define_array_lanes`): `select(L, k) = e` with `L` one of these is a
    // DEFINITIONAL equality, which `vc_equates_array_terms_beyond` admits.
    definitional_array_lanes: BTreeSet<String>,
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
    // The parts a `PtrFromParts` built a fat pointer from (or a copy of one),
    // per SSA value, with the block that built them: read as they are in that
    // block, everywhere when they mention no variable, and — under the
    // large-block encoding — in every block that block dominates
    // (`ptr_parts_view`, `translate_chc_large_block.rs` fact 2). A copy of a
    // fat pointer read where its parts are not exact is OPAQUE.
    ptr_parts: BTreeMap<ValueId, PtrParts>,
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
    // The metadata of an OPAQUE fat pointer (`PtrPartsView::Opaque`): a value
    // built by `PtrFromParts` read where its parts are not exact. One fresh,
    // UNBOUNDED havoc per SSA value (the metadata is a function of the value),
    // never the `isize::MAX`-bounded `slice_len` symbol: whatever length a
    // `PtrFromParts` was given is what the value carries.
    ptr_opaque_metadata: BTreeMap<ValueId, Expr>,
    // What each term mentions (variables, havocs), once per shared node.
    term_facts: large_block::TermFacts,
    // The large-block encoding of this function, when it applies
    // (`translate_chc_large_block.rs`); `None` translates every block per block.
    large_block: Option<large_block::LargeBlock>,
    // Whether this translator may use the large-block encoding: off for the
    // per-block oracles and for the per-block retranslation after a fallback.
    allow_large_block: bool,
    // The instruction of `current_block` being translated (large-block error
    // sites record it).
    current_instruction: usize,
    block_param_bindings: BTreeMap<BlockId, Vec<ValueBinding>>,
    // Immutable function parameters (entry-block params), threaded through every
    // block relation so dominance-scoped uses in downstream blocks resolve to the
    // entry value instead of a fresh, unconstrained symbolic.
    threaded_params: Vec<(ValueId, Ty)>,
    // Per-block subset of `threaded_params` actually carried by that block's
    // relation (excludes the entry block and any param the block redeclares).
    block_threaded_params: BTreeMap<BlockId, Vec<(ValueId, Ty)>>,
    // Liveness over-approximation: the set of threaded `ValueId`s that are
    // live-in at each block (read by the block's translation, or live-in at a
    // successor its terminator transfers to, and not defined by the block).
    // Only live values are threaded into a block relation; threading a dead
    // value is sound but imprecise, while failing to thread one the block's
    // translation reads loses precision (the read becomes a fresh havoc).
    block_live_params: BTreeMap<BlockId, std::collections::BTreeSet<u32>>,
    // The defining block of every threaded value (entry params: the entry).
    // Read only by the `carried_value_misses` instrumentation.
    threaded_def_block: BTreeMap<u32, BlockId>,
    // The block `translate_block` is translating, for the same instrumentation.
    current_block: Option<BlockId>,
    // Which liveness analysis sizes the block relations (see `LivenessOracle`).
    liveness: LivenessOracle,
    // Deterministic work counters; see `ChcTranslationWork`.
    work: ChcTranslationWork,
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
    // Self-call sites modeled by the inductive hypothesis; see
    // `ChcTranslationOutput::inductive_hypothesis_sites`.
    inductive_hypothesis_sites: Vec<TrustIrChcDiagnostic>,
    // One row per `Inst::Call` site when the census is enabled; see
    // `ChcTranslationOutput::call_summary_census`.
    call_summary_census: Vec<CallSummaryAttempt>,
    // States the CURRENT top-level direct-call-summary attempt may still process,
    // shared across every nesting depth. Reset at each depth-0 entry; see
    // `DIRECT_CALL_SUMMARY_TOTAL_STATES`.
    call_summary_states_left: usize,
    // `element_operand_tys` of each callee a summary has read an array element in,
    // computed on the callee's first `ExtractElement` and kept for this translator:
    // the work is linear in the distinct callees' sizes, however many call sites
    // and nested summaries reach them.
    callee_operand_tys: BTreeMap<FuncId, std::rc::Rc<BTreeMap<ValueId, Ty>>>,
    // Memoized type queries (composite shapes, byte layouts, lane evidence),
    // once per distinct type: `translate_chc_ty_facts.rs`.
    ty_facts: ty_facts::TyFacts,
    next_sym_id: u32,
}

/// What the translator recorded about the parts of a fat-pointer SSA value
/// (`ChcFuncTranslator::ptr_parts`).
#[derive(Debug, Clone)]
enum PtrParts {
    /// The data and metadata terms a `PtrFromParts` (or a copy of one) built it
    /// from in `block`; `closed` when neither mentions a variable.
    Exact { block: BlockId, data: Expr, metadata: Expr, closed: bool },
    /// A copy of such a value made where its parts were not exact: nothing is
    /// known of its metadata.
    Opaque,
}

/// How the block being translated may read a fat pointer's parts
/// (`ChcFuncTranslator::ptr_parts_view`).
#[derive(Debug, Clone)]
enum PtrPartsView {
    /// Exactly these data and metadata terms.
    Exact(Expr, Expr),
    /// Built by a `PtrFromParts`, but its parts are not exact here: the data is
    /// the value's own binding, the metadata an unbounded havoc.
    Opaque,
    /// No `PtrFromParts` built it: the historical reading (`slice_len`).
    Unrecorded,
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

#[derive(Debug, Clone)]
enum ValueBinding {
    Scalar(Expr),
    Aggregate(AggregateValue),
    Array(ArrayValue),
}

/// A fixed-size array value `[e; n]` with `n >= 1`, in the SMT-array model.
///
/// `lanes` has the SHAPE of ONE element's binding (a scalar, a struct of fields, or
/// a nested array), but every scalar leaf in it is an SMT ARRAY
/// `(Array (_ BitVec 64) S)` that maps a lane index to that leaf's value in that
/// lane — a struct of arrays. A nested array element nests the sort. So the number
/// of leaves, and with it the CHC relation columns and the size of every term built
/// here, is the ELEMENT type's leaf count, whatever `len` is. `len` itself is read
/// only to state the in-bounds obligation `index <u len`, as one BV64 constant.
///
/// The operations are McCarthy's exact functional-array semantics:
/// `InsertElement` is `store`, `ExtractElement` is `select`, a uniform `[v; n]`
/// (`ArraySplat`, `Constant::Splat`) is `((as const (Array BV64 S)) v)`.
///
/// JUNK-LANE INVARIANT. Lanes outside `[0, len)` are not part of the Rust value: a
/// `const_array` pins them to `v`, a fresh array leaves them free, a `store` never
/// reaches them through an in-bounds index. Nothing may let them constrain a
/// feasible path, so (a) every element access carries its own in-bounds
/// obligation — with memory checks on, an error rule after which the path
/// continues only under `in_bounds`; with them off, a guard that havocs the read
/// and the whole written array (never a dropped write) — and (b) NO encoder may
/// assert SMT equality between two array-sorted terms as a hypothesis — two Rust
/// arrays equal on `[0, len)` may differ on their junk lanes, so such an equality
/// would make a feasible path infeasible and mint a false proof. Array values
/// move only as relation arguments and through fresh definitional bindings; the
/// one array-sorted equality emitted is a flat literal's definition of a lane of
/// its own fresh lane variable (`define_array_lanes`); array-typed `ICmp` stays
/// refused (`is_eq_comparable_ty`). `vc_equates_array_terms_beyond` checks (b) on
/// every translation in debug builds.
///
/// SHAPE-ONLY ARRAYS. `lanes` is `None` when the array's CONTENT is not modeled
/// — only its length is. That is how every array is carried in a block that a
/// cycle of the CFG reaches (`ChcFuncTranslator::smt_arrays`,
/// `array_content_blocks`): the native CHC engine (ay-chc at the pinned revision)
/// answers Inconclusive for a problem with an array term in any clause reachable
/// from a loop, so there the translation emits NO array term at all, while the
/// blocks before the first loop — every block of an acyclic function — keep the
/// full model. A read there is a fresh value, a write is absorbed, and the
/// relations carry no column for the array; every access still carries its
/// in-bounds obligation, which needs only the length. The choice is by the CFG's
/// shape, never by a length. It costs precision the retired N-field model had
/// for arrays of at most 256 lanes in the same place: that model's `ExtractElement`
/// was always a fresh value too, but its stack cells answered constant GEP-lane
/// loads and its relations carried every lane across the loop. Here such a load
/// reads a fresh value. That gap closes when the engine decides array terms in a
/// loop (docs/ay-asks/2026-09-28-array-column-in-loop-inconclusive).
#[derive(Debug, Clone)]
struct ArrayValue {
    len: u64,
    lanes: Option<Box<ValueBinding>>,
}

/// When an element access is in bounds (`ChcFuncTranslator::array_lane_access`).
#[derive(Debug, Clone)]
enum InBounds {
    /// A constant lane below the length.
    Always,
    /// A constant lane at or past the length (or a negative one): undefined
    /// behaviour on every execution that reaches it.
    Never,
    /// A symbolic lane: in bounds exactly when this Bool term holds.
    When(Expr),
}

/// Where an element index of unknown signedness names a real lane if unsigned
/// but is negative (undefined behaviour) if signed (`LaneAccess::ambiguous`).
#[derive(Debug, Clone)]
enum Ambiguity {
    /// Nowhere: the index's type is known, or its two readings always agree.
    Nowhere,
    /// A constant index whose readings disagree.
    Always,
    /// A symbolic index: where this Bool term holds.
    When(Expr),
}

/// One element access: the BV64 lane it names, and when that lane is real.
#[derive(Debug, Clone)]
struct LaneAccess {
    lane: Expr,
    /// When the access names lane `lane` below the length, under every reading of
    /// the index's bits. Outside it and outside `ambiguous`, the access is out of
    /// bounds under every reading: undefined behaviour.
    in_bounds: InBounds,
    /// `Nowhere` unless the index's declared type is not a known integer type
    /// (`element_operand_tys` has none for it): where its TOP BIT is set and it is
    /// below the length as an unsigned value, it names a real lane if it is
    /// unsigned and is a negative (undefined-behaviour) index if it is signed. The
    /// model assumes neither reading there (see `discharge_element_bounds`).
    ambiguous: Ambiguity,
}

/// The lane an element access at the BV index `index` names in an array of `len`
/// lanes, and when that access is in bounds (`ChcFuncTranslator::array_lane_access`,
/// whose documentation states the rule): `signed` is the index's DECLARED
/// signedness, `None` when it has no declared integer type. Shared by the block
/// translator and the call-summary interpreter, so a read has ONE bounds rule
/// whichever of them models it — an array's (its length) or a SIMD vector's (its
/// lane count). `None` when `index` is not a bit-vector of width 1..=128
/// (malformed IR).
fn lane_access_of(index: Expr, signed: Option<bool>, len: u64) -> Option<LaneAccess> {
    let width = index.sort().bitvec_width()?;
    if width == 0 || width > 128 {
        return None;
    }
    let top_bit = 1u128 << (width - 1);
    if let Some(value) = bitvec_const_value(&index) {
        let top_bit_set = value & top_bit != 0;
        let below_len = value < u128::from(len);
        let (in_bounds, ambiguous) = match signed {
            Some(false) => (below_len, false),
            Some(true) => (below_len && !top_bit_set, false),
            None => (below_len && !top_bit_set, below_len && top_bit_set),
        };
        let lane = if in_bounds { u64::try_from(value).ok()? } else { 0 };
        return Some(LaneAccess {
            lane: Expr::bitvec_const(lane, 64),
            in_bounds: if in_bounds { InBounds::Always } else { InBounds::Never },
            ambiguous: if ambiguous { Ambiguity::Always } else { Ambiguity::Nowhere },
        });
    }
    // `index <u len` reading the bits unsigned, at a width that holds both.
    let unsigned_in_bounds = if width <= 64 {
        let widened =
            if width < 64 { index.clone().zero_extend(64 - width) } else { index.clone() };
        widened.try_bvult(Expr::bitvec_const(len, 64)).ok()?
    } else {
        index.clone().try_bvult(Expr::bitvec_const(u128::from(len), width)).ok()?
    };
    // In bounds under both readings: non-negative signed, below the length.
    let both_readings =
        index.clone().try_bvult(Expr::bitvec_const(u128::from(len).min(top_bit), width)).ok()?;
    let (in_bounds, ambiguous) = match signed {
        Some(false) => (unsigned_in_bounds, Ambiguity::Nowhere),
        Some(true) => (both_readings, Ambiguity::Nowhere),
        None if u128::from(len) > top_bit => {
            let top_bit_set =
                index.clone().try_bvult(Expr::bitvec_const(top_bit, width)).ok()?.not();
            (both_readings, Ambiguity::When(top_bit_set.and(unsigned_in_bounds)))
        }
        None => (both_readings, Ambiguity::Nowhere),
    };
    let lane = match width.cmp(&64) {
        std::cmp::Ordering::Less => index.zero_extend(64 - width),
        std::cmp::Ordering::Equal => index,
        std::cmp::Ordering::Greater => index.extract(63, 0),
    };
    Some(LaneAccess { lane, in_bounds: InBounds::When(in_bounds), ambiguous })
}

/// The SMT sort of a lane index: `usize` on the pinned 64-bit target.
fn array_index_sort() -> ay_bindings::Sort {
    ay_bindings::Sort::bitvec(64)
}

/// The value of a bit-vector constant, when `expr` is one that fits 128 bits.
fn bitvec_const_value(expr: &Expr) -> Option<u128> {
    match expr.value() {
        ay_bindings::ExprValue::BitVecConst { value, .. } => value.to_string().parse::<u128>().ok(),
        _ => None,
    }
}

/// `sort` lifted through `depth` enclosing arrays: `(Array BV64 … sort)`.
fn lifted_sort(sort: ay_bindings::Sort, depth: u32) -> ay_bindings::Sort {
    (0..depth).fold(sort, |inner, _| ay_bindings::Sort::array(array_index_sort(), inner))
}

impl ArrayValue {
    /// An array whose content is not modeled, only its length (see the
    /// shape-only note on the type).
    fn shape_only(len: u64) -> Self {
        Self { len, lanes: None }
    }

    /// `[v; len]`: every leaf of `v` becomes a constant array.
    fn splat(len: u64, element: &ValueBinding) -> Option<Self> {
        let lanes = element
            .map_leaves(&mut |leaf| Expr::try_const_array(array_index_sort(), leaf.clone()).ok())?;
        Some(Self { len, lanes: Some(Box::new(lanes)) })
    }

    /// The element at lane `index` (a BV64 term): `select` on every leaf. `None`
    /// for a shape-only array (the caller reads a fresh value).
    fn select(&self, index: &Expr) -> Option<ValueBinding> {
        self.lanes.as_ref()?.map_leaves(&mut |leaf| leaf.clone().try_select(index.clone()).ok())
    }

    /// This array with lane `index` replaced by `element`: `store` on every leaf.
    /// A shape-only array absorbs the write (its content is unconstrained anyway).
    fn store(&self, index: &Expr, element: &ValueBinding) -> Option<Self> {
        let Some(lanes) = &self.lanes else {
            return Some(self.clone());
        };
        let lanes = lanes.zip_leaves(element, &mut |leaf, value| {
            leaf.clone().try_store(index.clone(), value.clone()).ok()
        })?;
        Some(Self { len: self.len, lanes: Some(Box::new(lanes)) })
    }
}

/// A summary may carry a fat pointer through typed value operations without
/// interpreting its address or metadata. Keep that token separate from Scalar:
/// a numeric consumer must decline rather than inspect placeholder pointer bits.
/// No token identity or equality fact is represented. Exporting a token to the
/// outer translator produces fresh havoc, including tokens in aggregate fields.
#[derive(Debug, Clone)]
enum CallSummaryBinding {
    Scalar(Expr),
    /// A canonical direct unwritten Struct/Tuple lane. It transports inside
    /// its carrier but is NEVER an initialized unknown or scalar expression.
    Uninit(Ty),
    Aggregate(CallSummaryAggregate),
    OpaqueFatPtr(FatPtrKind),
    /// A non-empty array carried through the summary: `lanes` has the ELEMENT's
    /// shape with SMT-array leaves, exactly as `ArrayValue` (a fat-pointer leaf
    /// stays an opaque token).
    Array(CallSummaryArray),
}

#[derive(Debug, Clone)]
struct CallSummaryAggregate {
    fields: Vec<CallSummaryBinding>,
}

#[derive(Debug, Clone)]
struct CallSummaryArray {
    len: u64,
    /// `None` for a shape-only array, as `ArrayValue::lanes`.
    lanes: Option<Box<CallSummaryBinding>>,
}

#[derive(Debug, Clone)]
struct DirectCallSummary {
    returns: Vec<CallSummaryBinding>,
    error_conditions: Vec<Expr>,
}

#[derive(Debug, Clone)]
struct CallSummaryState {
    block: BlockId,
    locals: BTreeMap<ValueId, CallSummaryBinding>,
    path_conditions: Vec<Expr>,
    visited_blocks: Vec<BlockId>,
    /// PATH-LOCAL stack slots: `Alloca` result id -> cell type and current contents.
    ///
    /// Path-local is what makes this precise AND sound without any of the
    /// whole-function aliasing machinery `translate_block` needs: each explored
    /// summary path owns its own copy (cloned in `call_summary_successor_state`),
    /// the exploration is acyclic (`visited_blocks`), and a slot is admitted only
    /// when `call_summary_slot_is_directly_addressed` proves the alloca's address
    /// NEVER leaves the `ptr` operand of a non-volatile `Load`/`Store` — so there
    /// is no alias through which a write could be missed and no join at which two
    /// different contents could be conflated.
    slots: BTreeMap<ValueId, CallSummarySlot>,
}

/// One path-local stack cell. `value: None` means "not written on this path yet";
/// a read of it HAVOCs (fresh unconstrained value), never fabricates a default.
#[derive(Debug, Clone)]
struct CallSummarySlot {
    ty: Ty,
    value: Option<CallSummaryBinding>,
}

/// The actual arguments handed to one `try_direct_call_summary` invocation.
///
/// The outermost invocation names them as `ValueId`s in the CALLER's value space
/// (resolved with `resolve_call_summary_argument`); a NESTED invocation — the
/// interpreter summarizing a call it met inside a callee body — has already
/// resolved them into the enclosing summary's `locals`, and those bindings live in
/// no `ValueId` space the outer translator can name. Keeping the two spellings in
/// one type is what stops the recursion seam from re-resolving a nested actual
/// against the WRONG value space, which would silently bind a fresh symbol.
#[derive(Clone, Copy)]
enum CallSummaryArgs<'a> {
    Caller(&'a [ValueId]),
    Bindings {
        values: &'a [CallSummaryBinding],
        defined: &'a [bool],
        transport: &'a [bool],
        reference_inputs: &'a [bool],
        enclosing_transport_defined: bool,
    },
}

impl CallSummaryArgs<'_> {
    fn len(&self) -> usize {
        match self {
            Self::Caller(ids) => ids.len(),
            Self::Bindings { values, .. } => values.len(),
        }
    }
}

/// How deep the summary interpreter may follow a call it meets INSIDE a callee
/// body. Depth 0 is the callee itself; depth 1 is the closure a `core` combinator
/// wrapper invokes. A CHAINED combinator needs four:
/// `and_then`(0) → outer closure(1) → `map`(2) → inner closure(3) is what
/// `a3d_kernel::IntervalI64::add`'s single expression lowers to. This is only a
/// TERMINATION guard (mutual recursion A→B→A unfolds until it trips, then declines
/// fail-closed); the real cost bound is the SHARED state budget below.
pub(crate) const DIRECT_CALL_SUMMARY_MAX_DEPTH: usize = 6;

/// States the whole summary attempt (all depths together) may process. Without a
/// SHARED budget the per-invocation limit compounds: 64 states each spawning a
/// nested summary of 64 more is 64^(depth+1) worst case.
const DIRECT_CALL_SUMMARY_TOTAL_STATES: usize = 4096;

#[derive(Debug, Clone)]
struct CallSummaryReturn {
    values: Vec<CallSummaryBinding>,
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
            // One column per element leaf (each an SMT array), never per lane; a
            // shape-only array has none.
            Self::Array(array) => {
                array.lanes.as_ref().map(|lanes| lanes.flat_args()).unwrap_or_default()
            }
        }
    }

    /// The arguments this binding passes to a relation declared with
    /// `smt_arrays` (`declare_relation_binding_lifted`): `flat_args` for a
    /// relation that carries array columns; for one that does not (a block
    /// reachable from a cycle) every array contributes nothing, whatever content
    /// the source block modeled for it.
    fn relation_args(&self, smt_arrays: bool) -> Vec<Expr> {
        if smt_arrays {
            return self.flat_args();
        }
        match self {
            Self::Scalar(expr) => vec![expr.clone()],
            Self::Aggregate(aggregate) => {
                aggregate.fields.iter().flat_map(|field| field.relation_args(false)).collect()
            }
            Self::Array(_) => Vec::new(),
        }
    }

    /// `false` iff some array in this binding is shape-only (content not modeled).
    fn has_array_content(&self) -> bool {
        match self {
            Self::Scalar(_) => true,
            Self::Aggregate(aggregate) => aggregate.fields.iter().all(Self::has_array_content),
            Self::Array(array) => {
                array.lanes.as_ref().is_some_and(|lanes| lanes.has_array_content())
            }
        }
    }

    /// This binding with every scalar leaf replaced by `f(leaf)`, keeping the
    /// shape (and every nested array's `len`). `None` when `f` declines a leaf.
    fn map_leaves(&self, f: &mut impl FnMut(&Expr) -> Option<Expr>) -> Option<Self> {
        Some(match self {
            Self::Scalar(expr) => Self::Scalar(f(expr)?),
            Self::Aggregate(aggregate) => Self::Aggregate(AggregateValue {
                fields: aggregate
                    .fields
                    .iter()
                    .map(|field| field.map_leaves(f))
                    .collect::<Option<Vec<_>>>()?,
            }),
            Self::Array(array) => Self::Array(ArrayValue {
                len: array.len,
                lanes: match &array.lanes {
                    Some(lanes) => Some(Box::new(lanes.map_leaves(f)?)),
                    None => None,
                },
            }),
        })
    }

    /// Pair this binding's scalar leaves with `other`'s, which must have the same
    /// shape (same variants, field counts and nested lengths); `None` otherwise or
    /// when `f` declines a pair.
    fn zip_leaves(
        &self,
        other: &Self,
        f: &mut impl FnMut(&Expr, &Expr) -> Option<Expr>,
    ) -> Option<Self> {
        Some(match (self, other) {
            (Self::Scalar(left), Self::Scalar(right)) => Self::Scalar(f(left, right)?),
            (Self::Aggregate(left), Self::Aggregate(right))
                if left.fields.len() == right.fields.len() =>
            {
                Self::Aggregate(AggregateValue {
                    fields: left
                        .fields
                        .iter()
                        .zip(&right.fields)
                        .map(|(left, right)| left.zip_leaves(right, f))
                        .collect::<Option<Vec<_>>>()?,
                })
            }
            (Self::Array(left), Self::Array(right)) if left.len == right.len => {
                Self::Array(ArrayValue {
                    len: left.len,
                    lanes: match (&left.lanes, &right.lanes) {
                        (Some(left), Some(right)) => Some(Box::new(left.zip_leaves(right, f)?)),
                        (None, None) => None,
                        _ => return None,
                    },
                })
            }
            _ => return None,
        })
    }

    /// `ite(cond, self, other)` leaf by leaf (same shape required).
    fn select_by(&self, cond: &Expr, other: &Self) -> Option<Self> {
        self.zip_leaves(other, &mut |then_leaf, else_leaf| {
            Expr::try_ite(cond.clone(), then_leaf.clone(), else_leaf.clone()).ok()
        })
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
            source_consumption: construction_definedness::Analysis::new(module),
            vc: ChcVc::new(),
            values: BTreeMap::new(),
            aggregates: BTreeMap::new(),
            arrays: BTreeMap::new(),
            smt_arrays: false,
            array_content_blocks: array_content_blocks(func),
            element_operand_tys: element_operand_tys(func, module),
            definitional_array_lanes: BTreeSet::new(),
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
            ptr_opaque_metadata: BTreeMap::new(),
            term_facts: large_block::TermFacts::default(),
            large_block: None,
            allow_large_block: true,
            current_instruction: 0,
            block_param_bindings: BTreeMap::new(),
            threaded_params: Vec::new(),
            block_threaded_params: BTreeMap::new(),
            block_live_params: BTreeMap::new(),
            threaded_def_block: BTreeMap::new(),
            current_block: None,
            liveness: LivenessOracle::Precise,
            work: ChcTranslationWork::default(),
            block_threaded_bindings: BTreeMap::new(),
            promoted_cells: Vec::new(),
            cell_def_block: BTreeMap::new(),
            block_promoted_cells: BTreeMap::new(),
            block_live_cells: BTreeMap::new(),
            block_cell_bindings: BTreeMap::new(),
            diagnostics: Vec::new(),
            inductive_hypothesis_sites: Vec::new(),
            call_summary_census: Vec::new(),
            call_summary_states_left: DIRECT_CALL_SUMMARY_TOTAL_STATES,
            callee_operand_tys: BTreeMap::new(),
            ty_facts: ty_facts::TyFacts::default(),
            next_sym_id: 0,
        }
    }

    /// Record one direct-call site's fate. No-op unless the census is enabled.
    fn record_call_summary_attempt(
        &mut self,
        callee: FuncId,
        callee_name: Option<&str>,
        block: BlockId,
        instruction_index: usize,
        outcome: CallSummaryOutcome,
    ) {
        if !self.options.collect_call_summary_census {
            return;
        }
        self.call_summary_census.push(CallSummaryAttempt {
            caller: self.func.name.clone(),
            callee: callee_name
                .map_or_else(|| format!("#{}", callee.as_usize()), std::borrow::ToOwned::to_owned),
            block,
            instruction_index,
            outcome,
        });
    }

    fn translate(mut self) -> ChcTranslationOutput {
        // trust-ir wire v60: a typed signature ABI anywhere in the module is
        // transport this lowering does not model (`crate::signature_abi`).
        if first_typed_signature_abi(self.module).is_some() {
            self.add_global_unsupported_error(
                TrustIrChcUnsupportedReason::TypedSignatureAbiTransport,
            );
        }
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
        // Design step 8e: an acyclic function is one large-block query
        // (`translate_chc_large_block.rs`); planned before the relations are
        // declared, because its merged blocks get none.
        if self.allow_large_block {
            self.large_block =
                large_block::plan_large_block(self.func).map(large_block::LargeBlock::new);
        }
        self.declare_block_relations();
        self.add_entry_rule();

        let func = self.func;
        match self.large_block.as_ref().map(|large| large.plan.clone()) {
            None => {
                for block in &func.blocks {
                    self.translate_block(block);
                }
            }
            Some(plan) => {
                // The per-block records the translation appends from here on
                // are restored to block order afterwards (the region is
                // translated in topological order).
                let records = (
                    self.diagnostics.len(),
                    self.inductive_hypothesis_sites.len(),
                    self.call_summary_census.len(),
                );
                for id in &plan.order {
                    if let Some(block) = func.block(*id) {
                        self.translate_block(block);
                    }
                }
                // Blocks outside the region (unreachable from the entry) keep
                // their per-block relation and rules.
                for block in &func.blocks {
                    if block.id != func.entry && !plan.merged.contains(&block.id) {
                        self.translate_block(block);
                    }
                }
                self.large_block_finish();
                if self.large_block.as_ref().is_some_and(|large| large.violation.is_some()) {
                    // The rules did not have the shape the encoding's argument
                    // needs: translate the function per block instead.
                    let mut per_block = ChcFuncTranslator::new(func, self.module, self.options);
                    per_block.liveness = self.liveness;
                    per_block.allow_large_block = false;
                    let mut output = per_block.translate();
                    output.work.large_block_fallbacks += 1;
                    return output;
                }
                let position = |block: &BlockId| plan.position.get(block).copied();
                self.diagnostics[records.0..].sort_by_key(|row| position(&row.block));
                self.inductive_hypothesis_sites[records.1..]
                    .sort_by_key(|row| position(&row.block));
                self.call_summary_census[records.2..].sort_by_key(|row| position(&row.block));
                self.work.large_block_merged_blocks += plan.merged.len() as u64;
            }
        }
        self.current_block = None;
        let column_vars =
            self.large_block.as_ref().map(|large| large.map.columns.clone()).unwrap_or_default();
        // The junk-lane invariant (`ArrayValue`): no rule may equate two
        // array-sorted terms. Checked on every translation a debug build makes.
        debug_assert!(
            !vc_equates_array_terms_beyond(&self.vc, &self.definitional_array_lanes, &column_vars),
            "translate_chc asserted an equality between array-sorted terms in `{}`",
            self.func.name
        );

        ChcTranslationOutput {
            vc: self.vc,
            module_input_refusal: None,
            diagnostics: self.diagnostics,
            inductive_hypothesis_sites: self.inductive_hypothesis_sites,
            call_summary_census: self.call_summary_census,
            work: self.work,
            large_block: self.large_block.map(|large| large.map),
        }
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
        // before liveness runs, because threading a result used only within its own
        // block would merely add a candidate that liveness then finds dead everywhere.
        // POINTER results are intentionally excluded (`is_precise_stack_scalar_ty` omits
        // `Ptr`) so instruction-result pointers do not enter `valid_ref_ptrs`; only the
        // `Undef` and sealed TLS-address special cases still thread pointer values.
        let cross_block_general = self.cross_block_general_results();
        for block in &self.func.blocks {
            for node in &block.body {
                let threadable = match &node.inst {
                    // Opaque fat-pointer summary tokens do not widen ordinary
                    // cross-block threading or stack value support.
                    Inst::Undef { ty }
                        if is_call_summary_scalar_ty(ty) || self.is_composite_value_ty(ty) =>
                    {
                        Some(ty.clone())
                    }
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
                                is_precise_stack_scalar_ty(ty) || self.is_composite_value_ty(ty)
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
        self.threaded_def_block = def_block;

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
            // A merged block of the large-block encoding gets no relation: only
            // its column layout (S's signature), which its in-edges fill
            // (`large_block_enter`).
            if self.is_merged_block(block.id) {
                let own_param_ids: std::collections::BTreeSet<u32> =
                    block.params.iter().map(|(value, _)| value.index()).collect();
                let live_here = self.block_live_params.get(&block.id);
                let threaded_list: Vec<(ValueId, Ty)> = threaded
                    .iter()
                    .filter(|(value, _)| {
                        !own_param_ids.contains(&value.index())
                            && live_here.is_some_and(|live| live.contains(&value.index()))
                    })
                    .cloned()
                    .collect();
                let live_cells = self.block_live_cells.get(&block.id);
                let cell_list: Vec<(ValueId, Ty)> = promoted
                    .iter()
                    .filter(|(cell, _)| {
                        cell_def.get(&cell.index()) != Some(&block.id)
                            && live_cells.is_some_and(|live| live.contains(&cell.index()))
                    })
                    .cloned()
                    .collect();
                self.block_threaded_params.insert(block.id, threaded_list);
                self.block_promoted_cells.insert(block.id, cell_list);
                continue;
            }
            // A block reachable from a cycle declares its arrays shape-only: no
            // column (see `ArrayValue`, `array_content_blocks`).
            let smt_arrays = self.array_content_blocks.contains(&block.id);
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
                        smt_arrays,
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
                    smt_arrays,
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
                    smt_arrays,
                    &mut arg_sorts,
                );
                bindings.push(binding);
            }

            self.work.relation_arguments += arg_sorts.len() as u64;
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
            | Inst::MakeAggregate { ty, .. }
            | Inst::Load { ty, .. }
            | Inst::LoadSlot { ty, .. }
            | Inst::ExtractField { ty, .. }
            // v50 `[value; n]`: a pure SSA value of its declared array type. The
            // caller threads it only when that type is a trackable composite, and
            // then the def block's binding is the exact SMT-array model.
            | Inst::ArraySplat { ty, .. }
            // Element read and write: exact `select` / `store` results (the
            // element type, resp. the whole array type) — pure SSA values.
            | Inst::ExtractElement { ty, .. }
            | Inst::InsertElement { ty, .. } => ty.clone(),
            Inst::MakeClosure { ty, .. } => Ty::Closure(*ty),
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
                    is_precise_stack_scalar_ty(&ty) || self.is_composite_value_ty(&ty)
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

    /// Per-block live-in sets for relation-carried values: the threaded SSA
    /// values (entry params and cross-block instruction results) or, for the
    /// second call, the promoted mem2reg cells. `def_block` maps each carried id
    /// to the one block that defines it (entry params: the entry block; a cell:
    /// its `Alloca`'s block), which computes the value and therefore never
    /// receives it.
    ///
    /// Soundness (precision, not proof authority): a block relation carries a
    /// value iff it is live-in there. Liveness is the least solution of
    /// `live_in[B] = uses[B] ∪ ⋃_{S ∈ succ(B)} (live_in[S] \ own[B])`, where
    /// `own[B]` is B's block params plus the carried values B defines, `uses[B]`
    /// is every SSA operand of every instruction in B, and `succ(B)` is the set
    /// of blocks B's TERMINATOR can transfer to. That covers every read the
    /// translation makes of a carried value:
    ///
    /// * inside B, `translate_node` reads a value only as an operand of the
    ///   instruction it translates (a cell is reached through its own id as a
    ///   Load/Store/GEP/Borrow operand; `ptr_provenance` is rebuilt per block
    ///   from exactly such operands), and `uses[B]` lists every operand through
    ///   trust-ir's canonical exhaustive walk;
    /// * across B's outgoing edges, `add_transition_rule` reads the target's
    ///   carried prefix in B's context, which the `live_in[S] \ own[B]` term
    ///   covers — and the only transitions the translation emits are the
    ///   `Br`/`CondBr`/`Switch` edges of B's terminator.
    ///
    /// A read that none of this listed would find no binding and become a fresh
    /// havoc — never a false proof (havoc over-approximates), only a lost one.
    /// `ChcTranslationWork::carried_value_misses` counts such reads and the
    /// corpus tests pin it at zero. Dropping a column no read needs changes
    /// neither the reachable states nor the error rules.
    ///
    /// The previous analysis asked EVERY instruction for terminator successors,
    /// and every non-terminator answered "conservative", so any block holding an
    /// ordinary instruction read every carried value: every relation carried
    /// everything (measured: 14-15 values per relation at N=1 of the ever-init
    /// family, 28 at N=2). It survives only as the differential oracle
    /// (`LivenessOracle::Legacy`).
    fn compute_live_params(
        &mut self,
        threaded: &[(ValueId, Ty)],
        def_block: &BTreeMap<u32, BlockId>,
    ) -> BTreeMap<BlockId, std::collections::BTreeSet<u32>> {
        let carried: BTreeSet<u32> = threaded.iter().map(|(v, _)| v.index()).collect();
        match self.liveness {
            LivenessOracle::Precise => {
                carried_live_in(self.func, &carried, def_block, &mut self.work)
            }
            #[cfg(any(test, feature = "legacy-liveness-oracle"))]
            LivenessOracle::Legacy => legacy_carried_live_in(self.func, &carried, def_block),
        }
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
        // A merged block of the large-block encoding has no relation: its
        // inputs are bound from the transitions emitted into it, and every rule
        // it emits is absorbed into the function's one query rule, so `from` is
        // never emitted (`translate_chc_large_block.rs`).
        let from = if self.is_merged_block(block.id) {
            self.large_block_enter(block);
            RelationApp::nullary(ERROR_REL)
        } else {
            let Some(from) = self.block_app(block.id) else {
                return;
            };
            if self.large_block.as_ref().is_some_and(|large| large.map.root == block.id) {
                self.large_block_begin_root(block.id);
            }
            from
        };
        self.current_block = Some(block.id);
        // Array content is modeled here only when no cycle of the CFG reaches this
        // block; the block's relation was declared the same way.
        self.smt_arrays = self.array_content_blocks.contains(&block.id);

        self.values.clear();
        self.aggregates.clear();
        self.arrays.clear();
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
                    ValueBinding::Array(array) => {
                        self.arrays.insert(*value, array.clone());
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
                    ValueBinding::Array(array) => {
                        self.arrays.insert(*value, array.clone());
                    }
                }
            }
        }

        let mut path_constraints = Vec::new();
        for (instruction_index, node) in block.body.iter().enumerate() {
            self.work.instructions_translated += 1;
            self.current_instruction = instruction_index;
            if self.translate_node(node, block.id, instruction_index, &from, &mut path_constraints)
            {
                break;
            }
        }
        self.large_block_leave(block.id);
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
        if !matches!(&node.inst, Inst::Call { .. })
            && !construction_definedness::consumption_is_valid(
                &self.source_consumption,
                self.module,
                self.func,
                node,
                None,
                None,
            )
        {
            // Retain the error at its original program point before any later
            // constraint/unused-result shortcut can hide the inspection.
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::OperandConsumption,
                from,
                path_constraints,
            );
        }
        match &node.inst {
            Inst::BoxDeref { .. } => {
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::BoxDerefValidity,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::BinOp { op, ty, lhs, rhs } if ty.is_integer() => {
                self.translate_integer_binop(*op, ty, *lhs, *rhs, node, from, path_constraints);
                // A float op on an INTEGER type is ill-typed IR; eval_binop
                // havocs the result ("float_on_int"), so fail closed rather
                // than let the unconstrained value silently feed obligations
                // (mirrors the BMC lane's translate_integer_binop).
                if binop_is_floating_point(*op) {
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::FloatingPointArithmetic,
                        from,
                        path_constraints,
                    );
                }
                // A rotate is encoded EXACTLY (`bv_rotate`); only operands that
                // are not same-width bit-vectors leave eval_binop a havoc, and
                // that case fails closed like float-on-int. Both operands were
                // bound by `translate_integer_binop` above, so these resolves
                // return the same expressions it used.
                if matches!(op, BinOp::RotL | BinOp::RotR) {
                    let lhs_expr = self.resolve(*lhs, ty);
                    let rhs_expr = self.resolve(*rhs, ty);
                    if integer_rotate_is_unencodable(*op, ty, &lhs_expr, &rhs_expr) {
                        self.add_unsupported_error(
                            block,
                            instruction_index,
                            node,
                            TrustIrChcUnsupportedReason::NonIntegerBinaryOperation,
                            from,
                            path_constraints,
                        );
                    }
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
                    let reason = if ty.is_float() || binop_is_floating_point(*op) {
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
            // trust-ir v67-v70 tensor region (`crate::tensor_region`): a
            // constant of a tensor type, or a content-addressed `TensorBlob`,
            // has no sort and no bits here, so it fails closed by name before
            // the arm below could ask for either. Its result stays unbound.
            Inst::Const { ty, value }
                if let Some(construct) = crate::tensor_region::const_tensor_construct(ty, value) =>
            {
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::TensorRegion(construct),
                    from,
                    path_constraints,
                );
                false
            }
            Inst::Const { ty, value } => {
                if matches!(ty, Ty::Enum(_)) {
                    if let Some(binding) = dataless_enum::constant_tag(self.module, ty, value)
                        .and_then(dataless_enum::binding)
                    {
                        self.bind_aggregate_result(node, binding, ty);
                    } else {
                        let result = self.fresh_symbolic("unmodeled_enum_const", ty);
                        self.bind_first_result(node, result);
                        self.add_unsupported_error(
                            block, instruction_index, node,
                            TrustIrChcUnsupportedReason::UnmodeledConstant,
                            from, path_constraints,
                        );
                    }
                    return false;
                }
                // trust-ir v50 `Splat { elem, len }` at a trackable array type is
                // modeled exactly as one constant SMT array per leaf of `elem`'s
                // exact encoding (`exact_constant_binding`), whatever `len` is; a
                // list-spelled literal (`Array`, `Aggregate` at an array type,
                // `Bytes` at `[u8; n]`) as fresh lanes pinned by one definitional
                // equality per element (`define_array_lanes`), conjoined into ONE
                // path constraint here — the literal's text, at constant depth. An
                // array literal whose element has no exact encoding here gets fresh
                // lanes: O(1) in `len`, no error.
                let array_literal = match value {
                    Constant::Splat { .. } | Constant::Array(_) => true,
                    Constant::Aggregate(_) | Constant::Bytes { .. } => {
                        matches!(self.composite_shape(ty), Some(CompositeShape::Array { .. }))
                    }
                    _ => false,
                };
                let mut definitions = Vec::new();
                if array_literal
                    && let Some(binding) = self.exact_constant_binding(ty, value, &mut definitions)
                {
                    if !definitions.is_empty() {
                        path_constraints.push(Expr::and_many(definitions));
                    }
                    self.bind_binding_result(node, binding, ty);
                } else if let Constant::Splat { .. } | Constant::Array(_) | Constant::Aggregate(_) =
                    value
                    && let Some(CompositeShape::Array { .. }) = self.composite_shape(ty)
                {
                    // An array literal with an element this lowering cannot encode
                    // exactly: fresh lanes (the value of an unknown array), still
                    // typed, so every element access keeps its bounds obligation.
                    let havoc = self.fresh_value_binding("const_array", ty);
                    self.bind_binding_result(node, havoc, ty);
                } else if matches!(value, Constant::SymbolAddr { .. }) {
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
            // trust-ir v52 `kind` / v54 `site` name WHICH panic a failure is and
            // the entry it would call; the check fails iff `cond` is false
            // whatever they are, and a failed assert is a terminal panic.
            Inst::Assert { cond, kind: _, site: _ } => {
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
                if let Some(binding) = self.resolve_composite(*operand, ty) {
                    self.bind_binding_result(node, binding, ty);
                } else {
                    let expr = self.resolve(*operand, ty);
                    self.bind_first_result(node, expr);
                }
                if let Some(result) = node.results.first() {
                    self.copy_ptr_parts(*operand, *result);
                }
                // A thin-pointer `Copy` is the Rust producers' spelling of a borrow
                // (`transparent_pointer_alias`), so it inherits the referent's
                // interior-pointer provenance exactly as the `Borrow` arm does;
                // without it `*(&mut local)` would lose its base and the write
                // would reach no tracked cell.
                if transparent_pointer_alias(&node.inst).is_some() {
                    self.inherit_alias_provenance(node, *operand);
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
                if matches!(ty, Ty::Enum(_)) {
                    let selected = self.aggregates.get(then_val)
                        .zip(self.aggregates.get(else_val))
                        .and_then(|(then_value, else_value)| dataless_enum::select_binding(
                            self.module, ty, &cond_expr,
                            &ValueBinding::Aggregate(then_value.clone()),
                            &ValueBinding::Aggregate(else_value.clone()),
                        ));
                    if let Some(selected) = selected {
                        self.bind_aggregate_result(node, selected, ty);
                    } else {
                        let result = self.fresh_symbolic("unmodeled_enum_select", ty);
                        self.bind_first_result(node, result);
                        self.add_unsupported_error(
                            block, instruction_index, node,
                            TrustIrChcUnsupportedReason::AggregateProjection,
                            from, path_constraints,
                        );
                    }
                    return false;
                }
                // An array-typed `Select` is `ite(cond, then, else)` leaf by leaf on
                // the arrays' lanes, bound like any array value, so an element access
                // on the result reads its lanes (and its bounds need no declared
                // type). A mismatched arm (malformed IR) falls through below.
                if let Some(CompositeShape::Array { .. }) = self.composite_shape(ty)
                    && let Some(then_array) = self.resolve_array(*then_val, ty)
                    && let Some(else_array) = self.resolve_array(*else_val, ty)
                    && let Some(ValueBinding::Array(selected)) = ValueBinding::Array(then_array)
                        .select_by(&cond_expr, &ValueBinding::Array(else_array))
                {
                    self.bind_array_result(node, selected, ty);
                    return false;
                }
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
                    Some(binding) => self.bind_binding_result(node, binding, ty),
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
                        self.resolve_composite(result_id, ty);
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
            // trust-ir WS3.20 bulk memory: `memcpy` / `memmove` (MemCopy) and
            // `memset` (MemSet) over `bytes` bytes at `dst`, in an encoding whose
            // size does not depend on `bytes` (`translate_chc_bulk_memory.rs`):
            // exact undefined behaviour and an exact write where the range is one
            // whole object of a stack cell; a havoc of every cell the write could
            // reach, failing closed by name, where it is not. Never a dropped write,
            // whatever `check_memory_bounds` says.
            Inst::MemCopy { .. } | Inst::MemSet { .. } => {
                self.translate_bulk_memory(node, block, instruction_index, from, path_constraints);
                false
            }
            Inst::PtrData { ptr_ty, ptr } => {
                let data = match self.ptr_parts_view(*ptr) {
                    PtrPartsView::Exact(data, _) => data,
                    PtrPartsView::Opaque | PtrPartsView::Unrecorded => self.resolve(*ptr, ptr_ty),
                };
                self.bind_first_result(node, data);
                false
            }
            Inst::PtrMetadata { ptr_ty, metadata_ty, ptr } => {
                let view = self.ptr_parts_view(*ptr);
                let metadata = if let PtrPartsView::Exact(_, metadata) = view {
                    metadata
                } else if matches!(metadata_ty, Ty::Unit) {
                    Expr::true_()
                } else if matches!(view, PtrPartsView::Opaque) {
                    // A `PtrFromParts` value (or a copy) read where its parts are
                    // not exact: its metadata is whatever it was built with, so an
                    // UNBOUNDED havoc — the `slice_len` bound below is a fact
                    // about a reference, not about a constructed pointer.
                    self.opaque_ptr_metadata(*ptr, metadata_ty)
                } else if matches!(metadata_ty, Ty::U64) && !fat_ptr_metadata_is_vtable_word(ptr_ty)
                {
                    // A slice/str fat-pointer's metadata is its element/byte LENGTH
                    // (usize == U64). Model it as a symbolic instead of an opaque
                    // unsupported value, so the CHC/PDR lane can prove obligations over
                    // `s.len()` — e.g. `s.len() + 1` no-overflow and
                    // `while i < s.len() { i += 1 }`. Gated to `U64` so a `dyn Trait`
                    // vtable pointer (Ty::Ptr) is NOT mis-bounded — it keeps the
                    // opaque-unsupported path below — AND gated on the KIND
                    // (`fat_ptr_metadata_is_vtable_word`): `TraitObject` and its v40
                    // `dyn`-tail sibling `ContainerVtable` carry an opaque VTABLE WORD
                    // whatever `metadata_ty` a producer spelled, and a vtable word read
                    // as a length is a type confusion, so those kinds take the refusal
                    // below rather than a `slice_len` symbol. (trust-ir's validator
                    // rejects the mis-spelling; this lane does not validate hand-built
                    // modules, so the classification is enforced here as well.)
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
                    let closed = self.term_facts.is_closed(&data_expr)
                        && self.term_facts.is_closed(&metadata_expr);
                    if let Some(block) = self.current_block {
                        self.ptr_parts.insert(
                            *result,
                            PtrParts::Exact {
                                block,
                                data: data_expr,
                                metadata: metadata_expr,
                                closed,
                            },
                        );
                    }
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
                        self.copy_ptr_parts(*operand, result);
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
                    let data = match self.ptr_parts_view(*operand) {
                        PtrPartsView::Exact(data, _) => data,
                        PtrPartsView::Opaque | PtrPartsView::Unrecorded => {
                            self.resolve(*operand, src_ty)
                        }
                    };
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
            Inst::MakeAggregate { ty: ty @ Ty::Enum(_), variant, fields } => {
                if let Some(binding) = dataless_enum::variant_tag(self.module, ty, *variant, fields)
                    .and_then(dataless_enum::binding)
                {
                    self.bind_aggregate_result(node, binding, ty);
                } else {
                    let result = self.fresh_symbolic("unmodeled_enum_constructor", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block, instruction_index, node,
                        TrustIrChcUnsupportedReason::AggregateConstruction,
                        from, path_constraints,
                    );
                }
                false
            }
            // `MakeAggregate` at a non-empty array type, one operand per lane: the
            // flat definitional encoding of its operands (`eval_make_array`), one
            // path constraint, exact. Field aggregates use their existing
            // recursively tracked bindings below; other shapes fail closed.
            Inst::MakeAggregate { ty, variant, fields }
                if matches!(self.composite_shape(ty), Some(CompositeShape::Array { .. })) =>
            {
                let mut definitions = Vec::new();
                if let Some(array) = self.eval_make_array(ty, *variant, fields, &mut definitions) {
                    if !definitions.is_empty() {
                        path_constraints.push(Expr::and_many(definitions));
                    }
                    self.bind_array_result(node, array, ty);
                } else {
                    let result = self.fresh_symbolic("make_aggregate_result", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        TrustIrChcUnsupportedReason::AggregateConstruction,
                        from,
                        path_constraints,
                    );
                }
                false
            }
            Inst::MakeAggregate { ty, variant, fields } => {
                match self.eval_make_field_aggregate(ty, *variant, fields) {
                    Ok(aggregate) => self.bind_aggregate_result(node, aggregate, ty),
                    Err(reason) => {
                    let result = self.fresh_symbolic("make_aggregate_result", ty);
                    self.bind_first_result(node, result);
                    self.add_unsupported_error(
                        block,
                        instruction_index,
                        node,
                        reason,
                        from,
                        path_constraints,
                    );
                    }
                }
                false
            }
            // Do not erase a runtime closure's target or treat its captures as
            // an ordinary field constructor. Until closure values/application
            // have an exact model, even an unused constructor must fail closed:
            // consuming a poison capture is observable undefined behavior.
            Inst::MakeClosure { ty, .. } => {
                let result = self.fresh_symbolic("make_closure_result", &Ty::Closure(*ty));
                self.bind_first_result(node, result);
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::ClosureConstruction,
                    from,
                    path_constraints,
                );
                false
            }
            // trust-ir v67-v69 tensor region (`crate::tensor_region`): no tensor
            // value has a sort here, and the module input refuses every module
            // that stores one before any function is translated. A caller that
            // bypasses it still meets an unconditional error rule naming the
            // instruction. Results stay unbound and operands unread: binding a
            // result would need the tensor sort this lowering does not have.
            Inst::TensorContract { .. } => {
                self.add_tensor_region_error(
                    crate::TensorConstruct::TensorContract,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::TensorMap { .. } => {
                self.add_tensor_region_error(
                    crate::TensorConstruct::TensorMap,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::TensorReduce { .. } => {
                self.add_tensor_region_error(
                    crate::TensorConstruct::TensorReduce,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::TensorView { .. } => {
                self.add_tensor_region_error(
                    crate::TensorConstruct::TensorView,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::TensorGather { .. } => {
                self.add_tensor_region_error(
                    crate::TensorConstruct::TensorGather,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                false
            }
            Inst::TensorScatter { .. } => {
                self.add_tensor_region_error(
                    crate::TensorConstruct::TensorScatter,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                false
            }
            // trust-ir v50 `ArraySplat` (`[value; n]`, `ty = Array(e, n)`): pure
            // and total — no memory effect, no run-time obligation — so it never
            // raises an error rule. A trackable array binds one constant SMT array
            // per leaf of `value`'s binding (`eval_array_splat`), which is the
            // instruction's exact denotation (the Lean law
            // `ExtractElement i (splat v n) = v`, `i < n`) in constant size
            // whatever `n` is. An array whose element this model does not track
            // is ONE opaque fresh value: an unconstrained array over-approximates
            // `[value; n]`, and every consumer that would need its lanes either
            // havocs the read (`ExtractElement`) or fails closed
            // (`InsertElement`).
            Inst::ArraySplat { ty, value } => {
                if let Some(binding) = self.eval_array_splat(ty, *value) {
                    self.bind_binding_result(node, binding, ty);
                } else {
                    let result = self.fresh_symbolic("array_splat", ty);
                    self.bind_first_result(node, result);
                }
                false
            }
            Inst::ExtractField { ty, aggregate, field } => {
                if let Some(binding) = self.eval_extract_field(*aggregate, *field) {
                    // Trust (#46): the extracted field may itself be a nested
                    // aggregate (e.g. the tuple payload of `Some((a,b))`) — bind it as
                    // an aggregate so a SUBSEQUENT ExtractField on this result resolves.
                    self.bind_binding_result(node, binding, ty);
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
            // An array element READ: `select` on the array's SMT-array lanes, exact
            // at any index, with its own in-bounds obligation
            // (`translate_extract_element`). It never fails closed: a read this
            // model cannot place (a SIMD vector, an unbound array value) is a
            // fresh unconstrained value, which can never make a dependent
            // obligation falsely provable.
            Inst::ExtractElement { ty: dst_ty, array, index } => {
                self.translate_extract_element(
                    dst_ty,
                    *array,
                    *index,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                );
                false
            }
            // Exhaustive over `UnOp` (no wildcard): a new trust-ir variant is a
            // compile error here until this lane decides to model or refuse it.
            Inst::UnOp { op, ty, operand } => match op {
                // Logical / bitwise NOT is a TOTAL function whose value must be
                // BOUND, not havocked. An inlined `acc = !acc` (and `acc ^ true`,
                // which trustc const-folds to `UnOp::Not`) otherwise fell through
                // to the fail-closed fresh-symbolic path below, leaving `acc'`
                // free — so a loop-carried boolean accumulator was HAVOC'd and the
                // loop invariant (e.g. count-parity `acc <=> count[0]`) became
                // unprovable. Model `Not` PRECISELY (bool -> logical not, integer
                // -> bitwise complement), mirroring the direct-call summary
                // interpreter's `UnOp::Not` arm.
                UnOp::Not if matches!(ty, Ty::Bool) || ty.is_integer() => {
                    let operand_expr = self.resolve(*operand, ty);
                    let result = if matches!(ty, Ty::Bool) {
                        operand_expr.not()
                    } else {
                        operand_expr.bvnot()
                    };
                    self.bind_first_result(node, result);
                    false
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
                UnOp::Neg if ty.is_integer() => {
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
                    false
                }
                // Everything else keeps the fail-closed fresh-symbolic modeling
                // (`UnaryOperation`): `Not`/`Neg` on a non-integer operand, the
                // IEEE float ops, and the bit intrinsics `CtPop`/`CtLz`/`CtTz`/
                // `BSwap`/`BitReverse`, none of which has an exact encoding here.
                UnOp::Not
                | UnOp::Neg
                | UnOp::FNeg
                | UnOp::FAbs
                | UnOp::FSqrt
                | UnOp::FFloor
                | UnOp::FCeil
                | UnOp::FTrunc
                | UnOp::CtPop
                | UnOp::CtLz
                | UnOp::CtTz
                | UnOp::BSwap
                | UnOp::BitReverse => {
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
            },
            // An array element WRITE. The symmetric counterpart of the
            // `InsertField` arm above (struct/tuple field write): TrustIR
            // `InsertElement` is a PURE functional update — it READS `array` and
            // BINDS A NEW SSA result; the source value's binding is never mutated
            // (`trust_ir::interpret::eval_insert_element` clones before assigning).
            // So there is no in-place location whose tracked value a model could
            // leave stale; the only thing that must be right is the RESULT binding,
            // which is `store` on the SMT-array lanes at any index, constant or
            // symbolic, with its own in-bounds obligation (`eval_insert_element`).
            // The pervasive shape is the `[core::fmt::rt::Argument; N]` array every
            // `format!`/`write!` builds: one `InsertElement` at a CONSTANT index per
            // format argument. A write this model cannot place keeps the
            // fail-closed error rule below.
            Inst::InsertElement { ty, array, index, value } => {
                if let Some(result) = self.eval_insert_element(
                    ty,
                    *array,
                    *index,
                    *value,
                    block,
                    instruction_index,
                    node,
                    from,
                    path_constraints,
                ) {
                    self.bind_array_result(node, result, ty);
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
                if let Some(result_id) = node.results.first() {
                    self.copy_ptr_parts(*ptr, *result_id);
                }
                self.inherit_alias_provenance(node, *ptr);
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
            | Inst::Drop { .. }
            | Inst::CloseFrame { .. }
            | Inst::CoroSuspend { .. }
            | Inst::Invoke { .. }
            | Inst::LandingPad { .. }
            | Inst::Resume { .. }
            // trust-ir v53 no-unwind boundary calls and the unwinding twins
            // (v54 `AssertInvoke`, v55 `DropInvoke`, v56 `InvokeIndirect`): no
            // CHC model of the boundary, the unwind edge, the glue or the
            // dispatch, so each fails closed by name (`unsupported_unit_reason`).
            | Inst::CallCannotUnwind { .. }
            | Inst::CallIndirectCannotUnwind { .. }
            | Inst::AssertInvoke { .. }
            | Inst::DropInvoke { .. }
            | Inst::InvokeIndirect { .. }
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
        //
        // A bulk `MemCopy`/`MemSet` through the cell's address is a TRACKED use for
        // this decision (`BulkMemoryUse::Tracked`): `translate_bulk_memory` writes
        // the cell exactly or havocs it, never leaving a stale value. The
        // proof-authority gate and the promotion analysis keep the stricter
        // classification, so no cell they admit or promote ever reaches one.
        if matches!(
            stack_alloca_escape_classification_with(self.func, result, BulkMemoryUse::Tracked),
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
        self.func
            .blocks
            .iter()
            .flat_map(|b| b.body.iter())
            .any(|n| matches!(&n.inst, Inst::GEP { .. }) && n.results.iter().any(|r| *r == ptr))
    }

    fn translate_stack_load(&mut self, ty: &Ty, ptr: ValueId, node: &InstrNode) -> bool {
        if !self.stack_cells.contains_key(&ptr) {
            self.note_carried_cell_miss(ptr);
        }
        // Borrow/BorrowMut gives the alias a new SSA id while retaining the
        // base cell's whole-object provenance. Resolve that empty lane path to
        // the same cell as a direct load; matching the symbolic pointer value
        // alone would not establish this identity. The exact cell type is still
        // checked below, and an invalidated/absent cell supplies no stale value.
        let cell = self.stack_cells.get(&ptr).or_else(|| {
            let provenance = self.ptr_provenance.get(&ptr)?;
            if !provenance.lanes.as_ref()?.is_empty() {
                return None;
            }
            self.stack_cells.get(&provenance.base)
        });
        let Some(cell) = cell.cloned() else {
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
                lane_trace_gep(
                    "exit1_no_provenance",
                    self.ptr_is_gep_derived(ptr),
                    &self.func.name,
                );
                return false;
            };
            let Some(lanes) = provenance.lanes else {
                lane_trace("exit2_lanes_none");
                lane_trace_gep("exit2_lanes_none", self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            };
            // Exactly one constant lane: a nested path is not modelled here, and
            // the empty whole-cell path is handled by the lookup above.
            let [(field, field_ty)] = lanes.as_slice() else {
                let e3 = if lanes.is_empty() { "exit3a_empty_path" } else { "exit3b_nested_chain" };
                lane_trace(e3);
                lane_trace_gep(e3, self.ptr_is_gep_derived(ptr), &self.func.name);
                return false;
            };
            if field_ty != ty {
                lane_trace("exit4_field_ty_mismatch");
                lane_trace_gep(
                    "exit4_field_ty_mismatch",
                    self.ptr_is_gep_derived(ptr),
                    &self.func.name,
                );
                return false;
            }
            let Some(base_cell) = self.stack_cells.get(&provenance.base).cloned() else {
                lane_trace("exit5_base_not_tracked");
                lane_trace_gep(
                    "exit5_base_not_tracked",
                    self.ptr_is_gep_derived(ptr),
                    &self.func.name,
                );
                return false;
            };
            let leaf = match base_cell.value {
                ValueBinding::Aggregate(aggregate) => aggregate.fields.get(*field).cloned(),
                // An array cell's constant lane: `select` on its SMT-array lanes.
                // `extend_exact_gep_lanes` admitted the lane only below the length.
                ValueBinding::Array(array) if array.lanes.is_some() => u64::try_from(*field)
                    .ok()
                    .and_then(|lane| array.select(&Expr::bitvec_const(lane, 64))),
                // A SHAPE-ONLY array cell (a block a cycle of the CFG reaches, see
                // `ArrayValue`): the lane's VALUE is not modeled, but the ACCESS is
                // to owned stack memory at a lane `extend_exact_gep_lanes` admitted
                // below the length — valid by construction. So it reads a fresh
                // value, exactly as a load of an untracked owned cell does
                // (`known_stack` in the `Load` arm), and owes no memory error: a
                // fail-closed error here would poison every obligation of the
                // function over an access that is known to be in bounds.
                ValueBinding::Array(_) => Some(self.fresh_value_binding("stack_lane_read", ty)),
                ValueBinding::Scalar(_) => {
                    lane_trace("exit6_base_not_aggregate");
                    lane_trace_gep(
                        "exit6_base_not_aggregate",
                        self.ptr_is_gep_derived(ptr),
                        &self.func.name,
                    );
                    return false;
                }
            };
            let Some(leaf) = leaf else {
                return false;
            };
            self.bind_binding_result(node, leaf, ty);
            return true;
        };
        if cell.ty != *ty {
            return false;
        }

        self.bind_binding_result(node, cell.value, ty);
        true
    }

    fn translate_stack_store(&mut self, ty: &Ty, ptr: ValueId, value: ValueId) -> bool {
        let Some(cell_ty) = self.stack_cells.get(&ptr).map(|cell| cell.ty.clone()) else {
            self.note_carried_cell_miss(ptr);
            return false;
        };
        if cell_ty != *ty {
            return false;
        }

        let value_binding = if self.is_composite_value_ty(ty) {
            let Some(binding) = self.resolve_composite(value, ty) else {
                return false;
            };
            binding
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
    /// declared type. Declining is FAIL-CLOSED at the one call site, the GEP lane
    /// walk, which then records an unknown offset (a later store havocs the whole
    /// cell). Element accesses do not use this: `array_lane_access` reads a
    /// constant index by its declared signedness.
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

    /// Aggregate lane selected exactly by one single-scale GEP step (memoized
    /// per `(aggregate, field, pointee)` by `exact_gep_lane_ty`,
    /// `translate_chc_ty_facts.rs`).
    ///
    /// Struct precision requires complete declared byte layout: every field must
    /// have an offset and a layout, every range must fit the struct, no starts may
    /// alias, and no byte ranges may overlap (`exact_struct_ranges`). The selected
    /// field's declared start must equal `field * size_of(pointee_ty)`. Missing
    /// metadata is not evidence and therefore returns `None`. Arrays carry their
    /// own exact element stride and remain precise when it agrees with the
    /// pointee layout.
    fn exact_gep_lane_ty_uncached(
        &self,
        aggregate_ty: &Ty,
        field: usize,
        pointee_ty: &Ty,
    ) -> Option<Ty> {
        // The lane's type: a struct field, or an array's element for a lane below
        // its length (an array's lanes are not a field list — `CompositeShape`).
        let (field_tys, field_ty) = match self.composite_shape(aggregate_ty)? {
            CompositeShape::Fields(field_tys) => {
                let field_ty = field_tys.get(field)?.clone();
                (field_tys, field_ty)
            }
            CompositeShape::Array { elem, len } => {
                if u64::try_from(field).ok()? >= len {
                    return None;
                }
                (Vec::new(), elem)
            }
        };
        let field_ty = &field_ty;
        if field_ty != pointee_ty {
            return None;
        }

        let pointee_bits = self.layout_fact(pointee_ty)?.size_bits;
        if pointee_bits == 0 || pointee_bits % 8 != 0 {
            return None;
        }
        let gep_offset_bits = pointee_bits.checked_mul(u64::try_from(field).ok()?)?;

        match aggregate_ty {
            Ty::Struct(id) => {
                // The logical field identity must be unique at the selected byte
                // address and the aggregate binding must not hide byte aliases.
                let ranges = self.exact_struct_ranges(*id, &field_tys)?;
                if ranges.get(field)?.0 != gep_offset_bits {
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
                if self.layout_fact(aggregate_ty)?.stride_bits? != pointee_bits {
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
    /// type, a volatile or atomic store, a bulk `MemCopy`/`MemSet` — and as the
    /// fallback of `model_indirect_store`.
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
    ///   2. the cell's type is walked with `composite_shape` — the SAME table
    ///      `fresh_stack_cell_value` built the binding from and the `Load`/
    ///      `ExtractField` path reads it back through (an array lane is admitted
    ///      only below the length);
    ///   3. the stored type must equal the final lane type, and the binding tree
    ///      must actually have a composite node at every step: a field is replaced
    ///      in place, an array lane is `select`ed, updated and `store`d back
    ///      (`update_binding_lane`).
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

        let new_binding = if self.is_composite_value_ty(ty) {
            let Some(binding) = self.resolve_composite(value, ty) else {
                return false;
            };
            binding
        } else if is_precise_stack_scalar_ty(ty) {
            ValueBinding::Scalar(self.resolve(value, ty))
        } else {
            return false;
        };

        let Some(cell) = self.stack_cells.get(&base) else {
            return false;
        };
        let path: Vec<usize> = lanes.iter().map(|(field, _)| *field).collect();
        let Some(updated) = update_binding_lane(&cell.value, &path, new_binding) else {
            return false;
        };
        let Some(cell) = self.stack_cells.get_mut(&base) else {
            return false;
        };
        cell.value = updated;
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

    /// Give the result of a transparent alias of `referent` (a `Borrow`/`BorrowMut`,
    /// or a thin-pointer `Copy`: [`transparent_pointer_alias`]) the referent's
    /// interior-pointer provenance verbatim. Without this, `*(&mut local)` and
    /// `*(&mut local.field)` lose their base and the write is dropped.
    ///
    /// R3: an alias of one of the FUNCTION's own allocas from a block other than the
    /// defining one roots the same {base, whole-cell} provenance the defining block
    /// would have inherited (see the GEP arm's alloca-root fallback for the
    /// rationale and scope).
    fn inherit_alias_provenance(&mut self, node: &InstrNode, referent: ValueId) {
        let provenance = self.ptr_provenance.get(&referent).cloned().or_else(|| {
            self.func_alloca_ptrs
                .contains(&referent)
                .then(|| PtrProvenance { base: referent, lanes: Some(Vec::new()) })
        });
        if let Some(provenance) = provenance
            && let Some(result_id) = node.results.first()
        {
            self.ptr_provenance.insert(*result_id, provenance);
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
            // A thin-pointer `Copy` is the Rust producers' spelling of a borrow
            // (`transparent_pointer_alias`): its result inherits the referent's
            // provenance in `translate_node`'s `Copy` arm, so the operand is a
            // TRACKED position, not an escape. Any other `Copy` falls to `_`.
            inst @ Inst::Copy { .. } if transparent_pointer_alias(inst).is_some() => Vec::new(),
            // `ptr` is tracked; the written VALUE puts a pointer into memory.
            Inst::Store { value, .. } | Inst::AtomicStore { value, .. } => vec![*value],
            // `base` is tracked; an index is an ordinary operand.
            Inst::GEP { indices, .. } => indices.clone(),
            // Bulk memory reads and writes THROUGH `dst`/`src` (the arm models the
            // write exactly or havocs every cell it could reach); it puts no
            // address into memory. The byte count and fill byte are values.
            Inst::MemCopy { bytes, .. } => vec![*bytes],
            Inst::MemSet { byte, bytes, .. } => vec![*byte, *bytes],
            _ => uses,
        };
        for used in escaping {
            if let Some(provenance) = self.ptr_provenance.get(&used) {
                self.escaped_cell_bases.insert(provenance.base);
            }
        }
    }

    fn fresh_stack_cell_value(&mut self, ty: &Ty) -> Option<ValueBinding> {
        match self.composite_shape(ty) {
            Some(CompositeShape::Fields(field_tys)) => {
                let mut fields = Vec::with_capacity(field_tys.len());
                for (field_index, field_ty) in field_tys.iter().enumerate() {
                    // Trust (#46): recurse for nested-composite fields.
                    fields.push(self.resolve_field_binding(
                        &format!("stack_init_field{field_index}"),
                        field_ty,
                    )?);
                }
                return Some(ValueBinding::Aggregate(AggregateValue { fields }));
            }
            // One fresh SMT array per element leaf, whatever the length.
            Some(CompositeShape::Array { .. }) => {
                return self.fresh_binding_lifted("stack_init", ty, 0);
            }
            None => {}
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
                // A `Constant::TensorBlob` case (`crate::tensor_region`) is
                // refused by name, not as a generic switch.
                let reason = if crate::constant_carries_tensor_blob(&case.value) {
                    TrustIrChcUnsupportedReason::TensorRegion(
                        crate::TensorConstruct::TensorBlobConstant,
                    )
                } else {
                    TrustIrChcUnsupportedReason::Switch
                };
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    reason,
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

        if let Some(no_overflow) =
            integer_binop_overflow_obligation(op, ty, &lhs_expr, &rhs_expr, node, self.options)
        {
            self.add_error_rule(from, path_constraints, no_overflow.not());
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
            self.record_call_summary_attempt(
                callee,
                None,
                block,
                instruction_index,
                CallSummaryOutcome::NotAttempted { reason: "callee_not_in_module" },
            );
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

        if !construction_definedness::consumption_is_valid(
            &self.source_consumption,
            self.module,
            self.func,
            node,
            None,
            None,
        ) {
            self.bind_symbolic_call_results(&callee_func.name, callee_return_tys, node);
            self.record_call_summary_attempt(
                callee,
                Some(&callee_func.name),
                block,
                instruction_index,
                CallSummaryOutcome::NotAttempted { reason: "call_argument_transport" },
            );
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::CallArgumentTransport,
                from,
                path_constraints,
            );
            return;
        }

        // Trust (2026-09-14): a DIRECT SELF-call first tries the inductive
        // hypothesis (Park induction for recursive procedures); every fence miss
        // falls through to the historical unconditional error rule below.
        let mut ih_fence_miss: Option<&'static str> = None;
        if callee == self.func.id {
            match callee_func_ty.as_ref() {
                Some(func_ty) => match self.try_self_call_inductive_hypothesis(
                    &callee_func,
                    func_ty,
                    args,
                    node,
                    block,
                    instruction_index,
                    from,
                    path_constraints,
                ) {
                    Ok(()) => return,
                    Err(miss) => ih_fence_miss = Some(miss),
                },
                None => ih_fence_miss = Some("ih_fence:callee_func_ty_missing"),
            }
        }
        if self.is_recursive_direct_call(callee, &callee_func) {
            self.bind_symbolic_call_results(&callee_func.name, callee_return_tys, node);
            for (i, arg) in args.iter().enumerate() {
                let arg_ty = callee_func_ty
                    .as_ref()
                    .and_then(|func_ty| func_ty.params.get(i))
                    .unwrap_or(&Ty::I64);
                let _ = self.resolve(*arg, arg_ty);
            }
            self.record_call_summary_attempt(
                callee,
                Some(&callee_func.name),
                block,
                instruction_index,
                CallSummaryOutcome::NotAttempted {
                    reason: ih_fence_miss.unwrap_or("recursive_direct_call"),
                },
            );
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

        // A name and signature do not authenticate an intrinsic. Interpret the
        // provided body, or refuse the call if it cannot be summarized. Real
        // modular arithmetic is represented by a Wrapping-tagged BinOp and is
        // handled by the ordinary instruction semantics, including in summaries.
        let decline = DeclineSlot::default();
        if let Some(summary) =
            self.try_direct_call_summary(&callee_func, CallSummaryArgs::Caller(args), &decline, 0)
        {
            for condition in summary.error_conditions {
                self.add_error_rule(from, path_constraints, condition);
            }
            if let Some(callee_func_ty) = &callee_func_ty
                && summary.returns.len() == node.results.len()
                && summary.returns.len() == callee_func_ty.returns.len()
            {
                self.record_call_summary_attempt(
                    callee,
                    Some(&callee_func.name),
                    block,
                    instruction_index,
                    CallSummaryOutcome::Summarized,
                );
                for ((result, ty), binding) in
                    node.results.iter().zip(callee_func_ty.returns.iter()).zip(summary.returns)
                {
                    let binding = self.materialize_call_summary_binding(binding);
                    self.bind_call_result(*result, binding, ty);
                }
                return;
            }
            self.record_call_summary_attempt(
                callee,
                Some(&callee_func.name),
                block,
                instruction_index,
                CallSummaryOutcome::SummarizedArityMismatch,
            );
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
        self.record_call_summary_attempt(
            callee,
            Some(&callee_func.name),
            block,
            instruction_index,
            decline.into_outcome(),
        );

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

    /// Trust (2026-09-14): model a DIRECT SELF-call by the INDUCTIVE HYPOTHESIS.
    ///
    /// The whole-function panic-freedom aggregate asks "no `error` is reachable
    /// from the entry relation, for every entry state satisfying the entry
    /// `Assume`s (the bridge lowers `requires` clauses to exactly those)". Under
    /// that reading the standard Hoare rule for recursive procedures applies:
    /// assume the deeper activation is safe (its results are FRESH symbols, it
    /// contributes NO error rule), and in exchange (1) re-assert every entry
    /// precondition over the ACTUALS at the call site — the deeper activation is
    /// covered by the same universal statement only if its input satisfies the
    /// preconditions — and (2) keep every other obligation of the body exactly
    /// where it is. Then, by induction on the call tree: a panicking execution
    /// has an innermost panicking activation; every self-call before its panic
    /// point RETURNED with some values (a panicking deeper call would be a
    /// deeper panicking activation), those values are covered by the fresh
    /// symbols, the activation's input satisfied the preconditions (re-asserted
    /// by its caller), and so that activation is a witness against the VC —
    /// contradiction. Multiple self-calls (a call TREE) are the same argument;
    /// `first-party/clean/proofs/trust-soundness/general_recursion.lean`
    /// kernel-checks the single-chain, precondition-free special case.
    ///
    /// FENCE (affirmative, every miss falls back to the error rule):
    /// (a) arity matches the declared signature; (b) every parameter and every
    /// result is a POINTER-FREE scalar (`is_precise_stack_scalar_ty`, NOT the
    /// summary lane's predicate, which admits opaque `Ty::Ptr`), so the deeper
    /// activation can reach no memory of this activation through its inputs and
    /// hands none back; (c) the body is FRAME-LOCAL by an ALLOW-LIST of
    /// instruction kinds — no global address, no indirect call, no pointer
    /// forged from an integer, no fat-pointer part, no atomic/heap/dialect/
    /// coroutine instruction, and every `Store` writes through a pointer derived
    /// from this function's own `Alloca`s — so the deeper activation cannot
    /// clobber this activation's tracked cells (a new `Inst` variant is refused
    /// until listed); (d) every entry-block `Assume` that depends on a parameter
    /// is RE-INSTANTIABLE over the actuals (comparisons, boolean connectives,
    /// constants, copies); one that depends on a parameter through any other
    /// shape declines the whole site. An `Assume` that depends on no parameter
    /// (an authenticated fact about a value computed inside the activation) does
    /// not narrow the ENTRY state and is left alone.
    ///
    /// Escaped-cell invalidation at this call is the same as at every other
    /// call: `translate_node` runs `invalidate_cells_escaping_into_call` before
    /// dispatching to this arm.
    ///
    /// DEMOTION: the site is recorded in `inductive_hypothesis_sites`, which the
    /// bundle stamps as `inductive_hypothesis_site_count`; the driver holds any
    /// REFUTATION of such an obligation at Unknown (a counterexample may pass
    /// through a havoc'd self-call result) and declines the pre-solve refutation
    /// lanes, exactly as for fail-closed lowering sites. A PROOF stands.
    ///
    /// Mutual recursion (`f -> g -> f`, at any cycle length) is NOT this arm:
    /// the callee is not `self.func.id`, so the historical fail-closed handling
    /// of the other function's summary is unchanged.
    #[allow(clippy::too_many_arguments)]
    /// `Err` names the fence point that refused; the caller records it as the
    /// site's census reason so a miss on a real body is attributable without a
    /// debugger (v7/D3).
    fn try_self_call_inductive_hypothesis(
        &mut self,
        callee_func: &Function,
        callee_func_ty: &trust_ir::FuncTy,
        args: &[ValueId],
        node: &InstrNode,
        block: BlockId,
        instruction_index: usize,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) -> Result<(), &'static str> {
        // (a) arity.
        if callee_func_ty.params.len() != args.len()
            || node.results.len() != callee_func_ty.returns.len()
        {
            return Err("ih_fence:arity");
        }
        // (b) pointer-free scalars only, both directions. `is_precise_stack_scalar_ty`
        // admits an opaque `Ty::Ptr`; the exclusion is explicit and pinned.
        let pointer_free_scalar =
            |ty: &Ty| is_precise_stack_scalar_ty(ty) && !matches!(ty, Ty::Ptr | Ty::FatPtr(_));
        if !callee_func_ty.params.iter().all(pointer_free_scalar)
            || !callee_func_ty.returns.iter().all(pointer_free_scalar)
        {
            return Err("ih_fence:pointer_or_non_scalar_signature");
        }
        // (c) frame-local body.
        if !self_call_body_is_frame_local(callee_func) {
            return Err("ih_fence:body_not_frame_local");
        }
        // (d) entry preconditions over the actuals.
        let Some(entry) = callee_func.block(callee_func.entry) else {
            return Err("ih_fence:entry_block_missing");
        };
        if entry.params.len() != args.len() {
            return Err("ih_fence:entry_param_arity");
        }
        let mut actuals: BTreeMap<ValueId, Expr> = BTreeMap::new();
        for ((param, param_ty), arg) in entry.params.iter().zip(args) {
            actuals.insert(*param, self.resolve(*arg, param_ty));
        }
        let mut reasserted = Vec::new();
        for anode in &entry.body {
            let Inst::Assume { cond } = &anode.inst else { continue };
            match self.reinstantiate_entry_condition(entry, *cond, &actuals, 64) {
                Some((true, expr)) => reasserted.push(expr),
                Some((false, _)) => {}
                None => return Err("ih_fence:entry_assume_unmodeled"),
            }
        }
        // Admitted. (1) the deeper activation's input must satisfy every entry
        // precondition: an error rule per precondition, negated, on this path.
        for pre in reasserted {
            self.add_error_rule(from, path_constraints, pre.not());
        }
        // (2) the inductive hypothesis: fresh results, no error rule.
        self.bind_symbolic_call_results(
            &callee_func.name,
            Some(callee_func_ty.returns.as_slice()),
            node,
        );
        self.record_call_summary_attempt(
            callee_func.id,
            Some(&callee_func.name),
            block,
            instruction_index,
            CallSummaryOutcome::InductiveHypothesis,
        );
        self.inductive_hypothesis_sites.push(TrustIrChcDiagnostic {
            function: self.func.name.clone(),
            block,
            instruction_index,
            family: SemanticsFamily::Calls,
            reason: TrustIrChcUnsupportedReason::RecursiveSelfCallInductiveHypothesis,
            result_values: node.results.clone(),
        });
        Ok(())
    }

    /// Re-evaluate the boolean `value` (an entry-block `Assume` condition) with
    /// the entry parameters replaced by `actuals`. `Some((depends_on_param,
    /// expr))`, or `None` when any parameter-dependent leaf is a shape this
    /// evaluator does not model (fail closed). Only the bridge's precondition
    /// spellings are modeled: `ICmp` over parameters and constants, boolean
    /// `And`/`Or`/`Xor`, the `Select`-spelled connectives, and `Copy`.
    fn reinstantiate_entry_condition(
        &mut self,
        entry: &Block,
        value: ValueId,
        actuals: &BTreeMap<ValueId, Expr>,
        fuel: u32,
    ) -> Option<(bool, Expr)> {
        if let Some(actual) = actuals.get(&value) {
            return Some((true, actual.clone()));
        }
        if fuel == 0 {
            return None;
        }
        let node = entry.body.iter().find(|n| n.results.first() == Some(&value))?;
        match &node.inst {
            // Evaluated from the INSTRUCTION, never from `self.values`: that map
            // is cleared at every block boundary (`translate_block`), and the
            // bridge places a self-call in a non-entry block behind the
            // recursion guard — measured 2026-09-14 on
            // `tests/ui/trust/native_recursive_requires_fresh_context.rs`, where
            // the lookup form missed every entry constant and the fence fell
            // through to the historical error rule. A constant with no exact
            // bit-level encoding stays unmodeled (`None`).
            Inst::Const { ty, value } => {
                if matches!(value, Constant::SymbolAddr { .. }) {
                    return None;
                }
                let expr = const_to_expr(ty, value)?;
                Some((false, expr))
            }
            Inst::Copy { operand, .. } => {
                self.reinstantiate_entry_condition(entry, *operand, actuals, fuel - 1)
            }
            Inst::ICmp { op, ty, lhs, rhs } => {
                let (dl, l) = self.reinstantiate_entry_condition(entry, *lhs, actuals, fuel - 1)?;
                let (dr, r) = self.reinstantiate_entry_condition(entry, *rhs, actuals, fuel - 1)?;
                let expr = self.eval_icmp(*op, ty, &l, &r)?;
                Some((dl || dr, expr))
            }
            Inst::BinOp {
                op: op @ (BinOp::And | BinOp::Or | BinOp::Xor),
                ty: Ty::Bool,
                lhs,
                rhs,
            } => {
                let (dl, l) = self.reinstantiate_entry_condition(entry, *lhs, actuals, fuel - 1)?;
                let (dr, r) = self.reinstantiate_entry_condition(entry, *rhs, actuals, fuel - 1)?;
                let expr = self.eval_binop(*op, &Ty::Bool, &l, &r);
                Some((dl || dr, expr))
            }
            Inst::Select { ty: Ty::Bool, cond, then_val, else_val } => {
                let (dc, c) =
                    self.reinstantiate_entry_condition(entry, *cond, actuals, fuel - 1)?;
                let (dt, t) =
                    self.reinstantiate_entry_condition(entry, *then_val, actuals, fuel - 1)?;
                let (de, e) =
                    self.reinstantiate_entry_condition(entry, *else_val, actuals, fuel - 1)?;
                if !c.sort().is_bool() || !t.sort().is_bool() || !e.sort().is_bool() {
                    return None;
                }
                Some((dc || dt || de, Expr::ite(c, t, e)))
            }
            _ => None,
        }
    }

    /// `element_operand_tys` of the callee `callee_func`, computed on the first
    /// request for it and shared by every later summary of it in this translator
    /// (`callee_operand_tys`): linear in the sum of the distinct callees' sizes.
    fn callee_operand_tys_of(
        &mut self,
        callee_func: &Function,
    ) -> std::rc::Rc<BTreeMap<ValueId, Ty>> {
        let module = self.module;
        let passes = &mut self.work.callee_operand_type_passes;
        self.callee_operand_tys
            .entry(callee_func.id)
            .or_insert_with(|| {
                *passes += 1;
                std::rc::Rc::new(element_operand_tys(callee_func, module))
            })
            .clone()
    }

    fn is_recursive_direct_call(&self, callee: FuncId, callee_func: &Function) -> bool {
        callee == self.func.id
            || callee_func.blocks.iter().flat_map(|block| &block.body).any(
                |node| matches!(&node.inst, Inst::Call { callee, .. } if *callee == self.func.id),
            )
    }

    /// Bounded symbolic interpretation of `callee_func`, folded into the
    /// caller's encoding, or `None` when any construct is not modeled.
    ///
    /// EVERY exit -- each `return None` and each `?` -- records a unique
    /// labelled site into `decline` before returning, so the census can
    /// attribute a decline to the exact line that took it. First writer wins,
    /// so an exit inside `call_summary_successor_state` outranks the `?` that
    /// propagated it. `tests/call_summary_census_labels_every_exit.rs` fails
    /// when a new unlabelled exit appears here.
    fn try_direct_call_summary(
        &mut self,
        callee_func: &Function,
        args: CallSummaryArgs<'_>,
        decline: &DeclineSlot,
        depth: usize,
    ) -> Option<DirectCallSummary> {
        if !self.source_consumption.matches_function(callee_func) {
            decline!(decline, "callee_source_body_mismatch");
        }
        let callee_func_ty = self
            .module
            .func_types
            .get(callee_func.ty.as_usize())
            .or_decline(decline, "callee_func_ty_missing", line!())?
            .clone();
        // Split three ways deliberately. As ONE condition this was the census's
        // second-largest cause and it was a SUM: "the signature is not summary-
        // shaped" cannot tell an argument-count disagreement from a parameter
        // type the interpreter has no carrier for from a RETURN type it has no
        // carrier for, and those want different work.
        if callee_func_ty.params.len() != args.len() {
            decline!(decline, "signature_param_count_mismatch");
        }
        if let Some(ty) = callee_func_ty.params.iter().find(|ty| !self.is_call_summary_value_ty(ty))
        {
            // Carry the REJECTED CARRIER as a detail, on the same reasoning as the
            // `unmodeled_instruction` catch-all: "the interpreter has no carrier for
            // some parameter" reported as one number is a SUM over `&str`, `&[T]`,
            // `&dyn Trait`, `f64` and an over-budget aggregate, and those want
            // different work. First offending parameter wins, matching the
            // first-writer-wins discipline of `DeclineSlot`.
            decline.note_with_detail("signature_param_ty_unsupported", line!(), ty_carrier(ty));
            return None;
        }
        if let Some(ty) =
            callee_func_ty.returns.iter().find(|ty| !self.is_call_summary_value_ty(ty))
        {
            decline.note_with_detail("signature_return_ty_unsupported", line!(), ty_carrier(ty));
            return None;
        }

        let entry_block = callee_func.block(callee_func.entry).or_decline(
            decline,
            "entry_block_missing",
            line!(),
        )?;
        if entry_block.params.len() != args.len() {
            decline!(decline, "entry_block_param_arity");
        }

        let entry_defined: Vec<bool> = match args {
            CallSummaryArgs::Caller(ids) => ids
                .iter()
                .map(|value| {
                    construction_definedness::value_is_defined(
                        &self.source_consumption,
                        self.module,
                        self.func,
                        *value,
                        None,
                    )
                })
                .collect(),
            CallSummaryArgs::Bindings { defined, .. } => {
                if defined.len() != args.len() {
                    decline!(decline, "nested_argument_definedness_arity");
                }
                defined.to_vec()
            }
        };
        let entry_transport: Vec<bool> = match args {
            CallSummaryArgs::Caller(ids) => ids
                .iter()
                .map(|value| {
                    construction_definedness::value_is_transportable(
                        &self.source_consumption,
                        self.module,
                        self.func,
                        *value,
                        None,
                        None,
                    )
                })
                .collect(),
            CallSummaryArgs::Bindings { transport, .. } => {
                if transport.len() != args.len() {
                    decline!(decline, "nested_argument_transport_arity");
                }
                transport.to_vec()
            }
        };
        let invocation_transport_defined = entry_transport.iter().all(|valid| *valid)
            && match args {
                CallSummaryArgs::Caller(_) => true,
                CallSummaryArgs::Bindings { enclosing_transport_defined, .. } => {
                    enclosing_transport_defined
                }
            };
        if !invocation_transport_defined {
            decline!(decline, "entry_argument_transport");
        }
        let reference_inputs = match args {
            CallSummaryArgs::Caller(ids) => {
                self.source_consumption.reference_arguments(self.func, callee_func, ids, None)
            }
            CallSummaryArgs::Bindings { reference_inputs, .. } => {
                if reference_inputs.len() != args.len() {
                    decline!(decline, "nested_argument_reference_arity");
                }
                reference_inputs.to_vec()
            }
        };
        let _reference_scope =
            self.source_consumption.enter_reference_arguments(callee_func.id, reference_inputs);
        let mut locals = BTreeMap::new();
        for (index, (param, param_ty)) in entry_block.params.iter().enumerate() {
            if !self.is_call_summary_value_ty(param_ty) {
                decline!(decline, "entry_param_ty_unsupported");
            }
            let binding = match args {
                // Outermost invocation: the actuals are `ValueId`s in the CALLER's
                // (this translator's) value space.
                CallSummaryArgs::Caller(ids) => {
                    let arg =
                        ids.get(index).or_decline(decline, "caller_argument_missing", line!())?;
                    self.resolve_call_summary_argument(*arg, param_ty).or_decline(
                        decline,
                        "argument_not_resolvable",
                        line!(),
                    )?
                }
                // NESTED invocation: the actuals were already resolved by the
                // enclosing summary. Re-check the CARRIER VARIANT against the
                // declared parameter type — the same bar `call_summary_value`
                // applies — so a wrongly-sorted term can never enter the callee
                // model through the recursion seam.
                CallSummaryArgs::Bindings { values: bindings, .. } => {
                    let binding = bindings.get(index).or_decline(
                        decline,
                        "nested_argument_missing",
                        line!(),
                    )?;
                    if !call_summary_binding_matches_type(param_ty, binding) {
                        decline!(decline, "nested_argument_variant_mismatch");
                    }
                    binding.clone()
                }
            };
            locals.insert(*param, binding);
        }

        // The declared type of every array and index operand of the callee's element
        // accesses, fetched on the callee's first `ExtractElement`: an element read's
        // bounds obligation needs the index's signedness and the array's length
        // (`ExtractElement` arm below). `callee_operand_tys_of` computes it once per
        // callee for this translator, so an attempt that never meets a read does no
        // work for it.
        let mut callee_operand_tys: Option<std::rc::Rc<BTreeMap<ValueId, Ty>>> = None;

        let mut pending = vec![CallSummaryState {
            block: callee_func.entry,
            locals,
            path_conditions: Vec::new(),
            visited_blocks: Vec::new(),
            slots: BTreeMap::new(),
        }];
        let mut returns = Vec::new();
        let mut error_conditions = Vec::new();
        // Rung-2 recursion fixpoint: set when the callee calls ITSELF. A self-recursive callee's
        // single-invocation summary proves panic-freedom for ALL recursion depths ONLY if it
        // carries no per-level obligation (checked after the loop) — see the `Inst::Call` arm.
        let mut self_recursion_seen = false;

        // A depth-0 entry starts a fresh top-level attempt, so it (and only it)
        // resets the budget every nesting level then shares.
        if depth == 0 {
            self.call_summary_states_left = DIRECT_CALL_SUMMARY_TOTAL_STATES;
        }

        let mut processed_states = 0;
        while let Some(mut state) = pending.pop() {
            processed_states += 1;
            self.call_summary_states_left = self.call_summary_states_left.saturating_sub(1);
            if self.call_summary_states_left == 0 {
                decline!(decline, "shared_state_budget_exhausted");
            }
            if processed_states > DIRECT_CALL_SUMMARY_MAX_STATES
                || state.visited_blocks.contains(&state.block)
            {
                decline!(decline, "state_budget_or_block_revisit");
            }
            state.visited_blocks.push(state.block);

            let block = callee_func.block(state.block).or_decline(
                decline,
                "state_block_missing",
                line!(),
            )?;
            let mut terminated = false;
            for node in &block.body {
                if !construction_definedness::consumption_is_valid(
                    &self.source_consumption,
                    self.module,
                    callee_func,
                    node,
                    Some(&entry_defined),
                    Some(&entry_transport),
                ) {
                    if matches!(&node.inst, Inst::Call { .. }) {
                        decline!(decline, "call_argument_transport");
                    } else {
                        decline!(decline, "operand_consumption");
                    }
                }
                match &node.inst {
                    Inst::Const { ty, value } if is_call_summary_scalar_ty(ty) => {
                        // A constant without an exact bit-level encoding
                        // declines the whole summary (fail closed), like every
                        // other unmodeled construct in this interpreter.
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Scalar(const_to_expr(ty, value).or_decline(
                                decline,
                                "const_no_exact_encoding",
                                line!(),
                            )?),
                        )
                        .or_decline(
                            decline,
                            "const_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Const { ty: ty @ Ty::Enum(_), value } => {
                        let aggregate = dataless_enum::constant_tag(self.module, ty, value)
                            .and_then(dataless_enum::binding)
                            .or_decline(decline, "dataless_enum_constant", line!())?;
                        let binding = self
                            .call_summary_binding_from_value(ValueBinding::Aggregate(aggregate), ty)
                            .or_decline(decline, "dataless_enum_constant_binding", line!())?;
                        bind_call_summary_result(&mut state.locals, node, binding).or_decline(
                            decline,
                            "dataless_enum_constant_bind_conflict",
                            line!(),
                        )?;
                    }
                    // A zero-sized constant (`_0 = const ()`, which upstream
                    // 9f6141e78128 puts at the head of every drop shim) has
                    // exactly one inhabitant: the empty aggregate. Bind it
                    // exactly. Any other constant spelling, or a type with a
                    // non-empty field list, falls through to the independently
                    // checked aggregate carrier or declines (fail closed).
                    Inst::Const { ty, value }
                        if matches!(value, Constant::PhantomData)
                            && aggregate_field_tys_of(self.module, ty)
                                .is_some_and(|fields| fields.is_empty()) =>
                    {
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Aggregate(CallSummaryAggregate {
                                fields: Vec::new(),
                            }),
                        )
                        .or_decline(
                            decline,
                            "zst_const_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Const { ty: ty @ (Ty::Struct(_) | Ty::Tuple(_)), value } => {
                        let binding = self
                            .call_summary_constant_carrier(ty, value, true, 0)
                            .or_decline(decline, "aggregate_const_no_exact_carrier", line!())?;
                        bind_call_summary_result(&mut state.locals, node, binding).or_decline(
                            decline,
                            "aggregate_const_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Copy { ty, operand } if self.is_call_summary_value_ty(ty) => {
                        let binding = call_summary_value(&state.locals, *operand, ty).or_decline(
                            decline,
                            "copy_operand_unbound",
                            line!(),
                        )?;
                        bind_call_summary_result(&mut state.locals, node, binding).or_decline(
                            decline,
                            "copy_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::BinOp { op, ty, lhs, rhs } if ty.is_integer() => {
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs).or_decline(
                            decline,
                            "int_binop_lhs_unbound",
                            line!(),
                        )?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs).or_decline(
                            decline,
                            "int_binop_rhs_unbound",
                            line!(),
                        )?;
                        if let Some(no_overflow) = integer_binop_overflow_obligation(
                            *op,
                            ty,
                            &lhs_expr,
                            &rhs_expr,
                            node,
                            self.options,
                        ) {
                            error_conditions.push(call_summary_guarded_condition(
                                &state.path_conditions,
                                no_overflow.not(),
                            ));
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
                            CallSummaryBinding::Scalar(result),
                        )
                        .or_decline(
                            decline,
                            "int_binop_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::BinOp { op, ty, lhs, rhs } if matches!(ty, Ty::Bool) => {
                        // Logical And/Or/Xor on `Bool` carry no overflow/div-by-zero
                        // obligation; `eval_binop` models the connective precisely (as
                        // the main translate does), so a guard conjunction such as
                        // `x == i32::MIN && y == -1` (the signed-division overflow guard)
                        // threads through the summary instead of falling past the
                        // integer-only arm above to `_ => return None`.
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs).or_decline(
                            decline,
                            "bool_binop_lhs_unbound",
                            line!(),
                        )?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs).or_decline(
                            decline,
                            "bool_binop_rhs_unbound",
                            line!(),
                        )?;
                        let result = self.eval_binop(*op, ty, &lhs_expr, &rhs_expr);
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Scalar(result),
                        )
                        .or_decline(
                            decline,
                            "bool_binop_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::ICmp { op, ty, lhs, rhs } => {
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs).or_decline(
                            decline,
                            "icmp_lhs_unbound",
                            line!(),
                        )?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs).or_decline(
                            decline,
                            "icmp_rhs_unbound",
                            line!(),
                        )?;
                        let result = self.eval_icmp(*op, ty, &lhs_expr, &rhs_expr).or_decline(
                            decline,
                            "icmp_unsupported_comparison",
                            line!(),
                        )?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Scalar(result),
                        )
                        .or_decline(
                            decline,
                            "icmp_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Cast { op, src_ty, dst_ty, operand }
                        if is_call_summary_scalar_ty(src_ty)
                            && is_call_summary_scalar_ty(dst_ty) =>
                    {
                        let operand = call_summary_scalar(&state.locals, *operand).or_decline(
                            decline,
                            "cast_operand_unbound",
                            line!(),
                        )?;
                        let result = eval_cast_expr(*op, src_ty, dst_ty, operand).or_decline(
                            decline,
                            "cast_unsupported",
                            line!(),
                        )?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Scalar(result),
                        )
                        .or_decline(
                            decline,
                            "cast_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Select { ty: ty @ Ty::Enum(_), cond, then_val, else_val } => {
                        let cond = call_summary_bool(&state.locals, *cond).or_decline(
                            decline,
                            "enum_select_condition",
                            line!(),
                        )?;
                        let then_value = call_summary_value(&state.locals, *then_val, ty)
                            .or_decline(decline, "enum_select_then_unbound", line!())?;
                        let else_value = call_summary_value(&state.locals, *else_val, ty)
                            .or_decline(decline, "enum_select_else_unbound", line!())?;
                        if construction_definedness::contains_opaque(&then_value)
                            || construction_definedness::contains_opaque(&else_value)
                        {
                            decline!(decline, "enum_select_opaque_arm");
                        }
                        let then_value = self.materialize_call_summary_binding(then_value);
                        let else_value = self.materialize_call_summary_binding(else_value);
                        let selected = dataless_enum::select_binding(
                            self.module,
                            ty,
                            &cond,
                            &then_value,
                            &else_value,
                        )
                        .or_decline(
                            decline,
                            "enum_select_carrier",
                            line!(),
                        )?;
                        let selected = self
                            .call_summary_binding_from_value(ValueBinding::Aggregate(selected), ty)
                            .or_decline(decline, "enum_select_summary_carrier", line!())?;
                        bind_call_summary_result(&mut state.locals, node, selected).or_decline(
                            decline,
                            "enum_select_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Select { ty, cond, then_val, else_val }
                        if is_call_summary_scalar_ty(ty) =>
                    {
                        let cond_expr = call_summary_bool(&state.locals, *cond).or_decline(
                            decline,
                            "select_cond_not_bool",
                            line!(),
                        )?;
                        // Decline the summary when malformed TrustIR gives either arm
                        // an incompatible carrier. The caller then takes the existing
                        // fail-closed UnsupportedDirectCallSummary path.
                        let then_expr = normalize_expr_to_exact_ty(
                            &call_summary_scalar(&state.locals, *then_val).or_decline(
                                decline,
                                "select_then_unbound",
                                line!(),
                            )?,
                            ty,
                        )
                        .or_decline(
                            decline,
                            "select_then_carrier_mismatch",
                            line!(),
                        )?;
                        let else_expr = normalize_expr_to_exact_ty(
                            &call_summary_scalar(&state.locals, *else_val).or_decline(
                                decline,
                                "select_else_unbound",
                                line!(),
                            )?,
                            ty,
                        )
                        .or_decline(
                            decline,
                            "select_else_carrier_mismatch",
                            line!(),
                        )?;
                        let selected = Expr::try_ite(cond_expr, then_expr, else_expr)
                            .ok()
                            .or_decline(decline, "select_ite_ill_sorted", line!())?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Scalar(selected),
                        )
                        .or_decline(
                            decline,
                            "select_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::NullPtr => {
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Scalar(Expr::bitvec_const(0u64, 64)),
                        )
                        .or_decline(
                            decline,
                            "nullptr_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Undef { ty } if self.is_call_summary_value_ty(ty) => {
                        let result = self
                            .fresh_direct_call_summary_value("call_undef", ty)
                            .or_decline(decline, "undef_fresh_value_failed", line!())?;
                        bind_call_summary_result(&mut state.locals, node, result).or_decline(
                            decline,
                            "undef_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::DialectOp(op) if node.results.len() == 1 && is_thread_local_addr(op) => {
                        let result = self
                            .fresh_direct_call_summary_value("call_thread_local_addr", &Ty::Ptr)
                            .or_decline(decline, "thread_local_addr_fresh_failed", line!())?;
                        bind_call_summary_result(&mut state.locals, node, result).or_decline(
                            decline,
                            "thread_local_addr_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::ExtractField { ty, aggregate, field }
                        if self.is_call_summary_value_ty(ty) =>
                    {
                        // Trust (#46): a nested-aggregate field is read as its OWN nested
                        // binding. `CallSummaryBinding` already carries aggregates, so the field
                        // is taken whatever its shape; what must still hold is that the
                        // binding VARIANT matches the declared result type — the same bar
                        // `call_summary_value` applies on the `Inst::Copy` arm. A mismatch
                        // declines the whole summary (fail closed) rather than admitting a
                        // wrongly-sorted term into the callee model.
                        let result = call_summary_aggregate(&state.locals, *aggregate)
                            .or_decline(decline, "extract_field_aggregate_unbound", line!())?
                            .fields
                            .get(*field as usize)
                            .or_decline(decline, "extract_field_index_out_of_range", line!())?
                            .clone();
                        if !call_summary_binding_matches_type(ty, &result) {
                            decline!(decline, "extract_field_binding_variant_mismatch");
                        }
                        bind_call_summary_result(&mut state.locals, node, result).or_decline(
                            decline,
                            "extract_field_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::ExtractElement { ty, array, index } if is_call_summary_scalar_ty(ty) => {
                        // An element READ carries its OWN in-bounds obligation, exactly
                        // as `translate_extract_element` states it for a block of the
                        // translated function: an out-of-bounds index is trust-ir
                        // undefined behaviour however the producer guarded it, and the
                        // summary's error conditions are the ONLY record of the callee's
                        // obligations at the call site. (This arm used to read a fresh
                        // value with no rule, relying on a separately emitted `Assert`
                        // no validator requires — an out-of-bounds read in a summarized
                        // callee then left the caller's CHC safe. Decision TMC-1 admits
                        // array reads at the proof-authority gate, whose walk covers
                        // every summarized callee, so this is load-bearing there.)
                        //
                        // The length is the array operand's declared one (a fixed-size
                        // array's or a vector's), else its carried binding's; the index
                        // is read by its declared signedness (`lane_access_of`). Any of
                        // those unknown, or a sequence (no static length), declines the
                        // summary: the caller then takes the fail-closed
                        // `UnsupportedDirectCallSummary` path.
                        let operand_tys = callee_operand_tys
                            .get_or_insert_with(|| self.callee_operand_tys_of(callee_func))
                            .clone();
                        let len = match (operand_tys.get(array), state.locals.get(array)) {
                            (Some(Ty::Array(_, len)), _) => *len,
                            (Some(Ty::Vector(_, lanes)), _) => u64::from(*lanes),
                            (None, Some(CallSummaryBinding::Array(carried))) => carried.len,
                            _ => decline!(decline, "extract_element_length_unknown"),
                        };
                        let signed = operand_tys
                            .get(index)
                            .filter(|index_ty| index_ty.is_integer())
                            .map(Ty::is_signed)
                            .or_decline(decline, "extract_element_index_type_unknown", line!())?;
                        let index_expr = call_summary_scalar(&state.locals, *index).or_decline(
                            decline,
                            "extract_element_index_unbound",
                            line!(),
                        )?;
                        let access = lane_access_of(index_expr, Some(signed), len).or_decline(
                            decline,
                            "extract_element_index_not_bitvec",
                            line!(),
                        )?;
                        // The lane's value: the exact `select` on a carried scalar-
                        // element array whose sort is EXACTLY the result's — the bar
                        // `translate_extract_element` sets (`binding_matches_ty_at`),
                        // never a width-normalized one — else a fresh value (a
                        // translation havoc: sound for a proof, and no refutation gate
                        // grounds it). Where the lanes are not carried at all (the
                        // caller's call site is in a block a cycle reaches, where it
                        // carries arrays shape-only) the proof-authority gate has
                        // already refused the call (`ProofGradeElementReads::
                        // call_rejection`).
                        let selected = match state.locals.get(array) {
                            Some(CallSummaryBinding::Array(CallSummaryArray {
                                lanes: Some(lanes),
                                ..
                            })) => match lanes.as_ref() {
                                CallSummaryBinding::Scalar(column) => {
                                    column.clone().try_select(access.lane.clone()).ok().filter(
                                        |element| {
                                            binding_matches_ty_at(
                                                self.module,
                                                &ValueBinding::Scalar(element.clone()),
                                                ty,
                                                0,
                                            )
                                        },
                                    )
                                }
                                _ => None,
                            },
                            _ => None,
                        };
                        let element = match selected {
                            Some(element) => element,
                            None => self.fresh_symbolic("call_element_read", ty),
                        };
                        // The obligation. With memory checks on it is recorded and the
                        // path is NOT narrowed by the in-bounds condition: every later
                        // condition of an out-of-bounds path is satisfiable only on
                        // executions that already satisfy this read's own (weaker-
                        // guarded) error condition, so "is error reachable" — and the
                        // set of inputs that reach it — is the same either way, and
                        // pushing the condition would copy one more conjunct into
                        // every later obligation of the path (quadratic in the reads
                        // of a callee block; `call_summary_guarded_condition` builds a
                        // flat conjunction). The value read on such a path is a junk
                        // lane nothing can observe without the read's error firing
                        // first. The integer arms above treat their overflow and
                        // division obligations the same way.
                        //
                        // With memory checks OFF there is no rule, as in
                        // `discharge_element_bounds`, and the value outside the bounds
                        // is a fresh one: an unchecked out-of-bounds read never reads a
                        // modeled lane.
                        let value = if self.options.check_memory_bounds {
                            match access.in_bounds {
                                InBounds::Always => {}
                                InBounds::Never => {
                                    error_conditions.push(call_summary_guarded_condition(
                                        &state.path_conditions,
                                        Expr::true_(),
                                    ))
                                }
                                InBounds::When(in_bounds) => {
                                    error_conditions.push(call_summary_guarded_condition(
                                        &state.path_conditions,
                                        in_bounds.not(),
                                    ))
                                }
                            }
                            element
                        } else {
                            match access.in_bounds {
                                InBounds::Always => element,
                                InBounds::Never => self.fresh_symbolic("call_element_read_oob", ty),
                                InBounds::When(in_bounds) => {
                                    let havoc = self.fresh_symbolic("call_element_read_oob", ty);
                                    Expr::try_ite(in_bounds, element, havoc).ok().or_decline(
                                        decline,
                                        "extract_element_unchecked_ite",
                                        line!(),
                                    )?
                                }
                            }
                        };
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Scalar(value),
                        )
                        .or_decline(
                            decline,
                            "extract_element_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::MakeAggregate { ty: ty @ Ty::Enum(_), variant, fields } => {
                        let aggregate =
                            dataless_enum::variant_tag(self.module, ty, *variant, fields)
                                .and_then(dataless_enum::binding)
                                .or_decline(decline, "dataless_enum_constructor", line!())?;
                        let binding = self
                            .call_summary_binding_from_value(ValueBinding::Aggregate(aggregate), ty)
                            .or_decline(decline, "dataless_enum_constructor_binding", line!())?;
                        bind_call_summary_result(&mut state.locals, node, binding).or_decline(
                            decline,
                            "dataless_enum_constructor_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::MakeAggregate { ty, variant, fields }
                        if self.aggregate_field_tys(ty).is_some() =>
                    {
                        let field_tys = self.aggregate_field_tys(ty).or_decline(
                            decline,
                            "make_aggregate_field_tys_missing",
                            line!(),
                        )?;
                        if !matches!(ty, Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, 0))
                            || variant.is_some()
                            || fields.len() != field_tys.len()
                        {
                            decline!(decline, "make_aggregate_shape_mismatch");
                        }
                        if !construction_definedness::supported_type(self.module, ty) {
                            decline!(decline, "make_aggregate_opaque_field_type");
                        }
                        if !invocation_transport_defined {
                            decline!(decline, "make_aggregate_argument_transport_definedness");
                        }
                        let mut result = Vec::with_capacity(fields.len());
                        for (field, field_ty) in fields.iter().zip(&field_tys) {
                            if !construction_definedness::value_is_defined(
                                &self.source_consumption,
                                self.module,
                                callee_func,
                                *field,
                                Some(&entry_defined),
                            ) {
                                decline!(decline, "make_aggregate_operand_definedness");
                            }
                            let binding = call_summary_value(&state.locals, *field, field_ty)
                                .or_decline(decline, "make_aggregate_field_unbound", line!())?;
                            // A field must carry its exact existing value, never
                            // materialize an opaque token into a fresh fact.
                            if construction_definedness::contains_opaque(&binding) {
                                decline!(decline, "make_aggregate_opaque_field");
                            }
                            let binding = self.materialize_call_summary_binding(binding);
                            let binding = match binding {
                                ValueBinding::Scalar(expr) => ValueBinding::Scalar(
                                    normalize_expr_to_exact_ty(&expr, field_ty).or_decline(
                                        decline,
                                        "make_aggregate_field_sort_mismatch",
                                        line!(),
                                    )?,
                                ),
                                composite => composite,
                            };
                            if !binding_matches_ty_at(self.module, &binding, field_ty, 0) {
                                decline!(decline, "make_aggregate_field_shape_mismatch");
                            }
                            result.push(
                                self.call_summary_binding_from_value(binding, field_ty)
                                    .or_decline(
                                        decline,
                                        "make_aggregate_field_binding_mismatch",
                                        line!(),
                                    )?,
                            );
                        }
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Aggregate(CallSummaryAggregate { fields: result }),
                        )
                        .or_decline(
                            decline,
                            "make_aggregate_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::InsertField { ty, aggregate, field, value }
                        if self.aggregate_field_tys(ty).is_some() =>
                    {
                        let field_tys = self.aggregate_field_tys(ty).or_decline(
                            decline,
                            "insert_field_field_tys_missing",
                            line!(),
                        )?;
                        let field_index = *field as usize;
                        let value_ty = field_tys.get(field_index).or_decline(
                            decline,
                            "insert_field_index_out_of_range",
                            line!(),
                        )?;
                        let mut result = call_summary_aggregate(&state.locals, *aggregate)
                            .or_decline(decline, "insert_field_aggregate_unbound", line!())?;
                        if result.fields.len() != field_tys.len() {
                            decline!(decline, "insert_field_aggregate_arity_mismatch");
                        }
                        // Trust (#46): a nested-aggregate field VALUE is spliced as its own
                        // nested binding, so an ordinary wrapper/newtype constructor no
                        // longer bails on its first non-scalar field. `call_summary_value`
                        // matches the binding variant to the declared field type and
                        // returns `None` otherwise, so every shape it cannot represent
                        // still declines the summary (fail closed) — this widens what is
                        // ATTEMPTED, never what is trusted.
                        result.fields[field_index] =
                            call_summary_value(&state.locals, *value, value_ty).or_decline(
                                decline,
                                "insert_field_value_variant_mismatch",
                                line!(),
                            )?;
                        bind_call_summary_result(
                            &mut state.locals,
                            node,
                            CallSummaryBinding::Aggregate(result),
                        )
                        .or_decline(
                            decline,
                            "insert_field_bind_conflict",
                            line!(),
                        )?;
                    }
                    Inst::Assert { cond, kind: _, site: _ } => {
                        error_conditions.push(call_summary_guarded_condition(
                            &state.path_conditions,
                            call_summary_bool(&state.locals, *cond)
                                .or_decline(decline, "assert_cond_not_bool", line!())?
                                .not(),
                        ));
                    }
                    Inst::Br { target, args } => {
                        pending.push(
                            self.call_summary_successor_state(
                                callee_func,
                                &state,
                                *target,
                                args,
                                None,
                                decline,
                            )
                            .or_decline(
                                decline,
                                "br_successor_state",
                                line!(),
                            )?,
                        );
                        terminated = true;
                        break;
                    }
                    Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                        let cond_expr = call_summary_bool(&state.locals, *cond).or_decline(
                            decline,
                            "condbr_cond_not_bool",
                            line!(),
                        )?;
                        pending.push(
                            self.call_summary_successor_state(
                                callee_func,
                                &state,
                                *else_target,
                                else_args,
                                Some(cond_expr.clone().not()),
                                decline,
                            )
                            .or_decline(
                                decline,
                                "condbr_else_successor_state",
                                line!(),
                            )?,
                        );
                        pending.push(
                            self.call_summary_successor_state(
                                callee_func,
                                &state,
                                *then_target,
                                then_args,
                                Some(cond_expr),
                                decline,
                            )
                            .or_decline(
                                decline,
                                "condbr_then_successor_state",
                                line!(),
                            )?,
                        );
                        terminated = true;
                        break;
                    }
                    Inst::Return { values } => {
                        if values.len() != callee_func_ty.returns.len() {
                            decline!(decline, "return_arity_mismatch");
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
                                None => self
                                    .fresh_direct_call_summary_value("call_ret_havoc", ty)
                                    .or_decline(decline, "return_havoc_unsupported_ty", line!())?,
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
                    // Exhaustive over `UnOp` (no wildcard): a new trust-ir variant is
                    // a compile error here until the summary interpreter decides
                    // whether it is total, trapping, or unmodeled.
                    Inst::UnOp { op, ty, operand } => {
                        match op {
                            // SIGNED integer negation `-x` (e.g. `signed_min`'s
                            // `-(1i128 << (width-1))`), modeled precisely: result =
                            // `bvneg(x)`, and the OverflowNeg obligation (`-x` overflows
                            // iff `x == INT_MIN`) is recorded as a guarded error —
                            // redundant if the lowering also emits a separate
                            // neg-overflow `Assert`, sound if it does not (it never masks
                            // a real neg overflow; an unguarded `-(i128::MIN)` stays
                            // SAT/refutable). For a guarded operand (`1 << (width-1)`
                            // under `width <= 127`, always `< 2^(w-1)`) it is UNSAT, so
                            // the inlined negation discharges and the caller proves
                            // panic-free. A `Wrapping` negation carries no obligation
                            // (matches the `BinOp` arm).
                            UnOp::Neg if ty.is_integer() => {
                                let operand_expr = normalize_expr_to_ty(
                                    &call_summary_scalar(&state.locals, *operand).or_decline(
                                        decline,
                                        "neg_operand_unbound",
                                        line!(),
                                    )?,
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
                                        let width = operand_expr
                                            .sort()
                                            .bitvec_width()
                                            .unwrap_or(HOST_POINTER_BITS);
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
                                    CallSummaryBinding::Scalar(operand_expr.bvneg()),
                                )
                                .or_decline(
                                    decline,
                                    "neg_bind_conflict",
                                    line!(),
                                )?;
                            }
                            // Bitwise / logical NOT (`!x`) is TOTAL and modeled PRECISELY
                            // — a Bool operand negates (`not`), a BitVec operand
                            // bit-complements (`bvnot`), matching the main translate's
                            // precise handling. Precision here is load-bearing:
                            // `xor_accumulate_parity`'s body lowers `a ^ true` to
                            // `Select(true, !a, a)`, so a HAVOCED `!a` made the
                            // summarized result — and every loop cell it updates —
                            // unconstrained, blocking the count-parity loop invariant.
                            // `not`/`bvnot` never panic, so NO error condition is pushed.
                            UnOp::Not if is_call_summary_scalar_ty(ty) => {
                                let operand_expr = call_summary_scalar(&state.locals, *operand)
                                    .or_decline(decline, "not_operand_unbound", line!())?;
                                let result = if operand_expr.sort().is_bool() {
                                    operand_expr.not()
                                } else if operand_expr.sort().is_bitvec() {
                                    operand_expr.bvnot()
                                } else {
                                    decline!(decline, "not_operand_ill_sorted");
                                };
                                bind_call_summary_result(
                                    &mut state.locals,
                                    node,
                                    CallSummaryBinding::Scalar(result),
                                )
                                .or_decline(
                                    decline,
                                    "not_bind_conflict",
                                    line!(),
                                )?;
                            }
                            // The remaining UNARY ops are TOTAL — population count
                            // `CtPop`, the IEEE float unary ops (`FNeg`/`FAbs`/`FSqrt`/
                            // `FFloor`/`FCeil`/`FTrunc`), and the WS3.20 bit intrinsics
                            // (trust-ir defines `CtLz`/`CtTz` as TOTAL, `ctlz 0 = cttz 0 =
                            // width`, and `BSwap`/`BitReverse` as total permutations of the
                            // bits) — and NEVER panic (no overflow obligation, unlike the
                            // signed `Neg` above), but have no precise scalar model here.
                            // The result is a fresh-symbolic value (sound
                            // over-approximation: a downstream use stays `unknown`, never
                            // falsely proved) and NO error condition is pushed, so the
                            // summary CONTINUES instead of declining the whole callee
                            // (which would model the call as may-panic — a precision loss
                            // with no soundness justification). The main translator still
                            // fails them closed.
                            UnOp::CtPop
                            | UnOp::CtLz
                            | UnOp::CtTz
                            | UnOp::BSwap
                            | UnOp::BitReverse
                            | UnOp::FNeg
                            | UnOp::FAbs
                            | UnOp::FSqrt
                            | UnOp::FFloor
                            | UnOp::FCeil
                            | UnOp::FTrunc
                                if is_call_summary_scalar_ty(ty) =>
                            {
                                // Resolve the operand to confirm it is in scope on this
                                // path (a missing operand means a malformed CFG — decline,
                                // like the arms above). The resolved value is unused: the
                                // result is havoc, never panics.
                                let _ = call_summary_scalar(&state.locals, *operand).or_decline(
                                    decline,
                                    "total_unop_operand_unbound",
                                    line!(),
                                )?;
                                let result = self
                                    .fresh_direct_call_summary_value("call_unop_total", ty)
                                    .or_decline(decline, "total_unop_fresh_failed", line!())?;
                                bind_call_summary_result(&mut state.locals, node, result)
                                    .or_decline(decline, "total_unop_bind_conflict", line!())?;
                            }
                            // Every op on an operand type the arms above do not take
                            // (`Neg` on a non-integer, a non-scalar operand) is not
                            // modeled — decline under its own census tag (these exits
                            // used to reach the anonymous catch-all below).
                            UnOp::Neg
                            | UnOp::Not
                            | UnOp::CtPop
                            | UnOp::CtLz
                            | UnOp::CtTz
                            | UnOp::BSwap
                            | UnOp::BitReverse
                            | UnOp::FNeg
                            | UnOp::FAbs
                            | UnOp::FSqrt
                            | UnOp::FFloor
                            | UnOp::FCeil
                            | UnOp::FTrunc => decline!(decline, "unop_operand_ty_unmodeled"),
                        }
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
                        let lhs_expr = call_summary_scalar(&state.locals, *lhs).or_decline(
                            decline,
                            "overflow_lhs_unbound",
                            line!(),
                        )?;
                        let rhs_expr = call_summary_scalar(&state.locals, *rhs).or_decline(
                            decline,
                            "overflow_rhs_unbound",
                            line!(),
                        )?;
                        let no_overflow = integer_binop_no_overflow_condition(
                            binop,
                            ty,
                            &lhs_expr,
                            &rhs_expr,
                            self.options,
                        )
                        .or_decline(
                            decline,
                            "overflow_no_semantics",
                            line!(),
                        )?;
                        let value = self.eval_binop(binop, ty, &lhs_expr, &rhs_expr);
                        let flag = no_overflow.not();
                        let mut results = node.results.iter();
                        if let Some(value_result) = results.next() {
                            state.locals.insert(*value_result, CallSummaryBinding::Scalar(value));
                        }
                        if let Some(flag_result) = results.next() {
                            state.locals.insert(*flag_result, CallSummaryBinding::Scalar(flag));
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
                            decline!(decline, "self_recursive_result_arity");
                        }
                        for (result, ty) in node.results.iter().zip(callee_func_ty.returns.iter()) {
                            if !self.is_call_summary_value_ty(ty) {
                                decline!(decline, "self_recursive_result_ty_unsupported");
                            }
                            let havoc =
                                self.fresh_direct_call_summary_value("call_self_rec", ty)
                                    .or_decline(decline, "self_recursive_havoc_failed", line!())?;
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
                        let result = self
                            .fresh_direct_call_summary_value("call_load", ty)
                            .or_decline(decline, "valid_borrow_load_fresh_failed", line!())?;
                        bind_call_summary_result(&mut state.locals, node, result).or_decline(
                            decline,
                            "valid_borrow_load_bind_conflict",
                            line!(),
                        )?;
                    }
                    // ------------------------------------------------------------------
                    // THE RETURN-SLOT SHAPE. Everything from here to the nested `Call`
                    // arm exists to interpret ONE lowering idiom that `core`'s `Option`
                    // combinators are compiled into and that nothing above could cross:
                    //
                    //     %slot = Alloca<T>            ; the return place
                    //     Assume(discr == 0 || discr == 1)
                    //     Switch discr { 0 => none_arm, 1 => some_arm, default => bb_unreachable }
                    //     some_arm: %r = Call closure(...); Store<T> %slot, %r; Br join
                    //     none_arm: Store<T> %slot, None;                       Br join
                    //     join:    %out = Load<T> %slot; Return %out
                    //
                    // Before this, the interpreter met `Alloca` at its catch-all and
                    // declined, so EVERY caller of `Option::and_then` / `is_some_and` /
                    // `map` / `map_or` fell back to `translate_call`'s unconditional
                    // may-panic error rule (`UnsupportedDirectCallSummary`) and stayed
                    // UNKNOWN — measured on a3d-kernel: 12 of 12 unknown rows, all of them
                    // functions that pass a closure to a `core` `Option` combinator, and
                    // every one attributed by `call-summary-census` to
                    // `unmodeled_instruction/Alloca` (31 sites) or `.../Assume` (6 sites).
                    // ------------------------------------------------------------------

                    // A single-cell stack slot. ADMITTED ONLY when the alloca's address
                    // provably never leaves the `ptr` operand of a non-volatile
                    // `Load`/`Store` in this body (`call_summary_slot_is_directly_addressed`)
                    // AND every such access names the cell's own type
                    // (`stack_alloca_cell_accesses_match_type`).
                    //
                    // SOUNDNESS. The false proof this shape can mint is a DROPPED WRITE:
                    // if a store can reach the cell through an alias the model does not
                    // see, the later load returns the PRE-store value and the caller
                    // proves something about a value the program never holds. Both halves
                    // of the admission close that: with no `GEP`/`Borrow` derivation, no
                    // call argument, no stored VALUE, no block argument and no return
                    // carrying the address, the ONLY writer is a direct `Store` whose
                    // `ptr` is this exact SSA id — which the `Inst::Store` arm below
                    // models; and with every access at the cell type, no
                    // differently-typed store can be silently dropped. Anything else
                    // declines the whole summary, exactly as before this arm existed.
                    // (`count: Some(_)` — a VLA — has no single cell and is left to the
                    // catch-all.)
                    Inst::Alloca { ty, count: None, .. }
                        if self.is_call_summary_value_ty(ty) && node.results.len() == 1 =>
                    {
                        let result = *node.results.first().or_decline(
                            decline,
                            "alloca_result_missing",
                            line!(),
                        )?;
                        if !call_summary_slot_is_directly_addressed(callee_func, result) {
                            decline!(decline, "alloca_address_not_slot_confined");
                        }
                        if !stack_alloca_cell_accesses_match_type(callee_func, result, ty) {
                            decline!(decline, "alloca_access_ty_mismatch");
                        }
                        // The POINTER itself is modeled opaquely (a fresh `Ptr` symbol),
                        // so an incidental copy still type-checks; the CELL is tracked
                        // separately, keyed by this SSA id.
                        let ptr =
                            CallSummaryBinding::Scalar(self.fresh_symbolic("call_slot", &Ty::Ptr));
                        bind_call_summary_result(&mut state.locals, node, ptr).or_decline(
                            decline,
                            "alloca_bind_conflict",
                            line!(),
                        )?;
                        state.slots.insert(result, CallSummarySlot { ty: ty.clone(), value: None });
                    }

                    // Write a tracked slot. Anything else — an untracked pointer, a
                    // volatile access, a type the cell does not have, a value with no
                    // binding on this path — declines. In particular a store through a
                    // pointer this interpreter cannot attribute is NOT dropped: dropping
                    // it is precisely the stale-read false proof described above.
                    Inst::Store { ty, ptr, value, volatile, .. } if !*volatile => {
                        let binding = call_summary_value(&state.locals, *value, ty).or_decline(
                            decline,
                            "store_value_unbound",
                            line!(),
                        )?;
                        let slot = state.slots.get_mut(ptr).or_decline(
                            decline,
                            "store_target_not_tracked_slot",
                            line!(),
                        )?;
                        if slot.ty != *ty {
                            decline!(decline, "store_cell_ty_mismatch");
                        }
                        slot.value = Some(binding);
                    }

                    // Read a tracked slot. An UNWRITTEN cell reads as a fresh
                    // unconstrained value (havoc ⊇ any real content — it can only leave a
                    // dependent obligation unknown, never falsely proved); it must NEVER
                    // read as a zero/default, which would be a fabricated fact.
                    Inst::Load { ty, ptr, volatile, .. }
                        if !*volatile && state.slots.contains_key(ptr) =>
                    {
                        let slot = state
                            .slots
                            .get(ptr)
                            .or_decline(decline, "load_slot_missing", line!())?
                            .clone();
                        if slot.ty != *ty {
                            decline!(decline, "load_cell_ty_mismatch");
                        }
                        let binding = match slot.value {
                            Some(binding) => binding,
                            None => self
                                .fresh_direct_call_summary_value("call_slot_uninit", ty)
                                .or_decline(decline, "load_uninit_havoc_failed", line!())?,
                        };
                        if !call_summary_binding_matches_type(ty, &binding) {
                            decline!(decline, "load_binding_variant_mismatch");
                        }
                        bind_call_summary_result(&mut state.locals, node, binding).or_decline(
                            decline,
                            "load_bind_conflict",
                            line!(),
                        )?;
                    }

                    // A compiler-inserted fact about this path (the enum-validity
                    // `discr ∈ {0,1}` that precedes every `Option`/`Result` switch).
                    // Modeled EXACTLY as `translate_block`'s `Inst::Assume` arm models it
                    // — pushed onto the path conditions — so folding a body into a caller
                    // grants it no trust that translating the same body directly would
                    // not already grant. Omitting it would be conservative, not unsound:
                    // the unconstrained discriminant would make the switch's default edge
                    // (an `Unreachable`, i.e. an error condition) SATISFIABLE and the
                    // caller would refute rather than prove.
                    Inst::Assume { cond } => {
                        let cond_expr = call_summary_bool(&state.locals, *cond).or_decline(
                            decline,
                            "assume_cond_not_bool",
                            line!(),
                        )?;
                        state.path_conditions.push(cond_expr);
                    }

                    // Multi-way branch. The case split is COMPLETE and DISJOINT — one
                    // successor per case guarded by `selector == case`, plus the default
                    // guarded by the conjunction of their negations — which is exactly
                    // `translate_switch`'s encoding, and is precise rather than assumed.
                    //
                    // `exhaustive_enum_unreachable` is DELIBERATELY IGNORED. Using it to
                    // prune the default edge would ASSUME the discriminant is in range;
                    // instead the default edge is explored, reaches the `Unreachable`
                    // block, and contributes its guarded error condition. That condition
                    // is UNSAT exactly when a preceding `Assume` (or the incoming value)
                    // already established the range — so the flag is never load-bearing
                    // and a lowering that emitted it wrongly cannot launder a panic.
                    Inst::Switch { value, default, default_args, cases, .. } => {
                        let selector = call_summary_scalar(&state.locals, *value).or_decline(
                            decline,
                            "switch_selector_unbound",
                            line!(),
                        )?;
                        let mut case_guards = Vec::with_capacity(cases.len());
                        for case in cases {
                            let case_expr = switch_case_expr(&case.value, &selector).or_decline(
                                decline,
                                "switch_case_not_encodable",
                                line!(),
                            )?;
                            let guard = selector.clone().eq(case_expr);
                            case_guards.push(guard.clone());
                            pending.push(
                                self.call_summary_successor_state(
                                    callee_func,
                                    &state,
                                    case.target,
                                    &case.args,
                                    Some(guard),
                                    decline,
                                )
                                .or_decline(
                                    decline,
                                    "switch_case_successor_state",
                                    line!(),
                                )?,
                            );
                        }
                        let default_guard = match case_guards.len() {
                            0 => None,
                            1 => Some(case_guards[0].clone().not()),
                            _ => Some(Expr::and_many(
                                case_guards.into_iter().map(Expr::not).collect(),
                            )),
                        };
                        pending.push(
                            self.call_summary_successor_state(
                                callee_func,
                                &state,
                                *default,
                                default_args,
                                default_guard,
                                decline,
                            )
                            .or_decline(
                                decline,
                                "switch_default_successor_state",
                                line!(),
                            )?,
                        );
                        terminated = true;
                        break;
                    }

                    // A call to a DIFFERENT function whose body this module already
                    // holds — the combinator wrapper invoking the user's closure.
                    // Summarize it RECURSIVELY and fold the result in:
                    //   * every error condition it reports is re-guarded by THIS path's
                    //     conditions and kept, so a panic inside the closure still
                    //     reaches the caller's error relation (this is what makes an
                    //     adversarial closure refute rather than prove);
                    //   * its combined return values bind this call's results.
                    // Declining anywhere inside the nested attempt declines the whole
                    // outer summary — the existing fail-closed behaviour, unchanged.
                    Inst::Call { callee, args: call_args }
                        if *callee != callee_func.id
                            && *callee != self.func.id
                            && depth < DIRECT_CALL_SUMMARY_MAX_DEPTH =>
                    {
                        let nested_func = self.module.function_by_id(*callee).cloned().or_decline(
                            decline,
                            "nested_callee_not_in_module",
                            line!(),
                        )?;
                        let nested_func_ty = self
                            .module
                            .func_types
                            .get(nested_func.ty.as_usize())
                            .cloned()
                            .or_decline(decline, "nested_callee_func_ty_missing", line!())?;
                        if nested_func_ty.params.len() != call_args.len() {
                            decline!(decline, "nested_call_arg_arity");
                        }
                        if node.results.len() != nested_func_ty.returns.len() {
                            decline!(decline, "nested_call_result_arity");
                        }
                        let mut arg_bindings = Vec::with_capacity(call_args.len());
                        for (arg, param_ty) in call_args.iter().zip(nested_func_ty.params.iter()) {
                            arg_bindings.push(
                                call_summary_value(&state.locals, *arg, param_ty).or_decline(
                                    decline,
                                    "nested_call_arg_unbound",
                                    line!(),
                                )?,
                            );
                        }
                        let arg_defined: Vec<bool> = call_args
                            .iter()
                            .map(|arg| {
                                construction_definedness::value_is_defined(
                                    &self.source_consumption,
                                    self.module,
                                    callee_func,
                                    *arg,
                                    Some(&entry_defined),
                                )
                            })
                            .collect();
                        let arg_transport: Vec<bool> = call_args
                            .iter()
                            .map(|arg| {
                                construction_definedness::value_is_transportable(
                                    &self.source_consumption,
                                    self.module,
                                    callee_func,
                                    *arg,
                                    Some(&entry_defined),
                                    Some(&entry_transport),
                                )
                            })
                            .collect();
                        let arg_reference_inputs = self.source_consumption.reference_arguments(
                            callee_func,
                            &nested_func,
                            call_args,
                            Some(&entry_defined),
                        );
                        let nested = self
                            .try_direct_call_summary(
                                &nested_func,
                                CallSummaryArgs::Bindings {
                                    values: &arg_bindings,
                                    defined: &arg_defined,
                                    transport: &arg_transport,
                                    reference_inputs: &arg_reference_inputs,
                                    enclosing_transport_defined: invocation_transport_defined,
                                },
                                decline,
                                depth + 1,
                            )
                            .or_decline(decline, "nested_call_summary_declined", line!())?;
                        if nested.returns.len() != node.results.len() {
                            decline!(decline, "nested_call_summary_return_arity");
                        }
                        for condition in nested.error_conditions {
                            error_conditions.push(call_summary_guarded_condition(
                                &state.path_conditions,
                                condition,
                            ));
                        }
                        for ((result, ty), binding) in node
                            .results
                            .iter()
                            .zip(nested_func_ty.returns.iter())
                            .zip(nested.returns)
                        {
                            if !call_summary_binding_matches_type(ty, &binding) {
                                decline!(decline, "nested_call_result_variant_mismatch");
                            }
                            state.locals.insert(*result, binding);
                        }
                    }

                    // Any other instruction in the callee body is not modeled by the
                    // bounded summary interpreter — decline (fail closed / conservative).
                    _ => {
                        // ANONYMOUS CATCH-ALL: carry the opcode as a detail so this
                        // exit reports a SPLIT, not one undifferentiated wave.
                        decline.note_with_detail(
                            "unmodeled_instruction",
                            line!(),
                            inst_opcode(&node.inst),
                        );
                        return None;
                    }
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
                decline!(decline, "block_without_terminator");
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
            decline!(decline, "self_recursion_with_obligations");
        }
        // A callee with NO return path and NO declared result: the `-> !` shape
        // (trust-ir-bridge maps a `!` return to an empty result list, and ends every
        // diverging site `Unreachable`, behind `Assume(false)` when the site is the
        // never-typed call itself). `combine_call_summary_returns` has nothing to
        // combine and refuses, and until 2026-09-27 that refusal declined the whole
        // summary. So EVERY caller of a bundled `-> !` function got
        // `translate_call`'s unconditional may-panic error rule
        // (`UnsupportedDirectCallSummary`), even when the callee cannot panic.
        // Measured on trust stage-1 98725f8d7d with `fn stop() -> ! { unsafe {
        // c_exit(1) } }` and a caller whose other obligation was a guarded add.
        //
        // SOUND to summarize, and it is still exact about errors. The walk above
        // explored EVERY path of the callee. Case splits are complete, and a revisit,
        // an unmodelled instruction or a block with no terminator declines. Each
        // path ended either in `Return`, which here none did, or in `Unreachable`,
        // which pushed its guarded error condition into `error_conditions`. So
        // every way through the callee is either charged to the caller as an error
        // condition or infeasible. With zero declared results there is nothing to
        // bind. The caller's continuation after the call is an over-approximation.
        // It is kept, and it can only add error derivations, never remove one. A
        // callee that DOES declare results keeps the refusal. It would need a
        // havoc for a value no path produces, and nothing here requires it.
        let returns = if returns.is_empty() && callee_func_ty.returns.is_empty() {
            Vec::new()
        } else {
            combine_call_summary_returns(&returns, callee_func_ty.returns.len()).or_decline(
                decline,
                "returns_not_combinable",
                line!(),
            )?
        };
        Some(DirectCallSummary { returns, error_conditions })
    }

    /// Successor state for one summary CFG edge. Labels its own exits, so an
    /// edge-side decline is attributed here rather than to the `?` upstream.
    fn call_summary_successor_state(
        &self,
        callee_func: &Function,
        state: &CallSummaryState,
        target: BlockId,
        args: &[ValueId],
        guard: Option<Expr>,
        decline: &DeclineSlot,
    ) -> Option<CallSummaryState> {
        if state.visited_blocks.contains(&target) {
            decline!(decline, "successor_block_revisit");
        }

        let target_block =
            callee_func.block(target).or_decline(decline, "successor_block_missing", line!())?;
        if target_block.params.len() != args.len() {
            decline!(decline, "successor_param_arity_mismatch");
        }

        let mut locals = state.locals.clone();
        for (arg, (param, ty)) in args.iter().zip(target_block.params.iter()) {
            if !self.is_call_summary_value_ty(ty) {
                decline!(decline, "successor_param_ty_unsupported");
            }
            locals.insert(
                *param,
                call_summary_value(&state.locals, *arg, ty).or_decline(
                    decline,
                    "successor_arg_unbound",
                    line!(),
                )?,
            );
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
            // Stack cells are PATH state, exactly like `locals`: the successor
            // inherits what this path wrote, and a sibling successor gets its own
            // copy. Dropping this clone would silently reset every slot to
            // "unwritten" at each edge, which reads back as a HAVOC — sound, but it
            // is the whole reason the return-slot shape stays unprovable.
            slots: state.slots.clone(),
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
        // The target's relation carries array columns only when array content is
        // modeled there; into a block reachable from a cycle every array is passed
        // shape-only (no column), whatever this block modeled for it.
        let target_smt_arrays = self.array_content_blocks.contains(&target);
        let mut head_args = Vec::new();
        for (value, ty) in &target_threaded {
            head_args.extend(self.flatten_value_for_relation(*value, ty, target_smt_arrays));
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
            let flat = self.binding_relation_args(binding, ty, target_smt_arrays);
            head_args.extend(flat);
        }
        for (arg, (_, ty)) in args.iter().zip(target_block.params.iter()) {
            head_args.extend(self.flatten_value_for_relation(*arg, ty, target_smt_arrays));
        }

        if self.absorbing_large_block() {
            self.large_block_transition(target, guard, path_constraints, head_args);
            return;
        }
        if self.is_merged_block(target) {
            // A block outside the large-block region (none of its relation's
            // facts is derivable) transferring into a merged block, which has no
            // relation: the rule could never fire (`translate_chc_large_block.rs`,
            // fact 3).
            return;
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
        if self.absorbing_large_block() {
            self.large_block_error(path_constraints, condition);
            return;
        }
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
        self.add_unsupported_error_when(
            block,
            instruction_index,
            node,
            reason,
            from,
            path_constraints,
            Expr::true_(),
        );
    }

    /// `add_unsupported_error` whose fail-closed error rule fires only where
    /// `condition` holds on this path.
    #[allow(clippy::too_many_arguments)]
    fn add_unsupported_error_when(
        &mut self,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        reason: TrustIrChcUnsupportedReason,
        from: &RelationApp,
        path_constraints: &[Expr],
        condition: Expr,
    ) {
        self.diagnostics.push(TrustIrChcDiagnostic {
            function: self.func.name.clone(),
            block,
            instruction_index,
            family: family_for_inst(&node.inst),
            reason,
            result_values: node.results.clone(),
        });
        self.add_error_rule(from, path_constraints, condition);
    }

    /// The unconditional error rule that names a tensor-region instruction
    /// (`crate::tensor_region`).
    fn add_tensor_region_error(
        &mut self,
        construct: crate::TensorConstruct,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &[Expr],
    ) {
        self.add_unsupported_error(
            block,
            instruction_index,
            node,
            TrustIrChcUnsupportedReason::TensorRegion(construct),
            from,
            path_constraints,
        );
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

    /// `value`'s fat-pointer parts as the block being translated may read them
    /// (`translate_chc_large_block.rs`, fact 2): EXACT when a `PtrFromParts` (or
    /// a copy of one) built them in this block, when they mention no variable,
    /// or — under the large-block encoding — when the block that built them
    /// dominates this one (a compound part is then read through its part
    /// variable); OPAQUE for any other read of such a value; `Unrecorded` for a
    /// value no `PtrFromParts` built (a parameter, a load, a call result).
    ///
    /// The per-block encoding never reads an earlier block's non-closed parts:
    /// in a later block's rule their variables would be free, unnamed as havocs,
    /// and a refutation could pick them (the soundness review of 8e).
    fn ptr_parts_view(&mut self, value: ValueId) -> PtrPartsView {
        let Some(parts) = self.ptr_parts.get(&value).cloned() else {
            return PtrPartsView::Unrecorded;
        };
        let PtrParts::Exact { block, data, metadata, closed } = parts else {
            return PtrPartsView::Opaque;
        };
        let Some(here) = self.current_block else {
            return PtrPartsView::Opaque;
        };
        if closed || block == here {
            return PtrPartsView::Exact(data, metadata);
        }
        if self.large_block_dominates(block, here)
            && let Some(data) = self.large_block_part(block, here, data)
            && let Some(metadata) = self.large_block_part(block, here, metadata)
        {
            return PtrPartsView::Exact(data, metadata);
        }
        PtrPartsView::Opaque
    }

    /// Record for `to`, a copy of the fat pointer `from` made in the block being
    /// translated (`Copy`, a same-type pointer cast, a borrow), what `from`'s
    /// parts are here: exact parts become `to`'s own, built in this block; an
    /// opaque `from` makes `to` opaque, with the same metadata symbol.
    fn copy_ptr_parts(&mut self, from: ValueId, to: ValueId) {
        let closed =
            matches!(self.ptr_parts.get(&from), Some(PtrParts::Exact { closed: true, .. }));
        match self.ptr_parts_view(from) {
            PtrPartsView::Unrecorded => {}
            PtrPartsView::Opaque => {
                self.ptr_parts.insert(to, PtrParts::Opaque);
                if let Some(symbol) = self.ptr_opaque_metadata.get(&from).cloned() {
                    self.ptr_opaque_metadata.insert(to, symbol);
                }
            }
            PtrPartsView::Exact(data, metadata) => {
                if let Some(block) = self.current_block {
                    self.ptr_parts.insert(to, PtrParts::Exact { block, data, metadata, closed });
                }
            }
        }
    }

    /// The metadata of the opaque fat pointer `value`: one fresh, UNBOUNDED
    /// havoc per SSA value (`ptr_opaque_metadata`).
    fn opaque_ptr_metadata(&mut self, value: ValueId, metadata_ty: &Ty) -> Expr {
        if let Some(symbol) = self.ptr_opaque_metadata.get(&value) {
            return symbol.clone();
        }
        let symbol = self.fresh_symbolic("fat_metadata", metadata_ty);
        self.ptr_opaque_metadata.insert(value, symbol.clone());
        symbol
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

    /// Instrumentation for `ChcTranslationWork::carried_value_misses`: `value`
    /// is being read with no binding in the current block. Counts it when it is
    /// a threaded value defined in ANOTHER block that this (non-entry) block's
    /// relation does not carry — the read the liveness analysis should have
    /// seen. Never changes what the translation emits.
    fn note_carried_value_miss(&mut self, value: ValueId) {
        let Some(block) = self.current_block else {
            return;
        };
        let id = value.index();
        if block == self.func.entry
            || self.threaded_def_block.get(&id).is_none_or(|def| *def == block)
            || self.block_live_params.get(&block).is_some_and(|live| live.contains(&id))
            || self
                .func
                .block(block)
                .is_some_and(|b| b.params.iter().any(|(param, _)| param.index() == id))
        {
            return;
        }
        self.work.carried_value_misses += 1;
    }

    /// `note_carried_value_miss` for a promoted cell accessed through its own
    /// pointer while absent from `stack_cells`.
    fn note_carried_cell_miss(&mut self, cell: ValueId) {
        let Some(block) = self.current_block else {
            return;
        };
        let id = cell.index();
        if block == self.func.entry
            || self.cell_def_block.get(&id).is_none_or(|def| *def == block)
            || self.block_live_cells.get(&block).is_some_and(|live| live.contains(&id))
        {
            return;
        }
        self.work.carried_value_misses += 1;
    }

    fn resolve(&mut self, value: ValueId, ty: &Ty) -> Expr {
        if let Some(expr) = self.values.get(&value) {
            return expr.clone();
        }
        self.note_carried_value_miss(value);
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

    /// Bind an array result: its SMT-array binding, plus the same opaque scalar
    /// placeholder an aggregate result gets for the `resolve` readers.
    fn bind_array_result(&mut self, node: &InstrNode, array: ArrayValue, ty: &Ty) {
        if let Some(result) = node.results.first() {
            let opaque = self.fresh_symbolic("array", ty);
            self.values.insert(*result, opaque);
            self.arrays.insert(*result, array);
        }
    }

    /// Bind `node`'s first result to `binding`, whatever its shape.
    fn bind_binding_result(&mut self, node: &InstrNode, binding: ValueBinding, ty: &Ty) {
        match binding {
            ValueBinding::Scalar(expr) => self.bind_first_result(node, expr),
            ValueBinding::Aggregate(aggregate) => self.bind_aggregate_result(node, aggregate, ty),
            ValueBinding::Array(array) => self.bind_array_result(node, array, ty),
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
            ValueBinding::Array(array) => {
                let opaque = self.fresh_symbolic("call_array", ty);
                self.values.insert(result, opaque);
                self.arrays.insert(result, array);
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
        self.fresh_symbolic_lifted(prefix, ty, 0)
    }

    /// A fresh unconstrained variable of `ty`'s sort lifted through `depth`
    /// enclosing arrays (`depth == 0` is `fresh_symbolic`).
    ///
    /// The ONE place this translator declares a variable that is not a block-
    /// relation argument, and it declares it as a TRANSLATION HAVOC
    /// (`ChcVc::declare_havoc_var`): a refutation gate must never take a constraint
    /// on it — even an equality such as an assertion's `(= h 263)` — for a
    /// definition of a program value (`trust_mc_driver`'s bounded-unroll grounding
    /// gate reads the reserved name).
    fn fresh_symbolic_lifted(&mut self, prefix: &str, ty: &Ty, depth: u32) -> Expr {
        let stem = format!("{}_{}_{}", sanitize_name(&self.func.name), prefix, self.next_sym_id);
        self.next_sym_id += 1;
        self.vc.declare_havoc_var(&stem, lifted_sort(ty_to_sort(ty), depth))
    }

    fn fresh_call_summary_value(&mut self, prefix: &str, ty: &Ty) -> Option<ValueBinding> {
        if is_call_summary_scalar_ty(ty) {
            return Some(ValueBinding::Scalar(self.fresh_symbolic(prefix, ty)));
        }

        match self.composite_shape(ty)? {
            CompositeShape::Fields(field_tys) => {
                let mut fields = Vec::with_capacity(field_tys.len());
                for (field_index, field_ty) in field_tys.iter().enumerate() {
                    // Trust (#46): recurse for nested-aggregate fields.
                    fields.push(self.resolve_field_binding(
                        &format!("{prefix}_field{field_index}"),
                        field_ty,
                    )?);
                }
                Some(ValueBinding::Aggregate(AggregateValue { fields }))
            }
            CompositeShape::Array { .. } => self.fresh_binding_lifted(prefix, ty, 0),
        }
    }

    /// A fresh binding of `ty` — independent unconstrained leaves, the value of an
    /// undefined / unknown `ty` — with every leaf lifted through `depth` enclosing
    /// arrays. An array gets ONE fresh SMT array per leaf of its element, so its
    /// cost is the element's leaf count, never its length. `None` when `ty` is
    /// neither a scalar field nor a trackable composite.
    fn fresh_binding_lifted(&mut self, prefix: &str, ty: &Ty, depth: u32) -> Option<ValueBinding> {
        match self.composite_shape(ty) {
            Some(CompositeShape::Fields(field_tys)) => {
                let mut fields = Vec::with_capacity(field_tys.len());
                for (index, field_ty) in field_tys.iter().enumerate() {
                    fields.push(self.fresh_binding_lifted(
                        &format!("{prefix}_f{index}"),
                        field_ty,
                        depth,
                    )?);
                }
                Some(ValueBinding::Aggregate(AggregateValue { fields }))
            }
            Some(CompositeShape::Array { len, .. }) if !self.smt_arrays => {
                Some(ValueBinding::Array(ArrayValue::shape_only(len)))
            }
            Some(CompositeShape::Array { elem, len }) => Some(ValueBinding::Array(ArrayValue {
                len,
                lanes: Some(Box::new(self.fresh_binding_lifted(
                    &format!("{prefix}_lanes"),
                    &elem,
                    depth + 1,
                )?)),
            })),
            None if is_scalar_field_ty(ty) => {
                Some(ValueBinding::Scalar(self.fresh_symbolic_lifted(prefix, ty, depth)))
            }
            None => None,
        }
    }

    /// Exact known scalar fields and explicit direct Uninit lanes, following
    /// canonical constant placement. No arbitrary aggregate/opaque encoding or
    /// initializedness fact is inferred from a fresh summary value.
    fn call_summary_constant_carrier(
        &self,
        ty: &Ty,
        constant: &Constant,
        direct_uninit_lanes: bool,
        depth: u32,
    ) -> Option<CallSummaryBinding> {
        if depth as usize >= construction_definedness::MAX_DEFINEDNESS_DEPTH {
            return None;
        }
        if is_call_summary_scalar_ty(ty) {
            return const_to_expr(ty, constant).map(CallSummaryBinding::Scalar);
        }
        if matches!((ty, constant), (Ty::Unit, Constant::PhantomData)) {
            return Some(CallSummaryBinding::Aggregate(CallSummaryAggregate {
                fields: Vec::new(),
            }));
        }
        if !matches!(ty, Ty::Struct(_) | Ty::Tuple(_)) {
            return None;
        }
        let Constant::Aggregate(constants) = constant else { return None };
        let fields = self.aggregate_field_tys(ty)?;
        if fields.len() != constants.len() {
            return None;
        }
        let fields = fields
            .iter()
            .zip(constants)
            .map(|(ty, constant)| {
                if matches!(constant, Constant::Uninit) {
                    direct_uninit_lanes.then(|| CallSummaryBinding::Uninit(ty.clone()))
                } else {
                    self.call_summary_constant_carrier(ty, constant, false, depth + 1)
                }
            })
            .collect::<Option<Vec<_>>>()?;
        Some(CallSummaryBinding::Aggregate(CallSummaryAggregate { fields }))
    }

    fn fresh_direct_call_summary_value(
        &mut self,
        prefix: &str,
        ty: &Ty,
    ) -> Option<CallSummaryBinding> {
        if let Ty::FatPtr(kind) = ty {
            return Some(CallSummaryBinding::OpaqueFatPtr(*kind));
        }
        let binding = self.fresh_call_summary_value(prefix, ty)?;
        self.call_summary_binding_from_value(binding, ty)
    }

    /// Import an existing value without importing numeric meaning for any fat
    /// pointer leaf. Aggregate shaping retains the existing depth/leaf bounds.
    fn call_summary_binding_from_value(
        &self,
        binding: ValueBinding,
        ty: &Ty,
    ) -> Option<CallSummaryBinding> {
        match (binding, ty) {
            (ValueBinding::Scalar(_), Ty::FatPtr(kind)) => {
                Some(CallSummaryBinding::OpaqueFatPtr(*kind))
            }
            (ValueBinding::Scalar(expr), _) if is_scalar_field_ty(ty) => {
                Some(CallSummaryBinding::Scalar(expr))
            }
            (ValueBinding::Aggregate(aggregate), _) => {
                let fields = self.aggregate_field_tys(ty)?;
                if fields.len() != aggregate.fields.len() {
                    return None;
                }
                let fields = aggregate
                    .fields
                    .into_iter()
                    .zip(fields.iter())
                    .map(|(binding, ty)| self.call_summary_binding_from_value(binding, ty))
                    .collect::<Option<Vec<_>>>()?;
                Some(CallSummaryBinding::Aggregate(CallSummaryAggregate { fields }))
            }
            // An array's lanes have its ELEMENT's shape, so they are imported
            // against the element type. A fat-pointer leaf becomes the same opaque
            // token a fat-pointer field does: a token carries no data, so the lanes
            // of such a leaf carry none either.
            (ValueBinding::Array(array), _) => {
                let CompositeShape::Array { elem, len } = self.composite_shape(ty)? else {
                    return None;
                };
                if len != array.len {
                    return None;
                }
                let lanes = match array.lanes {
                    Some(lanes) => {
                        Some(Box::new(self.call_summary_binding_from_value(*lanes, &elem)?))
                    }
                    None => None,
                };
                Some(CallSummaryBinding::Array(CallSummaryArray { len, lanes }))
            }
            _ => None,
        }
    }

    /// Token-only fat values acquire fresh opaque placeholders at the boundary
    /// back to ordinary translation. Reusing a token never creates an equality
    /// between independently unknown addresses or metadata.
    fn materialize_call_summary_binding(&mut self, binding: CallSummaryBinding) -> ValueBinding {
        self.materialize_call_summary_binding_at(binding, 0)
    }

    /// `materialize_call_summary_binding` for a binding nested inside `depth`
    /// arrays: a token inside array lanes becomes a fresh placeholder of the
    /// LIFTED sort, so the lanes stay well-sorted relation columns.
    fn materialize_call_summary_binding_at(
        &mut self,
        binding: CallSummaryBinding,
        depth: u32,
    ) -> ValueBinding {
        match binding {
            CallSummaryBinding::Scalar(expr) => ValueBinding::Scalar(expr),
            CallSummaryBinding::Uninit(ty) => {
                // Value overapproximation only. Source-SSA initializedness
                // remains false until actual writes; every consuming ordinary
                // and summary operation is checked independently. The explicit
                // Uninit marker survives all operations INSIDE a summary.
                self.fresh_binding_lifted("call_uninit_carrier", &ty, depth).unwrap_or_else(|| {
                    ValueBinding::Scalar(self.fresh_symbolic_lifted(
                        "call_uninit_carrier",
                        &ty,
                        depth,
                    ))
                })
            }
            CallSummaryBinding::OpaqueFatPtr(kind) => ValueBinding::Scalar(
                self.fresh_symbolic_lifted("call_opaque_fat_ptr", &Ty::FatPtr(kind), depth),
            ),
            CallSummaryBinding::Aggregate(aggregate) => {
                let fields = aggregate
                    .fields
                    .into_iter()
                    .map(|field| self.materialize_call_summary_binding_at(field, depth))
                    .collect();
                ValueBinding::Aggregate(AggregateValue { fields })
            }
            CallSummaryBinding::Array(array) => ValueBinding::Array(ArrayValue {
                len: array.len,
                lanes: array.lanes.map(|lanes| {
                    Box::new(self.materialize_call_summary_binding_at(*lanes, depth + 1))
                }),
            }),
        }
    }

    fn aggregate_field_tys(&self, ty: &Ty) -> Option<Vec<Ty>> {
        aggregate_field_tys_of(self.module, ty)
    }

    fn is_composite_value_ty(&self, ty: &Ty) -> bool {
        is_composite_value_ty(self.module, ty)
    }

    /// Trust (#46): build a fresh `ValueBinding` for a field of type `ty` — a scalar
    /// gets a fresh symbol; a (possibly nested) composite is recursively built with
    /// fresh leaves. Returns `None` if `ty` is neither scalar nor a trackable
    /// composite (fail closed).
    fn resolve_field_binding(&mut self, prefix: &str, ty: &Ty) -> Option<ValueBinding> {
        self.fresh_binding_lifted(prefix, ty, 0)
    }

    /// A fresh binding of `ty`, or a single fresh scalar placeholder when `ty` has
    /// no tracked shape — the value of an unknown `ty` either way.
    fn fresh_value_binding(&mut self, prefix: &str, ty: &Ty) -> ValueBinding {
        match self.fresh_binding_lifted(prefix, ty, 0) {
            Some(binding) => binding,
            None => ValueBinding::Scalar(self.fresh_symbolic(prefix, ty)),
        }
    }

    fn is_call_summary_value_ty(&self, ty: &Ty) -> bool {
        is_call_summary_scalar_ty(ty)
            || matches!(ty, Ty::FatPtr(_))
            || self.is_composite_value_ty(ty)
    }

    fn resolve_call_summary_argument(
        &mut self,
        value: ValueId,
        ty: &Ty,
    ) -> Option<CallSummaryBinding> {
        if let Ty::FatPtr(kind) = ty {
            return Some(CallSummaryBinding::OpaqueFatPtr(*kind));
        }
        if is_call_summary_scalar_ty(ty) {
            return Some(CallSummaryBinding::Scalar(self.resolve(value, ty)));
        }

        let binding = self.resolve_composite(value, ty)?;
        self.call_summary_binding_from_value(binding, ty)
    }

    fn resolve_aggregate(&mut self, value: ValueId, ty: &Ty) -> Option<AggregateValue> {
        if let Some(aggregate) = self.aggregates.get(&value) {
            return Some(aggregate.clone());
        }

        let field_tys = self.aggregate_field_tys(ty)?;
        self.note_carried_value_miss(value);
        let mut fields = Vec::with_capacity(field_tys.len());
        for (field_index, field_ty) in field_tys.iter().enumerate() {
            // Trust (#46): recurse so a nested-composite field gets a nested binding
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

    /// The SMT-array binding of `value` at the non-empty array type `ty`: its
    /// existing binding, or — for a value with none in this block — fresh
    /// unconstrained lanes (one fresh SMT array per element leaf), recorded so
    /// every later read of the same SSA value sees the same lanes. `None` when
    /// `ty` is not a trackable non-empty array, or the existing binding has
    /// another length (malformed IR; the caller fails closed).
    fn resolve_array(&mut self, value: ValueId, ty: &Ty) -> Option<ArrayValue> {
        let CompositeShape::Array { len, .. } = self.composite_shape(ty)? else {
            return None;
        };
        if let Some(array) = self.arrays.get(&value) {
            return (array.len == len).then(|| array.clone());
        }
        self.note_carried_value_miss(value);
        let ValueBinding::Array(array) =
            self.fresh_binding_lifted(&format!("v{}", value.index()), ty, 0)?
        else {
            return None;
        };
        self.arrays.insert(value, array.clone());
        Some(array)
    }

    /// `value`'s binding at the trackable composite type `ty` (fields or SMT
    /// arrays), or `None` when `ty` is not one.
    fn resolve_composite(&mut self, value: ValueId, ty: &Ty) -> Option<ValueBinding> {
        match self.composite_shape(ty)? {
            CompositeShape::Fields(_) => {
                self.resolve_aggregate(value, ty).map(ValueBinding::Aggregate)
            }
            CompositeShape::Array { .. } => self.resolve_array(value, ty).map(ValueBinding::Array),
        }
    }

    /// `value`'s binding at `ty`, whatever its shape; `None` when `ty` is neither a
    /// scalar field nor a trackable composite.
    fn resolve_binding(&mut self, value: ValueId, ty: &Ty) -> Option<ValueBinding> {
        if is_scalar_field_ty(ty) {
            return Some(ValueBinding::Scalar(self.resolve(value, ty)));
        }
        self.resolve_composite(value, ty)
    }

    /// `value` as an ELEMENT of type `elem_ty` about to be spliced into array
    /// lanes: a scalar is normalized to its exact carrier, and the whole binding
    /// must have exactly `elem_ty`'s shape and sorts. `None` (the caller fails
    /// closed or havocs) otherwise, so a mis-sorted term never reaches a column.
    fn element_binding(&mut self, value: ValueId, elem_ty: &Ty) -> Option<ValueBinding> {
        let binding = match self.resolve_binding(value, elem_ty)? {
            ValueBinding::Scalar(expr) => {
                ValueBinding::Scalar(normalize_expr_to_exact_ty(&expr, elem_ty)?)
            }
            composite => composite,
        };
        binding_matches_ty_at(self.module, &binding, elem_ty, 0).then_some(binding)
    }

    /// `value`'s arguments to a relation declared with `target_smt_arrays`.
    fn flatten_value_for_relation(
        &mut self,
        value: ValueId,
        ty: &Ty,
        target_smt_arrays: bool,
    ) -> Vec<Expr> {
        if let Some(binding) = self.resolve_composite(value, ty) {
            return self.binding_relation_args(binding, ty, target_smt_arrays);
        }
        if self.is_composite_value_ty(ty) {
            // A composite value whose binding does not fit its declared type
            // (malformed IR): forward fresh columns of the declared shape, so the
            // relation application stays well-sorted, never a scalar placeholder.
            let fresh = self.fresh_value_binding(&format!("v{}", value.index()), ty);
            return self.binding_relation_args(fresh, ty, target_smt_arrays);
        }
        vec![self.resolve(value, ty)]
    }

    /// `binding`'s arguments to a relation declared with `target_smt_arrays`
    /// (`ValueBinding::relation_args`). Into a relation that carries array
    /// columns, a binding holding a shape-only array — which a block that models
    /// array content never builds; this is defensive — forwards fresh columns of
    /// `ty`'s shape instead, so the application always matches the signature.
    fn binding_relation_args(
        &mut self,
        binding: ValueBinding,
        ty: &Ty,
        target_smt_arrays: bool,
    ) -> Vec<Expr> {
        if target_smt_arrays && !binding.has_array_content() {
            let modeled_here = std::mem::replace(&mut self.smt_arrays, true);
            let fresh = self.fresh_value_binding("relation_fill", ty);
            self.smt_arrays = modeled_here;
            return fresh.flat_args();
        }
        binding.relation_args(target_smt_arrays)
    }

    fn eval_extract_field(&mut self, aggregate: ValueId, field: u32) -> Option<ValueBinding> {
        let Some(binding) = self.aggregates.get(&aggregate) else {
            self.note_carried_value_miss(aggregate);
            return None;
        };
        binding.fields.get(field as usize).cloned()
    }

    /// Build a complete field aggregate from the exact ordered operand
    /// bindings. No unwritten seed, fresh field, or omitted operand enters this
    /// constructor. The existing shape/sort checker also covers nested arrays
    /// and aggregates; enums and other untracked shapes retain their refusal.
    fn eval_make_field_aggregate(
        &mut self,
        ty: &Ty,
        variant: Option<u32>,
        fields: &[ValueId],
    ) -> Result<AggregateValue, TrustIrChcUnsupportedReason> {
        let field_tys = self
            .aggregate_field_tys(ty)
            .ok_or(TrustIrChcUnsupportedReason::AggregateConstruction)?;
        if !matches!(ty, Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, 0))
            || variant.is_some()
            || fields.len() != field_tys.len()
        {
            return Err(TrustIrChcUnsupportedReason::AggregateConstruction);
        }
        if !construction_definedness::supported_type(self.module, ty) {
            return Err(TrustIrChcUnsupportedReason::AggregateOpaqueValue);
        }
        let mut bindings = Vec::with_capacity(fields.len());
        for (field, field_ty) in fields.iter().zip(&field_tys) {
            if !construction_definedness::value_is_defined(
                &self.source_consumption,
                self.module,
                self.func,
                *field,
                None,
            ) {
                return Err(TrustIrChcUnsupportedReason::AggregateOperandDefinedness);
            }
            bindings.push(
                self.element_binding(*field, field_ty)
                    .ok_or(TrustIrChcUnsupportedReason::AggregateConstruction)?,
            );
        }
        Ok(AggregateValue { fields: bindings })
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
        // Trust (#46): the inserted field may itself be a nested composite.
        result.fields[field_index] = if is_scalar_field_ty(&value_ty) {
            ValueBinding::Scalar(self.resolve(value, &value_ty))
        } else {
            self.resolve_composite(value, &value_ty)?
        };
        Some(result)
    }

    /// The lane an element access at `index` names in an array of `len` lanes,
    /// and when that access is in bounds.
    ///
    /// The lane is `index` as a `usize` bit-vector (BV64): zero-extended from a
    /// narrower index, the low 64 bits of a wider one (exact whenever the access
    /// is in bounds, since `len < 2^64`). `len` enters only as ONE constant.
    ///
    /// SIGNEDNESS. An index's bits mean what its DECLARED type says (trust-ir
    /// `interpret.rs :: runtime_index`): an unsigned index is its value, so a `u8`
    /// of 200 names lane 200 of a `[T; 256]`; a signed index with its top bit set
    /// is negative, which is undefined behaviour even where its bits read back as
    /// an in-bounds unsigned value (`-1i8` is not lane 255). The declared type
    /// comes from `element_operand_tys`:
    ///
    /// * unsigned: in bounds iff `index <u len`;
    /// * signed: in bounds iff `index <u min(len, 2^(w-1))` at its width `w`, i.e.
    ///   non-negative and below the length;
    /// * not a known integer type: in bounds where both readings agree it is
    ///   (`index <u min(len, 2^(w-1))`), and `ambiguous` where they disagree (top
    ///   bit set, below the length unsigned). `discharge_element_bounds` assumes
    ///   neither reading there.
    ///
    /// `None` when the index is not a bit-vector of width 1..=128 (malformed IR).
    fn array_lane_access(&mut self, index: ValueId, len: u64) -> Option<LaneAccess> {
        let declared = self.element_operand_tys.get(&index).filter(|ty| ty.is_integer()).cloned();
        let signed = declared.as_ref().map(Ty::is_signed);
        let index = self.resolve(index, declared.as_ref().unwrap_or(&Ty::Usize));
        lane_access_of(index, signed, len)
    }

    /// Emit an element access's in-bounds obligation on this path, and return
    /// where the access is EXACT from here on: `Always` (the plain `select` /
    /// `store`), `Never` (no lane: the caller havocs), `When(c)` (exact under `c`,
    /// a havoc outside it).
    ///
    /// With memory checks ON: an error rule where the access is out of bounds
    /// under every reading of the index — trust-ir undefined behaviour — and,
    /// where an index of unknown signedness reads differently signed and unsigned,
    /// a DIAGNOSTIC-backed unsupported error (`UnmodeledElementIndex`), so that
    /// case is never a clean refutation or a proof. The path then continues only
    /// under `in_bounds`: execution does not continue past undefined behaviour, so
    /// no later constraint of the path reads a junk lane, and every counterexample
    /// through the access reads a real lane. This is neutral for "is `error`
    /// reachable": a path on which the access can be out of bounds already
    /// derives `error` at the access.
    ///
    /// With memory checks OFF there is no rule. The caller guards the access with
    /// the returned condition: outside it a read is a fresh value and a write
    /// havocs the whole array — never a dropped write, which would let a later
    /// read see a value the program overwrote (turning off a diagnostic must never
    /// turn on a stale read).
    fn discharge_element_bounds(
        &mut self,
        access: &LaneAccess,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &mut Vec<Expr>,
    ) -> InBounds {
        if !self.options.check_memory_bounds {
            return access.in_bounds.clone();
        }
        let (out_of_bounds, ambiguous) = match (&access.in_bounds, &access.ambiguous) {
            (InBounds::Always, _) => return InBounds::Always,
            (InBounds::Never, Ambiguity::Nowhere) => (Some(Expr::true_()), None),
            (InBounds::Never, Ambiguity::Always) => (None, Some(Expr::true_())),
            (InBounds::Never, Ambiguity::When(ambiguous)) => {
                (Some(ambiguous.clone().not()), Some(ambiguous.clone()))
            }
            (InBounds::When(in_bounds), Ambiguity::Nowhere) => {
                (Some(in_bounds.clone().not()), None)
            }
            (InBounds::When(_), Ambiguity::Always) => (None, Some(Expr::true_())),
            (InBounds::When(in_bounds), Ambiguity::When(ambiguous)) => (
                Some(in_bounds.clone().not().and(ambiguous.clone().not())),
                Some(ambiguous.clone()),
            ),
        };
        if let Some(out_of_bounds) = out_of_bounds {
            self.add_error_rule(from, path_constraints, out_of_bounds);
        }
        if let Some(ambiguous) = ambiguous {
            self.add_unsupported_error_when(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::UnmodeledElementIndex,
                from,
                path_constraints,
                ambiguous,
            );
        }
        match &access.in_bounds {
            InBounds::Always => InBounds::Always,
            InBounds::Never => {
                // Undefined behaviour (or an unmodeled index) on every execution
                // that gets here: no execution continues past it.
                path_constraints.push(Expr::false_());
                InBounds::Never
            }
            InBounds::When(in_bounds) => {
                path_constraints.push(in_bounds.clone());
                InBounds::Always
            }
        }
    }

    /// `ExtractElement { ty: dst_ty, array, index }`: `select` on every leaf of the
    /// array's lanes — exact at a symbolic index as at a constant one — under the
    /// access's own in-bounds obligation (`discharge_element_bounds`).
    ///
    /// The array is its binding in this block or, for an array value with none (an
    /// array-typed result this model binds only as a placeholder, such as an
    /// opaque call's), fresh lanes of its DECLARED type (`element_operand_tys`),
    /// recorded so every read of that value agrees. Either way the access has a
    /// length, so it always carries its bounds obligation. A read of a SHAPE-ONLY
    /// array (a block a cycle reaches), of an array whose element this model does
    /// not track, or of malformed IR whose element type is not the result type, is
    /// a fresh value under the same obligation. A SIMD vector's lanes are not
    /// modeled, but its length is its declared lane count, so its read is a fresh
    /// value under the same obligation too (trust-ir makes an out-of-bounds vector
    /// read undefined behaviour, `eval_extract_element`, exactly as an array's) —
    /// the bound `try_direct_call_summary` states for the same read in a callee. An
    /// operand whose length this model does not know (a sequence, or no declared
    /// type) is a fresh value, and with memory checks on the read fails closed
    /// (`UnmodeledElementLength`): its out-of-bounds case is undefined behaviour
    /// this model cannot state, so the path can never be proved through it. An
    /// index this model cannot place (not a bit-vector) fails closed.
    #[allow(clippy::too_many_arguments)]
    fn translate_extract_element(
        &mut self,
        dst_ty: &Ty,
        array: ValueId,
        index: ValueId,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &mut Vec<Expr>,
    ) {
        let declared = self.element_operand_tys.get(&array).cloned();
        let binding = match self.arrays.get(&array).cloned() {
            Some(binding) => Some(binding),
            None => match &declared {
                Some(ty) => self.resolve_array(array, ty),
                None => {
                    self.note_carried_value_miss(array);
                    None
                }
            },
        };
        let len = match (&binding, &declared) {
            (Some(binding), _) => Some(binding.len),
            (None, Some(Ty::Array(_, len))) => Some(*len),
            (None, Some(Ty::Vector(_, lanes))) => Some(u64::from(*lanes)),
            (None, _) => None,
        };
        let Some(len) = len else {
            let havoc = self.fresh_value_binding("element_read", dst_ty);
            self.bind_binding_result(node, havoc, dst_ty);
            if self.options.check_memory_bounds {
                self.add_unsupported_error(
                    block,
                    instruction_index,
                    node,
                    TrustIrChcUnsupportedReason::UnmodeledElementLength,
                    from,
                    path_constraints,
                );
            }
            return;
        };
        let Some(access) = self.array_lane_access(index, len) else {
            let havoc = self.fresh_value_binding("element_read", dst_ty);
            self.bind_binding_result(node, havoc, dst_ty);
            self.add_unsupported_error(
                block,
                instruction_index,
                node,
                TrustIrChcUnsupportedReason::UnmodeledElementIndex,
                from,
                path_constraints,
            );
            return;
        };
        // The lane's value: exact `select`, or a fresh value where the lanes are not
        // modeled (see above). The obligation below needs only the length.
        let element = match binding
            .and_then(|binding| binding.select(&access.lane))
            .filter(|element| binding_matches_ty_at(self.module, element, dst_ty, 0))
        {
            Some(element) => element,
            None => self.fresh_value_binding("element_read", dst_ty),
        };
        let value = match self.discharge_element_bounds(
            &access,
            block,
            instruction_index,
            node,
            from,
            path_constraints,
        ) {
            InBounds::Always => element,
            InBounds::Never => self.fresh_value_binding("element_read_oob", dst_ty),
            InBounds::When(in_bounds) => {
                let havoc = self.fresh_value_binding("element_read_oob", dst_ty);
                match element.select_by(&in_bounds, &havoc) {
                    Some(guarded) => guarded,
                    None => havoc,
                }
            }
        };
        self.bind_binding_result(node, value, dst_ty);
    }

    /// EXACT model of an array element WRITE `InsertElement { ty, array, index,
    /// value }` (`ty` is the ARRAY's own type — `trust_ir::interpret ::
    /// eval_insert_element` starts with `expect_ty(array, result_ty)`): `store` on
    /// every leaf of the lanes, at a symbolic index as at a constant one. TrustIR
    /// `InsertElement` is a PURE functional update — the result is a fresh SSA value
    /// and the source keeps its own (still correct) binding — so nothing stale
    /// survives under any name.
    ///
    /// Its in-bounds obligation is the read's (`discharge_element_bounds`): with
    /// memory checks on the path continues only in bounds, where the write is the
    /// plain `store`; with them off the write is guarded, `ite(in_bounds, store,
    /// havoc)`, so a write that is not known to land in bounds leaves an
    /// unconstrained array — never the unchanged one, which would drop a write
    /// the program may have made.
    ///
    /// `None` — the caller keeps the pre-existing FAIL-CLOSED path, deliberately NOT
    /// a havoc that would forget the write — when `ty` is not a trackable non-empty
    /// array (a SIMD vector, an empty array, an untrackable element), the element
    /// does not have exactly the element type's shape and sorts, or the index is
    /// not a bit-vector. No rule is added before that is known, so a declined
    /// write adds only its fail-closed rule.
    #[allow(clippy::too_many_arguments)]
    fn eval_insert_element(
        &mut self,
        ty: &Ty,
        array: ValueId,
        index: ValueId,
        value: ValueId,
        block: BlockId,
        instruction_index: usize,
        node: &InstrNode,
        from: &RelationApp,
        path_constraints: &mut Vec<Expr>,
    ) -> Option<ArrayValue> {
        let CompositeShape::Array { elem, len } = self.composite_shape(ty)? else {
            return None;
        };
        let base = self.resolve_array(array, ty)?;
        let access = self.array_lane_access(index, len)?;
        let element = self.element_binding(value, &elem)?;
        let stored = base.store(&access.lane, &element)?;
        Some(
            match self.discharge_element_bounds(
                &access,
                block,
                instruction_index,
                node,
                from,
                path_constraints,
            ) {
                InBounds::Always => stored,
                InBounds::Never => self.fresh_array_value("element_write_oob", ty)?,
                InBounds::When(in_bounds) => {
                    let havoc = self.fresh_array_value("element_write_oob", ty)?;
                    let ValueBinding::Array(guarded) = ValueBinding::Array(stored)
                        .select_by(&in_bounds, &ValueBinding::Array(havoc))?
                    else {
                        return None;
                    };
                    guarded
                }
            },
        )
    }

    /// Fresh unconstrained lanes of the non-empty array type `ty` (shape-only in a
    /// block that does not model array content).
    fn fresh_array_value(&mut self, prefix: &str, ty: &Ty) -> Option<ArrayValue> {
        match self.fresh_binding_lifted(prefix, ty, 0)? {
            ValueBinding::Array(array) => Some(array),
            _ => None,
        }
    }

    /// EXACT model of trust-ir v50 `ArraySplat { ty, value }` (`[value; n]`): one
    /// constant SMT array per leaf of `value`'s binding, `((as const (Array BV64 S))
    /// v)`, so a read of ANY in-bounds lane yields exactly `value` (the Lean law
    /// `ExtractElement i (splat v n) = v`, `i < n`) — constant size whatever `n` is.
    /// `[value; 0]` is the zero-field aggregate. `None` (the caller binds one opaque
    /// fresh value) when `ty` is not a trackable array or `value` does not have the
    /// element type's exact shape.
    ///
    /// Sound because `ArraySplat` is pure and total: the result is a fresh SSA
    /// value and `value` keeps its own binding, so nothing stale survives. The
    /// constant array also pins the lanes outside `[0, n)`; the junk-lane invariant
    /// on `ArrayValue` is what keeps them from mattering.
    fn eval_array_splat(&mut self, ty: &Ty, value: ValueId) -> Option<ValueBinding> {
        match self.composite_shape(ty)? {
            CompositeShape::Array { len, .. } if !self.smt_arrays => {
                Some(ValueBinding::Array(ArrayValue::shape_only(len)))
            }
            CompositeShape::Array { elem, len } => {
                let element = self.element_binding(value, &elem)?;
                Some(ValueBinding::Array(ArrayValue::splat(len, &element)?))
            }
            CompositeShape::Fields(fields) if fields.is_empty() && matches!(ty, Ty::Array(..)) => {
                Some(ValueBinding::Aggregate(AggregateValue { fields: Vec::new() }))
            }
            CompositeShape::Fields(_) => None,
        }
    }

    /// `value`'s exact binding at `ty`, for the constants whose encoding is
    /// exact: an integer / float / bool / vector literal at a scalar type
    /// (`const_to_expr`, which answers `None` rather than approximate bits); a
    /// (nested) `Splat` at a trackable array type of exactly its length, which is
    /// one constant SMT array per leaf of the element; and a list-spelled array
    /// literal — `Array`, the legacy `Aggregate` spelling at an array type, or
    /// `Bytes` at `[u8; n]` — of exactly its length, encoded flat
    /// (`define_array_lanes`), whose definitional lane equalities are appended to
    /// `definitions` for the caller to add to the defining path. Every other
    /// constant — `SymbolAddr`/`FnDef` (whose `const_to_expr` answer is a
    /// placeholder, not the value), a struct aggregate, `Uninit` — answers `None`,
    /// and the caller then discards `definitions`.
    fn exact_constant_binding(
        &mut self,
        ty: &Ty,
        value: &Constant,
        definitions: &mut Vec<Expr>,
    ) -> Option<ValueBinding> {
        match value {
            Constant::Int(_)
            | Constant::U128(_)
            | Constant::Float(_)
            | Constant::Bool(_)
            | Constant::Vector(_)
                if is_scalar_field_ty(ty) =>
            {
                // The lane must inhabit the exact carrier a fresh field of `ty`
                // gets (kind and width, not `Sort` equality), or relation
                // threading would apply a mis-sorted argument.
                normalize_expr_to_exact_ty(&const_to_expr(ty, value)?, ty).map(ValueBinding::Scalar)
            }
            Constant::Splat { elem, len } => match self.composite_shape(ty)? {
                CompositeShape::Array { len: lanes, .. } if lanes == *len && !self.smt_arrays => {
                    Some(ValueBinding::Array(ArrayValue::shape_only(lanes)))
                }
                CompositeShape::Array { elem: elem_ty, len: lanes } if lanes == *len => {
                    let element = self.exact_constant_binding(&elem_ty, elem, definitions)?;
                    Some(ValueBinding::Array(ArrayValue::splat(lanes, &element)?))
                }
                CompositeShape::Fields(fields)
                    if fields.is_empty() && *len == 0 && matches!(ty, Ty::Array(..)) =>
                {
                    Some(ValueBinding::Aggregate(AggregateValue { fields: Vec::new() }))
                }
                CompositeShape::Array { .. } | CompositeShape::Fields(_) => None,
            },
            // A list-spelled array literal `[e0, e1, …]` (`Aggregate` is its legacy
            // spelling at an array type, with the same contract): each element's
            // exact binding, then the flat definitional encoding, one equality per
            // element leaf — the literal's own text.
            Constant::Array(elems) | Constant::Aggregate(elems) => {
                match self.composite_shape(ty)? {
                    CompositeShape::Array { len, .. }
                        if u64::try_from(elems.len()).ok()? == len && !self.smt_arrays =>
                    {
                        Some(ValueBinding::Array(ArrayValue::shape_only(len)))
                    }
                    CompositeShape::Array { elem: elem_ty, len }
                        if u64::try_from(elems.len()).ok()? == len =>
                    {
                        let mut elements = Vec::with_capacity(elems.len());
                        for elem in elems {
                            elements.push(self.exact_constant_binding(
                                &elem_ty,
                                elem,
                                definitions,
                            )?);
                        }
                        let array = self.define_array_lanes(ty, &elements, definitions)?;
                        Some(ValueBinding::Array(array))
                    }
                    CompositeShape::Fields(fields)
                        if fields.is_empty() && elems.is_empty() && matches!(ty, Ty::Array(..)) =>
                    {
                        Some(ValueBinding::Aggregate(AggregateValue { fields: Vec::new() }))
                    }
                    CompositeShape::Array { .. } | CompositeShape::Fields(_) => None,
                }
            }
            // A byte string at `[u8; n]` (trust-ir executes it as `n` `u8` lanes and
            // refuses any other element type): a list literal of its bytes.
            Constant::Bytes { data, .. } => match self.composite_shape(ty)? {
                CompositeShape::Array { elem: Ty::U8, len }
                    if u64::try_from(data.len()).ok()? == len && !self.smt_arrays =>
                {
                    Some(ValueBinding::Array(ArrayValue::shape_only(len)))
                }
                CompositeShape::Array { elem: Ty::U8, len }
                    if u64::try_from(data.len()).ok()? == len =>
                {
                    let elements: Vec<ValueBinding> = data
                        .iter()
                        .map(|byte| ValueBinding::Scalar(Expr::bitvec_const(*byte, 8)))
                        .collect();
                    Some(ValueBinding::Array(self.define_array_lanes(
                        ty,
                        &elements,
                        definitions,
                    )?))
                }
                CompositeShape::Fields(fields)
                    if fields.is_empty() && data.is_empty() && matches!(ty, Ty::Array(..)) =>
                {
                    Some(ValueBinding::Aggregate(AggregateValue { fields: Vec::new() }))
                }
                CompositeShape::Array { .. } | CompositeShape::Fields(_) => None,
            },
            _ => None,
        }
    }

    /// The array of the non-empty array type `ty` whose lanes `0..elements.len()`
    /// are exactly `elements` (each with the element type's exact shape and
    /// sorts), encoded FLAT: fresh lanes `L` (one fresh SMT array per element leaf)
    /// and, per element `k` and leaf, the definitional equality `select(L, k) =
    /// e_k`, appended to `definitions`. The caller conjoins them into one term on
    /// the defining path.
    ///
    /// Size is the elements' own (a literal's text; a `MakeAggregate`'s operand
    /// list), and DEPTH is constant. A store chain `store(…store(a, 0, e0)…)` would
    /// be as deep as the literal is long, and every recursive consumer of the term
    /// (the solver's preprocessing, a `Drop` of the term) overflows its stack at
    /// tens of thousands of elements — a process abort, not a fail-closed answer.
    ///
    /// The equalities are DEFINITIONAL: each names a distinct lane of the fresh
    /// `L` exactly once, so for every value of the elements some `L` satisfies all
    /// of them — they can never make a path infeasible. `L`'s lanes outside
    /// `0..n` stay free: junk nothing reads (`ArrayValue`). A scalar leaf gives a
    /// scalar equality; a leaf that is itself an array (a nested array element)
    /// gives an array-sorted one whose left side is a lane of the fresh `L` — the
    /// only array equality the junk-lane invariant admits, and `L` is recorded in
    /// `definitional_array_lanes` so `vc_equates_array_terms_beyond` can tell.
    ///
    /// In a block that does not model array content this is the shape-only array.
    fn define_array_lanes(
        &mut self,
        ty: &Ty,
        elements: &[ValueBinding],
        definitions: &mut Vec<Expr>,
    ) -> Option<ArrayValue> {
        let array = self.fresh_array_value("array_literal", ty)?;
        let Some(lanes) = &array.lanes else {
            return Some(array);
        };
        lanes.map_leaves(&mut |leaf| {
            if let ay_bindings::ExprValue::Var { name } = leaf.value() {
                self.definitional_array_lanes.insert(name.clone());
            }
            Some(leaf.clone())
        })?;
        for (lane, element) in elements.iter().enumerate() {
            let slot = array.select(&Expr::bitvec_const(u64::try_from(lane).ok()?, 64))?;
            slot.zip_leaves(element, &mut |slot_leaf, element_leaf| {
                definitions.push(slot_leaf.clone().try_eq(element_leaf.clone()).ok()?);
                Some(slot_leaf.clone())
            })?;
        }
        Some(array)
    }

    /// `MakeAggregate { ty, fields }` at a non-empty array type `ty` with one
    /// operand per lane (trust-ir `eval_make_aggregate`): the flat definitional
    /// encoding of its operands (`define_array_lanes`), whose equalities go to
    /// `definitions`. `None` (the caller keeps the fail-closed rule) for any other
    /// type, a variant index, a lane count other than the length, or an operand
    /// without the element type's exact shape.
    fn eval_make_array(
        &mut self,
        ty: &Ty,
        variant: Option<u32>,
        fields: &[ValueId],
        definitions: &mut Vec<Expr>,
    ) -> Option<ArrayValue> {
        let CompositeShape::Array { elem, len } = self.composite_shape(ty)? else {
            return None;
        };
        if variant.is_some() || u64::try_from(fields.len()).ok()? != len {
            return None;
        }
        let mut elements = Vec::with_capacity(fields.len());
        for field in fields {
            elements.push(self.element_binding(*field, &elem)?);
        }
        self.define_array_lanes(ty, &elements, definitions)
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
                // trust-ir WS3.20 rotates: TOTAL (amount reduced modulo the
                // width), encoded EXACTLY by the shared `bv_rotate`. The integer
                // BinOp arm fails closed on the unencodable havoc; the direct-call
                // summary keeps that havoc as a sound over-approximation (a rotate
                // never traps, so no error condition is owed).
                BinOp::RotL | BinOp::RotR => bv_rotate(lhs, rhs, matches!(op, BinOp::RotL))
                    .unwrap_or_else(|| self.fresh_symbolic("rotate_unencodable", ty)),
                BinOp::FAdd
                | BinOp::FSub
                | BinOp::FMul
                | BinOp::FDiv
                | BinOp::FRem
                | BinOp::FMin
                | BinOp::FMax
                | BinOp::FCopySign => self.fresh_symbolic("float_on_int", ty),
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
                // Every other op on `Bool` is ill-typed: havoc; the non-integer
                // BinOp arm fails closed because only And/Or/Xor count as
                // `modeled_precisely`. Listed, not `_`, so a new `BinOp` must be
                // placed before this compiles (mirrors `translate::eval_binop`).
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::UDiv
                | BinOp::SDiv
                | BinOp::URem
                | BinOp::SRem
                | BinOp::FAdd
                | BinOp::FSub
                | BinOp::FMul
                | BinOp::FDiv
                | BinOp::FRem
                | BinOp::FMin
                | BinOp::FMax
                | BinOp::FCopySign
                | BinOp::Shl
                | BinOp::LShr
                | BinOp::AShr
                | BinOp::RotL
                | BinOp::RotR => self.fresh_symbolic("binop_result", ty),
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
                ValueBinding::Scalar(_) | ValueBinding::Array(_) => return None,
            };
        }
        match binding {
            ValueBinding::Scalar(expr) => Some(expr),
            ValueBinding::Aggregate(_) | ValueBinding::Array(_) => None,
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

#[cfg(test)]
fn translate_function(
    func: &Function,
    module: &Module,
    options: &TranslateOptions,
) -> ChcTranslationOutput {
    translate_function_with_encoding(func, module, options, ChcEncoding::Automatic)
}

fn translate_function_with_encoding(
    func: &Function,
    module: &Module,
    options: &TranslateOptions,
    encoding: ChcEncoding,
) -> ChcTranslationOutput {
    let mut translator = ChcFuncTranslator::new(func, module, options);
    match encoding {
        ChcEncoding::Automatic => {}
        ChcEncoding::PerBlock => translator.allow_large_block = false,
        #[cfg(any(test, feature = "legacy-liveness-oracle"))]
        ChcEncoding::Legacy => {
            translator.liveness = LivenessOracle::Legacy;
            translator.allow_large_block = false;
        }
    }
    translator.translate()
}

/// `translate_function` in the per-block encoding, for the tests that read one
/// block's relation or transition rules.
#[cfg(test)]
fn translate_function_per_block(
    func: &Function,
    module: &Module,
    options: &TranslateOptions,
) -> ChcTranslationOutput {
    let mut translator = ChcFuncTranslator::new(func, module, options);
    translator.allow_large_block = false;
    translator.translate()
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
            if (src_ty.is_integer() || matches!(src_ty, Ty::Bool)) && dst_ty.is_integer() =>
        {
            let src_width = src_ty.bit_width_with(HOST_POINTER_BITS)?;
            let dst_width = dst_ty.bit_width_with(HOST_POINTER_BITS)?;
            // Canonical TrustIR treats Bool as a one-bit resize lane. Adapt
            // its SMT Bool carrier once, then use the same opcode-defined
            // resize below: SExt(true) is all ones, while ZExt(true) is one.
            let operand = if matches!(src_ty, Ty::Bool) {
                Expr::ite(
                    operand,
                    Expr::bitvec_const(1u64, src_width),
                    Expr::bitvec_const(0u64, src_width),
                )
            } else {
                operand
            };
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
        Inst::UnOp { operand, .. }
        | Inst::Cast { operand, .. }
        | Inst::BoxDeref { operand, .. } => {
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
        | Inst::Dealloc { ptr }
        | Inst::Drop { ptr, .. } => {
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
        // WS3.20 bulk memory: every operand is a value read. Enumerated exactly
        // (not left to the conservative arm) so the alias analyses see WHICH
        // pointers reach it. The proof-authority gate, the promotion analysis and
        // `function_escaped_bases` count a `dst`/`src` use as an escape
        // (`BulkMemoryUse::Escapes`). Only the translator's own cell decision
        // (`translate_alloca`, `BulkMemoryUse::Tracked`) and
        // `record_interior_pointer_escapes` treat it as a tracked position, because
        // `translate_bulk_memory` writes the cell exactly or havocs it: a cell
        // whose address reaches a MemCopy/MemSet stays precise across it in the
        // diagnostic lane, and no admitted or promoted cell ever reaches one.
        Inst::MemCopy { dst, src, bytes, .. } => {
            uses.push(*dst);
            uses.push(*src);
            uses.push(*bytes);
            false
        }
        Inst::MemSet { dst, byte, bytes } => {
            uses.push(*dst);
            uses.push(*byte);
            uses.push(*bytes);
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
        Inst::Call { args, .. } | Inst::CallCannotUnwind { args, .. } => {
            uses.extend(args.iter().copied());
            false
        }
        Inst::CallIndirect { callee, args, .. }
        | Inst::CallIndirectCannotUnwind { callee, args, .. } => {
            uses.push(*callee);
            uses.extend(args.iter().copied());
            false
        }
        Inst::Return { values } => {
            uses.extend(values.iter().copied());
            false
        }
        Inst::MakeAggregate { fields, .. } | Inst::MakeClosure { captures: fields, .. } => {
            uses.extend(fields.iter().copied());
            false
        }
        // v50 `[value; n]` reads exactly ONE operand, once, whatever `n` is (the
        // lane count lives in the type). A pointer in `value` is thereby copied
        // into an aggregate value: every alias analysis that consumes this list
        // treats a use by an instruction it does not model positionally as an
        // escape, which is the right answer for a pointer that now lives in `n`
        // lanes.
        Inst::ArraySplat { value, .. } => {
            uses.push(*value);
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
        // An Assert's v52 `kind` operands are read only on failure, a terminal
        // panic outcome, so the check itself reads only `cond`.
        Inst::Assume { cond } | Inst::Assert { cond, kind: _, site: _ } => {
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
        // Opaque: we cannot (or do not) enumerate its reads, so report it
        // conservatively. Listed rather than `_` so a FUTURE variant is a compile
        // error here instead of silently inheriting a classification.
        Inst::DialectOp(_)
        | Inst::CoroSuspend { .. }
        | Inst::Invoke { .. }
        | Inst::AssertInvoke { .. }
        | Inst::DropInvoke { .. }
        | Inst::InvokeIndirect { .. }
        | Inst::LandingPad { .. }
        | Inst::Resume { .. } => true,
        // trust-ir v67-v69 tensor region (`crate::tensor_region`): refused by
        // name wherever it is translated, and absent from every module this
        // lowering admits. Reported conservatively (every in-scope value
        // possibly read) rather than enumerated, so a caller that bypassed the
        // module input keeps liveness a sound over-approximation.
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => true,
    }
}

/// The declared type of every value `func` uses as the array or the index
/// operand of an `ExtractElement`/`InsertElement`: a block parameter's declared
/// type, or an instruction result's (`InstrNode::result_tys`). Two linear passes
/// over the function. A value with no declared type here (a result the
/// instruction does not type) is simply absent.
fn element_operand_tys(func: &Function, module: &Module) -> BTreeMap<ValueId, Ty> {
    let mut wanted: BTreeSet<ValueId> = BTreeSet::new();
    for node in func.blocks.iter().flat_map(|block| block.body.iter()) {
        if let Inst::ExtractElement { array, index, .. }
        | Inst::InsertElement { array, index, .. } = &node.inst
        {
            wanted.insert(*array);
            wanted.insert(*index);
        }
    }
    let mut tys = BTreeMap::new();
    if wanted.is_empty() {
        return tys;
    }
    for block in &func.blocks {
        for (value, ty) in &block.params {
            if wanted.contains(value) {
                tys.insert(*value, ty.clone());
            }
        }
        for node in &block.body {
            if node.results.iter().any(|result| wanted.contains(result)) {
                for (result, ty) in node.results.iter().zip(node.result_tys(module)) {
                    if wanted.contains(result) {
                        tys.insert(*result, ty);
                    }
                }
            }
        }
    }
    tys
}

/// The blocks of `func` in which array CONTENT is modeled with SMT arrays
/// (`ChcFuncTranslator::smt_arrays`): every block that no cycle of the CFG reaches
/// — a block ON a cycle reaches itself. The native CHC engine at the pinned ay
/// revision answers Inconclusive for an array term in any clause reachable from a
/// loop, while it decides array terms in an acyclic problem and in the acyclic
/// part before a loop; so the blocks before every loop (all of them, in an acyclic
/// function) model array content and every block a loop reaches carries its
/// arrays shape-only. The set is closed under predecessors: a block whose
/// predecessor is reachable from a cycle is itself.
///
/// A terminator whose successors are not statically known may lead anywhere, a
/// cycle included, so such a function models no array content at all (the empty
/// set). Linear in the CFG: an iterative three-colour DFS finds the back edges —
/// every cycle has one, and its target lies on the cycle — and one forward sweep
/// from their targets marks everything a cycle reaches. A malformed body that
/// repeats a block id is one node (it shares one relation).
fn array_content_blocks(func: &Function) -> BTreeSet<BlockId> {
    let mut slot_of: BTreeMap<BlockId, usize> = BTreeMap::new();
    for block in &func.blocks {
        let next = slot_of.len();
        slot_of.entry(block.id).or_insert(next);
    }
    let nodes = slot_of.len();
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); nodes];
    for block in &func.blocks {
        let Some(terminator) = block.body.last() else {
            continue;
        };
        let mut targets = Vec::new();
        if liveness_terminator_successors(&terminator.inst, &mut targets) {
            return BTreeSet::new();
        }
        let from = slot_of[&block.id];
        for target in targets {
            let Some(&to) = slot_of.get(&target) else {
                return BTreeSet::new();
            };
            successors[from].push(to);
        }
    }
    // 0 = unvisited, 1 = on the DFS stack, 2 = finished.
    let mut colour = vec![0u8; nodes];
    let mut reached_from_cycle = vec![false; nodes];
    let mut frontier: Vec<usize> = Vec::new();
    for root in 0..nodes {
        if colour[root] != 0 {
            continue;
        }
        let mut stack: Vec<(usize, usize)> = vec![(root, 0)];
        colour[root] = 1;
        while let Some((node, next)) = stack.last_mut() {
            let node = *node;
            if let Some(&successor) = successors[node].get(*next) {
                *next += 1;
                match colour[successor] {
                    0 => {
                        colour[successor] = 1;
                        stack.push((successor, 0));
                    }
                    // A back edge: its target is on a cycle.
                    1 if !reached_from_cycle[successor] => {
                        reached_from_cycle[successor] = true;
                        frontier.push(successor);
                    }
                    _ => {}
                }
            } else {
                colour[node] = 2;
                stack.pop();
            }
        }
    }
    while let Some(node) = frontier.pop() {
        for &successor in &successors[node] {
            if !reached_from_cycle[successor] {
                reached_from_cycle[successor] = true;
                frontier.push(successor);
            }
        }
    }
    slot_of.into_iter().filter(|(_, slot)| !reached_from_cycle[*slot]).map(|(id, _)| id).collect()
}

/// Successors blocks of a terminator. An unrecognized terminator is reported via
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

/// The blocks a TERMINATOR can transfer control to, for relation liveness only.
/// Returns `true` for a terminator it does not know.
///
/// Callers pass terminators only (`Inst::is_terminator`): an ordinary
/// instruction hands control to the next instruction of its own block, never to
/// another block. Asking `collect_terminator_successors` about every instruction
/// was the liveness bug: its `_ => true` arm made every block holding an
/// ordinary instruction read every carried value.
///
/// This is a separate function, not a widening of `collect_terminator_successors`,
/// because that one also feeds `promoted_cell_is_definitely_initialized`, a
/// proof-admission predicate that deliberately refuses the terminators listed
/// here; liveness only sizes relations and must not move that decision.
fn liveness_terminator_successors(inst: &Inst, successors: &mut Vec<BlockId>) -> bool {
    match inst {
        // The translation lowers `Invoke` to an unconditional fail-closed error
        // and emits no transition out of it, so these edges only widen liveness;
        // they are listed because they ARE the instruction's edges.
        Inst::Invoke { normal_dest, unwind_dest, .. } => {
            successors.push(*normal_dest);
            successors.push(*unwind_dest);
            false
        }
        // Leave the function (`Resume` unwinds to the caller, `CoroSuspend`
        // returns to the resumer).
        Inst::Resume { .. } | Inst::CoroSuspend { .. } => false,
        other => collect_terminator_successors(other, successors),
    }
}

/// Live-in sets of the relation-carried values `carried`, keyed by block. See
/// `ChcFuncTranslator::compute_live_params` for the equations and the soundness
/// argument.
///
/// Uses are every SSA operand of every instruction (trust-ir's canonical
/// exhaustive walk, so no instruction is ever "not enumerable"); successors come
/// only from terminators. The fixpoint is computed by delta propagation: each
/// `(block, value)` pair enters a live-in set at most once and is then offered to
/// each predecessor once, so the work is `Σ_b |live_in(b)| · |preds(b)|` set
/// operations — proportional to the relation columns it produces, never to
/// blocks × carried values, and independent of how many rounds a round-robin
/// sweep would need.
fn carried_live_in(
    func: &Function,
    carried: &BTreeSet<u32>,
    def_block: &BTreeMap<u32, BlockId>,
    work: &mut ChcTranslationWork,
) -> BTreeMap<BlockId, BTreeSet<u32>> {
    if carried.is_empty() {
        return BTreeMap::new();
    }
    // One slot per distinct block id (a malformed body that repeats an id shares
    // one relation, so its blocks share one slot; the union is conservative).
    let mut slot_of: BTreeMap<BlockId, usize> = BTreeMap::new();
    for block in &func.blocks {
        let next = slot_of.len();
        slot_of.entry(block.id).or_insert(next);
    }
    let slots = slot_of.len();

    // own[B]: B's block params and the carried values B defines.
    let mut own: Vec<BTreeSet<u32>> = vec![BTreeSet::new(); slots];
    for (id, block) in def_block {
        if carried.contains(id)
            && let Some(&slot) = slot_of.get(block)
        {
            own[slot].insert(*id);
        }
    }
    for block in &func.blocks {
        own[slot_of[&block.id]].extend(block.params.iter().map(|(value, _)| value.index()));
    }

    let mut seeds: Vec<Vec<u32>> = vec![Vec::new(); slots];
    let mut succs: Vec<Vec<usize>> = vec![Vec::new(); slots];
    for block in &func.blocks {
        let slot = slot_of[&block.id];
        let mut conservative = false;
        let mut targets = Vec::new();
        for node in &block.body {
            node.inst.visit_value_operands(|value| {
                let id = value.index();
                if carried.contains(&id) && !own[slot].contains(&id) {
                    seeds[slot].push(id);
                }
            });
            if node.inst.is_terminator() {
                conservative |= liveness_terminator_successors(&node.inst, &mut targets);
            }
        }
        if conservative {
            // An unknown terminator may hand control anywhere: assume it reads
            // every carried value it does not itself define.
            seeds[slot].extend(carried.iter().filter(|id| !own[slot].contains(id)));
        }
        // A target outside the function is malformed control flow, which the
        // translation turns into a fail-closed error rule, not a transition.
        succs[slot].extend(targets.iter().filter_map(|target| slot_of.get(target)));
    }

    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); slots];
    for (slot, targets) in succs.iter_mut().enumerate() {
        targets.sort_unstable();
        targets.dedup();
        for &target in targets.iter() {
            preds[target].push(slot);
        }
    }

    let mut live: Vec<BTreeSet<u32>> = vec![BTreeSet::new(); slots];
    let mut pending: std::collections::VecDeque<(usize, Vec<u32>)> =
        std::collections::VecDeque::new();
    for (slot, seed) in seeds.into_iter().enumerate() {
        let delta: Vec<u32> = seed.into_iter().filter(|id| live[slot].insert(*id)).collect();
        if !delta.is_empty() {
            work.live_in_insertions += delta.len() as u64;
            pending.push_back((slot, delta));
        }
    }
    while let Some((slot, delta)) = pending.pop_front() {
        for &pred in &preds[slot] {
            work.live_in_edge_visits += delta.len() as u64;
            let added: Vec<u32> = delta
                .iter()
                .copied()
                .filter(|id| !own[pred].contains(id) && live[pred].insert(*id))
                .collect();
            if !added.is_empty() {
                work.live_in_insertions += added.len() as u64;
                pending.push_back((pred, added));
            }
        }
    }

    slot_of.into_iter().map(|(block, slot)| (block, std::mem::take(&mut live[slot]))).collect()
}

/// The liveness analysis this crate shipped before `carried_live_in`, kept
/// VERBATIM (modulo being a free function) as the differential oracle of the
/// verdict-parity tests. It asks every instruction for terminator successors, so
/// any block holding an ordinary instruction is "conservative" and reads every
/// carried value. Never compiled into production builds.
#[cfg(any(test, feature = "legacy-liveness-oracle"))]
fn legacy_carried_live_in(
    func: &Function,
    param_ids: &BTreeSet<u32>,
    def_block: &BTreeMap<u32, BlockId>,
) -> BTreeMap<BlockId, BTreeSet<u32>> {
    if param_ids.is_empty() {
        return BTreeMap::new();
    }

    let mut direct_uses: BTreeMap<BlockId, BTreeSet<u32>> = BTreeMap::new();
    let mut successors: BTreeMap<BlockId, Vec<BlockId>> = BTreeMap::new();
    let mut block_defs: BTreeMap<BlockId, BTreeSet<u32>> = BTreeMap::new();
    for (&id, &blk) in def_block {
        if param_ids.contains(&id) {
            block_defs.entry(blk).or_default().insert(id);
        }
    }

    for block in &func.blocks {
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
            param_ids.clone()
        } else {
            raw_uses.into_iter().map(|v| v.index()).filter(|id| param_ids.contains(id)).collect()
        };
        for d in &own {
            uses.remove(d);
        }

        direct_uses.insert(block.id, uses);
        successors.insert(block.id, succs);
    }

    let mut live: BTreeMap<BlockId, BTreeSet<u32>> =
        func.blocks.iter().map(|b| (b.id, BTreeSet::new())).collect();

    let mut changed = true;
    while changed {
        changed = false;
        for block in &func.blocks {
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

fn sanitize_name(name: &str) -> String {
    name.chars().map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' }).collect()
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

/// How the CHC value model carries a value of a TRACKABLE composite type.
#[derive(Debug, Clone)]
enum CompositeShape {
    /// A struct, tuple, closure, `()` or EMPTY array: one binding per field.
    Fields(Vec<Ty>),
    /// A non-empty fixed-size array `[elem; len]`: one SMT array per scalar leaf
    /// of `elem` (`ArrayValue`). Nothing about it is sized by `len`.
    Array { elem: Ty, len: u64 },
}

/// The composite shape of `ty`, or `None` when `ty` is not a trackable composite
/// (a scalar, an enum, a fat pointer, or a composite with a non-trackable leaf or
/// over `MAX_AGGREGATE_LEAVES` leaves).
///
/// Trust (#46): a free function (so the recursive block-relation declaration can
/// borrow `&Module` + `&mut vc` as disjoint fields while a `&self.func` block
/// iteration is live). A struct/tuple is trackable when every field is a scalar OR
/// itself a trackable composite; a non-empty array when its element is.
fn composite_shape_of(module: &Module, ty: &Ty) -> Option<CompositeShape> {
    // `aggregate_leaf_count_within` returns `None` unless every leaf bottoms out in
    // a scalar, and bounds the struct-DAG leaf count (see `MAX_AGGREGATE_LEAVES`).
    // An array counts as its element's leaves ONCE, so no length enters it. Over
    // budget ⇒ `None` ⇒ every caller that gates expansion on this function
    // uniformly treats the value as a single opaque scalar (fail closed).
    aggregate_leaf_count_within(module, ty, MAX_AGGREGATE_LEAVES)?;
    if let Some((elem, len)) = nonempty_array_elem(module, ty) {
        return Some(CompositeShape::Array { elem, len });
    }
    immediate_aggregate_field_tys(module, ty).map(CompositeShape::Fields)
}

/// The field types of a trackable struct/tuple/closure/unit/EMPTY-array `ty`.
/// `None` for a scalar, a non-trackable composite and a NON-EMPTY array — an
/// array's lanes are not fields (`composite_shape_of`, `ArrayValue`).
fn aggregate_field_tys_of(module: &Module, ty: &Ty) -> Option<Vec<Ty>> {
    match composite_shape_of(module, ty)? {
        CompositeShape::Fields(fields) => Some(fields),
        CompositeShape::Array { .. } => None,
    }
}

/// `true` iff the value model tracks `ty` as a composite (fields or SMT arrays).
fn is_composite_value_ty(module: &Module, ty: &Ty) -> bool {
    composite_shape_of(module, ty).is_some()
}

/// `(element type, length)` of a NON-EMPTY `Ty::Array`, with no trackability
/// check. An empty array `[T; 0]` has no lane and is the zero-field aggregate.
fn nonempty_array_elem(module: &Module, ty: &Ty) -> Option<(Ty, u64)> {
    let Ty::Array(elem, len) = ty else {
        return None;
    };
    if *len == 0 {
        return None;
    }
    Some((module.types.get(elem.as_usize())?.clone(), *len))
}

/// Does `actual` inhabit `expected` exactly (Bool, bit-vector WIDTH, array index
/// and element sorts)? `Sort` equality alone is not relied on, because AY's
/// equality historically did not always distinguish bit-vector widths.
fn sort_matches(actual: &ay_bindings::Sort, expected: &ay_bindings::Sort) -> bool {
    if expected.is_bool() {
        return actual.is_bool();
    }
    if let Some(width) = expected.bitvec_width() {
        return actual.bitvec_width() == Some(width);
    }
    match (actual.array_sort(), expected.array_sort()) {
        (Some(actual), Some(expected)) => {
            sort_matches(&actual.index_sort, &expected.index_sort)
                && sort_matches(&actual.element_sort, &expected.element_sort)
        }
        _ => false,
    }
}

/// Does `binding` have exactly the shape and leaf sorts a value of `ty` gets,
/// with every scalar leaf lifted through `depth` enclosing arrays? This is the
/// bar an element must clear before it is spliced into an `ArrayValue`, so a
/// mis-sorted term can never reach a relation column.
fn binding_matches_ty_at(module: &Module, binding: &ValueBinding, ty: &Ty, depth: u32) -> bool {
    match (binding, composite_shape_of(module, ty)) {
        (ValueBinding::Scalar(expr), None) => {
            is_scalar_field_ty(ty) && sort_matches(expr.sort(), &lifted_sort(ty_to_sort(ty), depth))
        }
        (ValueBinding::Aggregate(aggregate), Some(CompositeShape::Fields(fields))) => {
            aggregate.fields.len() == fields.len()
                && aggregate
                    .fields
                    .iter()
                    .zip(&fields)
                    .all(|(field, field_ty)| binding_matches_ty_at(module, field, field_ty, depth))
        }
        (ValueBinding::Array(array), Some(CompositeShape::Array { elem, len })) => {
            array.len == len
                && array
                    .lanes
                    .as_ref()
                    .is_none_or(|lanes| binding_matches_ty_at(module, lanes, &elem, depth + 1))
        }
        _ => false,
    }
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
    if is_composite_value_ty(module, ty) {
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
    !is_precise_stack_scalar_ty(ty) && !is_composite_value_ty(module, ty)
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
/// - a composite with a non-trackable leaf, or any type over `MAX_AGGREGATE_LEAVES`
///   (a struct DAG; an array counts its element once) — `aggregate_leaf_count_within`
///   declines, so the translator would model the cell opaquely and there is no binding
///   to thread.
///
/// An array cell of ANY length is promotable here: its binding is one SMT-array column
/// per element leaf (`ArrayValue`), so nothing about it is sized by the length. The
/// proof-authority lanes that consult this predicate (lane 2,
/// `promoted_cell_alloca_reject`; lane 4, `borrowed_block_local_cell_is_admissible`)
/// admit such a cell on the same argument as any other promoted or borrowed cell,
/// whatever its length (decision TMC-2, `docs/DECISION_QUEUE.md`).
fn promotable_cell_ty(module: &Module, ty: &Ty) -> bool {
    is_precise_stack_scalar_ty(ty) || is_composite_value_ty(module, ty)
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
/// `BorrowMut`, or by a thin-pointer `Copy` ([`transparent_pointer_alias`]) — is used
/// across the function.
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

/// The pointer value `inst` binds its single result to UNCHANGED, when `inst` is a
/// transparent alias of one: `ptr` for `Borrow`/`BorrowMut`, `operand` for a `Copy`
/// at a THIN pointer type (`Ptr`, `Ref`, `RefMut`, `PtrConst`, `PtrMut`).
///
/// WHY `Copy` IS HERE. A Rust producer spells every reference it creates as the
/// place's address value or a `Copy` of it, never as a permission instruction
/// (trust-ir `docs/SPEC_RATIFICATIONS.md`, "A Rust reference carries no permission
/// instruction"): the MIR bridge's thin `&place` / `&mut place` is a `Copy` at `Ptr`
/// carrying its `SharedBorrow` / `UniqueBorrow` claim, as its fat reborrow already
/// was. The translator gives both spellings the same value (the operand's resolved
/// address), so every analysis that follows a borrow as an alias must follow the
/// `Copy` the same way, or a Copy-spelled reference costs the precision a
/// Borrow-spelled one had. The claim is not consulted: it has no operational
/// meaning, and an unclaimed thin-pointer `Copy` (`&raw const place`) is the same
/// alias.
///
/// THE SOUNDNESS CONDITION, stated rather than assumed: an analysis that admits an
/// alias through this predicate tracks the alias RESULT's own uses exactly as it
/// tracks the referent's. A call argument, a store of the alias as a VALUE, a block
/// argument, a `Select` operand or any use the analysis does not enumerate is an
/// escape of the referent. `copy_alias_into_a_call_invalidates_the_cell` is the
/// dual that fails if a caller breaks this.
///
/// No permission transition is implied: a `Copy` never touches the permission
/// machine (trust-ir Lean `stepInst_copy_preserves_memory_and_permissions`), so
/// the borrowed-cell lane joins a `Copy` to its alias set without one.
///
/// A `Copy` at a FAT pointer type carries metadata a thin address does not, and a
/// `Copy` at any other type is not a pointer: both answer `None`, so every caller
/// keeps its fail-closed default for them.
pub(crate) fn transparent_pointer_alias(inst: &Inst) -> Option<ValueId> {
    match inst {
        Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => Some(*ptr),
        Inst::Copy { ty, operand } if is_transparent_alias_pointer_ty(ty) => Some(*operand),
        _ => None,
    }
}

/// The thin pointer types at which a `Copy` is a [`transparent_pointer_alias`]. A
/// reference-counted `Rc` is a thin word too, but no Rust producer spells a
/// reference at it, so it keeps its historical (escape) reading here.
fn is_transparent_alias_pointer_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Ptr | Ty::Ref(_) | Ty::RefMut(_) | Ty::PtrConst(_) | Ty::PtrMut(_))
}

/// Whether `inst` is a TRANSPARENT BORROW of promotion candidate `cell` which the
/// translator models exactly and whose derived pointers all stay inside the model.
/// A thin-pointer `Copy` of the cell is the same borrow in the Rust producers'
/// spelling ([`transparent_pointer_alias`]).
///
/// SPLIT OUT FROM THE STEP-2 ARM ON PURPOSE. [`promote_cell_borrows`] is a
/// process-global `OnceLock`, so a test cannot toggle the flag in-process; a
/// tripwire that could only run under an env var is a tripwire that does not run.
/// Keeping the decision here lets `a_borrow_stored_as_a_value_is_still_refused`
/// exercise the real predicate in the DEFAULT lane.
///
/// The escape classification is the load-bearing half — see the call site.
fn borrow_use_is_transparently_promotable(func: &Function, inst: &Inst, cell: ValueId) -> bool {
    transparent_pointer_alias(inst).is_some_and(|referent| referent.index() == cell.index())
        && stack_alloca_escape_classification(func, cell) != StackCellEscape::Unbounded
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
/// instruction outside the {GEP, Borrow, BorrowMut, thin-pointer Copy} closure produces a new pointer from
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
    stack_alloca_escape_classification_with(func, alloca_result, BulkMemoryUse::Escapes)
}

/// How [`stack_alloca_escape_classification_with`] counts a cell address in the
/// `dst`/`src` position of a bulk `MemCopy`/`MemSet`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BulkMemoryUse {
    /// An escape (`Unbounded`): the classification the proof-authority gate and
    /// the promotion analysis use, unchanged.
    Escapes,
    /// A tracked access, like a `Load`/`Store` `ptr`: the CHC translator's own
    /// cell decision, whose bulk arm writes the cell exactly or havocs it.
    Tracked,
}

/// [`stack_alloca_escape_classification`], choosing how a bulk-memory pointer
/// operand counts. Its byte count and fill byte are values in either mode.
pub(crate) fn stack_alloca_escape_classification_with(
    func: &Function,
    alloca_result: ValueId,
    bulk: BulkMemoryUse,
) -> StackCellEscape {
    // Fixpoint over GEP/Borrow derivations (a thin-pointer `Copy` is a borrow in the
    // Rust producers' spelling: `transparent_pointer_alias`). The IR is SSA, but a
    // derivation may be written before the block that defines its base is visited,
    // so iterate to stability rather than assuming a single ordered pass suffices.
    let mut derived: BTreeSet<ValueId> = BTreeSet::new();
    derived.insert(alloca_result);
    loop {
        let mut grew = false;
        for block in &func.blocks {
            for node in &block.body {
                let base = match &node.inst {
                    Inst::GEP { base, .. } => *base,
                    inst => match transparent_pointer_alias(inst) {
                        Some(referent) => referent,
                        None => continue,
                    },
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
                // A thin-pointer `Copy` is a derivation exactly like a borrow: its
                // result joined `derived` above, so its own uses are classified by
                // this same loop. A `Copy` at any other type is not an alias and
                // falls to the fail-closed `_` arm.
                inst @ Inst::Copy { .. } if transparent_pointer_alias(inst).is_some() => {}
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
                // `dst`/`src` are read and written THROUGH, like a `Load`/`Store`
                // `ptr`; a derived pointer as the byte count or fill byte is a value.
                Inst::MemCopy { bytes, .. } if bulk == BulkMemoryUse::Tracked => {
                    if derived.contains(bytes) {
                        return StackCellEscape::Unbounded;
                    }
                }
                Inst::MemSet { byte, bytes, .. } if bulk == BulkMemoryUse::Tracked => {
                    if derived.contains(byte) || derived.contains(bytes) {
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
/// Is `slot`'s address used ONLY as the `ptr` operand of a non-volatile
/// `Load`/`Store` in `func`? — the admission gate for the call-summary
/// interpreter's path-local stack cells.
///
/// This is STRICTLY STRONGER than [`StackCellEscape::Contained`], which also
/// admits `GEP`/`Borrow`/`BorrowMut` derivations because `translate_block` carries
/// a whole interior-pointer provenance model for them. The summary interpreter
/// carries none: it keys a cell by the alloca's own SSA id, so a write through a
/// DERIVED pointer would be invisible to it and the following read would return
/// the pre-store value — a fabricated fact, i.e. a false proof. Refusing every
/// derivation is what makes the id-keyed model exact rather than optimistic.
///
/// Fail-closed in both directions: an instruction whose operands
/// `collect_inst_value_uses` cannot statically enumerate is treated as possibly
/// taking the address, and a `Store` that carries the address as its *value*
/// (rather than its `ptr`) is a leak like any other.
fn call_summary_slot_is_directly_addressed(func: &Function, slot: ValueId) -> bool {
    for block in &func.blocks {
        for node in &block.body {
            // The defining `Alloca` mentions the slot only as its own result.
            if matches!(&node.inst, Inst::Alloca { .. }) && node.results.contains(&slot) {
                continue;
            }
            let addressed_only_as_access_ptr = match &node.inst {
                Inst::Load { ptr, volatile: false, .. } => *ptr == slot,
                Inst::Store { ptr, value, volatile: false, .. } => *ptr == slot && *value != slot,
                _ => false,
            };
            if addressed_only_as_access_ptr {
                continue;
            }
            let mut uses = Vec::new();
            // `true` means this instruction's operands are NOT statically
            // enumerable, so it may read anything in scope — including the slot
            // address. Refuse the slot rather than guess.
            if collect_inst_value_uses(&node.inst, &mut uses) || uses.contains(&slot) {
                return false;
            }
        }
    }
    true
}

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
                                let projectable_aggregate =
                                    candidate_ty.get(&used.index()).is_some_and(|ty| {
                                        matches!(ty, Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_, _))
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
    PointeeNotScalarOrAggregate {
        ty: String,
    },
    /// No `Alloca { count: None, align: None, ty: <exactly this ty> }` in the
    /// function defines this value.
    NoExactDefiningAlloca,
    /// A `Load` through the cell pointer outside the defining block. This is
    /// the clause a cross-block escape analysis would have to replace.
    LoadInOtherBlock {
        block: u32,
        definition_block: u32,
    },
    /// A `Load` in the defining block not preceded there by a `Store`.
    LoadBeforeStore {
        block: u32,
    },
    LoadVolatile {
        block: u32,
    },
    LoadAligned {
        block: u32,
    },
    LoadTypeMismatch {
        block: u32,
        access_ty: String,
        cell_ty: String,
    },
    StoreInOtherBlock {
        block: u32,
        definition_block: u32,
    },
    StoreVolatile {
        block: u32,
    },
    StoreAligned {
        block: u32,
    },
    StoreTypeMismatch {
        block: u32,
        access_ty: String,
        cell_ty: String,
    },
    /// The cell POINTER itself is the stored value — it escaped into memory.
    PointerStoredAsValue {
        block: u32,
    },
    /// An instruction whose operands `collect_inst_value_uses` does not
    /// enumerate appears anywhere in the function; it could read any pointer.
    OpaqueInstruction {
        block: u32,
        inst: String,
    },
    /// The cell pointer is an operand of some instruction other than a direct
    /// `Load`/`Store` through it (a `GEP` base, a `Call` argument, a `Borrow`).
    PointerUsedByInstruction {
        block: u32,
        inst: String,
    },
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
    PointeeNotPreciseScalar {
        ty: String,
    },
    AccessTypeMismatch {
        access: &'static str,
        access_ty: String,
        cell_ty: String,
    },
    PointerStoredAsValue,
    OpaqueInstruction {
        inst: String,
    },
    PointerUsedByInstruction {
        inst: String,
    },
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
    let end =
        rendered.find(|c: char| !c.is_ascii_alphanumeric() && c != '_').unwrap_or(rendered.len());
    rendered[..end].to_string()
}

/// Whether proof-grade native ingestion may admit a metadata-less, single-cell
/// `Alloca` without importing source authority.
///
/// This deliberately mirrors the CHC translator's tracked-versus-opaque split.
/// The first lane (below) is the per-block `stack_cells`
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
/// A third lane admits direct opaque fat-pointer slots across blocks after
/// MUST initialization analysis; each load remains fresh havoc. A fourth lane
/// admits initialized whole-cell Borrow/BorrowMut aliases whose
/// complete use set remains within the defining block; it independently checks
/// initialization, access types and permission transitions for every alias.
/// The caller must first validate the full module's SSA definitions, dominance,
/// types and CFG, as the native proof-authority gate does.
pub fn single_cell_alloca_is_admissible(
    module: &Module,
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> bool {
    single_cell_alloca_rejection(module, function, alloca_result, ty).is_none()
}

/// The reason form of [`single_cell_alloca_is_admissible`]: `None` iff the cell
/// is admitted, otherwise the direct and promoted lanes' first blocking condition.
///
/// This is the sole implementation — the boolean above is defined as
/// `.is_none()` — so a verdict cannot differ between the measured and unmeasured
/// paths. Each later lane runs only after the earlier lanes declined; the
/// borrowed-cell lane adds no diagnostic authority to the rejection reasons.
pub fn single_cell_alloca_rejection(
    module: &Module,
    function: &Function,
    alloca_result: ValueId,
    ty: &Ty,
) -> Option<SingleCellAllocaRejection> {
    let block_local = block_local_alloca_reject(function, alloca_result, ty)?;
    let promoted = promoted_cell_alloca_reject(module, function, alloca_result, ty)?;
    if opaque_fat_pointer_cell_is_admissible(module, function, alloca_result, ty) {
        return None;
    }
    if borrowed_block_local_cell_is_admissible(module, function, alloca_result, ty) {
        return None;
    }
    Some(SingleCellAllocaRejection { block_local, promoted })
}

/// A directly addressed fat-pointer slot needs no value promotion: the CHC
/// translator retains its owned-stack identity across blocks and every opaque
/// load is fresh havoc. Access safety still requires a real allocation, exact
/// whole-cell access types and definite initialization on every CFG path.
/// No address derivation, escape, volatile access or alignment claim is admitted.
fn opaque_fat_pointer_cell_is_admissible(
    module: &Module,
    function: &Function,
    cell: ValueId,
    ty: &Ty,
) -> bool {
    if !matches!(ty, Ty::FatPtr(_)) || !stack_cell_is_translator_opaque(module, ty) {
        return false;
    }
    let mut defined = false;
    for block in &function.blocks {
        for node in &block.body {
            if node.results.contains(&cell) {
                if defined
                    || !matches!(&node.inst, Inst::Alloca { ty: cell_ty, count: None, align: None } if cell_ty == ty)
                {
                    return false;
                }
                defined = true;
            }
            let mut uses = Vec::new();
            if collect_inst_value_uses(&node.inst, &mut uses) {
                return false;
            }
            if !uses.contains(&cell) {
                continue;
            }
            match &node.inst {
                Inst::Load { ty: access_ty, ptr, volatile: false, align: None }
                    if *ptr == cell && access_ty == ty => {}
                Inst::Store { ty: access_ty, ptr, value, volatile: false, align: None }
                    if *ptr == cell && access_ty == ty && *value != cell => {}
                _ => return false,
            }
        }
    }
    defined && promoted_cell_is_definitely_initialized(function, cell.index())
}

/// Initialized whole-cell borrows that stay within the defining block. This
/// lane uses the translator's provenance-aware whole-cell loads and stores; it
/// does not rely on root-id-only definite initialization or alias promotion.
/// Every borrow follows a real exact-type store, and every derived address is
/// used only for another borrow or an unqualified exact-type load/store.
/// Permission transitions are checked independently of value initialization:
/// shared borrows may be repeated but forbid later writes, while a mutable
/// borrow is unique and cannot be reborrowed in this lane. EndBorrow is excluded.
/// A thin-pointer `Copy` of an alias (the Rust producers' spelling of a
/// reference, [`transparent_pointer_alias`]) is an alias with no permission
/// transition. Calls, GEPs, pointer escape and cross-block uses remain outside
/// this lane.
fn borrowed_block_local_cell_is_admissible(
    module: &Module,
    function: &Function,
    cell: ValueId,
    ty: &Ty,
) -> bool {
    // An array cell of any length is tracked in constant size (`promotable_cell_ty`),
    // so its length never decides this lane (decision TMC-2).
    if !promotable_cell_ty(module, ty) {
        return false;
    }
    let mut definitions = function.blocks.iter().filter(|block| {
        block.body.iter().any(|node| {
            node.results.contains(&cell)
                && matches!(&node.inst, Inst::Alloca { ty: cell_ty, count: None, align: None } if cell_ty == ty)
        })
    });
    let Some(definition) = definitions.next() else {
        return false;
    };
    if definitions.next().is_some() {
        return false;
    }

    enum Permission {
        Owned,
        Shared,
        Mutable,
    }
    let mut aliases = BTreeSet::from([cell]);
    let mut defined = false;
    let mut initialized = false;
    let mut permission = Permission::Owned;
    for node in &definition.body {
        if node.results.contains(&cell) {
            if defined
                || !matches!(&node.inst, Inst::Alloca { ty: cell_ty, count: None, align: None } if cell_ty == ty)
            {
                return false;
            }
            defined = true;
            continue;
        }
        let mut uses = Vec::new();
        if collect_inst_value_uses(&node.inst, &mut uses) {
            return false;
        }
        if !uses.iter().any(|value| aliases.contains(value)) {
            continue;
        }
        if !defined {
            return false;
        }
        match &node.inst {
            Inst::Borrow { ptr } | Inst::BorrowMut { ptr }
                if aliases.contains(ptr) && initialized && node.results.len() == 1 =>
            {
                // TrustIR's permission semantics permit Owned -> Mutable and
                // Owned/Shared -> Shared only. Value aliasing alone cannot
                // justify a second mutable borrow, or a shared reborrow of it.
                if matches!(node.inst, Inst::BorrowMut { .. }) {
                    if !matches!(permission, Permission::Owned) {
                        return false;
                    }
                    permission = Permission::Mutable;
                } else {
                    if matches!(permission, Permission::Mutable) {
                        return false;
                    }
                    permission = Permission::Shared;
                }
                if !aliases.insert(node.results[0]) {
                    return false;
                }
            }
            // A thin-pointer `Copy` of an alias is the Rust producers' spelling of a
            // reference (`transparent_pointer_alias`). It joins the alias set with NO
            // permission transition: a `Copy` never touches the permission machine,
            // so it neither takes nor conflicts with a borrow. The cell stays exactly
            // modeled because every alias use is still one of this lane's three
            // forms, all in this block; the soundness dual is
            // `copy_alias_into_a_call_invalidates_the_cell`.
            inst @ Inst::Copy { operand, .. }
                if transparent_pointer_alias(inst).is_some()
                    && aliases.contains(operand)
                    && initialized
                    && node.results.len() == 1 =>
            {
                if !aliases.insert(node.results[0]) {
                    return false;
                }
            }
            Inst::Load { ty: access_ty, ptr, volatile: false, align: None }
                if aliases.contains(ptr) && access_ty == ty && initialized => {}
            Inst::Store { ty: access_ty, ptr, value, volatile: false, align: None }
                if aliases.contains(ptr)
                    && access_ty == ty
                    && !aliases.contains(value)
                    && !matches!(permission, Permission::Shared) =>
            {
                initialized = true;
            }
            _ => return false,
        }
    }
    // Scan after collecting the whole local alias set, so block storage order
    // cannot hide an alias use in an earlier-listed successor or predecessor.
    for block in &function.blocks {
        if block.id == definition.id {
            continue;
        }
        for node in &block.body {
            let mut uses = Vec::new();
            if collect_inst_value_uses(&node.inst, &mut uses)
                || uses.iter().any(|value| aliases.contains(value))
            {
                return false;
            }
        }
    }
    // The lane is for a cell reached through at least one ALIAS (a borrow, or a
    // Copy-spelled reference). Before Copy-spelled references this read "not
    // `Owned`", which is the same condition while every alias was a borrow.
    defined && aliases.len() > 1
}

/// Whether a borrow operand belongs to an initialized, block-local whole-cell
/// alias family that the CHC translator models exactly. Native proof admission
/// uses this same structural check for the Borrow/BorrowMut instruction as for
/// its Alloca; no public validity annotation or rollout flag supplies a fact.
pub fn initialized_local_borrow_is_admissible(
    module: &Module,
    function: &Function,
    operand: ValueId,
) -> bool {
    let mut current = operand;
    let mut visited = BTreeSet::new();
    while visited.insert(current) {
        let mut definitions = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .filter(|node| node.results.contains(&current));
        let Some(definition) = definitions.next() else {
            return false;
        };
        if definitions.next().is_some() {
            return false;
        }
        match &definition.inst {
            Inst::Alloca { ty, .. } => {
                return borrowed_block_local_cell_is_admissible(module, function, current, ty);
            }
            // A borrow, or a Copy-spelled reference (`transparent_pointer_alias`).
            inst => match transparent_pointer_alias(inst) {
                Some(referent) => current = referent,
                None => return false,
            },
        }
    }
    false
}

/// Why the native proof-authority gate refuses one `ExtractElement`, or a `Call` that
/// would fold one into its caller (decision TMC-1, `docs/DECISION_QUEUE.md`).
/// Produced only by [`ProofGradeElementReads::rejection`] and
/// [`ProofGradeElementReads::call_rejection`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExtractElementReject {
    /// The array operand has no declared type in its function (no block parameter or
    /// typed instruction result defines it), so the read has no length to state its
    /// bounds obligation with.
    UntypedArray,
    /// The array operand's declared type is not a non-empty fixed-size array whose
    /// element the SMT-array model tracks: a SIMD vector or a sequence (the translator
    /// reads either as a fresh value, not a `select` of modeled lanes), an empty
    /// array, or an array whose element is not trackable (`composite_shape_of`, which
    /// still bounds an element's leaf count by `MAX_AGGREGATE_LEAVES` and its nesting
    /// by `AGGREGATE_LEAF_WALK_DEPTH` until the datatype-sort work retires them).
    NotAnSmtArray { ty: Ty },
    /// The result type is not exactly the array's element type. trust-ir's validator
    /// lets a refinement stand on either side (`decided_by_the_consumption_rule`), but
    /// the translator reads such a mismatch as a fresh value, not a `select`.
    ElementTypeMismatch { element: Ty, result: Ty },
    /// The index operand's declared type is not an integer type, so which lane its
    /// bits name is not known (the translator's `UnmodeledElementIndex`).
    UnmodeledIndex,
    /// The read is in a block that a cycle of the CFG reaches, where the translator
    /// carries every array SHAPE-ONLY (its length, not its lanes; see `ArrayValue`):
    /// the read would be a fresh value, not a `select` of the modeled lanes.
    ShapeOnlyArray,
    /// A `Call`, in a block a cycle of the CFG reaches, of a callee whose summarized
    /// body reads an array element (`ElementReadingFunctions`). The caller folds the
    /// callee's body into the call's block (`try_direct_call_summary`), where it
    /// carries every array shape-only, so the callee's read would be a fresh value,
    /// not a `select` of modeled lanes: the `ShapeOnlyArray` refusal, at the call
    /// site that places the read there.
    ShapeOnlyArrayInCallee { callee: String },
}

impl ExtractElementReject {
    pub fn kind(&self) -> &'static str {
        match self {
            Self::UntypedArray => "untyped_array",
            Self::NotAnSmtArray { .. } => "not_an_smt_array",
            Self::ElementTypeMismatch { .. } => "element_type_mismatch",
            Self::UnmodeledIndex => "unmodeled_index",
            Self::ShapeOnlyArray => "shape_only_array",
            Self::ShapeOnlyArrayInCallee { .. } => "shape_only_array_in_callee",
        }
    }
}

impl std::fmt::Display for ExtractElementReject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotAnSmtArray { ty } => write!(f, "{}(ty={ty})", self.kind()),
            Self::ElementTypeMismatch { element, result } => {
                write!(f, "{}(element={element}, result={result})", self.kind())
            }
            Self::ShapeOnlyArrayInCallee { callee } => {
                write!(f, "{}(callee=`{callee}`)", self.kind())
            }
            other => write!(f, "{}", other.kind()),
        }
    }
}

/// The functions of a module whose SUMMARIZED body can read an array element
/// (decision TMC-1): every function with an `ExtractElement`, and every function
/// that reaches one through direct `Call` edges — the edges
/// `try_direct_call_summary` follows when it folds a nested callee into the same
/// call site. Built once per module: one pass over every instruction to collect the
/// readers and the reverse call edges, then one worklist sweep up those edges, so
/// the cost is linear in the module's size (log-factor maps) whatever the shape of
/// its call graph, cycles included.
#[derive(Debug, Clone)]
pub struct ElementReadingFunctions {
    reading: BTreeSet<FuncId>,
}

impl ElementReadingFunctions {
    pub fn new(module: &Module) -> Self {
        let mut reading: BTreeSet<FuncId> = BTreeSet::new();
        let mut callers: BTreeMap<FuncId, Vec<FuncId>> = BTreeMap::new();
        for function in &module.functions {
            for node in function.blocks.iter().flat_map(|block| block.body.iter()) {
                match &node.inst {
                    Inst::ExtractElement { .. } => {
                        reading.insert(function.id);
                    }
                    Inst::Call { callee, .. } => {
                        callers.entry(*callee).or_default().push(function.id);
                    }
                    _ => {}
                }
            }
        }
        let mut frontier: Vec<FuncId> = reading.iter().copied().collect();
        while let Some(callee) = frontier.pop() {
            for caller in callers.get(&callee).into_iter().flatten() {
                if reading.insert(*caller) {
                    frontier.push(*caller);
                }
            }
        }
        Self { reading }
    }

    /// Whether `function`'s summarized body can read an array element.
    pub fn reads(&self, function: FuncId) -> bool {
        self.reading.contains(&function)
    }
}

/// The native proof-authority gate's view of the array element READS of one
/// function (decision TMC-1): the translator's own `element_operand_tys` and
/// `array_content_blocks`, each one linear pass over the function, computed once
/// per function, and each distinct array type's shape decided once — so gating
/// every read of a function is linear in its size, never a re-walk per read.
///
/// An `ExtractElement { ty, array, index }` in block `block` is admitted exactly
/// when
///
/// 1. `array`'s DECLARED type is a non-empty fixed-size array the value model
///    tracks (`composite_shape_of` is `CompositeShape::Array`);
/// 2. `ty` is exactly that array's element type;
/// 3. `index`'s declared type is an integer type; and
/// 4. `block` is one where array content is modeled: no cycle of the CFG reaches
///    it (`array_content_blocks`).
///
/// Those are the reads `ChcFuncTranslator::translate_extract_element` models as
/// the exact `select(lanes, index)` — the lanes of the operand's binding in the
/// block or, for an operand with none, fresh lanes of its declared type recorded
/// so every read of it agrees — under the access's OWN in-bounds obligation
/// (`discharge_element_bounds`): with memory checks on, as the proof-grade lane
/// requires, an error rule where the index is out of bounds as its declared
/// signedness reads it (`array_lane_access`, trust-ir `runtime_index`), after which
/// the block's path continues only in bounds. The same read inside a callee that a
/// caller summarizes carries the same obligation and reads the same `select`
/// (`try_direct_call_summary`'s `ExtractElement` arm) wherever the call's block
/// models array content; a call in a block a cycle reaches, of a callee that reads
/// an element, is refused at the call ([`Self::call_rejection`]). Every other read
/// fails closed at the gate: a vector or sequence read is a fresh value, an index
/// of unknown signedness is `UnmodeledElementIndex`, and a read in a block a cycle
/// reaches is a fresh value of a shape-only array.
///
/// The caller must first validate the full module, as the gate does.
#[derive(Debug, Clone)]
pub struct ProofGradeElementReads<'m> {
    module: &'m Module,
    operand_tys: BTreeMap<ValueId, Ty>,
    content_blocks: BTreeSet<BlockId>,
    /// Each array operand type's element type when it is an SMT-modeled array, else
    /// `None`; filled on the type's first read, so `composite_shape_of` runs once
    /// per distinct type, never once per read.
    element_tys: std::collections::HashMap<Ty, Option<Ty>>,
}

impl<'m> ProofGradeElementReads<'m> {
    /// The view of `function`'s element reads, from the translator's own analyses.
    pub fn new(module: &'m Module, function: &Function) -> Self {
        Self {
            module,
            operand_tys: element_operand_tys(function, module),
            content_blocks: array_content_blocks(function),
            element_tys: std::collections::HashMap::new(),
        }
    }

    /// Why the gate refuses `ExtractElement { ty: result_ty, array, index }` in
    /// `block`, or `None` when it is admitted (see the type's documentation).
    pub fn rejection(
        &mut self,
        block: BlockId,
        result_ty: &Ty,
        array: ValueId,
        index: ValueId,
    ) -> Option<ExtractElementReject> {
        let Some(array_ty) = self.operand_tys.get(&array) else {
            return Some(ExtractElementReject::UntypedArray);
        };
        let module = self.module;
        let element = self.element_tys.entry(array_ty.clone()).or_insert_with(|| {
            match composite_shape_of(module, array_ty) {
                Some(CompositeShape::Array { elem, .. }) => Some(elem),
                _ => None,
            }
        });
        let Some(element) = element else {
            return Some(ExtractElementReject::NotAnSmtArray { ty: array_ty.clone() });
        };
        if element != result_ty {
            return Some(ExtractElementReject::ElementTypeMismatch {
                element: element.clone(),
                result: result_ty.clone(),
            });
        }
        if !self.operand_tys.get(&index).is_some_and(Ty::is_integer) {
            return Some(ExtractElementReject::UnmodeledIndex);
        }
        if !self.content_blocks.contains(&block) {
            return Some(ExtractElementReject::ShapeOnlyArray);
        }
        None
    }

    /// Why the gate refuses a `Call` of `callee` in `block`, or `None` when it is
    /// admitted as far as element reads go: refused exactly when `block` is one a
    /// cycle of the CFG reaches and `callee`'s summarized body reads an array
    /// element (`readers`), since the summary would read it where this function
    /// carries arrays shape-only ([`ExtractElementReject::ShapeOnlyArrayInCallee`]).
    pub fn call_rejection(
        &self,
        block: BlockId,
        callee: &Function,
        readers: &ElementReadingFunctions,
    ) -> Option<ExtractElementReject> {
        (!self.content_blocks.contains(&block) && readers.reads(callee.id))
            .then(|| ExtractElementReject::ShapeOnlyArrayInCallee { callee: callee.name.clone() })
    }
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
    // A fat pointer is also a fixed-size value that can occupy one stack slot.
    // Its value stays opaque in the translator: every load is fresh havoc,
    // never a fabricated data/metadata pair. Admission only establishes the
    // slot's access safety; the exact-type, initialization, same-block and
    // non-escape checks below remain mandatory. Pointee accesses and metadata
    // operations retain their independent native proof-authority gates.
    if !is_precise_stack_scalar_ty(ty) && !aggregate && !matches!(ty, Ty::FatPtr(_)) {
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
    let widen = *WIDEN.get_or_init(|| std::env::var_os("TRUST_ALLOCA_ESCAPE_GATE_WIDEN").is_some());
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
        // An EMPTY array has no lane and no data: the zero-field aggregate, like
        // `()`. A non-empty array is NOT a field aggregate — its lanes are SMT
        // arrays over the element's leaves (`CompositeShape::Array`), so nothing
        // here is ever sized by its length.
        Ty::Array(_, 0) => Some(Vec::new()),
        // A first-class closure is an aggregate of its CAPTURES, in capture order
        // (the `func` slot is not a field). This mirrors the interpreter
        // (`InterpretValueKind::Closure { captures }`) and the module validator's
        // `validate_field_access` closure arm EXACTLY, so `ExtractField`/
        // `InsertField` on a closure env project a consistent capture symbol
        // instead of poisoning the function's shared ERROR relation. Captures that
        // are themselves non-trackable make the enclosing `aggregate_leaf_count_within`
        // check fall back to opaque/fail-closed — sound, just not proved.
        Ty::Closure(id) => Some(module.closure_type(*id)?.captures.clone()),
        Ty::Enum(_) => dataless_enum::tag_type(module, ty).map(|tag| vec![tag]),
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
    aggregate_leaf_count_within_depth(module, ty, budget, AGGREGATE_LEAF_WALK_DEPTH)
}

/// Depth guard for [`aggregate_leaf_count_within`]. The leaf BUDGET alone cannot
/// terminate the walk on a CYCLIC type table (a struct whose field chain reaches
/// itself): in a pure cycle no scalar leaf is ever reached, so `total` never
/// advances and the budget short-circuit never fires — measured as an unbounded
/// `aggregate_leaf_count_within` recursion (SIGBUS stack overflow) on ny-cert's
/// recursive arena types. Exceeding the depth answers `None` — "not a trackable
/// aggregate" — which every caller already treats as the fail-closed
/// opaque/havoc path; a missed promotion, never a wrong one. The cap is far
/// above any genuine trackable nesting (the budget bounds real leaf counts long
/// before 64 levels).
const AGGREGATE_LEAF_WALK_DEPTH: u32 = 64;

fn aggregate_leaf_count_within_depth(
    module: &Module,
    ty: &Ty,
    budget: usize,
    depth: u32,
) -> Option<usize> {
    // This slice admits only top-level register enum carriers. A one-field
    // addition must not silently enable enums nested in tuples/structs/arrays.
    if matches!(ty, Ty::Enum(_)) && depth != AGGREGATE_LEAF_WALK_DEPTH {
        return None;
    }
    let depth = depth.checked_sub(1)?;
    // Mirror `declare_relation_binding_rec`'s precedence: a part that is itself a
    // trackable (within-budget) composite is expanded; otherwise it is one scalar
    // leaf — but only if it is a valid scalar, else the parent is not trackable.
    let part_leaves =
        |part: &Ty| match aggregate_leaf_count_within_depth(module, part, budget, depth) {
            Some(count) => Some(count),
            None if is_scalar_field_ty(part) => Some(1),
            None => None,
        };
    // A non-empty array is ONE SMT array per leaf of its element: the element's
    // leaf count, counted once, whatever the length.
    if let Some((elem, _len)) = nonempty_array_elem(module, ty) {
        return part_leaves(&elem).filter(|leaves| *leaves <= budget);
    }
    let fields = immediate_aggregate_field_tys(module, ty)?;
    let mut total = 0usize;
    for field in &fields {
        total = total.saturating_add(part_leaves(field)?);
        if total > budget {
            return None;
        }
    }
    Some(total)
}

/// `true` iff some rule of `vc` asserts SMT equality or disequality between two
/// ARRAY-sorted terms — the hypothesis the junk-lane invariant on `ArrayValue`
/// forbids, because two arrays that agree on `[0, len)` may still differ on
/// their junk lanes. Linear in the rule DAGs: a shared subterm is visited once.
#[cfg(test)]
pub(crate) fn vc_equates_array_terms(vc: &ChcVc) -> bool {
    vc_equates_array_terms_beyond(vc, &BTreeSet::new(), &BTreeSet::new())
}

/// `vc_equates_array_terms` of a translation, admitting its large-block column
/// definitions (`LargeBlockMap::columns`).
#[cfg(test)]
pub(crate) fn output_equates_array_terms(output: &ChcTranslationOutput) -> bool {
    let columns = output.large_block.as_ref().map(|map| map.columns.clone()).unwrap_or_default();
    vc_equates_array_terms_beyond(&output.vc, &BTreeSet::new(), &columns)
}

/// `vc_equates_array_terms`, admitting the DEFINITIONAL lane equalities of a flat
/// array literal (`define_array_lanes`): `select(L, k) = e` where `L` is one of
/// `definitional` (a fresh lane variable) and `k` a constant — each `(L, k)`
/// defined at most once, which is what makes it definitional; a second one is
/// reported. Also admits `c = t` with `c` one of `columns`, a large-block
/// definitional variable (`LargeBlockMap::columns`): a fresh variable the
/// encoding defines by ONE unconditional equality — a second equality with the
/// same variable on its left would be a hypothesis on two array terms, and is
/// reported. Walks every term of every rule: body constraints, the body
/// relation's arguments and the head's arguments.
pub(crate) fn vc_equates_array_terms_beyond(
    vc: &ChcVc,
    definitional: &BTreeSet<String>,
    columns: &BTreeSet<String>,
) -> bool {
    let mut seen: BTreeSet<*const ay_bindings::ExprValue> = BTreeSet::new();
    let mut defined: BTreeSet<(String, String)> = BTreeSet::new();
    let mut defined_columns: BTreeSet<&str> = BTreeSet::new();
    let mut stack: Vec<&Expr> = Vec::new();
    for rule in &vc.rules {
        stack.extend(rule.body.constraints.iter());
        if let Some(app) = &rule.body.relation {
            stack.extend(app.args.iter());
        }
        stack.extend(rule.head.args.iter());
    }
    while let Some(expr) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(expr.value())) {
            continue;
        }
        match expr.value() {
            ay_bindings::ExprValue::Eq(left, right)
                if left.sort().is_array()
                    && matches!(left.value(), ay_bindings::ExprValue::Var { name } if columns.contains(name)) =>
            {
                // A large-block definition: once per variable; walk only the
                // defining term.
                if let ay_bindings::ExprValue::Var { name } = left.value()
                    && !defined_columns.insert(name.as_ref())
                {
                    return true;
                }
                stack.push(right);
                continue;
            }
            ay_bindings::ExprValue::Eq(left, _) if left.sort().is_array() => {
                let lane = match left.value() {
                    ay_bindings::ExprValue::Select { array, index } => {
                        match (array.value(), index.value()) {
                            (
                                ay_bindings::ExprValue::Var { name },
                                ay_bindings::ExprValue::BitVecConst { value, .. },
                            ) if definitional.contains(name) => {
                                Some((name.clone(), value.to_string()))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let Some(lane) = lane else {
                    return true;
                };
                if !defined.insert(lane) {
                    return true;
                }
            }
            ay_bindings::ExprValue::Distinct(terms)
                if terms.iter().any(|term| term.sort().is_array()) =>
            {
                return true;
            }
            _ => {}
        }
        stack.extend(expr.children());
    }
    false
}

/// `binding` with the part at constant lane `path` replaced by `new`: a field of
/// an aggregate, or — through an array — a `select` of the lane, updated in
/// place, `store`d back. A shape-only array absorbs the write, as
/// `ArrayValue::store` does (its content is unconstrained anyway; the caller has
/// checked the path against the cell's TYPE). `None` when the path does not fit
/// the shape. Each level copies only the parts it keeps, so the cost is the
/// binding's size plus the path's length, not their product.
fn update_binding_lane(
    binding: &ValueBinding,
    path: &[usize],
    new: ValueBinding,
) -> Option<ValueBinding> {
    let Some((&first, rest)) = path.split_first() else {
        return Some(new);
    };
    match binding {
        ValueBinding::Aggregate(aggregate) => {
            let child = aggregate.fields.get(first)?;
            let updated = update_binding_lane(child, rest, new)?;
            let mut fields = Vec::with_capacity(aggregate.fields.len());
            let mut updated = Some(updated);
            for (index, field) in aggregate.fields.iter().enumerate() {
                fields.push(if index == first { updated.take()? } else { field.clone() });
            }
            Some(ValueBinding::Aggregate(AggregateValue { fields }))
        }
        ValueBinding::Array(array) if array.lanes.is_none() => Some(binding.clone()),
        ValueBinding::Array(array) => {
            let lane = Expr::bitvec_const(u64::try_from(first).ok()?, 64);
            let updated = update_binding_lane(&array.select(&lane)?, rest, new)?;
            Some(ValueBinding::Array(array.store(&lane, &updated)?))
        }
        ValueBinding::Scalar(_) => None,
    }
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
    smt_arrays: bool,
    arg_sorts: &mut Vec<ay_bindings::Sort>,
) -> ValueBinding {
    declare_relation_binding_lifted(module, vc, prefix, ty, 0, smt_arrays, arg_sorts)
}

/// `declare_relation_binding_rec` for a value nested inside `depth` arrays: every
/// scalar leaf is declared at its sort lifted through those arrays, so a
/// `[e; n]` column is one `(Array BV64 S)` variable per leaf of `e` — never one
/// per lane. With `smt_arrays` off (a block a cycle of the CFG reaches) an array
/// is shape-only and declares no column at all.
fn declare_relation_binding_lifted(
    module: &Module,
    vc: &mut ChcVc,
    prefix: &str,
    ty: &Ty,
    depth: u32,
    smt_arrays: bool,
    arg_sorts: &mut Vec<ay_bindings::Sort>,
) -> ValueBinding {
    match composite_shape_of(module, ty) {
        Some(CompositeShape::Fields(field_tys)) => {
            let mut fields = Vec::with_capacity(field_tys.len());
            for (field_index, field_ty) in field_tys.iter().enumerate() {
                fields.push(declare_relation_binding_lifted(
                    module,
                    vc,
                    &format!("{prefix}_field{field_index}"),
                    field_ty,
                    depth,
                    smt_arrays,
                    arg_sorts,
                ));
            }
            ValueBinding::Aggregate(AggregateValue { fields })
        }
        Some(CompositeShape::Array { len, .. }) if !smt_arrays => {
            ValueBinding::Array(ArrayValue::shape_only(len))
        }
        Some(CompositeShape::Array { elem, len }) => ValueBinding::Array(ArrayValue {
            len,
            lanes: Some(Box::new(declare_relation_binding_lifted(
                module,
                vc,
                &format!("{prefix}_lanes"),
                &elem,
                depth + 1,
                smt_arrays,
                arg_sorts,
            ))),
        }),
        None => {
            let sort = lifted_sort(ty_to_sort(ty), depth);
            arg_sorts.push(sort.clone());
            ValueBinding::Scalar(vc.declare_var(prefix.to_string(), sort))
        }
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

/// Trust (2026-09-14): the ALLOW-LIST fence of `try_self_call_inductive_hypothesis`
/// (c). Every instruction kind not listed — including any variant added to
/// `Inst` later — refuses. Every `Store` must write through a pointer derived
/// from this function's own `Alloca`s (through `GEP`/`Copy`/pointer-to-pointer
/// casts), so a deeper activation of the same body cannot clobber this
/// activation's tracked cells: with pointer-free parameters it holds no pointer
/// INTO this frame, and with no forged, global, fat or heap pointer it can write
/// nowhere but its own frame.
fn self_call_body_is_frame_local(func: &Function) -> bool {
    let mut frame_ptrs: BTreeSet<ValueId> = BTreeSet::new();
    // Fixpoint over pointer derivations (SSA, but a derivation may precede the
    // block that defines its base in emission order).
    loop {
        let before = frame_ptrs.len();
        for block in &func.blocks {
            for node in &block.body {
                let Some(result) = node.results.first().copied() else { continue };
                let derived = match &node.inst {
                    Inst::Alloca { .. } => true,
                    Inst::GEP { base, .. } => frame_ptrs.contains(base),
                    Inst::Copy { operand, .. } => frame_ptrs.contains(operand),
                    Inst::Cast { op: CastOp::PtrToPtr | CastOp::Bitcast, operand, .. } => {
                        frame_ptrs.contains(operand)
                    }
                    _ => false,
                };
                if derived {
                    frame_ptrs.insert(result);
                }
            }
        }
        if frame_ptrs.len() == before {
            break;
        }
    }
    func.blocks.iter().flat_map(|b| b.body.iter()).all(|node| match &node.inst {
        Inst::Store { ptr, .. } => frame_ptrs.contains(ptr),
        Inst::Cast { op, .. } => !matches!(op, CastOp::IntToPtr),
        // Complete field construction is pure, like InsertField below. This
        // effect fence grants no operand-definedness or value-model fact;
        // the ordinary constructor/actual-transport guards still check those.
        Inst::MakeAggregate { ty: Ty::Struct(_) | Ty::Tuple(_), variant: None, .. } => true,
        Inst::BinOp { .. }
        | Inst::UnOp { .. }
        | Inst::Overflow { .. }
        | Inst::ICmp { .. }
        | Inst::FCmp { .. }
        | Inst::Load { .. }
        | Inst::Alloca { .. }
        | Inst::GEP { .. }
        | Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Call { .. }
        | Inst::Return { .. }
        | Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        // v50 `[value; n]`: a pure value construction, no memory write.
        | Inst::ArraySplat { .. }
        | Inst::Const { .. }
        | Inst::NullPtr
        | Inst::Undef { .. }
        | Inst::Assume { .. }
        | Inst::Assert { .. }
        | Inst::Unreachable
        | Inst::Copy { .. }
        | Inst::Select { .. } => true,
        _ => false,
    })
}

fn is_call_summary_scalar_ty(ty: &Ty) -> bool {
    // A pointer is modeled opaquely (it is never dereferenced precisely in the
    // summary — a `ValidBorrow` Load havocs the loaded value), so a reference
    // parameter such as `&[u32; N]` is a trackable call-summary value.
    is_precise_stack_scalar_ty(ty) || matches!(ty, Ty::Ptr)
}

fn call_summary_value(
    values: &BTreeMap<ValueId, CallSummaryBinding>,
    value: ValueId,
    ty: &Ty,
) -> Option<CallSummaryBinding> {
    if let CallSummaryBinding::Uninit(actual) = values.get(&value)? {
        return (actual == ty).then(|| CallSummaryBinding::Uninit(actual.clone()));
    }
    if let Ty::FatPtr(kind) = ty {
        return match values.get(&value)? {
            CallSummaryBinding::OpaqueFatPtr(actual) if actual == kind => {
                Some(CallSummaryBinding::OpaqueFatPtr(*kind))
            }
            _ => None,
        };
    }
    if is_call_summary_scalar_ty(ty) {
        return Some(CallSummaryBinding::Scalar(call_summary_scalar(values, value)?));
    }
    // A non-empty array carries its SMT-array lanes; every other composite its
    // fields. The binding VARIANT must match the declared type, so a wrongly-shaped
    // term never enters the callee model.
    if is_nonempty_array_ty(ty) {
        return match values.get(&value)? {
            CallSummaryBinding::Array(array) => Some(CallSummaryBinding::Array(array.clone())),
            _ => None,
        };
    }

    Some(CallSummaryBinding::Aggregate(call_summary_aggregate(values, value)?))
}

/// `true` for `[T; n]` with `n >= 1` — the types whose value is SMT-array lanes
/// rather than fields.
fn is_nonempty_array_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Array(_, len) if *len > 0)
}

fn call_summary_binding_matches_type(ty: &Ty, binding: &CallSummaryBinding) -> bool {
    match binding {
        CallSummaryBinding::Uninit(actual) => actual == ty,
        CallSummaryBinding::OpaqueFatPtr(kind) => {
            matches!(ty, Ty::FatPtr(actual) if actual == kind)
        }
        CallSummaryBinding::Scalar(_) => is_call_summary_scalar_ty(ty),
        CallSummaryBinding::Aggregate(_) => {
            !is_call_summary_scalar_ty(ty)
                && !matches!(ty, Ty::FatPtr(_))
                && !is_nonempty_array_ty(ty)
        }
        CallSummaryBinding::Array(array) => {
            matches!(ty, Ty::Array(_, len) if *len == array.len && *len > 0)
        }
    }
}

fn call_summary_scalar(
    values: &BTreeMap<ValueId, CallSummaryBinding>,
    value: ValueId,
) -> Option<Expr> {
    match values.get(&value)? {
        CallSummaryBinding::Scalar(expr) => Some(expr.clone()),
        CallSummaryBinding::Aggregate(_)
        | CallSummaryBinding::Uninit(_)
        | CallSummaryBinding::OpaqueFatPtr(_)
        | CallSummaryBinding::Array(_) => None,
    }
}

fn call_summary_aggregate(
    values: &BTreeMap<ValueId, CallSummaryBinding>,
    value: ValueId,
) -> Option<CallSummaryAggregate> {
    match values.get(&value)? {
        CallSummaryBinding::Scalar(_)
        | CallSummaryBinding::Uninit(_)
        | CallSummaryBinding::OpaqueFatPtr(_)
        | CallSummaryBinding::Array(_) => None,
        CallSummaryBinding::Aggregate(aggregate) => Some(aggregate.clone()),
    }
}

fn call_summary_bool(
    values: &BTreeMap<ValueId, CallSummaryBinding>,
    value: ValueId,
) -> Option<Expr> {
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
) -> Option<Vec<CallSummaryBinding>> {
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
    then_value: &CallSummaryBinding,
    else_value: CallSummaryBinding,
) -> Option<CallSummaryBinding> {
    match (then_value, else_value) {
        (CallSummaryBinding::Uninit(then_ty), CallSummaryBinding::Uninit(else_ty))
            if *then_ty == else_ty =>
        {
            Some(CallSummaryBinding::Uninit(else_ty))
        }
        (
            CallSummaryBinding::OpaqueFatPtr(then_kind),
            CallSummaryBinding::OpaqueFatPtr(else_kind),
        ) if *then_kind == else_kind => {
            // Both concrete results inhabit this fat-pointer kind. Forget their
            // identity and the selection; no content or equality fact is needed
            // to transport an opaque value through the caller.
            Some(CallSummaryBinding::OpaqueFatPtr(else_kind))
        }
        (CallSummaryBinding::Scalar(then_expr), CallSummaryBinding::Scalar(else_expr)) => {
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
            Expr::try_ite(guard, then_expr.clone(), else_expr).ok().map(CallSummaryBinding::Scalar)
        }
        (
            CallSummaryBinding::Aggregate(then_aggregate),
            CallSummaryBinding::Aggregate(else_aggregate),
        ) if then_aggregate.fields.len() == else_aggregate.fields.len() => {
            // Trust (#46): recurse so nested-aggregate fields are merged field-by-
            // field (not `ite`'d as if they were scalars).
            let mut fields = Vec::with_capacity(then_aggregate.fields.len());
            for (then_field, else_field) in then_aggregate.fields.iter().zip(else_aggregate.fields)
            {
                fields.push(combine_call_summary_binding(guard.clone(), then_field, else_field)?);
            }
            Some(CallSummaryBinding::Aggregate(CallSummaryAggregate { fields }))
        }
        // Two paths' arrays merge lane-for-lane: `ite` on each SMT-array leaf (a
        // whole-array `ite`, never an equality between arrays).
        (CallSummaryBinding::Array(then_array), CallSummaryBinding::Array(else_array))
            if then_array.len == else_array.len =>
        {
            let lanes = match (&then_array.lanes, else_array.lanes) {
                (Some(then_lanes), Some(else_lanes)) => {
                    Some(Box::new(combine_call_summary_binding(guard, then_lanes, *else_lanes)?))
                }
                (None, None) => None,
                _ => return None,
            };
            Some(CallSummaryBinding::Array(CallSummaryArray { len: then_array.len, lanes }))
        }
        _ => None,
    }
}

fn bind_call_summary_result(
    values: &mut BTreeMap<ValueId, CallSummaryBinding>,
    node: &InstrNode,
    binding: CallSummaryBinding,
) -> Option<()> {
    values.insert(*node.results.first()?, binding);
    Some(())
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
    let newtype_path_of = |ty: &Ty| pointer_newtype_field_path(ty, module, POINTER_NEWTYPE_FUEL);
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
        CastOp::PtrToInt => is_thin_pointer_ty(src_ty) && is_pointer_width_unsigned_ty(dst_ty),
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
/// * `FatPtr(ContainerLen)` — the metadata IS a length (of the DST at the container's
///   tail), but the kind carries no element type, so non-ZST-ness cannot be decided:
///   NOT bounded.
/// * `FatPtr(TraitObject | ContainerVtable)` — the metadata is an opaque VTABLE WORD,
///   not a length at all (`fat_ptr_metadata_is_vtable_word`): nothing to bound.
/// * anything else — an element the module's type table cannot resolve, or a non-fat
///   `ptr_ty` spelling — is NOT bounded (fail-closed).
///
/// The fat-pointer kinds are matched EXHAUSTIVELY so a kind added to trust-ir later
/// must decide its bound here rather than inheriting `false` silently.
fn fat_ptr_metadata_len_is_isize_bounded(module: &Module, ptr_ty: &Ty) -> bool {
    let Ty::FatPtr(kind) = ptr_ty else {
        return false;
    };
    // No wildcard inside: a sixth kind is a compile error here, not a silent `false`.
    match kind {
        FatPtrKind::Str => true,
        FatPtrKind::Slice(elem) => module
            .ty(*elem)
            .is_some_and(|elem| ty_is_definitely_non_zst(module, elem, NON_ZST_FUEL)),
        FatPtrKind::ContainerLen | FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable => {
            false
        }
    }
}

/// Whether the metadata word of a fat pointer of type `ptr_ty` is an OPAQUE VTABLE
/// WORD rather than a length.
///
/// This is trust-ir's own classification (`FatPtrKind` docs and
/// `PointerMetadataShape::metadata_ty`): `TraitObject` and its v40 `dyn`-tail
/// container sibling `ContainerVtable` carry a vtable pointer; `Slice`, `Str` and
/// `ContainerLen` carry an unsigned length. It is decided by what the metadata
/// MEANS, never by the `metadata_ty` a producer spelled, because a vtable word read
/// as a length is a type confusion — the translator must never mint a `slice_len`
/// symbol for one, and must never push a length bound on one. Exhaustive on purpose:
/// a kind added later must be placed in a bucket here, not fall into one.
fn fat_ptr_metadata_is_vtable_word(ptr_ty: &Ty) -> bool {
    let Ty::FatPtr(kind) = ptr_ty else {
        return false;
    };
    // No wildcard inside: a sixth kind must be placed here, not fall into a bucket.
    match kind {
        FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable => true,
        FatPtrKind::Slice(_) | FatPtrKind::Str | FatPtrKind::ContainerLen => false,
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
        Inst::CallIndirect { .. } | Inst::InvokeIndirect { .. } => {
            TrustIrChcUnsupportedReason::IndirectCall
        }
        Inst::CallCannotUnwind { .. } | Inst::CallIndirectCannotUnwind { .. } => {
            TrustIrChcUnsupportedReason::NoUnwindCallBoundary
        }
        Inst::AssertInvoke { .. } => TrustIrChcUnsupportedReason::UnwindingCheck,
        Inst::Fence { .. } => TrustIrChcUnsupportedReason::Fence,
        Inst::EndBorrow { .. } => TrustIrChcUnsupportedReason::EndBorrow,
        Inst::Retain { .. } | Inst::Release { .. } => {
            TrustIrChcUnsupportedReason::ReferenceCounting
        }
        Inst::Dealloc { .. } => TrustIrChcUnsupportedReason::HeapDeallocation,
        Inst::Drop { .. } | Inst::DropInvoke { .. } => TrustIrChcUnsupportedReason::DropGlue,
        Inst::CloseFrame { .. } => TrustIrChcUnsupportedReason::BindingFrameClose,
        Inst::DialectOp(_) => TrustIrChcUnsupportedReason::DialectOperation,
        _ => TrustIrChcUnsupportedReason::MalformedControlFlow,
    }
}

#[cfg(test)]
mod aggregate_leaf_budget_tests {
    //! The leaf accounting behind every trackability decision.
    //!
    //! History: the N-field array model (`bd37bce4a`) flattened `[[[u8; 256]; 256];
    //! 256]` into `256^3 ~= 16.7M` permanently-live CHC variables and OOM'd the host;
    //! `MAX_AGGREGATE_LEAVES` was added to bound it, next to a per-dimension
    //! `len <= 256` cap. Arrays are now SMT arrays — one per element leaf — so an
    //! array counts its element's leaves ONCE and no length enters the count (the
    //! 256 cap is gone). `MAX_AGGREGATE_LEAVES` stays for what is still exponential
    //! in the type text: struct DAGs, pinned below by a struct-DAG witness.
    use super::*;
    use trust_ir::{FieldDef, StructDef, StructId};
    use trust_ir_build::ModuleBuilder;

    // Intentionally independent of the production constant: relaxing the
    // production limit must make the one-over-bound regression test fail.
    const EXPECTED_AGGREGATE_LEAF_WALK_DEPTH: u32 = 64;

    fn nested_singleton_tuple(depth: u32) -> Ty {
        (0..depth).fold(Ty::U8, |inner, _| Ty::Tuple(vec![inner]))
    }

    #[test]
    fn recursive_struct_type_is_not_trackable() {
        let mut mb = ModuleBuilder::new("agg_leaf_recursive_struct");
        let recursive_id = StructId::new(0);
        mb.add_struct(StructDef {
            id: recursive_id,
            name: "Recursive".to_owned(),
            fields: vec![FieldDef {
                name: "next".to_owned(),
                ty: Ty::Struct(recursive_id),
                offset: None,
            }],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let recursive = Ty::Struct(recursive_id);

        assert_eq!(
            aggregate_leaf_count_within(&module, &recursive, MAX_AGGREGATE_LEAVES),
            None,
            "a cyclic aggregate table must exhaust the descent budget and fail closed"
        );
        assert!(
            aggregate_field_tys_of(&module, &recursive).is_none(),
            "a cyclic aggregate must not be admitted as trackable"
        );
    }

    #[test]
    fn ordinary_finite_nested_aggregate_retains_leaf_count() {
        let nested = Ty::Tuple(vec![Ty::Tuple(vec![Ty::U8, Ty::Tuple(vec![Ty::Bool, Ty::Unit])])]);
        let module = ModuleBuilder::new("agg_leaf_finite_nested")
            .build()
            .expect("ModuleBuilder::build: test fixture");

        assert_eq!(
            aggregate_leaf_count_within(&module, &nested, MAX_AGGREGATE_LEAVES),
            Some(2),
            "finite nested aggregates retain their scalar-leaf accounting"
        );
        assert!(aggregate_field_tys_of(&module, &nested).is_some());
    }

    #[test]
    fn aggregate_walk_exact_depth_boundary_is_trackable() {
        let module = ModuleBuilder::new("agg_leaf_depth_boundary")
            .build()
            .expect("ModuleBuilder::build: test fixture");
        let at_depth_limit = nested_singleton_tuple(EXPECTED_AGGREGATE_LEAF_WALK_DEPTH);

        assert_eq!(
            aggregate_leaf_count_within(&module, &at_depth_limit, MAX_AGGREGATE_LEAVES),
            Some(1),
            "exactly the configured number of aggregate descents remains trackable"
        );
    }

    #[test]
    fn aggregate_walk_one_over_depth_boundary_fails_closed() {
        let module = ModuleBuilder::new("agg_leaf_depth_over")
            .build()
            .expect("ModuleBuilder::build: test fixture");
        let over_depth_limit = nested_singleton_tuple(EXPECTED_AGGREGATE_LEAF_WALK_DEPTH + 1);

        assert_eq!(
            aggregate_leaf_count_within(&module, &over_depth_limit, MAX_AGGREGATE_LEAVES),
            None,
            "the depth guard is charged on descent and rejects the first aggregate beyond it"
        );
    }

    /// An array is ONE SMT array per leaf of its element, so its leaf count is its
    /// element's, whatever its length: `[u8; n]` is one leaf at every `n`, and the
    /// nested `[[u8; n]; n]` that used to flatten into `n^2` leaves (16_384 at
    /// `n = 128`, the shape that OOM'd before `MAX_AGGREGATE_LEAVES`) is one leaf of
    /// sort `(Array BV64 (Array BV64 BV8))`. Lengths are compared small and huge;
    /// nothing here allocates anything of size `n`.
    #[test]
    fn an_array_counts_its_element_leaves_once_whatever_its_length() {
        let mut mb = ModuleBuilder::new("agg_leaf_array_once");
        let u8_ty = mb.add_type(Ty::U8);
        let row_2 = mb.add_type(Ty::Array(u8_ty, 2));
        let row_128 = mb.add_type(Ty::Array(u8_ty, 128));
        let row_huge = mb.add_type(Ty::Array(u8_ty, u64::MAX));
        let module = mb.build().expect("ModuleBuilder::build: test fixture");

        for (label, ty) in [
            ("[u8; 2]", Ty::Array(u8_ty, 2)),
            ("[u8; 257]", Ty::Array(u8_ty, 257)),
            ("[u8; u64::MAX]", Ty::Array(u8_ty, u64::MAX)),
            ("[[u8; 2]; 2]", Ty::Array(row_2, 2)),
            ("[[u8; 128]; 128]", Ty::Array(row_128, 128)),
            ("[[u8; u64::MAX]; u64::MAX]", Ty::Array(row_huge, u64::MAX)),
        ] {
            assert_eq!(
                aggregate_leaf_count_within(&module, &ty, MAX_AGGREGATE_LEAVES),
                Some(1),
                "{label}: one leaf, whatever the length"
            );
            assert!(
                matches!(composite_shape_of(&module, &ty), Some(CompositeShape::Array { .. })),
                "{label}: trackable as SMT-array lanes"
            );
            assert!(
                aggregate_field_tys_of(&module, &ty).is_none(),
                "{label}: an array's lanes are never a field list"
            );
        }
        // A struct element contributes its own field leaves, once.
        let mut pairs = ModuleBuilder::new("agg_leaf_array_of_pairs");
        let pair_id = pairs.add_type(Ty::Tuple(vec![Ty::U32, Ty::Bool]));
        let pairs = pairs.build().expect("ModuleBuilder::build: test fixture");
        for len in [2, 3, u64::MAX] {
            assert_eq!(
                aggregate_leaf_count_within(&pairs, &Ty::Array(pair_id, len), MAX_AGGREGATE_LEAVES),
                Some(2),
                "[(u32, bool); {len}] has the element's two leaves"
            );
        }
        // The empty array is the zero-field aggregate: no lane, no leaf.
        assert_eq!(
            aggregate_leaf_count_within(&module, &Ty::Array(u8_ty, 0), MAX_AGGREGATE_LEAVES),
            Some(0)
        );
        assert_eq!(aggregate_field_tys_of(&module, &Ty::Array(u8_ty, 0)), Some(Vec::new()));
    }

    /// `k` nested two-field structs flatten to `2^k` leaves — exponential in the
    /// type text, because every struct field is its own CHC column. That is what
    /// `MAX_AGGREGATE_LEAVES` still bounds after arrays stopped counting by length
    /// (it retires only with a datatype-sort model for ALL aggregates): a DAG of
    /// 13 doublings is 8192 leaves, past the cap, so it is NOT trackable and
    /// collapses to one opaque scalar instead of 8192 relation columns.
    #[test]
    fn a_struct_dag_over_the_leaf_budget_is_not_trackable() {
        let module = ModuleBuilder::new("agg_leaf_struct_dag")
            .build()
            .expect("ModuleBuilder::build: test fixture");
        let dag = |doublings: u32| {
            (0..doublings).fold(Ty::U8, |inner, _| Ty::Tuple(vec![inner.clone(), inner]))
        };
        // 2^12 == 4096 == MAX_AGGREGATE_LEAVES: exactly at the inclusive cap.
        assert_eq!(
            aggregate_leaf_count_within(&module, &dag(12), MAX_AGGREGATE_LEAVES),
            Some(MAX_AGGREGATE_LEAVES),
            "a 4096-leaf struct DAG sits exactly at the inclusive cap"
        );
        assert!(aggregate_field_tys_of(&module, &dag(12)).is_some());
        // One more doubling is 8192 leaves: over the cap, fail closed.
        assert_eq!(
            aggregate_leaf_count_within(&module, &dag(13), MAX_AGGREGATE_LEAVES),
            None,
            "an 8192-leaf struct DAG must fail closed via the leaf-count budget"
        );
        assert!(aggregate_field_tys_of(&module, &dag(13)).is_none());
        assert!(stack_cell_is_translator_opaque(&module, &dag(13)));
    }

    /// An array of an over-budget struct DAG is over budget too: the element's
    /// leaves are what the lanes carry, once.
    #[test]
    fn an_array_of_an_over_budget_struct_dag_is_not_trackable() {
        let mut mb = ModuleBuilder::new("agg_leaf_array_of_dag");
        let dag = (0..13).fold(Ty::U8, |inner, _| Ty::Tuple(vec![inner.clone(), inner]));
        let dag_id = mb.add_type(dag);
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        assert_eq!(
            aggregate_leaf_count_within(&module, &Ty::Array(dag_id, 2), MAX_AGGREGATE_LEAVES),
            None
        );
        assert!(composite_shape_of(&module, &Ty::Array(dag_id, 2)).is_none());
    }

    /// A WIDTHLESS leaf keeps its whole enclosing aggregate non-trackable, and
    /// `Ty::Sequence` is the widthless leaf the call-summary lane keeps reaching
    /// for. This test exists because that reach is tempting and WRONG here.
    ///
    /// `aggregate_leaf_count_within` looks like call-summary machinery. It is not:
    /// it is the single trackability oracle behind `aggregate_field_tys_of`, and
    /// `classify_aggregate_stack_cell`'s doc comment names that sharing as the
    /// property that keeps the translator's tracked-vs-opaque alloca split from
    /// drifting. So admitting a widthless leaf here as "one opaque leaf" — which
    /// reads as a local relaxation of a summary budget — silently does three
    /// things at once:
    ///
    ///   1. `declare_relation_binding_rec` expands the aggregate into per-leaf CHC
    ///      relation arguments and must produce a SORT for a leaf that has no bit
    ///      width;
    ///   2. `classify_aggregate_stack_cell` flips the enclosing stack cell from
    ///      `OpaqueSafe` to `RequiresNonEscape` — i.e. from havoc-on-load to
    ///      TRACKED — for a leaf into which no value is ever actually stored,
    ///      which is the stale-read false proof the load arms are written to avoid;
    ///   3. only then, incidentally, does the call summary get further.
    ///
    /// Measured 2026-09-18: a probe adding `None if matches!(field, Ty::Sequence(_))
    /// => 1` to the leaf walk passed all 267 tests in this crate. Nothing pinned
    /// (1) or (2). This test is that pin — it asserts the refusal at the oracle AND
    /// at the stack-cell classifier, so the same relaxation cannot pass silently
    /// again. Widening the call-summary lane to carry sequences is a separate,
    /// legitimate change: it belongs in the summary's own binding and constructor
    /// (the `OpaqueFatPtr` precedent), never in this shared walk.
    #[test]
    fn sequence_bearing_aggregate_is_not_trackable_and_its_stack_cell_stays_opaque() {
        let mut mb = ModuleBuilder::new("agg_leaf_sequence_field");
        let u8_ty = mb.add_type(Ty::U8);
        let seq_id = mb.add_type(Ty::Sequence(u8_ty));
        let bearing_id = StructId::new(0);
        mb.add_struct(StructDef {
            id: bearing_id,
            name: "SequenceBearing".to_owned(),
            fields: vec![
                FieldDef { name: "len".to_owned(), ty: Ty::U64, offset: None },
                FieldDef { name: "items".to_owned(), ty: Ty::Sequence(u8_ty), offset: None },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let bearing = Ty::Struct(bearing_id);
        let _ = seq_id;

        // The premise the walk actually rests on: a sequence has no bit width, so
        // it is not a scalar leaf. If this ever becomes true, the rest of this
        // test is measuring something else.
        assert!(
            !is_scalar_field_ty(&Ty::Sequence(u8_ty)),
            "a sequence must not be a scalar leaf — it carries no bit width"
        );

        assert_eq!(
            aggregate_leaf_count_within(&module, &bearing, MAX_AGGREGATE_LEAVES),
            None,
            "one widthless leaf makes the whole enclosing aggregate non-trackable"
        );
        assert!(
            aggregate_field_tys_of(&module, &bearing).is_none(),
            "a sequence-bearing aggregate must not be admitted as trackable"
        );
        assert!(
            matches!(
                classify_aggregate_stack_cell(&module, &bearing),
                StackCellAdmission::OpaqueSafe
            ),
            "a sequence-bearing stack cell must stay OPAQUE: tracking it would \
             answer a load from a cell whose sequence leaf never received a value"
        );

        // A tuple reaches the same refusal by the same route — the property is the
        // widthless leaf, not the struct table.
        let tuple_bearing = Ty::Tuple(vec![Ty::U64, Ty::Sequence(u8_ty)]);
        assert_eq!(
            aggregate_leaf_count_within(&module, &tuple_bearing, MAX_AGGREGATE_LEAVES),
            None,
            "the refusal follows the widthless leaf, not the aggregate's spelling"
        );

        // Positive control: the SAME shape with the sequence field replaced by an
        // ordinary scalar is trackable, so the refusals above are attributable to
        // the sequence leaf and not to some unrelated property of this module.
        let control = Ty::Tuple(vec![Ty::U64, Ty::U8]);
        assert_eq!(
            aggregate_leaf_count_within(&module, &control, MAX_AGGREGATE_LEAVES),
            Some(2),
            "positive control: the same shape with a scalar in place of the sequence is trackable"
        );
    }
}

#[cfg(test)]
mod whole_cell_borrow_load_tests {
    use super::*;
    use trust_ir_build::ModuleBuilder;
    use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;

    #[derive(Clone, Copy, Debug)]
    enum Read {
        Shared,
        Mutable,
        Reborrow,
        AfterWrite,
        AfterCall,
        WrongType,
    }

    /// How the fixture spells each reference it takes: the permission instructions,
    /// or the Rust producers' spelling, a `Copy` of the address at `Ptr`
    /// (`transparent_pointer_alias`). The bridge's `Copy` also carries a
    /// `SharedBorrow`/`UniqueBorrow` claim; the translator never reads a claim, so
    /// the fixture leaves it off.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Spelling {
        Borrow,
        Copy,
    }

    fn fixture(aggregate: bool, read: Read) -> (Module, FuncId, ValueId, Ty) {
        fixture_spelled(aggregate, read, Spelling::Borrow)
    }

    /// One reference to `of`, spelled as `spelling` says.
    fn reference(
        fb: &mut trust_ir_build::FunctionBuilder<'_>,
        spelling: Spelling,
        of: ValueId,
        mutable: bool,
    ) -> ValueId {
        match (spelling, mutable) {
            (Spelling::Borrow, false) => fb.borrow(of),
            (Spelling::Borrow, true) => fb.borrow_mut(of),
            (Spelling::Copy, _) => fb.copy(Ty::Ptr, of),
        }
    }

    fn fixture_spelled(
        aggregate: bool,
        read: Read,
        spelling: Spelling,
    ) -> (Module, FuncId, ValueId, Ty) {
        let mut mb = ModuleBuilder::new("whole_cell_borrow_load");
        let sink_ty = mb.add_func_type(vec![Ty::Ptr], vec![]);
        let sink_id = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
        {
            let mut sink = mb.function("sink", sink_ty);
            let entry = sink.create_block();
            sink.switch_to_block(entry);
            sink.set_entry(entry);
            sink.add_block_param(entry, Ty::Ptr);
            sink.ret(vec![]);
            sink.build();
        }
        let fn_ty = mb.add_func_type(vec![], vec![]);
        let function = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("read_borrowed_cell", fn_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let seven = fb.const_value(Ty::U32, Constant::Int(7));
        let cell_ty = if aggregate { Ty::Tuple(vec![Ty::U32, Ty::Bool]) } else { Ty::U32 };
        let initial = if aggregate {
            let empty =
                fb.const_value(cell_ty.clone(), Constant::Aggregate(vec![Constant::Uninit; 2]));
            let with_number = fb.insert_field(cell_ty.clone(), empty, 0, seven);
            let yes = fb.const_value(Ty::Bool, Constant::Bool(true));
            fb.insert_field(cell_ty.clone(), with_number, 1, yes)
        } else {
            seven
        };
        let slot = fb.alloca(cell_ty.clone());
        fb.store(cell_ty.clone(), slot, initial);
        let alias =
            reference(&mut fb, spelling, slot, !matches!(read, Read::Shared | Read::Reborrow));
        let alias = if matches!(read, Read::Reborrow) {
            reference(&mut fb, spelling, alias, false)
        } else {
            alias
        };
        if matches!(read, Read::AfterWrite) {
            let zero = fb.const_value(Ty::U32, Constant::Int(0));
            let replacement =
                if aggregate { fb.insert_field(cell_ty.clone(), initial, 0, zero) } else { zero };
            fb.store(cell_ty.clone(), alias, replacement);
        }
        if matches!(read, Read::AfterCall) {
            fb.call_void(sink_id, vec![alias]);
        }
        let access_ty = if matches!(read, Read::WrongType) { Ty::U64 } else { cell_ty.clone() };
        let loaded = fb.load(access_ty.clone(), alias);
        let (number, expected, number_ty) = if matches!(read, Read::WrongType) {
            (loaded, fb.const_value(Ty::U64, Constant::Int(7)), Ty::U64)
        } else if aggregate {
            (fb.extract_field(Ty::U32, loaded, 0), seven, Ty::U32)
        } else {
            (loaded, seven, Ty::U32)
        };
        let equals_initial = fb.icmp(ICmpOp::Eq, number_ty, number, expected);
        fb.assert(equals_initial);
        fb.ret(vec![]);
        fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), function, slot, cell_ty)
    }

    #[test]
    fn original_aggregate_undef_borrow_fixtures_are_runtime_ub_and_refused() {
        for read in [Read::Shared, Read::Reborrow, Read::Mutable, Read::AfterWrite, Read::AfterCall]
        {
            for spelling in [Spelling::Borrow, Spelling::Copy] {
                let (mut module, function, _, ty) = fixture_spelled(true, read, spelling);
                let source =
                    module.functions.iter_mut().find(|source| source.id == function).unwrap();
                let seed = source
                    .blocks
                    .iter_mut()
                    .flat_map(|block| &mut block.body)
                    .find(|node| {
                        matches!(&node.inst, Inst::Const { ty: seed_ty,
                        value: Constant::Aggregate(fields) } if seed_ty == &ty
                            && fields.iter().all(|field| matches!(field, Constant::Uninit)))
                    })
                    .unwrap();
                // Restore the exact original Undef instruction, retaining every
                // other original definition/use/SSA id and its actual UB.
                seed.inst = Inst::Undef { ty };
                let error = trust_ir::interpret::Interpreter::with_module(&module)
                    .execute_func(function, [])
                    .unwrap_err();
                assert_eq!(error.code, trust_ir::interpret::InterpretErrorCode::UndefinedBehavior);
                let output = translate_function(
                    module.function_by_id(function).unwrap(),
                    &module,
                    &TranslateOptions::default(),
                );
                assert!(output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption));
                assert!(super::smt_array_tests::error_reachable(&output));
            }
        }
    }

    #[test]
    fn original_interior_field_undef_is_runtime_ub_and_refused() {
        for spelling in [Spelling::Borrow, Spelling::Copy] {
            let (mut module, function) = interior_field_fixture(spelling);
            let source = module.functions.iter_mut().find(|source| source.id == function).unwrap();
            let seed = source
                .blocks
                .iter_mut()
                .flat_map(|block| &mut block.body)
                .find(|node| {
                    matches!(&node.inst, Inst::Const {
                    value: Constant::Aggregate(fields), .. }
                    if fields.iter().all(|field| matches!(field, Constant::Uninit)))
                })
                .unwrap();
            let Inst::Const { ty, .. } = &seed.inst else { unreachable!() };
            seed.inst = Inst::Undef { ty: ty.clone() };
            assert_eq!(
                trust_ir::interpret::Interpreter::with_module(&module)
                    .execute_func(function, [])
                    .unwrap_err()
                    .code,
                trust_ir::interpret::InterpretErrorCode::UndefinedBehavior
            );
            let output = translate_function(
                module.function_by_id(function).unwrap(),
                &module,
                &TranslateOptions::default(),
            );
            assert!(
                output.diagnostics.iter().any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
            );
        }
    }

    fn probe(aggregate: bool, read: Read) -> ChcTranslationOutput {
        probe_spelled(aggregate, read, Spelling::Borrow)
    }

    fn probe_spelled(aggregate: bool, read: Read, spelling: Spelling) -> ChcTranslationOutput {
        let (module, function, _, _) = fixture_spelled(aggregate, read, spelling);
        trust_ir_function_to_chc_translation_output(&module, function, &TranslateOptions::default())
            .expect("whole-cell alias fixture translates")
    }

    // Every fixture has one source assertion in one straight-line block. Inspect
    // its error condition directly, without treating a rendered solver verdict
    // or saved report as proof authority.
    fn assertion_error(output: &ChcTranslationOutput) -> Option<bool> {
        let errors: Vec<_> =
            output.vc.rules.iter().filter(|rule| rule.head.name.as_str() == ERROR_REL).collect();
        assert_eq!(errors.len(), 1, "one assertion error, no unsupported memory edge");
        let mut result = Some(true);
        for condition in &errors[0].body.constraints {
            match try_eval_to_bool(condition) {
                Some(false) => return Some(false),
                Some(true) => {}
                None => result = None,
            }
        }
        result
    }

    #[test]
    fn whole_cell_borrow_load_preserves_scalar_and_aggregate_values() {
        for aggregate in [false, true] {
            for read in [Read::Shared, Read::Mutable, Read::Reborrow] {
                let output = probe(aggregate, read);
                assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
                assert_eq!(assertion_error(&output), Some(false));
            }
        }
    }

    #[test]
    fn whole_cell_borrow_load_observes_the_latest_alias_write() {
        for aggregate in [false, true] {
            let output = probe(aggregate, Read::AfterWrite);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert_eq!(assertion_error(&output), Some(true), "the written zero must refute == 7");
        }
    }

    #[test]
    fn whole_cell_borrow_load_does_not_resurrect_a_call_invalidated_value() {
        for aggregate in [false, true] {
            let output = probe(aggregate, Read::AfterCall);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert_eq!(assertion_error(&output), None, "a call-escaping cell stays havoced");
        }
    }

    #[test]
    fn whole_cell_borrow_load_rejects_a_mismatched_access_type() {
        for aggregate in [false, true] {
            let output = probe(aggregate, Read::WrongType);
            assert!(
                output.diagnostics.iter().any(|diagnostic| {
                    diagnostic.reason
                        == TrustIrChcUnsupportedReason::MemoryAccessWithoutPreciseModel
                }),
                "a U64 load cannot import the stored U32 or tuple value"
            );
        }
    }

    #[test]
    fn initialized_local_borrows_reach_the_structural_alloca_lane() {
        for aggregate in [false, true] {
            for read in [Read::Shared, Read::Mutable, Read::Reborrow, Read::AfterWrite] {
                let (module, function, cell, ty) = fixture(aggregate, read);
                let function = module.function_by_id(function).unwrap();
                assert!(borrowed_block_local_cell_is_admissible(&module, function, cell, &ty));
                assert!(single_cell_alloca_is_admissible(&module, function, cell, &ty));
            }
        }
    }

    #[test]
    fn borrowed_alloca_lane_rejects_call_escape_and_type_mismatch() {
        for aggregate in [false, true] {
            for read in [Read::AfterCall, Read::WrongType] {
                let (module, function, cell, ty) = fixture(aggregate, read);
                let function = module.function_by_id(function).unwrap();
                assert!(!borrowed_block_local_cell_is_admissible(&module, function, cell, &ty));
                assert!(!single_cell_alloca_is_admissible(&module, function, cell, &ty));
            }
        }
    }

    #[test]
    fn borrowed_alloca_lane_rejects_permission_conflicts() {
        for hazard in [
            "mutable_after_mutable",
            "shared_after_mutable",
            "mutable_after_shared",
            "shared_write_alias",
            "shared_write_root",
        ] {
            let read =
                if hazard.starts_with("shared_write") { Read::AfterWrite } else { Read::Mutable };
            let (mut module, function, cell, ty) = fixture(false, read);
            let body =
                &mut module.functions.iter_mut().find(|f| f.id == function).unwrap().blocks[0].body;
            let borrow_index =
                body.iter().position(|node| matches!(node.inst, Inst::BorrowMut { .. })).unwrap();
            let alias = body[borrow_index].results[0];
            if matches!(hazard, "mutable_after_shared" | "shared_write_alias" | "shared_write_root")
            {
                body[borrow_index].inst = Inst::Borrow { ptr: cell };
            }
            if hazard.ends_with("after_mutable") || hazard == "mutable_after_shared" {
                let inst = if hazard == "shared_after_mutable" {
                    Inst::Borrow { ptr: alias }
                } else {
                    Inst::BorrowMut { ptr: alias }
                };
                body.insert(borrow_index + 1, InstrNode::new(inst).with_result(ValueId::new(1000)));
            }
            if hazard == "shared_write_root" {
                for node in &mut body[borrow_index + 1..] {
                    if let Inst::Store { ptr, .. } = &mut node.inst {
                        *ptr = cell;
                    }
                }
            }
            let function = module.function_by_id(function).unwrap();
            assert!(
                !borrowed_block_local_cell_is_admissible(&module, function, cell, &ty),
                "{hazard}"
            );
            assert!(!single_cell_alloca_is_admissible(&module, function, cell, &ty), "{hazard}");
        }
    }

    #[test]
    fn borrowed_alloca_lane_rejects_uninitialized_or_qualified_accesses() {
        for hazard in
            ["uninitialized", "volatile", "aligned", "store_type", "extent", "alloca_align"]
        {
            let (mut module, function, cell, ty) = fixture(false, Read::Mutable);
            let body =
                &mut module.functions.iter_mut().find(|f| f.id == function).unwrap().blocks[0].body;
            match hazard {
                "uninitialized" => body.retain(|node| !matches!(node.inst, Inst::Store { .. })),
                "volatile" | "aligned" => {
                    for node in body {
                        if let Inst::Load { volatile, align, .. } = &mut node.inst {
                            if hazard == "volatile" {
                                *volatile = true;
                            } else {
                                *align = Some(4);
                            }
                        }
                    }
                }
                "store_type" => {
                    for node in body {
                        if let Inst::Store { ty, .. } = &mut node.inst {
                            *ty = Ty::U64;
                        }
                    }
                }
                "extent" | "alloca_align" => {
                    for node in body {
                        if let Inst::Alloca { count, align, .. } = &mut node.inst {
                            if hazard == "extent" {
                                *count = Some(ValueId::new(0));
                            } else {
                                *align = Some(4);
                            }
                        }
                    }
                }
                _ => unreachable!(),
            }
            let function = module.function_by_id(function).unwrap();
            assert!(
                !borrowed_block_local_cell_is_admissible(&module, function, cell, &ty),
                "{hazard}"
            );
            assert!(!single_cell_alloca_is_admissible(&module, function, cell, &ty), "{hazard}");
        }
    }

    #[test]
    fn borrowed_alloca_lane_rejects_alias_escape_and_cross_block_loads() {
        for cross_block in [false, true] {
            let (mut module, function, cell, ty) = fixture(false, Read::Mutable);
            let func = module.functions.iter_mut().find(|f| f.id == function).unwrap();
            let alias = func.blocks[0]
                .body
                .iter()
                .find_map(|node| {
                    matches!(node.inst, Inst::BorrowMut { .. }).then(|| node.results[0])
                })
                .unwrap();
            if cross_block {
                let load_index = func.blocks[0]
                    .body
                    .iter()
                    .position(|node| matches!(node.inst, Inst::Load { .. }))
                    .unwrap();
                let mut successor = Block::new(BlockId::new(1));
                successor.body = func.blocks[0].body.split_off(load_index);
                func.blocks[0]
                    .body
                    .push(InstrNode::new(Inst::Br { target: successor.id, args: vec![] }));
                // The successor is deliberately listed first: admission must not
                // depend on seeing the definition block before its alias use.
                func.blocks.insert(0, successor);
            } else {
                let body = &mut func.blocks[0].body;
                let holder = ValueId::new(1000);
                body.insert(
                    body.len() - 1,
                    InstrNode::new(Inst::Alloca { ty: Ty::Ptr, count: None, align: None })
                        .with_result(holder),
                );
                body.insert(
                    body.len() - 1,
                    InstrNode::new(Inst::Store {
                        ty: Ty::Ptr,
                        ptr: holder,
                        value: alias,
                        volatile: false,
                        align: None,
                    }),
                );
            }
            let function = module.function_by_id(function).unwrap();
            assert!(!borrowed_block_local_cell_is_admissible(&module, function, cell, &ty));
            assert!(!single_cell_alloca_is_admissible(&module, function, cell, &ty));
        }
    }

    // ---- Copy-spelled references (`transparent_pointer_alias`) ----
    //
    // A Rust producer spells `&place` / `&mut place` as a `Copy` of the address, not
    // as a permission instruction (trust-ir SPEC "A Rust reference carries no
    // permission instruction"). These pin that the translator and the borrowed-cell
    // lane give that spelling the borrow's exact model, and that its soundness
    // guards (escape, call invalidation) hold for it too.

    /// A cell of `(u32, bool)` holding `(7, true)`; `&mut cell.0 = 0` through a
    /// reference to the field's GEP; then the cell is loaded and `cell.0 == 0`
    /// asserted. The interior-field store shape the provenance lanes follow.
    fn interior_field_fixture(spelling: Spelling) -> (Module, FuncId) {
        let mut mb = ModuleBuilder::new("interior_field_reference_store");
        // A declared layout, so the field GEP names exactly one lane (an
        // undeclared tuple layout drops the store to "unknown offset").
        let struct_id = mb.add_struct(trust_ir::StructDef {
            id: trust_ir::value::StructId::new(0),
            name: "interior_field::S".to_string(),
            fields: vec![
                trust_ir::FieldDef { name: "a".into(), ty: Ty::U32, offset: Some(0) },
                trust_ir::FieldDef { name: "b".into(), ty: Ty::Bool, offset: Some(4) },
            ],
            size: Some(8),
            align: Some(4),
            repr: trust_ir::StructRepr::Rust,
            origin: None,
        });
        let fn_ty = mb.add_func_type(vec![], vec![]);
        let function = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("write_through_field_reference", fn_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let cell_ty = Ty::Struct(struct_id);
        let seven = fb.const_value(Ty::U32, Constant::Int(7));
        let yes = fb.const_value(Ty::Bool, Constant::Bool(true));
        let empty = fb.const_value(cell_ty.clone(), Constant::Aggregate(vec![Constant::Uninit; 2]));
        let with_number = fb.insert_field(cell_ty.clone(), empty, 0, seven);
        let initial = fb.insert_field(cell_ty.clone(), with_number, 1, yes);
        let slot = fb.alloca(cell_ty.clone());
        fb.store(cell_ty.clone(), slot, initial);
        let index = fb.iconst(Ty::U64, 0);
        let field = fb.gep(Ty::U32, slot, vec![index]);
        let field_ref = reference(&mut fb, spelling, field, true);
        let zero = fb.const_value(Ty::U32, Constant::Int(0));
        fb.store(Ty::U32, field_ref, zero);
        let loaded = fb.load(cell_ty.clone(), slot);
        let number = fb.extract_field(Ty::U32, loaded, 0);
        let written = fb.icmp(ICmpOp::Eq, Ty::U32, number, zero);
        fb.assert(written);
        fb.ret(vec![]);
        fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), function)
    }

    /// M-a. Every permission-legal whole-cell shape, and the interior-field store,
    /// translates to the same verdict whether its references are borrows or
    /// Copy-spelled. Fails before `transparent_pointer_alias` reaches the translator
    /// and the lanes: the Copy rows lose the referent's provenance, are classed as
    /// escapes, and come back havoced (`None`) where the borrow rows are exact.
    #[test]
    fn copy_and_borrow_references_translate_identically() {
        for aggregate in [false, true] {
            for read in
                [Read::Shared, Read::Mutable, Read::Reborrow, Read::AfterWrite, Read::AfterCall]
            {
                let borrow = probe_spelled(aggregate, read, Spelling::Borrow);
                let copy = probe_spelled(aggregate, read, Spelling::Copy);
                assert!(copy.diagnostics.is_empty(), "{:?}", copy.diagnostics);
                assert_eq!(
                    assertion_error(&copy),
                    assertion_error(&borrow),
                    "aggregate={aggregate} read={read:?}"
                );
                let (bm, bf, bcell, bty) = fixture_spelled(aggregate, read, Spelling::Borrow);
                let (cm, cf, ccell, cty) = fixture_spelled(aggregate, read, Spelling::Copy);
                let (bfunc, cfunc) =
                    (bm.function_by_id(bf).unwrap(), cm.function_by_id(cf).unwrap());
                assert_eq!(
                    single_cell_alloca_is_admissible(&cm, cfunc, ccell, &cty),
                    single_cell_alloca_is_admissible(&bm, bfunc, bcell, &bty),
                    "aggregate={aggregate} read={read:?}"
                );
            }
        }
        let outputs = [Spelling::Borrow, Spelling::Copy].map(|spelling| {
            let (module, function) = interior_field_fixture(spelling);
            trust_ir_function_to_chc_translation_output(
                &module,
                function,
                &TranslateOptions::default(),
            )
            .expect("interior-field fixture translates")
        });
        for output in &outputs {
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        }
        assert_eq!(assertion_error(&outputs[1]), assertion_error(&outputs[0]));
        assert_eq!(
            assertion_error(&outputs[1]),
            Some(false),
            "the write through the Copy-spelled field reference reaches the cell's lane"
        );
    }

    /// The M-b subject, `let mut x = 5; { let r = &mut x; *r = 6; } let s = &x; *s`:
    /// block-local and call-free, its two references spelled as `spelling` says.
    fn reborrow_after_mutable_fixture(spelling: Spelling) -> (Module, FuncId, ValueId) {
        let mut mb = ModuleBuilder::new("shared_after_mutable_reference");
        let fn_ty = mb.add_func_type(vec![], vec![]);
        let function = mb.peek_next_func_id().expect("peek_next_func_id: test fixture");
        let mut fb = mb.function("read_after_scoped_mutable_reference", fn_ty);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let slot = fb.alloca(Ty::U32);
        let five = fb.const_value(Ty::U32, Constant::Int(5));
        fb.store(Ty::U32, slot, five);
        let r = reference(&mut fb, spelling, slot, true);
        let six = fb.const_value(Ty::U32, Constant::Int(6));
        fb.store(Ty::U32, r, six);
        let s = reference(&mut fb, spelling, slot, false);
        let read = fb.load(Ty::U32, s);
        let is_six = fb.icmp(ICmpOp::Eq, Ty::U32, read, six);
        fb.assert(is_six);
        fb.ret(vec![]);
        fb.build();
        (mb.build().expect("ModuleBuilder::build: test fixture"), function, slot)
    }

    /// M-b. A Copy-spelled reference is not held to the permission machine: the
    /// scoped `&mut` followed by a `&` of the same local is admitted by the gate's
    /// Alloca predicate and proved. Its Borrow-spelled twin (a `BorrowMut` that is
    /// never ended, then a `Borrow`) is refused by the borrowed-cell lane's
    /// permission check, which is the machine's own reading of that spelling.
    #[test]
    fn copy_reference_is_not_held_to_the_permission_machine() {
        let (module, function, cell) = reborrow_after_mutable_fixture(Spelling::Copy);
        let func = module.function_by_id(function).unwrap();
        assert!(borrowed_block_local_cell_is_admissible(&module, func, cell, &Ty::U32));
        assert!(single_cell_alloca_is_admissible(&module, func, cell, &Ty::U32));
        let output = trust_ir_function_to_chc_translation_output(
            &module,
            function,
            &TranslateOptions::default(),
        )
        .expect("Copy-spelled fixture translates");
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        assert_eq!(assertion_error(&output), Some(false), "`*s == 6` is proved");

        let (module, function, cell) = reborrow_after_mutable_fixture(Spelling::Borrow);
        let func = module.function_by_id(function).unwrap();
        assert!(!borrowed_block_local_cell_is_admissible(&module, func, cell, &Ty::U32));
        assert!(!single_cell_alloca_is_admissible(&module, func, cell, &Ty::U32));
    }

    /// M-c, the soundness dual of `transparent_pointer_alias`: a Copy-spelled `&mut`
    /// of the cell handed to an opaque call. The call may write through it, so the
    /// cell's old value must not be proved afterwards, and the lane must refuse the
    /// cell. Passes before M1 (a `Copy` operand was an escape); fails if the alias
    /// predicate ever lets the Copy RESULT's call use stop counting as an escape.
    #[test]
    fn copy_alias_into_a_call_invalidates_the_cell() {
        for aggregate in [false, true] {
            let output = probe_spelled(aggregate, Read::AfterCall, Spelling::Copy);
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
            assert_eq!(assertion_error(&output), None, "a call-escaping cell stays havoced");
            let (module, function, cell, ty) =
                fixture_spelled(aggregate, Read::AfterCall, Spelling::Copy);
            let function = module.function_by_id(function).unwrap();
            assert!(!borrowed_block_local_cell_is_admissible(&module, function, cell, &ty));
            assert!(!single_cell_alloca_is_admissible(&module, function, cell, &ty));
            assert_eq!(
                stack_alloca_escape_classification(function, cell),
                StackCellEscape::IntoCallsOnly
            );
        }
    }

    /// A Copy-spelled alias written into memory as a VALUE is the escape the
    /// borrowed lane refuses for a borrow (`..._rejects_alias_escape_...` above).
    #[test]
    fn copy_alias_stored_as_a_value_is_refused_by_the_lane() {
        let (mut module, function, cell, ty) =
            fixture_spelled(false, Read::Mutable, Spelling::Copy);
        let func = module.functions.iter_mut().find(|f| f.id == function).unwrap();
        let alias = func.blocks[0]
            .body
            .iter()
            .find_map(|node| matches!(node.inst, Inst::Copy { .. }).then(|| node.results[0]))
            .unwrap();
        let body = &mut func.blocks[0].body;
        let holder = ValueId::new(1000);
        body.insert(
            body.len() - 1,
            InstrNode::new(Inst::Alloca { ty: Ty::Ptr, count: None, align: None })
                .with_result(holder),
        );
        body.insert(
            body.len() - 1,
            InstrNode::new(Inst::Store {
                ty: Ty::Ptr,
                ptr: holder,
                value: alias,
                volatile: false,
                align: None,
            }),
        );
        let function = module.function_by_id(function).unwrap();
        assert!(!borrowed_block_local_cell_is_admissible(&module, function, cell, &ty));
        assert!(!single_cell_alloca_is_admissible(&module, function, cell, &ty));
        assert_eq!(stack_alloca_escape_classification(function, cell), StackCellEscape::Unbounded);
    }

    /// The alias predicate itself: a borrow's operand, and a `Copy`'s operand at
    /// exactly the five thin reference/pointer types; never a `Copy` at a fat
    /// pointer, a reference-counted word or a non-pointer type.
    #[test]
    fn transparent_pointer_alias_is_exactly_the_borrows_and_thin_pointer_copies() {
        let p = ValueId::new(3);
        assert_eq!(transparent_pointer_alias(&Inst::Borrow { ptr: p }), Some(p));
        assert_eq!(transparent_pointer_alias(&Inst::BorrowMut { ptr: p }), Some(p));
        for ty in [
            Ty::Ptr,
            Ty::Ref(Box::new(Ty::U8)),
            Ty::RefMut(Box::new(Ty::U8)),
            Ty::PtrConst(Box::new(Ty::U8)),
            Ty::PtrMut(Box::new(Ty::U8)),
        ] {
            assert_eq!(transparent_pointer_alias(&Inst::Copy { ty, operand: p }), Some(p));
        }
        for ty in [Ty::FatPtr(FatPtrKind::Str), Ty::Rc(Box::new(Ty::U8)), Ty::U64, Ty::Usize] {
            assert_eq!(transparent_pointer_alias(&Inst::Copy { ty, operand: p }), None);
        }
        assert_eq!(transparent_pointer_alias(&Inst::EndBorrow { borrow_ptr: p }), None);
        assert_eq!(
            transparent_pointer_alias(&Inst::Load {
                ty: Ty::Ptr,
                ptr: p,
                volatile: false,
                align: None
            }),
            None
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

        (mb.build().expect("ModuleBuilder::build: test fixture"), acc, entry, header, body, exit)
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

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

        (mb.build().expect("ModuleBuilder::build: test fixture"), cell, join)
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

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
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

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
        build_aggregate_clamp_join_input(shape, false)
    }

    fn build_aggregate_clamp_join_input(
        shape: AggregateJoinShape,
        initialized: bool,
    ) -> (Module, ValueId, Ty, BlockId) {
        let pair = Ty::Tuple(vec![Ty::U64, Ty::U64]);
        let mut mb = ModuleBuilder::new("mem2reg_aggregate_join");
        let ft = mb.add_func_type(
            if initialized {
                vec![Ty::Bool, Ty::U64, Ty::U64]
            } else {
                vec![Ty::Bool, pair.clone()]
            },
            vec![pair.clone()],
        );
        let mut fb = mb.function("pair_join", ft);

        let entry = fb.create_block();
        let then_block = fb.create_block();
        let else_block = fb.create_block();
        let join = fb.create_block();
        fb.set_entry(entry);

        fb.switch_to_block(entry);
        let cond = fb.add_block_param(entry, Ty::Bool);
        let p = if initialized {
            let x = fb.add_block_param(entry, Ty::U64);
            let y = fb.add_block_param(entry, Ty::U64);
            fb.make_aggregate(pair.clone(), vec![x, y])
        } else {
            fb.add_block_param(entry, pair.clone())
        };
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

        (mb.build().expect("ModuleBuilder::build: test fixture"), cell, pair, join)
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

        let output = translate_function_per_block(func, &module, &options);
        assert!(output.diagnostics.is_empty(), "the promoted aggregate lowers with no diagnostics");

        let (aliased_module, ..) = build_aggregate_clamp_join(AggregateJoinShape::Aliased);
        let aliased =
            translate_function_per_block(&aliased_module.functions[0], &aliased_module, &options);
        assert_eq!(
            relation_arity(&output, join) - relation_arity(&aliased, join),
            2,
            "promotion adds exactly one relation leaf per flattened tuple field"
        );
    }

    #[test]
    fn original_cross_block_partial_transport_does_not_initialize_fields() {
        use trust_ir::interpret::{
            InterpretErrorCode, InterpretValue, InterpretValueKind, Interpreter,
        };
        let (mut module, _, pair, _) =
            build_aggregate_clamp_join_input(AggregateJoinShape::Clean, false);
        for condition in [false, true] {
            let input = InterpretValue {
                ty: pair.clone(),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(Ty::U64, 7).unwrap(),
                    InterpretValue { ty: Ty::U64, kind: InterpretValueKind::Uninit },
                ]),
            };
            let condition =
                InterpretValue { ty: Ty::Bool, kind: InterpretValueKind::Bool(condition) };
            let result = Interpreter::with_module(&module)
                .execute_func(FuncId::new(0), [condition, input])
                .unwrap();
            assert!(matches!(&result.returns[0].kind, InterpretValueKind::Aggregate(fields)
                if matches!(fields[1].kind, InterpretValueKind::Uninit)));
        }
        let output = translate_function_per_block(
            &module.functions[0],
            &module,
            &TranslateOptions::default(),
        );
        assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        let mut signature = module.func_types[module.functions[0].ty.as_usize()].clone();
        signature.params.clear();
        signature.returns.clear();
        let ty = trust_ir::FuncTyId::new(module.func_types.len() as u32);
        module.func_types.push(signature);
        let mut caller =
            Function::new(FuncId::new(1), "consume_unwritten_field", ty, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body = vec![
            InstrNode::new(Inst::Const { ty: Ty::Bool, value: Constant::Bool(true) })
                .with_result(ValueId::new(0)),
            InstrNode::new(Inst::Const {
                ty: pair.clone(),
                value: Constant::Aggregate(vec![Constant::Int(7), Constant::Uninit]),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0), ValueId::new(1)],
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::U64,
                aggregate: ValueId::new(2),
                field: 1,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return { values: vec![] }),
        ];
        caller.blocks.push(entry);
        module.functions.push(caller);
        assert_eq!(
            Interpreter::with_module(&module).execute_func(FuncId::new(1), []).unwrap_err().code,
            InterpretErrorCode::UndefinedBehavior
        );
        let output =
            translate_function(&module.functions[1], &module, &TranslateOptions::default());
        assert!(
            output
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.reason
                    == TrustIrChcUnsupportedReason::OperandConsumption)
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
        let outer = Ty::Tuple(vec![Ty::U64, inner.clone(), Ty::Unit]);

        let build = |alias: bool, initialized: bool| {
            let mut mb = ModuleBuilder::new("mem2reg_nested_join");
            let ft = mb.add_func_type(
                if initialized {
                    vec![Ty::Bool, Ty::U64, Ty::U64, Ty::Bool]
                } else {
                    vec![Ty::Bool, outer.clone()]
                },
                vec![outer.clone()],
            );
            let mut fb = mb.function("nested_join", ft);
            let entry = fb.create_block();
            let then_block = fb.create_block();
            let else_block = fb.create_block();
            let join = fb.create_block();
            fb.set_entry(entry);

            fb.switch_to_block(entry);
            let cond = fb.add_block_param(entry, Ty::Bool);
            let p = if initialized {
                let x = fb.add_block_param(entry, Ty::U64);
                let y = fb.add_block_param(entry, Ty::U64);
                let flag = fb.add_block_param(entry, Ty::Bool);
                let nested = fb.make_aggregate(inner.clone(), vec![y, flag]);
                let unit = fb.const_value(Ty::Unit, Constant::PhantomData);
                fb.make_aggregate(outer.clone(), vec![x, nested, unit])
            } else {
                fb.add_block_param(entry, outer.clone())
            };
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
            (mb.build().expect("ModuleBuilder::build: test fixture"), cell, join)
        };

        let (original, _, _) = build(false, false);
        {
            use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
            let value = InterpretValue {
                ty: outer.clone(),
                kind: InterpretValueKind::Aggregate(vec![
                    InterpretValue::int(Ty::U64, 7).unwrap(),
                    InterpretValue {
                        ty: inner.clone(),
                        kind: InterpretValueKind::Aggregate(vec![
                            InterpretValue { ty: Ty::U64, kind: InterpretValueKind::Uninit },
                            InterpretValue { ty: Ty::Bool, kind: InterpretValueKind::Bool(true) },
                        ]),
                    },
                    InterpretValue { ty: Ty::Unit, kind: InterpretValueKind::Unit },
                ]),
            };
            let condition = InterpretValue { ty: Ty::Bool, kind: InterpretValueKind::Bool(true) };
            let result = Interpreter::with_module(&original)
                .execute_func(FuncId::new(0), [condition, value])
                .unwrap();
            assert!(matches!(&result.returns[0].kind, InterpretValueKind::Aggregate(fields)
                if matches!(&fields[1].kind, InterpretValueKind::Aggregate(inner)
                    if matches!(inner[0].kind, InterpretValueKind::Uninit))));
            let output = translate_function_per_block(
                &original.functions[0],
                &original,
                &TranslateOptions::default(),
            );
            assert!(output.diagnostics.is_empty(), "{:?}", output.diagnostics);
        }
        let (module, cell, join) = build(false, false);
        let (aliased_module, ..) = build(true, false);
        let options = TranslateOptions::default();

        assert!(single_cell_alloca_is_admissible(&module, &module.functions[0], cell, &outer));
        let output = translate_function_per_block(&module.functions[0], &module, &options);
        let aliased =
            translate_function_per_block(&aliased_module.functions[0], &aliased_module, &options);
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
        let output = translate_function_per_block(&module.functions[0], &module, &options);

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
            assert_eq!(
                rejection.promoted.kind(),
                expected,
                "{shape:?} refused for the wrong reason"
            );
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

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
        build_referenced_cross_block(shape, false)
    }

    /// [`build_borrowed_cross_block`], with the reference spelled either as the
    /// `BorrowMut` permission instruction or (`copy_spelled`) as the Rust producers'
    /// `Copy` of the address at `Ptr` (`transparent_pointer_alias`).
    fn build_referenced_cross_block(
        shape: BorrowShape,
        copy_spelled: bool,
    ) -> (Module, ValueId, Ty) {
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
        // THE BORROW
        let borrowed = if copy_spelled { fb.copy(Ty::Ptr, cell) } else { fb.borrow_mut(cell) };
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

        (mb.build().expect("ModuleBuilder::build: test fixture"), cell, cell_ty)
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
                transparent_pointer_alias(&node.inst)
                    .is_some_and(|referent| referent.index() == cell.index())
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

    /// The tripwire above, with the reference spelled as the Rust producers spell
    /// it: a thin-pointer `Copy` of the cell. The `Copy` joins the derivation
    /// closure exactly as the borrow did, so its RESULT written into memory is the
    /// same escape. If this goes green, a Copy-spelled reference is the unsound
    /// hole the borrow arm's escape guard exists to close.
    #[test]
    fn a_copy_reference_stored_as_a_value_is_still_refused() {
        let (module, cell, ty) = build_referenced_cross_block(BorrowShape::StoredAsValue, true);
        assert!(
            !borrow_is_transparently_promotable(&module, cell),
            "a Copy-spelled reference whose RESULT is written into memory must never be promotable",
        );
        assert_eq!(
            stack_alloca_escape_classification(&module.functions[0], cell),
            StackCellEscape::Unbounded,
            "and it must be refused for the ESCAPE reason, not incidentally",
        );
        assert!(single_cell_alloca_rejection(&module, &module.functions[0], cell, &ty).is_some());
    }

    /// The Copy-spelled twin of the positive half below: a thin-pointer `Copy` of
    /// the cell is the same transparent derivation, so the classification and the
    /// promotion predicate answer exactly as they do for the borrow.
    #[test]
    fn a_copy_reference_classifies_exactly_like_the_borrow() {
        for shape in
            [BorrowShape::Transparent, BorrowShape::ScalarTransparent, BorrowShape::StoredAsValue]
        {
            let (borrow_module, borrow_cell, _) = build_referenced_cross_block(shape, false);
            let (copy_module, copy_cell, _) = build_referenced_cross_block(shape, true);
            assert_eq!(
                stack_alloca_escape_classification(&copy_module.functions[0], copy_cell),
                stack_alloca_escape_classification(&borrow_module.functions[0], borrow_cell),
                "{shape:?}"
            );
            assert_eq!(
                borrow_is_transparently_promotable(&copy_module, copy_cell),
                borrow_is_transparently_promotable(&borrow_module, borrow_cell),
                "{shape:?}"
            );
        }
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
        for shape in
            [BorrowShape::Transparent, BorrowShape::ScalarTransparent, BorrowShape::StoredAsValue]
        {
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

        let module = mb.build().expect("ModuleBuilder::build: test fixture");
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
                EnumVariant { name: "A".to_string(), fields: Vec::new(), field_names: Vec::new() },
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
        InstrNode::new(Inst::Load { ty, ptr: ValueId::new(ptr), volatile: false, align: None })
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
            func(
                0,
                vec![block(
                    0,
                    vec![
                        alloca(0, i64_.clone()),
                        store(0, 1, i64_.clone()),
                        load(2, 0, i64_.clone()),
                        ret(),
                    ],
                )],
            ),
            cell,
            i64_.clone(),
        ));

        // Lane 1: floats still have no admitted stack-cell lane. Fat-pointer
        // cells have separate access-safety and opaque-value regression tests.
        all.push((
            "pointee_not_scalar_or_aggregate",
            func(0, vec![block(0, vec![alloca(0, Ty::F32), ret()])]),
            cell,
            Ty::F32,
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
                    vec![alloca(0, i64_.clone()), alloca(3, Ty::Ptr), store(3, 0, Ty::Ptr), ret()],
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
                    block(1, vec![store(0, 1, Ty::Tuple(vec![Ty::I64, Ty::I64])), ret()]),
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
        assert_eq!(
            reason_for("array_alloca_count_some").block_local.kind(),
            "no_exact_defining_alloca"
        );
        assert_eq!(
            reason_for("array_alloca_count_some").promoted.kind(),
            "no_exact_defining_alloca"
        );
        assert_eq!(reason_for("aligned_alloca").block_local.kind(), "no_exact_defining_alloca");
        assert_eq!(reason_for("aligned_alloca").promoted.kind(), "no_exact_defining_alloca");
    }

    #[test]
    fn reason_kinds_are_stable_grep_tokens() {
        // The gate log histogram is built by grepping `reason=<lane1>/<lane2>`, so
        // a bucket name must never contain a separator that breaks the split.
        for (_, function, cell, ty) in fixtures() {
            if let Some(reason) =
                single_cell_alloca_rejection(&taxonomy_module(), &function, cell, &ty)
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
                let now =
                    promoted_cell_alloca_reject(&module, &function, cell, &probe_ty).is_none();
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

/// trust-ir v40 `FatPtrKind::ContainerVtable`: every place this translator classifies
/// a fat-pointer KIND must place the new kind by what its metadata MEANS.
#[cfg(test)]
mod fat_ptr_kind_classification_tests {
    use super::{
        fat_ptr_metadata_is_vtable_word, fat_ptr_metadata_len_is_isize_bounded, ty_carrier,
    };
    use trust_ir::Module;
    use trust_ir::ty::{FatPtrKind, Ty};
    use trust_ir::value::TyId;

    fn every_kind() -> [FatPtrKind; 5] {
        [
            FatPtrKind::Slice(TyId::new(0)),
            FatPtrKind::Str,
            FatPtrKind::TraitObject { trait_id: 0 },
            FatPtrKind::ContainerLen,
            FatPtrKind::ContainerVtable,
        ]
    }

    /// The census names the v40 kind by ITS OWN label. Folding it into
    /// `TraitObject`'s (or an `Other` bucket) would be the attribution failure
    /// the exhaustive match exists to prevent.
    #[test]
    fn census_carrier_names_container_vtable_as_its_own_class() {
        assert_eq!(ty_carrier(&Ty::FatPtr(FatPtrKind::ContainerVtable)), "FatPtr_ContainerVtable");
        let labels: std::collections::BTreeSet<String> =
            every_kind().iter().map(|kind| ty_carrier(&Ty::FatPtr(*kind))).collect();
        assert_eq!(labels.len(), every_kind().len(), "two fat-pointer kinds share a census label");
    }

    /// Metadata meaning: `ContainerVtable` follows `TraitObject` (a vtable word),
    /// never `Slice`/`Str`/`ContainerLen` (a length) — trust-ir's own rule.
    #[test]
    fn container_vtable_metadata_is_a_vtable_word_not_a_length() {
        for kind in every_kind() {
            let is_vtable =
                matches!(kind, FatPtrKind::TraitObject { .. } | FatPtrKind::ContainerVtable);
            assert_eq!(fat_ptr_metadata_is_vtable_word(&Ty::FatPtr(kind)), is_vtable, "{kind:?}");
        }
        assert!(!fat_ptr_metadata_is_vtable_word(&Ty::Ptr), "a thin pointer has no metadata word");
    }

    /// No `len <= isize::MAX` bound may ever be pushed for a vtable-word kind, and
    /// `ContainerLen` (a length with no element type) stays unbounded too.
    #[test]
    fn no_isize_length_bound_for_vtable_word_or_container_len_kinds() {
        let module = Module::new("classification");
        for kind in [
            FatPtrKind::ContainerVtable,
            FatPtrKind::TraitObject { trait_id: 0 },
            FatPtrKind::ContainerLen,
        ] {
            assert!(!fat_ptr_metadata_len_is_isize_bounded(&module, &Ty::FatPtr(kind)), "{kind:?}");
        }
        assert!(fat_ptr_metadata_len_is_isize_bounded(&module, &Ty::FatPtr(FatPtrKind::Str)));
    }
}

#[cfg(test)]
mod make_aggregate_operand_tests {
    use super::*;

    #[test]
    fn make_closure_uses_preserve_capture_order_and_duplicates() {
        for captures in [vec![], vec![ValueId::new(7), ValueId::new(2), ValueId::new(7)]] {
            let inst = Inst::MakeClosure {
                ty: trust_ir::value::ClosureTyId::new(0),
                func: FuncId::new(42),
                captures: captures.clone(),
            };
            let mut uses = vec![ValueId::new(99)];
            assert!(!collect_inst_value_uses(&inst, &mut uses));
            let mut expected = vec![ValueId::new(99)];
            expected.extend(captures);
            assert_eq!(uses, expected);
        }
    }

    #[test]
    fn make_closure_pointer_capture_is_an_unbounded_cell_escape() {
        let mut function = Function::new(
            FuncId::new(0),
            "capture_escape",
            trust_ir::value::FuncTyId::new(0),
            BlockId::new(0),
        );
        let mut block = trust_ir::Block::new(BlockId::new(0));
        block.body.push(
            InstrNode::new(Inst::Alloca { ty: Ty::I64, count: None, align: None })
                .with_result(ValueId::new(7)),
        );
        block.body.push(
            InstrNode::new(Inst::MakeClosure {
                ty: trust_ir::value::ClosureTyId::new(0),
                func: FuncId::new(42),
                captures: vec![ValueId::new(7)],
            })
            .with_result(ValueId::new(8)),
        );
        block.body.push(InstrNode::new(Inst::Return { values: vec![] }));
        function.blocks.push(block);
        assert_eq!(
            stack_alloca_escape_classification(&function, ValueId::new(7)),
            StackCellEscape::Unbounded
        );
    }

    #[test]
    fn make_aggregate_uses_preserve_lane_order_and_duplicates() {
        for fields in [vec![], vec![ValueId::new(7), ValueId::new(2), ValueId::new(7)]] {
            let inst = Inst::MakeAggregate {
                ty: Ty::Tuple(vec![]),
                variant: None,
                fields: fields.clone(),
            };
            let mut uses = vec![ValueId::new(99)];
            assert!(!collect_inst_value_uses(&inst, &mut uses));
            let mut expected = vec![ValueId::new(99)];
            expected.extend(fields);
            assert_eq!(uses, expected);
        }
    }

    /// v50 `[value; n]` reads its one operand exactly once, at every length:
    /// the lane count is in the type, never in the operand list.
    #[test]
    fn array_splat_uses_its_one_operand_once_at_any_length() {
        for len in [1, 256, u64::MAX] {
            let inst = Inst::ArraySplat {
                ty: Ty::Array(trust_ir::TyId::new(0), len),
                value: ValueId::new(7),
            };
            let mut uses = vec![ValueId::new(99)];
            assert!(!collect_inst_value_uses(&inst, &mut uses), "len {len}");
            assert_eq!(uses, vec![ValueId::new(99), ValueId::new(7)], "len {len}");
        }
    }
}
