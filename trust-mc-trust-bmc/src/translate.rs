// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Core translation from trust_ir to trust_mc BMC verification conditions.
//!
//! Walks a `trust_ir::Module`, generating `BmcVc` for each function. Each
//! potentially-failing instruction becomes a `Violation` in the VC. Bare trust_ir
//! proof annotations are metadata only and cannot suppress obligations without
//! a checked-evidence API.

use std::collections::BTreeMap;

use ay_bindings::{Expr, ExprValue, Sort};
use trust_ir::inst::{BinOp, Inst, OverflowOp, UnOp};
use trust_ir::node::InstrNode;
use trust_ir::proof::ProofAnnotation;
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Function, Module};
use trust_mc_core::bmc::{BmcQuery, BmcVc};
use trust_mc_core::decl::Decl;
use trust_mc_core::ident::{PropertyId, SourceLocation};
use trust_mc_core::violation::{PropertyKind, Violation};

use crate::bulk_count::{ByteCount, Truth};
use crate::signature_abi::first_typed_signature_abi;

/// Trust: host target thin-pointer width in bits. trust-ir `Ty::bit_width()`
/// returns `None` for pointer-like types as of trust-ir 6ed4bf0 (pointer width
/// became target-dependent — a wasm32 correctness fix). Trust verifies host-target
/// (64-bit) code, so resolve pointers at 64 via `bit_width_with`, exactly
/// restoring the pre-6ed4bf0 `Some(64)` behavior. See the matching const in
/// `translate_chc.rs`.
const HOST_POINTER_BITS: u32 = 64;

/// Options controlling VC generation.
#[derive(Debug, Clone)]
pub struct TranslateOptions {
    /// Emit signed overflow checks (default: true).
    pub check_signed_overflow: bool,
    /// Emit unsigned overflow checks (default: true).
    pub check_unsigned_overflow: bool,
    /// Emit division-by-zero checks (default: true).
    pub check_div_by_zero: bool,
    /// Emit memory bounds checks for Load/Store (default: true).
    pub check_memory_bounds: bool,
    /// SMT logic hint for the generated queries.
    pub logic: Option<String>,
    /// Timeout in milliseconds for each query.
    pub timeout_ms: Option<u64>,
    /// Collect the direct-call-summary census into
    /// `ChcTranslationOutput::call_summary_census` (default: false).
    ///
    /// PURELY OBSERVATIONAL. It switches no check off, emits no rule,
    /// suppresses no rule and changes no verdict -- it records, per
    /// `Inst::Call` site, whether the modular call summary succeeded and which
    /// labelled exit a decline took. Off by default so production translation
    /// allocates nothing for it.
    pub collect_call_summary_census: bool,
}

impl Default for TranslateOptions {
    fn default() -> Self {
        Self {
            check_signed_overflow: true,
            check_unsigned_overflow: true,
            check_div_by_zero: true,
            check_memory_bounds: true,
            logic: Some("QF_BV".to_owned()),
            timeout_ms: None,
            collect_call_summary_census: false,
        }
    }
}

/// Translate a `trust_ir::Module` into a set of BMC verification conditions.
///
/// Valid modules yield one `BmcVc` per actual function. Invalid modules yield
/// one unconditional module-input `Other` refusal, even with no functions; it
/// has no fabricated function owner or source symbols. No instruction-level
/// assumption can hide input invalidity. A valid empty library has no function
/// obligations; an empty batch is never program-proof authority. Potentially
/// failing operations retain their checks despite bare proof annotations.
pub fn trust_ir_to_bmc_vc(module: &Module, options: &TranslateOptions) -> Vec<BmcVc> {
    crate::input::ModuleInput::new(module).all(options)
}

/// Translate one function from a `trust_ir::Module` into a BMC verification condition.
///
/// The complete module is canonically validated before translation. An
/// existing selection in an invalid module yields an unconditional module-input
/// `Other` refusal. `None` denotes an actually absent function: a refusal to
/// translate that selection, never a successful verification or evidence that
/// the module was valid.
pub fn trust_ir_function_to_bmc_vc(
    module: &Module,
    function: FuncId,
    options: &TranslateOptions,
) -> Option<BmcVc> {
    crate::input::ModuleInput::new(module).function(function, options)
}

/// A symbolic memory region created by an `Alloca` instruction.
///
/// Each memory region is modeled as an SMT array mapping 64-bit addresses
/// (offsets within the region) to elements of the allocated type. Stores
/// update the array, loads select from it.
#[derive(Debug, Clone)]
#[allow(dead_code)] // base_ptr retained for diagnostics and future use
struct MemoryRegion {
    /// The symbolic array representing this memory region's contents.
    /// Sort: `Array(BV64, element_sort)` where element_sort comes from the
    /// allocation type.
    array: Expr,
    /// The element sort for bounds checking and type consistency.
    element_sort: Sort,
    /// The number of elements in this region (None = unknown/symbolic).
    count: Option<u64>,
    /// The base pointer expression associated with this region.
    base_ptr: Expr,
    /// The `Alloca`'s declared type: the type of every element, whose byte size
    /// a bulk `MemCopy`/`MemSet` compares its count with.
    ty: Ty,
}

/// What a bulk instruction writes: a copy of `src`, or a fill with `byte`.
#[derive(Debug, Clone, Copy)]
enum BulkWrite {
    Copy { src: ValueId, overlap: bool },
    Fill { byte: ValueId },
}

/// Does `ty` take the 64-bit compound placeholder sort in [`ty_to_sort`] — one
/// element standing for a value whose bytes the array model does not split?
fn ty_is_compound_placeholder(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Struct(_)
            | Ty::Array(_, _)
            | Ty::Tuple(_)
            | Ty::Enum(_)
            | Ty::Set(_, _)
            | Ty::Sequence(_)
            | Ty::Record(_)
            | Ty::Closure(_)
            | Ty::Refine(_, _)
            | Ty::Dialect(_)
    )
}

/// What a whole-cell bulk write leaves in the destination region.
enum WholeCellWrite {
    /// A copy from a cell of the same type: the source region's whole array.
    Region(Expr),
    /// A fill of an integer cell: its one element.
    Element(Expr),
}

/// The element of an INTEGER `ty` (`size` bytes) whose every byte is `byte`, or
/// `None` for any other type: a `bool`, `char`, float or pointer has invalid or
/// unmodeled byte images, and a compound type is one placeholder in this model.
fn repeated_byte_element(ty: &Ty, size: u64, byte: &Expr) -> Option<Expr> {
    if !ty.is_integer() || byte.sort().bitvec_width() != Some(8) {
        return None;
    }
    let width = ty_to_sort(ty).bitvec_width()?;
    if width == 0 || u64::from(width) != size.checked_mul(8)? {
        return None;
    }
    let mut repeated = byte.clone();
    for _ in 1..width / 8 {
        repeated = repeated.try_concat(byte.clone()).ok()?;
    }
    Some(repeated)
}

/// A CFG edge into a block, recorded while translating the predecessor's
/// terminator in the guarded-path encoding.
#[derive(Debug, Clone)]
struct IncomingEdge {
    /// Exact condition under which this edge is taken:
    /// `guard(predecessor) AND edge condition` (branch leg / switch case).
    guard: Expr,
    /// Block-parameter argument expressions, evaluated in the predecessor's
    /// context and normalized to the target's parameter types.
    args: Vec<Expr>,
}

/// Which compare-exchange a `CmpXchg` node is (trust-ir v48 `weak` flag).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CmpXchgStrength {
    /// Succeeds exactly when the current value equals the expected one.
    Strong,
    /// May also fail spuriously when the values are equal.
    Weak,
}

/// Per-function translation state.
struct FuncTranslator<'a> {
    func: &'a Function,
    module: &'a Module,
    options: &'a TranslateOptions,
    /// Maps ValueId → symbolic Expr for SSA values.
    values: BTreeMap<ValueId, Expr>,
    /// Declarations accumulated for the VC.
    decls: Vec<Decl>,
    /// Path constraints accumulated for the VC.
    constraints: Vec<Expr>,
    /// Violations accumulated for the VC.
    violations: Vec<Violation>,
    /// Counter for generating unique property IDs.
    next_property_id: u32,
    /// Counter for generating unique symbolic variable names.
    next_sym_id: u32,
    /// Memory regions: maps the pointer ValueId from Alloca to its region.
    memory_regions: BTreeMap<ValueId, MemoryRegion>,
    /// GEP result pointers: maps pointer ValueId to (base_ptr_id, offset_expr).
    gep_results: BTreeMap<ValueId, (ValueId, Expr)>,
    /// Pointer lane facts for values built by PtrFromParts.
    ptr_parts: BTreeMap<ValueId, (Expr, Expr)>,
    /// Reachability at the current instruction: the block-entry guard AND
    /// every assumption already encountered in that block. A later assumption
    /// must not constrain an earlier violation or another block's prefix.
    current_guard: Expr,
}

impl<'a> FuncTranslator<'a> {
    fn new(func: &'a Function, module: &'a Module, options: &'a TranslateOptions) -> Self {
        Self {
            func,
            module,
            options,
            values: BTreeMap::new(),
            decls: Vec::new(),
            constraints: Vec::new(),
            violations: Vec::new(),
            next_property_id: 0,
            next_sym_id: 0,
            memory_regions: BTreeMap::new(),
            gep_results: BTreeMap::new(),
            ptr_parts: BTreeMap::new(),
            current_guard: Expr::true_(),
        }
    }

    fn alloc_property_id(&mut self, desc: impl Into<String>) -> PropertyId {
        let id = self.next_property_id;
        self.next_property_id += 1;
        PropertyId::with_description(id, desc)
    }

    /// Create a fresh symbolic variable for a given trust_ir type.
    fn fresh_symbolic(&mut self, prefix: &str, ty: &Ty) -> Expr {
        let sort = ty_to_sort(ty);
        let name = format!("{}_{}", prefix, self.next_sym_id);
        self.next_sym_id += 1;
        let expr = Expr::var(&name, sort.clone());
        self.decls.push(Decl::constant(&name, sort));
        expr
    }

    /// Resolve an already-validated SSA value to its symbolic expression.
    fn resolve(&mut self, val: ValueId, ty: &Ty) -> Expr {
        if let Some(expr) = self.values.get(&val) {
            return expr.clone();
        }
        // Complete module validity precedes this walk; entry and block parameters
        // are bound explicitly. This existing conservative diagnostic fallback
        // is not permission to invent an undefined/non-dominating source value.
        let expr = self.fresh_symbolic(&format!("v{}", val.0), ty);
        self.values.insert(val, expr.clone());
        expr
    }

    /// Bind a ValueId to an expression.
    fn bind(&mut self, val: ValueId, expr: Expr) {
        self.values.insert(val, expr);
    }

    /// Add a violation (potential property failure).
    ///
    /// Capture the current instruction-prefix guard. Later assumptions must
    /// not alter the feasible paths on which this instruction can fail.
    fn add_violation(&mut self, kind: PropertyKind, condition: Expr, msg: &str, node: &InstrNode) {
        let prop_id = self.alloc_property_id(msg);
        let condition = and_guard(&self.current_guard, condition);
        let mut violation = Violation::new(prop_id, kind, condition).with_message(msg);
        if let Some(span) = &node.span {
            violation = violation.with_location(SourceLocation::new(
                format!("{}:{}", self.module.name, span.file),
                span.line,
            ));
        }
        self.violations.push(violation);
    }

    /// Add an always-failing VC for trust_ir semantics this translator cannot model exactly.
    ///
    /// The refusal fires on the prefix reaching this instruction, including
    /// preceding assumptions but never assumptions appearing later.
    fn add_unsupported_semantics(&mut self, reason: impl Into<String>, node: &InstrNode) {
        let reason = reason.into();
        self.add_violation(
            PropertyKind::Other,
            Expr::true_(),
            &format!("unsupported trust_ir semantics in {}: {reason}", self.func.name),
            node,
        );
    }

    /// Add an always-failing VC scoped to an explicit guard (used for
    /// unsupported semantics discovered while wiring CFG edges, where no
    /// single instruction node is being translated).
    fn add_guarded_unsupported_violation(&mut self, reason: impl Into<String>, guard: Expr) {
        let reason = reason.into();
        let msg = format!("unsupported trust_ir semantics in {}: {reason}", self.func.name);
        let prop_id = self.alloc_property_id(&msg);
        let violation = Violation::new(prop_id, PropertyKind::Other, guard).with_message(&msg);
        self.violations.push(violation);
    }

    /// Apply a memory-array update only when the current block executes.
    ///
    /// In a guarded CFG region a store in an untaken branch must not be
    /// observable elsewhere, so the update is wrapped in
    /// `ite(guard, updated, original)`. An unconditional prefix (guard = true)
    /// keeps the plain update.
    fn guard_array_update(&self, updated: Expr, original: Expr) -> Expr {
        if expr_is_true(&self.current_guard) {
            updated
        } else {
            Expr::ite(self.current_guard.clone(), updated, original)
        }
    }

    /// Resolve a pointer to its backing memory region, if any.
    ///
    /// Walks through GEP chains to find the original Alloca. Returns the
    /// region and the offset expression within it.
    fn resolve_memory_region(&self, ptr: ValueId) -> Option<(&MemoryRegion, Expr)> {
        // Direct alloca pointer
        if let Some(region) = self.memory_regions.get(&ptr) {
            return Some((region, Expr::bitvec_const(0u64, 64)));
        }
        // GEP result pointer — chase to base
        if let Some((base_id, offset)) = self.gep_results.get(&ptr) {
            if let Some(region) = self.memory_regions.get(base_id) {
                return Some((region, offset.clone()));
            }
            // Nested GEP: chase one more level
            if let Some((base_base_id, base_offset)) = self.gep_results.get(base_id) {
                if let Some(region) = self.memory_regions.get(base_base_id) {
                    let combined = base_offset.clone().bvadd(offset.clone());
                    return Some((region, combined));
                }
            }
        }
        None
    }

    /// Translate the entire function.
    fn translate(mut self) -> BmcVc {
        // trust-ir wire v60: a typed signature ABI anywhere in the module is
        // transport this lowering does not model (`crate::signature_abi`).
        if let Some(func_ty) = first_typed_signature_abi(self.module) {
            self.add_guarded_unsupported_violation(
                format!("typed signature ABI transport (function type #{func_ty})"),
                Expr::true_(),
            );
        }
        // Create symbolic variables for block parameters of the entry block.
        if let Some(entry_block) = self.func.blocks.iter().find(|b| b.id == self.func.entry) {
            for (val, ty) in &entry_block.params {
                let expr = self.fresh_symbolic(&format!("param_{}", val.0), ty);
                self.values.insert(*val, expr);
            }
        }

        match self.acyclic_topo_order() {
            // Acyclic, structurally well-formed CFG: exact guarded-path
            // encoding. Single-block functions start with a constant-true
            // entry guard and use the same instruction-prefix semantics.
            Some(order) => self.translate_guarded_blocks(&order),
            // No execution order is modeled for a cyclic or malformed CFG.
            // Refuse the structure independently of any instruction-local
            // assumption; a linear walk could hide this refusal or conflate
            // values and memory from unrelated blocks.
            //
            // A `Constant::TensorBlob` switch case (`crate::tensor_region`) is
            // one such structure: it is named rather than lumped in with the
            // generic refusal.
            None => {
                let blob_case = self.func.blocks.iter().flat_map(|block| &block.body).any(|node| {
                    matches!(node.inst, Inst::Switch { .. })
                        && crate::tensor_region::inst_carries_tensor_blob(&node.inst)
                });
                let reason = if blob_case {
                    tensor_region_semantics(crate::TensorConstruct::TensorBlobConstant)
                } else {
                    "path-sensitive control flow (cyclic or structurally unsupported CFG)"
                        .to_owned()
                };
                self.add_guarded_unsupported_violation(reason, Expr::true_());
            }
        }

        let query = query_for_options(self.options);

        BmcVc {
            decls: self.decls,
            constraints: self.constraints,
            violations: self.violations,
            query,
            model_queries: Vec::new(),
        }
    }

    /// Topologically order the function's blocks for the guarded-path BMC
    /// encoding.
    ///
    /// Returns `None` — making the caller fall back to the legacy fail-closed
    /// linear translation — unless ALL structural requirements hold:
    ///
    /// - block ids are unique and the entry block exists;
    /// - every block ends with exactly one supported terminator
    ///   (`Br`/`CondBr`/`Switch`/`Return`/`Unreachable`) and contains no
    ///   terminator before its last instruction;
    /// - every branch target exists and is passed exactly as many arguments
    ///   as the target declares block parameters;
    /// - switch case values are scalar (`Int`/`Bool`) constants with no
    ///   duplicate values;
    /// - the CFG has no cycles. Loops require bounded unrolling, which this
    ///   encoding does not implement yet, so they remain fail-closed.
    fn acyclic_topo_order(&self) -> Option<Vec<usize>> {
        let blocks = &self.func.blocks;
        if blocks.is_empty() {
            return None;
        }

        let mut index_of: BTreeMap<BlockId, usize> = BTreeMap::new();
        for (idx, block) in blocks.iter().enumerate() {
            if index_of.insert(block.id, idx).is_some() {
                // Duplicate block ids make edge targets ambiguous.
                return None;
            }
        }
        index_of.get(&self.func.entry)?;

        let mut successors: Vec<Vec<usize>> = vec![Vec::new(); blocks.len()];
        for (idx, block) in blocks.iter().enumerate() {
            let (terminator, body) = block.body.split_last()?;
            if body.iter().any(|node| node.inst.is_terminator()) {
                // Control flow leaves the block before its last instruction.
                return None;
            }

            let mut targets: Vec<(BlockId, usize)> = Vec::new();
            match &terminator.inst {
                Inst::Br { target, args } => targets.push((*target, args.len())),
                Inst::CondBr { then_target, then_args, else_target, else_args, .. } => {
                    targets.push((*then_target, then_args.len()));
                    targets.push((*else_target, else_args.len()));
                }
                Inst::Switch { default, default_args, cases, .. } => {
                    targets.push((*default, default_args.len()));
                    let mut seen_values: Vec<&trust_ir::constant::Constant> =
                        Vec::with_capacity(cases.len());
                    for case in cases {
                        if !matches!(
                            case.value,
                            trust_ir::constant::Constant::Int(_)
                                | trust_ir::constant::Constant::Bool(_)
                        ) {
                            return None;
                        }
                        if seen_values.contains(&&case.value) {
                            // Duplicate case values have ambiguous semantics.
                            return None;
                        }
                        seen_values.push(&case.value);
                        targets.push((case.target, case.args.len()));
                    }
                }
                Inst::Return { .. } | Inst::Unreachable => {}
                // Not a supported block terminator.
                _ => return None,
            }

            for (target, arg_count) in targets {
                let target_idx = *index_of.get(&target)?;
                if blocks[target_idx].params.len() != arg_count {
                    return None;
                }
                successors[idx].push(target_idx);
            }
        }

        // Kahn's algorithm over every block. Blocks unreachable from the
        // entry still need an order position (their guards become `false`);
        // a cycle anywhere rejects the function.
        let mut in_degree = vec![0usize; blocks.len()];
        for succs in &successors {
            for &succ in succs {
                in_degree[succ] += 1;
            }
        }
        let mut ready: Vec<usize> = (0..blocks.len()).filter(|&i| in_degree[i] == 0).collect();
        let mut order = Vec::with_capacity(blocks.len());
        while let Some(idx) = ready.pop() {
            order.push(idx);
            for &succ in &successors[idx] {
                in_degree[succ] -= 1;
                if in_degree[succ] == 0 {
                    ready.push(succ);
                }
            }
        }
        (order.len() == blocks.len()).then_some(order)
    }

    /// Translate an acyclic multi-block CFG with the guarded-path encoding.
    ///
    /// Every block gets an exact reachability guard:
    /// - entry block guard = `true`;
    /// - `guard(b)` = OR over incoming edges of
    ///   `guard(pred) AND edge condition`.
    ///
    /// Each instruction sees that entry guard conjoined with the assumptions
    /// preceding it. Violations retain that prefix, memory updates are guarded,
    /// and outgoing edges carry the final prefix. Block parameters remain
    /// fresh symbolics constrained only by their feasible incoming edges.
    fn translate_guarded_blocks(&mut self, order: &[usize]) {
        let func = self.func;
        let mut incoming: BTreeMap<BlockId, Vec<IncomingEdge>> = BTreeMap::new();

        for &idx in order {
            let block = &func.blocks[idx];
            let is_entry = block.id == func.entry;
            // All predecessors precede this block in topological order, so
            // every incoming edge has already been recorded.
            let edges = incoming.remove(&block.id).unwrap_or_default();

            let guard = if is_entry {
                // Execution always starts at the entry block. Any edge into
                // the entry can only originate from a block that is itself
                // unreachable (a reachable predecessor would form a cycle),
                // so such edges carry a false guard and are safely dropped.
                Expr::true_()
            } else {
                self.define_block_guard(idx, &edges)
            };

            if !is_entry {
                self.bind_block_params(idx, &edges);
            }

            self.current_guard = guard.clone();
            // acyclic_topo_order guarantees a non-empty body.
            let Some((terminator, body)) = block.body.split_last() else {
                continue;
            };
            for node in body {
                self.translate_node(node);
            }
            match &terminator.inst {
                Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } => {
                    let outgoing_guard = self.current_guard.clone();
                    self.record_outgoing_edges(terminator, &outgoing_guard, &mut incoming);
                }
                // Return / Unreachable: translated normally; their VCs are
                // scoped to the block guard via add_violation.
                _ => self.translate_node(terminator),
            }
            self.current_guard = Expr::true_();
        }
    }

    /// Declare the guard for a non-entry block: a fresh boolean constrained
    /// to equal the disjunction of its incoming edge conditions. A block
    /// with no incoming edges is structurally unreachable (guard = `false`).
    fn define_block_guard(&mut self, block_idx: usize, edges: &[IncomingEdge]) -> Expr {
        if edges.is_empty() {
            return Expr::false_();
        }
        let mut disjuncts: Vec<Expr> = edges.iter().map(|edge| edge.guard.clone()).collect();
        let combined = if disjuncts.len() == 1 {
            disjuncts.pop().expect("one disjunct must exist")
        } else {
            Expr::or_many(disjuncts)
        };
        if expr_is_true(&combined) {
            // Unconditionally reachable (e.g. a straight `br` chain): keep
            // the literal `true` guard so downstream VCs stay unconditional.
            return Expr::true_();
        }
        // Name the guard so downstream conditions stay small and shared.
        let guard = self.fresh_symbolic(&format!("bb{block_idx}_guard"), &Ty::Bool);
        self.constraints.push(guard.clone().iff(combined));
        guard
    }

    /// Bind each parameter of a non-entry block to a fresh symbolic,
    /// constrained per incoming edge: `edge taken => param == passed arg`.
    ///
    /// Incoming edges are pairwise mutually exclusive on any single
    /// execution of an acyclic CFG (a second taken edge would require
    /// re-entering the block, i.e. a cycle), so values flowing from
    /// different predecessors are never conflated. When no edge is taken the
    /// parameter is unconstrained, which is harmless because every effect in
    /// the block is scoped to its (then-false) guard.
    fn bind_block_params(&mut self, block_idx: usize, edges: &[IncomingEdge]) {
        let func = self.func;
        let params = &func.blocks[block_idx].params;
        for (param_pos, (param_id, ty)) in params.iter().enumerate() {
            let param = self.fresh_symbolic(&format!("bb{block_idx}_v{}", param_id.0), ty);
            self.values.insert(*param_id, param.clone());
            for edge in edges {
                let Some(arg) = edge.args.get(param_pos) else {
                    continue;
                };
                if arg.sort() == param.sort() {
                    let binding = param.clone().eq(arg.clone());
                    self.constraints.push(implied_under_guard(&edge.guard, binding));
                } else {
                    // Sort mismatch (malformed trust_ir): leave the parameter
                    // unconstrained on this edge — an over-approximation that
                    // cannot mask a violation — and fail closed whenever the
                    // edge is feasible.
                    self.add_guarded_unsupported_violation(
                        format!(
                            "block parameter v{} receives a value of mismatched sort",
                            param_id.0
                        ),
                        edge.guard.clone(),
                    );
                }
            }
        }
    }

    /// Record the outgoing CFG edges of a branching terminator, resolving
    /// edge conditions and block arguments in the predecessor's context.
    fn record_outgoing_edges(
        &mut self,
        node: &InstrNode,
        guard: &Expr,
        incoming: &mut BTreeMap<BlockId, Vec<IncomingEdge>>,
    ) {
        match &node.inst {
            Inst::Br { target, args } => {
                self.record_edge(*target, args, None, guard, incoming);
            }
            Inst::CondBr { cond, then_target, then_args, else_target, else_args } => {
                let cond_expr = self.resolve(*cond, &Ty::Bool);
                let cond_expr = if cond_expr.sort().is_bool() {
                    cond_expr
                } else {
                    // The branch condition has no boolean semantics here
                    // (malformed trust_ir). Branch on a fresh unconstrained
                    // boolean instead — a sound over-approximation that keeps
                    // the two legs exclusive and exhaustive — and fail closed
                    // whenever this block is reachable.
                    self.add_unsupported_semantics(
                        "non-boolean conditional branch condition",
                        node,
                    );
                    self.fresh_symbolic("branch_cond", &Ty::Bool)
                };
                self.record_edge(*then_target, then_args, Some(cond_expr.clone()), guard, incoming);
                self.record_edge(*else_target, else_args, Some(cond_expr.not()), guard, incoming);
            }
            Inst::Switch { .. } => {
                self.record_switch_edges(node, guard, incoming);
            }
            _ => {}
        }
    }

    /// Record the outgoing edges of a `Switch` terminator.
    ///
    /// Case edge condition: `selector == case constant`; default edge
    /// condition: none of the cases matched. If the case constants cannot be
    /// encoded exactly against the selector's sort (sort mismatch, or values
    /// that collide after truncation to the selector width), the choice is
    /// over-approximated with prioritized fresh booleans (exactly one edge
    /// taken, matching real switch determinism) and the function fails
    /// closed whenever this block is reachable.
    fn record_switch_edges(
        &mut self,
        node: &InstrNode,
        guard: &Expr,
        incoming: &mut BTreeMap<BlockId, Vec<IncomingEdge>>,
    ) {
        let Inst::Switch { value, default, default_args, cases, exhaustive_enum_unreachable: _ } =
            &node.inst
        else {
            return;
        };

        let selector = match self.values.get(value) {
            Some(expr) => expr.clone(),
            None => self.resolve(*value, &Ty::I64),
        };

        let mut case_consts: Vec<Expr> = Vec::with_capacity(cases.len());
        let mut exact = true;
        for case in cases {
            match switch_case_expr(&case.value, &selector) {
                Some(constant) if !case_consts.contains(&constant) => case_consts.push(constant),
                _ => {
                    exact = false;
                    break;
                }
            }
        }

        let case_conds: Vec<Expr> = if exact {
            case_consts.into_iter().map(|constant| selector.clone().eq(constant)).collect()
        } else {
            self.add_unsupported_semantics(
                "switch with non-scalar, mismatched, or overlapping case values",
                node,
            );
            let picks: Vec<Expr> =
                (0..cases.len()).map(|_| self.fresh_symbolic("switch_pick", &Ty::Bool)).collect();
            let mut conds = Vec::with_capacity(picks.len());
            let mut none_before: Option<Expr> = None;
            for pick in picks {
                let cond = match &none_before {
                    None => pick.clone(),
                    Some(prev) => prev.clone().and(pick.clone()),
                };
                conds.push(cond);
                let not_pick = pick.not();
                none_before = Some(match none_before {
                    None => not_pick,
                    Some(prev) => prev.and(not_pick),
                });
            }
            conds
        };

        let default_cond = match case_conds.len() {
            0 => None,
            1 => Some(case_conds[0].clone().not()),
            _ => Some(Expr::and_many(case_conds.iter().cloned().map(Expr::not).collect())),
        };

        for (case, cond) in cases.iter().zip(case_conds.iter()) {
            self.record_edge(case.target, &case.args, Some(cond.clone()), guard, incoming);
        }
        self.record_edge(*default, default_args, default_cond, guard, incoming);
    }

    /// Record one CFG edge, evaluating block arguments in the predecessor's
    /// context and normalizing them to the target's parameter types.
    fn record_edge(
        &mut self,
        target: BlockId,
        args: &[ValueId],
        cond: Option<Expr>,
        pred_guard: &Expr,
        incoming: &mut BTreeMap<BlockId, Vec<IncomingEdge>>,
    ) {
        let func = self.func;
        // acyclic_topo_order verified existence and arity; clone the params
        // to release the shared borrow before resolving arguments.
        let params: Vec<(ValueId, Ty)> =
            func.block(target).map(|block| block.params.clone()).unwrap_or_default();
        let mut arg_exprs = Vec::with_capacity(args.len());
        for (arg, (_, ty)) in args.iter().zip(params.iter()) {
            let expr = self.resolve(*arg, ty);
            arg_exprs.push(normalize_expr_to_ty(&expr, ty));
        }
        let edge_guard = match cond {
            None => pred_guard.clone(),
            Some(cond) => and_guard(pred_guard, cond),
        };
        incoming
            .entry(target)
            .or_default()
            .push(IncomingEdge { guard: edge_guard, args: arg_exprs });
    }

    /// Translate a single instruction node.
    fn translate_node(&mut self, node: &InstrNode) {
        match &node.inst {
            // --- Arithmetic ---
            Inst::BinOp { op, ty, lhs, rhs } if ty.is_integer() => {
                self.translate_integer_binop(*op, ty, *lhs, *rhs, node);
            }

            // --- Division/remainder (always check div-by-zero) ---
            Inst::BinOp {
                op: op @ (BinOp::SDiv | BinOp::UDiv | BinOp::SRem | BinOp::URem),
                ty,
                lhs,
                rhs,
            } if ty.is_float() => {
                // Float division: no overflow check, but still evaluate.
                let lhs_expr = self.resolve(*lhs, ty);
                let rhs_expr = self.resolve(*rhs, ty);
                let result = self.fresh_symbolic("fdiv_result", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics(
                    format!("floating-point division/remainder operation {op:?}"),
                    node,
                );
                let _ = (lhs_expr, rhs_expr, op);
            }

            // --- Other BinOps (float arith, boolean connectives, vectors) ---
            Inst::BinOp { op, ty, lhs, rhs } => {
                let lhs_expr = self.resolve(*lhs, ty);
                let rhs_expr = self.resolve(*rhs, ty);
                let result = self.eval_binop(*op, ty, &lhs_expr, &rhs_expr);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                // Boolean connectives, including canonical BAnd/BOr/BXor,
                // are modeled PRECISELY by `eval_binop`. Every other
                // non-integer binop result is a havoc: fail closed so the
                // unconstrained value can never silently decide an obligation
                // — floating-point arithmetic in particular has no bitvector
                // encoding here (rounding, NaN/∞ propagation, -0.0).
                let modeled_precisely = matches!(ty, Ty::Bool)
                    && lhs_expr.sort().is_bool()
                    && rhs_expr.sort().is_bool()
                    && matches!(
                        op,
                        BinOp::And
                            | BinOp::Or
                            | BinOp::Xor
                            | BinOp::BAnd
                            | BinOp::BOr
                            | BinOp::BXor
                    );
                if !modeled_precisely {
                    let reason = if ty.is_float() || binop_is_floating_point(*op) {
                        format!("floating-point binary operation {op:?}")
                    } else {
                        format!("non-integer binary operation {op:?} on {ty:?}")
                    };
                    self.add_unsupported_semantics(reason, node);
                }
            }

            // --- Constants ---
            // trust-ir v67-v70 tensor region (`crate::tensor_region`): a
            // `TensorBlob`, or any constant of a tensor type, has no bits and
            // no sort here, so it fails closed by name before the arm below
            // could havoc it at a sort this lane does not have. Its result
            // stays unbound, as for the tensor instructions.
            Inst::Const { ty, value }
                if let Some(construct) =
                    crate::tensor_region::const_tensor_construct(ty, value) =>
            {
                self.add_tensor_region_violation(construct, node);
            }
            Inst::Const { ty, value } => {
                let expr = if matches!(value, trust_ir::constant::Constant::SymbolAddr { .. }) {
                    let expr = self.fresh_symbolic("symbol_addr", ty);
                    self.add_unsupported_semantics("relocatable symbol address constant", node);
                    expr
                } else if let Some(expr) = const_to_expr(ty, value) {
                    expr
                } else {
                    // No exact bit-level encoding (e.g. an F16 float constant,
                    // an F32 constant whose payload is not an exactly-widened
                    // f32, or a malformed vector constant). Havoc the value —
                    // a sound over-approximation — and fail closed so the
                    // wrong-bits placeholder can never decide an obligation.
                    let expr = self.fresh_symbolic("unmodeled_const", ty);
                    self.add_unsupported_semantics(
                        format!("constant without an exact bit-level encoding for {ty:?}"),
                        node,
                    );
                    expr
                };
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, expr);
                }
            }

            // --- Comparisons (no VCs when modeled exactly, just bind result) ---
            Inst::ICmp { op, ty, lhs, rhs } => {
                let lhs_expr = self.resolve(*lhs, ty);
                let rhs_expr = self.resolve(*rhs, ty);
                match self.eval_icmp(*op, ty, &lhs_expr, &rhs_expr) {
                    Some(result) => {
                        if let Some(result_id) = node.results.first() {
                            self.bind(*result_id, result);
                        }
                    }
                    None => {
                        // The comparison has no exact bit-level semantics for
                        // this type (mirrors translate_chc::eval_icmp).
                        // CRITICAL for floats: bitvector equality over IEEE-754
                        // bit patterns is NOT float equality (-0.0 == +0.0 but
                        // different bits; NaN != NaN but identical bits), and
                        // signed/unsigned bitvector order is not IEEE order.
                        // Havoc the boolean result and fail closed.
                        let result = self.fresh_symbolic("unsupported_icmp_result", &Ty::Bool);
                        if let Some(result_id) = node.results.first() {
                            self.bind(*result_id, result);
                        }
                        let reason = if ty.is_float() {
                            format!("floating-point comparison via ICmp on {ty:?}")
                        } else {
                            format!(
                                "integer comparison without exact bit-level semantics on {ty:?}"
                            )
                        };
                        self.add_unsupported_semantics(reason, node);
                    }
                }
            }

            // --- Load (array-based memory model) ---
            Inst::Load { ty, ptr, .. } => {
                self.translate_load(ty, *ptr, node);
            }

            // --- Store (array-based memory model) ---
            Inst::Store { ty, ptr, value, .. } => {
                // R129: a store carrying `ProofAnnotation::RegionHavocStore`
                // is a BULK write whose target set the producer could not
                // bound (e.g. `copy_nonoverlapping` with a symbolic element
                // count). This array-based memory model would translate it as
                // constraining a SINGLE (symbolic) index, leaving every OTHER
                // index at its pre-write value — a later read of an element
                // the real copy overwrote would return a STALE value, the
                // false-proof shape the annotation's consumer contract names.
                // Per that contract this backend has no sound reading and
                // MUST fail closed; the CHC lane owns the audited
                // whole-tracked-cell invalidation reading.
                if node.proofs.contains(&ProofAnnotation::RegionHavocStore) {
                    self.add_unsupported_semantics(
                        "region-havoc store: the array memory model would \
                         under-approximate the write set (stale-read hazard); \
                         whole-region invalidation is required",
                        node,
                    );
                } else {
                    self.translate_store(ty, *ptr, *value, node);
                }
            }

            // --- Assert → direct VC ---
            // trust-ir v52 `kind` and v54 `site` name WHICH panic a failed check
            // is and the entry it would call; neither changes when the check
            // fails (iff `cond` is false), and a failed assert is a terminal
            // panic outcome whatever its site, so the violation is the same.
            Inst::Assert { cond, kind: _, site: _ } => {
                let cond_expr = self.resolve(*cond, &Ty::Bool);
                if cond_expr.sort().is_bool() {
                    // Violation condition is !cond — if cond is false, the assert fails.
                    let violation_cond = cond_expr.not();
                    self.add_violation(
                        PropertyKind::Assertion,
                        violation_cond,
                        &format!("assertion failure in {}", self.func.name),
                        node,
                    );
                } else {
                    // Non-boolean assertion operand (malformed trust_ir):
                    // fail closed instead of emitting an ill-sorted VC.
                    self.add_unsupported_semantics("non-boolean assert condition", node);
                }
            }

            // --- Assume → remaining execution guard ---
            Inst::Assume { cond } => {
                let cond_expr = self.resolve(*cond, &Ty::Bool);
                if cond_expr.sort().is_bool() {
                    // Restrict only the remaining execution. A global
                    // constraint would retroactively erase earlier failures.
                    self.current_guard = and_guard(&self.current_guard, cond_expr);
                } else {
                    // Non-boolean assumption operand (malformed trust_ir):
                    // fail closed instead of emitting an ill-sorted constraint.
                    self.add_unsupported_semantics("non-boolean assume condition", node);
                }
            }

            // --- Return (postcondition VCs) ---
            Inst::Return { values } => {
                self.translate_return(values, node);
            }

            // --- Alloca (array-based memory region) ---
            Inst::Alloca { ty, count, .. } => {
                self.translate_alloca(ty, count.as_ref(), node);
            }

            Inst::HeapAlloc { .. } => {
                let ptr = self.fresh_symbolic("heap_alloc_ptr", &Ty::Ptr);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, ptr);
                }
                self.add_unsupported_semantics("heap allocation semantics", node);
            }

            // --- GEP (pointer arithmetic with bounds checking) ---
            // `inbounds` is a trust-ir backend hint (no-wrap GEP folding). We
            // deliberately ignore it here: turning it into an in-bounds
            // assumption could mask a real out-of-bounds access and make BMC
            // miss a violation (unsound for bug-finding). Keep the conservative
            // plain pointer-arithmetic translation.
            Inst::GEP { pointee_ty, base, indices, inbounds: _ } => {
                self.translate_gep(pointee_ty, *base, indices, node);
            }

            // --- Pointer lanes ---
            Inst::PtrData { ptr_ty, ptr } => {
                let data = self
                    .ptr_parts
                    .get(ptr)
                    .map(|(data, _)| data.clone())
                    .unwrap_or_else(|| self.resolve(*ptr, ptr_ty));
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, data);
                }
            }

            Inst::PtrMetadata { ptr_ty, metadata_ty, ptr } => {
                let metadata = if let Some((_, metadata)) = self.ptr_parts.get(ptr) {
                    metadata.clone()
                } else if matches!(metadata_ty, Ty::Unit) {
                    Expr::true_()
                } else {
                    let metadata = self.fresh_symbolic("ptr_metadata", metadata_ty);
                    self.add_unsupported_semantics(
                        format!("pointer metadata extraction from {ptr_ty:?}"),
                        node,
                    );
                    metadata
                };
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, metadata);
                }
            }

            Inst::PtrFromParts { ptr_ty: _, metadata_ty, data, metadata } => {
                let data_expr = self.resolve(*data, &Ty::Ptr);
                let metadata_expr = if matches!(metadata_ty, Ty::Unit) {
                    Expr::true_()
                } else {
                    self.resolve(*metadata, metadata_ty)
                };
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, data_expr.clone());
                    self.ptr_parts.insert(*result_id, (data_expr, metadata_expr));
                }
            }

            // --- Copy (identity) ---
            Inst::Copy { ty, operand } => {
                let expr = self.resolve(*operand, ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, expr);
                    if let Some(parts) = self.ptr_parts.get(operand).cloned() {
                        self.ptr_parts.insert(*result_id, parts);
                    }
                }
            }

            // --- Select ---
            Inst::Select { ty, cond, then_val, else_val } => {
                let cond_expr = self.resolve(*cond, &Ty::Bool);
                let then_expr = self.resolve(*then_val, ty);
                let else_expr = self.resolve(*else_val, ty);
                let result = Expr::ite(cond_expr, then_expr, else_expr);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
            }

            // --- Cast (fail closed until exact cast semantics land) ---
            Inst::Cast { op: _, src_ty: _, dst_ty, operand: _ } => {
                let result = self.fresh_symbolic("cast_result", dst_ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("cast operation", node);
            }

            // --- NullPtr ---
            Inst::NullPtr => {
                let expr = Expr::bitvec_const(0u64, 64);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, expr);
                }
            }

            Inst::GlobalAddr { .. } => {
                let ptr = self.fresh_symbolic("global_addr", &Ty::Ptr);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, ptr);
                }
                self.add_unsupported_semantics("global address semantics", node);
            }

            // --- Undef ---
            Inst::Undef { ty } => {
                let expr = self.fresh_symbolic("undef", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, expr);
                }
            }

            // --- Call (interprocedural) ---
            Inst::Call { callee, args } => {
                self.translate_call(*callee, args, node);
            }

            // --- Control flow needing path-exact semantics ---
            // Only reachable via the legacy linear translation, i.e. when
            // `acyclic_topo_order` rejected the function (loops/back-edges
            // or a structurally malformed CFG). Acyclic CFGs are handled
            // exactly by `translate_guarded_blocks` and never get here.
            Inst::Switch { .. } if crate::tensor_region::inst_carries_tensor_blob(&node.inst) => {
                self.add_tensor_region_violation(crate::TensorConstruct::TensorBlobConstant, node);
            }
            Inst::Br { .. } | Inst::CondBr { .. } | Inst::Switch { .. } => {
                self.add_unsupported_semantics(
                    "path-sensitive control flow (cyclic or structurally unsupported CFG)",
                    node,
                );
            }

            Inst::Unreachable => {
                // add_violation scopes the condition to the current block
                // guard, so this fires exactly when a feasible path reaches
                // the Unreachable instruction (and stays unconditional in
                // straight-line code, where the guard is literally true).
                self.add_violation(
                    PropertyKind::Unreachable,
                    Expr::true_(),
                    &format!("unreachable instruction reached in {}", self.func.name),
                    node,
                );
            }

            Inst::CallIndirect { .. } => {
                self.add_unsupported_semantics("indirect call dispatch", node);
            }

            Inst::Fence { .. } => {
                self.add_unsupported_semantics("atomic fence ordering", node);
            }

            // --- Unary operations: exact integer Not/Neg, otherwise fail closed by name ---
            Inst::UnOp { op, ty, operand } => {
                let operand_expr = normalize_expr_to_ty(&self.resolve(*operand, ty), ty);
                let result = match op {
                    UnOp::Not if ty.is_integer() && *operand_expr.sort() == ty_to_sort(ty) => {
                        operand_expr.bvnot()
                    }
                    UnOp::Neg if ty.is_integer() && *operand_expr.sort() == ty_to_sort(ty) => {
                        // Match the CHC lane's overflow policy. Raw IR negation
                        // is modular; the selected policy adds an obligation.
                        // The value is always bvneg; only that obligation is
                        // suppressed by Wrapping or the selected overflow policy.
                        if !node.proofs.contains(&ProofAnnotation::Wrapping) {
                            let no_overflow = if ty.is_signed() {
                                self.options
                                    .check_signed_overflow
                                    .then(|| operand_expr.clone().bvneg_no_overflow())
                            } else {
                                self.options.check_unsigned_overflow.then(|| {
                                    operand_expr.clone().eq(Expr::bitvec_const(
                                        0u64,
                                        ty.bit_width_with(HOST_POINTER_BITS)
                                            .expect("integer type has a bit width"),
                                    ))
                                })
                            };
                            if let Some(no_overflow) = no_overflow {
                                let signedness = if ty.is_signed() { "signed" } else { "unsigned" };
                                self.add_violation(
                                    PropertyKind::ArithmeticOverflow,
                                    no_overflow.not(),
                                    &format!("{signedness} neg overflow in {}", self.func.name),
                                    node,
                                );
                            }
                        }
                        operand_expr.bvneg()
                    }
                    // Exhaustive so a new trust-ir operation must be deliberately
                    // modeled or refused. Type/sort mismatches also stay refused.
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
                        self.add_unsupported_semantics(
                            format!("unary operation {}", unop_name(*op)),
                            node,
                        );
                        self.fresh_symbolic("unop_result", ty)
                    }
                };
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
            }

            // --- Overflow check instruction (CheckedBinaryOp) ---
            // Produces (wrapped_result, overflow_flag). The result is the
            // two's-complement wrapped op (matching Rust's checked arithmetic);
            // the flag is the negation of the no-overflow predicate. Binding the
            // flag to its real meaning lets the following `Assert{Overflow}`
            // panic-freedom obligation be proved (or refuted) rather than failing
            // closed — the obligation references exactly this flag.
            Inst::Overflow { op, ty, lhs, rhs } => {
                let binop = overflow_op_to_binop(*op);
                let lhs_expr = self.resolve(*lhs, ty);
                let rhs_expr = self.resolve(*rhs, ty);
                let result_val = self.eval_binop(binop, ty, &lhs_expr, &rhs_expr);
                let mut results = node.results.iter();
                if let Some(r) = results.next() {
                    self.bind(*r, result_val);
                }
                if let Some(r) = results.next() {
                    match integer_binop_no_overflow_condition(
                        binop,
                        ty,
                        &lhs_expr,
                        &rhs_expr,
                        self.options,
                    ) {
                        Some(no_overflow) => self.bind(*r, no_overflow.not()),
                        None => {
                            // Non-integer operand or overflow checks disabled:
                            // keep the flag symbolic and fail closed.
                            let flag = self.fresh_symbolic("ovf_flag", &Ty::Bool);
                            self.bind(*r, flag);
                            self.add_unsupported_semantics("overflow intrinsic result pair", node);
                        }
                    }
                }
            }

            // MakeAggregate has no BMC construction model yet. A symbolic result
            // must retain an unsupported VC even when the result is unused.
            Inst::MakeAggregate { ty, .. } => {
                let result = self.fresh_symbolic("make_aggregate_result", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("MakeAggregate construction", node);
            }

            // A closure carries a function target as well as ordered captures.
            // This lane has no closure value/application model. Refuse even an
            // unused constructor: construction consumes captures, so merely
            // havocing the result could hide poison or handle misuse.
            Inst::MakeClosure { ty, .. } => {
                let result = self.fresh_symbolic("make_closure_result", &Ty::Closure(*ty));
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("MakeClosure construction", node);
            }

            // trust-ir v50 `ArraySplat` (`[value; n]`, `ty = Array(e, n)`): pure
            // and total — no memory effect, no run-time obligation. This lane
            // has no aggregate VALUE model: an array is the opaque carrier sort
            // `ty_to_sort` gives every compound type, the same one a constant
            // array literal gets from `const_to_expr`. So the result is ONE
            // fresh value whatever `n` is (constant size; nothing walks the
            // lanes), and it needs no unsupported VC: an unconstrained array
            // over-approximates `[value; n]` (every real value is a model), and
            // every consumer that could inspect a lane — `ExtractElement`,
            // `InsertElement`, `ExtractField`, `InsertField`, and the eq/order
            // type gates of `ICmp` — independently fails closed, exactly as for
            // an `Undef` or a constant array. An operand-free fresh value also
            // reads nothing of `value`, so no fact about it is imported.
            Inst::ArraySplat { ty, value: _ } => {
                let result = self.fresh_symbolic("array_splat", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
            }

            Inst::ExtractField { ty, aggregate: _, field: _ }
            | Inst::ExtractElement { ty, array: _, index: _ } => {
                let result = self.fresh_symbolic("extract_result", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("aggregate extraction", node);
            }

            Inst::InsertField { ty, aggregate, field: _, value: _ }
            | Inst::InsertElement { ty, array: aggregate, index: _, value: _ } => {
                let _agg_expr = self.resolve(*aggregate, ty);
                let result = self.fresh_symbolic("insert_result", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("aggregate insertion", node);
            }

            // --- AtomicLoad (same as Load for sequential BMC) ---
            Inst::AtomicLoad { ty, ptr, ordering: _ } => {
                self.translate_load(ty, *ptr, node);
            }

            // --- AtomicStore (same as Store for sequential BMC) ---
            Inst::AtomicStore { ty, ptr, value, ordering: _ } => {
                self.translate_store(ty, *ptr, *value, node);
            }

            // --- AtomicRMW (read-modify-write: load old, compute, store new) ---
            Inst::AtomicRMW { op, ty, ptr, value, ordering: _ } => {
                self.translate_atomic_rmw(*op, ty, *ptr, *value, node);
            }

            // --- CmpXchg (conditional exchange with VC) ---
            Inst::CmpXchg { ty, ptr, expected, desired, weak, .. } => {
                let strength = if *weak { CmpXchgStrength::Weak } else { CmpXchgStrength::Strong };
                self.translate_cmpxchg(ty, *ptr, *expected, *desired, strength, node);
            }

            // --- FCmp (fail closed: havoc result + unsupported VC) ---
            //
            // SOUNDNESS DECISION: FCmp is NEVER lowered to bitvector equality
            // or bitvector order over the operands' IEEE-754 bit patterns,
            // even though float constants carry exact bit patterns. Bit
            // equality is not IEEE equality (-0.0 == +0.0 but different bits;
            // NaN != NaN but identical bits) and two's-complement order is
            // not IEEE sign-magnitude order. Until a real FP theory (or
            // bit-blasted IEEE encoding) lands, the result is a fresh
            // unconstrained boolean — an over-approximation that can never
            // decide the predicate either way — and the instruction emits an
            // always-failing unsupported-semantics VC so no obligation
            // touching float comparison can be reported proof-grade.
            Inst::FCmp { ty, lhs, rhs, .. } => {
                let _lhs = self.resolve(*lhs, ty);
                let _rhs = self.resolve(*rhs, ty);
                let result = self.fresh_symbolic("fcmp_result", &Ty::Bool);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("floating-point comparison", node);
            }

            Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => {
                let result = self.resolve(*ptr, &Ty::Ptr);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("borrow permission semantics", node);
            }

            Inst::EndBorrow { .. } => {
                self.add_unsupported_semantics("end-borrow permission semantics", node);
            }

            Inst::Retain { .. } | Inst::Release { .. } => {
                self.add_unsupported_semantics("reference-counting semantics", node);
            }

            Inst::IsUnique { .. } => {
                let result = self.fresh_symbolic("is_unique_result", &Ty::Bool);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("reference-count uniqueness semantics", node);
            }

            Inst::Dealloc { .. } => {
                self.add_unsupported_semantics("heap deallocation semantics", node);
            }

            // trust-ir v47 `Drop { ty, ptr }` runs `ty`'s drop glue on the place
            // at `ptr`: a destructor call whose body (user `Drop` impls, nested
            // field drops, deallocation) is not part of this node, so it may read
            // or write anything reachable from `ptr` and may panic. No sound
            // transfer function exists here without that body, so it fails
            // closed by name.
            Inst::Drop { .. } => {
                self.add_unsupported_semantics("drop-glue semantics", node);
            }

            Inst::OpenFrame { .. } | Inst::BindSlot { .. } => {
                let result = self.fresh_symbolic("binding_frame", &Ty::Ptr);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("binding-frame semantics", node);
            }

            Inst::LoadSlot { ty, .. } => {
                let result = self.fresh_symbolic("binding_slot", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("binding-frame slot load semantics", node);
            }

            Inst::CloseFrame { .. } => {
                self.add_unsupported_semantics("binding-frame close semantics", node);
            }

            Inst::CoroSuspend { .. } => {
                self.add_unsupported_semantics("coroutine suspend semantics", node);
            }

            Inst::Invoke { .. } => {
                self.add_unsupported_semantics(
                    "invoke call with exception-handling semantics",
                    node,
                );
            }

            Inst::LandingPad { .. } => {
                self.add_unsupported_semantics(
                    "landing-pad exception-handler entry semantics",
                    node,
                );
            }

            Inst::Resume { .. } => {
                self.add_unsupported_semantics("exception resume/re-raise semantics", node);
            }

            // trust-ir v53 no-unwind call boundaries: a normal return means what
            // `Call` / `CallIndirect` means, and an unwind out of the callee must
            // be stopped at the site (the target enforces it or refuses). This
            // lane models neither the boundary nor, for the indirect form, the
            // dispatch, so both fail closed by name.
            Inst::CallCannotUnwind { .. } => {
                self.add_unsupported_semantics("direct call with a no-unwind boundary", node);
            }

            Inst::CallIndirectCannotUnwind { .. } => {
                self.add_unsupported_semantics(
                    "indirect call dispatch with a no-unwind boundary",
                    node,
                );
            }

            // The trust-ir unwinding twins (v54 `AssertInvoke`, v55 `DropInvoke`,
            // v56 `InvokeIndirect`) are terminators with `Invoke`'s successor
            // discipline. Like `Invoke`, none has an edge in this lane
            // (`record_outgoing_edges`), and each fails closed by name.
            Inst::AssertInvoke { .. } => {
                self.add_unsupported_semantics(
                    "sited check with an exception-handling unwind edge",
                    node,
                );
            }

            Inst::DropInvoke { .. } => {
                self.add_unsupported_semantics(
                    "drop-glue semantics with an exception-handling unwind edge",
                    node,
                );
            }

            Inst::InvokeIndirect { .. } => {
                self.add_unsupported_semantics(
                    "indirect invoke call with exception-handling semantics",
                    node,
                );
            }

            // Structural element-wise sequence maps: whole-sequence semantics
            // (map `+k` / `Bool.not` over every element) have no precise BMC
            // encoding yet, so bind the result symbolically and fail closed.
            Inst::SeqMapAddK { ty, .. } | Inst::SeqMapNot { ty, .. } | Inst::SeqMap { ty, .. } => {
                let result = self.fresh_symbolic("seq_map_result", ty);
                if let Some(result_id) = node.results.first() {
                    self.bind(*result_id, result);
                }
                self.add_unsupported_semantics("structural sequence-map semantics", node);
            }

            // --- Bulk memory (trust-ir WS3.20): `memcpy`/`memmove`/`memset` ---
            // `bytes` bytes at `dst`. Exact where `dst` (and a copy's `src`) is a
            // single-cell `Alloca` named whole: in-bounds, overlap and the write
            // are compared with the cell's byte size, once, whatever `bytes` is.
            // Anything else keeps the previous model: the region the write lands
            // in is havocked and the instruction fails closed by name. See
            // `translate_bulk_memory`.
            Inst::MemCopy { dst, src, bytes, overlap } => {
                self.translate_bulk_memory(
                    *dst,
                    BulkWrite::Copy { src: *src, overlap: *overlap },
                    *bytes,
                    node,
                );
            }
            Inst::MemSet { dst, byte, bytes } => {
                self.translate_bulk_memory(*dst, BulkWrite::Fill { byte: *byte }, *bytes, node);
            }

            Inst::DialectOp(_) => {
                self.add_unsupported_semantics("dialect operation", node);
            }

            // trust-ir v67-v69 tensor region (`crate::tensor_region`): no tensor
            // value has a sort in this lane (`UnsupportedSort::Tensor`), and the
            // module input refuses every module that stores one before any
            // function is translated. If a caller bypasses it, each instruction
            // still fails closed by name, with an always-failing violation. Its
            // results are deliberately left unbound and its operands unread:
            // binding a result would need a tensor sort this lane does not have.
            Inst::TensorContract { .. } => {
                self.add_tensor_region_violation(crate::TensorConstruct::TensorContract, node);
            }
            Inst::TensorMap { .. } => {
                self.add_tensor_region_violation(crate::TensorConstruct::TensorMap, node);
            }
            Inst::TensorReduce { .. } => {
                self.add_tensor_region_violation(crate::TensorConstruct::TensorReduce, node);
            }
            Inst::TensorView { .. } => {
                self.add_tensor_region_violation(crate::TensorConstruct::TensorView, node);
            }
            Inst::TensorGather { .. } => {
                self.add_tensor_region_violation(crate::TensorConstruct::TensorGather, node);
            }
            Inst::TensorScatter { .. } => {
                self.add_tensor_region_violation(crate::TensorConstruct::TensorScatter, node);
            }
        }
    }

    /// The always-failing violation that names a tensor-region instruction or
    /// constant (`crate::tensor_region`).
    fn add_tensor_region_violation(&mut self, construct: crate::TensorConstruct, node: &InstrNode) {
        self.add_unsupported_semantics(tensor_region_semantics(construct), node);
    }

    /// `MemCopy` / `MemSet` in the typed array memory model.
    ///
    /// The model has one SMT array per `Alloca`, indexed by ELEMENT, so a byte
    /// range has an exact reading only when it is a whole element. That is the
    /// case decided here, in an encoding whose size does not depend on `bytes`:
    /// `dst` (and a copy's `src`) is a single-cell `Alloca` pointer, which names
    /// its whole cell at offset 0, so
    ///
    /// * `bytes == 0` is a no-op (even through a dangling pointer);
    /// * `bytes >u size_of(cell)` on either side is out of bounds;
    /// * a `memcpy` from a cell to itself overlaps whenever `bytes != 0`;
    /// * `bytes == size_of(cell)` copies the source cell when both cells have the
    ///   SAME type (its whole region array, so a lane read of a compound cell
    ///   reads the source's lane too), or fills an INTEGER cell with the byte
    ///   repeated to its width.
    ///
    /// A defined, non-empty range that is none of these (a strict prefix of the
    /// cell, a copy between cells of different types, a fill of a non-integer
    /// cell) havocs the destination and fails closed by name where it happens;
    /// an operand that is not a single-cell `Alloca` pointer keeps the previous
    /// model (havoc the region, fail closed wherever `bytes != 0`).
    fn translate_bulk_memory(
        &mut self,
        dst: ValueId,
        write: BulkWrite,
        bytes: ValueId,
        node: &InstrNode,
    ) {
        let _dst = self.resolve(dst, &Ty::Ptr);
        let spelling = match write {
            BulkWrite::Copy { overlap: true, .. } => "memmove",
            BulkWrite::Copy { overlap: false, .. } => "memcpy",
            BulkWrite::Fill { .. } => "memset",
        };
        let (src_cell, byte) = match write {
            BulkWrite::Copy { src, .. } => {
                let _src = self.resolve(src, &Ty::Ptr);
                (Some(self.bulk_cell(src)), None)
            }
            BulkWrite::Fill { byte } => (None, Some(self.resolve(byte, &Ty::U8))),
        };
        let count = ByteCount::new(self.resolve(bytes, &Ty::Usize));
        let zero = count.as_ref().map_or(Truth::Known(false), |count| count.equals(0));
        if zero.is_true() {
            return;
        }
        let dst_cell = self.bulk_cell(dst);
        let exact = match (count, dst_cell, src_cell) {
            (Some(count), Some(dst_cell), None) => Some((count, dst_cell, None)),
            (Some(count), Some(dst_cell), Some(Some(src_cell))) => {
                Some((count, dst_cell, Some(src_cell)))
            }
            _ => None,
        };
        let Some((count, (dst_key, dst_ty, dst_size), src_cell)) = exact else {
            // No exact cell: the previous model, now silent where `bytes == 0`.
            let nonzero = zero.negate();
            self.havoc_bulk_write_destination(dst, &nonzero);
            self.add_violation(
                PropertyKind::Other,
                nonzero.expr(),
                &format!(
                    "unsupported trust_ir semantics in {}: bulk memory {} with a dynamic \
                     byte count: the typed array memory model has no byte-granular write or \
                     range-bounds model",
                    self.func.name,
                    if spelling == "memset" {
                        "fill (memset)".to_owned()
                    } else {
                        format!("copy ({spelling})")
                    },
                ),
                node,
            );
            return;
        };

        // Undefined behaviour, decided exactly.
        let mut out_of_bounds = count.exceeds(dst_size);
        let mut overlapping = Truth::Known(false);
        if let Some((src_key, _, src_size)) = &src_cell {
            out_of_bounds = out_of_bounds.or(count.exceeds(*src_size));
            if matches!(write, BulkWrite::Copy { overlap: false, .. }) && *src_key == dst_key {
                overlapping = zero.clone().negate();
            }
        }
        if self.options.check_memory_bounds {
            if !out_of_bounds.is_false() {
                self.add_violation(
                    PropertyKind::OutOfBounds,
                    out_of_bounds.expr(),
                    &format!("bulk memory {spelling} out of bounds in {}", self.func.name),
                    node,
                );
            }
            if !overlapping.is_false() {
                self.add_violation(
                    PropertyKind::UndefinedBehavior,
                    overlapping.expr(),
                    &format!("{spelling} source and destination overlap in {}", self.func.name),
                    node,
                );
            }
        }
        let undefined = out_of_bounds.or(overlapping);

        // What a whole-cell write leaves in the region, if this write has one.
        //
        // A copy between two cells of one type takes the source's WHOLE array,
        // not its element 0. A cell of a compound type is one 64-bit placeholder
        // element here, but a lane `GEP` into it (memory checks off) reads array
        // index `k`: storing only element 0 would leave every such index holding
        // its pre-copy value, a stale read the source's bytes overwrote. The
        // whole array is the source cell index for index, so every read of the
        // destination after the copy is the same read of the source before it.
        // A fill writes only an INTEGER cell, which is its element 0 alone.
        let whole_write = match (&src_cell, &byte) {
            (Some((src_key, src_ty, src_size)), None)
                if *src_ty == dst_ty && *src_size == dst_size =>
            {
                self.memory_regions
                    .get(src_key)
                    .map(|region| WholeCellWrite::Region(region.array.clone()))
            }
            (None, Some(byte)) => {
                repeated_byte_element(&dst_ty, dst_size, byte).map(WholeCellWrite::Element)
            }
            _ => None,
        };
        let whole = match &whole_write {
            Some(_) => count.equals(dst_size),
            None => Truth::Known(false),
        };
        let unplaced =
            zero.clone().negate().and(whole.clone().negate()).and(undefined.clone().negate());
        if !unplaced.is_false() {
            self.add_violation(
                PropertyKind::Other,
                unplaced.expr(),
                &format!(
                    "unsupported trust_ir semantics in {}: bulk memory {spelling} of a range \
                     that is not one whole element of a stack cell: the typed array memory \
                     model has no partial-element or reinterpreting write",
                    self.func.name
                ),
                node,
            );
        }

        let Some(original) = self.memory_regions.get(&dst_key).map(|region| region.array.clone())
        else {
            return;
        };
        let stored = whole_write.map(|write| match write {
            WholeCellWrite::Region(source) => source,
            WholeCellWrite::Element(element) => {
                original.clone().store(Expr::bitvec_const(0u64, 64), element)
            }
        });
        // A fresh array where the cell's content is unknown afterwards: a range
        // nothing places, and (whatever the checks) an undefined execution.
        let havoc = if unplaced.is_false() && undefined.is_false() {
            None
        } else {
            let sort = original.sort().clone();
            let name = format!("mem_bulk_write_{}", self.next_sym_id);
            self.next_sym_id += 1;
            self.decls.push(Decl::constant(&name, sort.clone()));
            Some(Expr::var(&name, sort))
        };
        let otherwise = match (&havoc, unplaced.is_false()) {
            (Some(havoc), false) => zero.select(original.clone(), havoc.clone()),
            _ => Some(original.clone()),
        };
        let updated = match (stored, otherwise) {
            (Some(stored), Some(otherwise)) => whole.select(stored, otherwise),
            (None, otherwise) => otherwise,
            (Some(_), None) => None,
        };
        let updated = match (updated, &havoc) {
            (Some(updated), Some(havoc)) if !undefined.is_false() => {
                undefined.select(havoc.clone(), updated)
            }
            (updated, _) => updated,
        };
        match updated {
            Some(updated) => {
                let new_array = self.guard_array_update(updated, original);
                if let Some(region) = self.memory_regions.get_mut(&dst_key) {
                    region.array = new_array;
                }
            }
            // An ill-sorted case never stands in for the write: forget the cell.
            None => self.havoc_bulk_write_destination(dst_key, &Truth::Known(true)),
        }
    }

    /// The single-cell region a bulk operand names WHOLE: an `Alloca` result
    /// (offset 0) whose region holds one element of a type with a byte size.
    /// `(region key, cell type, size in bytes)`.
    fn bulk_cell(&self, ptr: ValueId) -> Option<(ValueId, Ty, u64)> {
        let region = self.memory_regions.get(&ptr)?;
        if region.count != Some(1) {
            return None;
        }
        let bits = self.module.ty_layout_shape(&region.ty).ok()?.size_bits;
        (bits % 8 == 0).then(|| (ptr, region.ty.clone(), bits / 8))
    }

    /// Reset the tracked region a bulk write through `dst` lands in to a fresh,
    /// unconstrained array where `when` holds (and the current block executes).
    ///
    /// Defense in depth under the failing VC the caller also emits: the write set
    /// of such a bulk write is not representable in this element-indexed model,
    /// so the only sound update is to forget the whole region rather than leave
    /// any element holding its pre-write value.
    fn havoc_bulk_write_destination(&mut self, dst: ValueId, when: &Truth) {
        if when.is_false() {
            return;
        }
        let Some(key) = self.find_region_key_for_ptr(dst) else {
            return;
        };
        let Some(region) = self.memory_regions.get(&key) else {
            return;
        };
        let original = region.array.clone();
        let array_sort = original.sort().clone();
        let array_name = format!("mem_bulk_write_{}", self.next_sym_id);
        self.next_sym_id += 1;
        let fresh = Expr::var(&array_name, array_sort.clone());
        self.decls.push(Decl::constant(&array_name, array_sort));
        let Some(written) = when.select(fresh, original.clone()) else {
            return;
        };
        let new_array = self.guard_array_update(written, original);
        if let Some(region) = self.memory_regions.get_mut(&key) {
            region.array = new_array;
        }
    }

    /// Translate an integer binary operation, emitting overflow/div-by-zero VCs.
    fn translate_integer_binop(
        &mut self,
        op: BinOp,
        ty: &Ty,
        lhs: ValueId,
        rhs: ValueId,
        node: &InstrNode,
    ) {
        let lhs_expr = self.resolve(lhs, ty);
        let rhs_expr = self.resolve(rhs, ty);

        if let Some(no_overflow) =
            integer_binop_no_overflow_condition(op, ty, &lhs_expr, &rhs_expr, self.options)
        {
            let signedness = if ty.is_signed() { "signed" } else { "unsigned" };
            // Violation when no_overflow is false.
            let overflow_occurs = no_overflow.not();
            self.add_violation(
                PropertyKind::ArithmeticOverflow,
                overflow_occurs,
                &format!("{signedness} {} overflow in {}", op_name(op), self.func.name),
                node,
            );
        }

        if let Some(is_zero) = integer_binop_div_by_zero_condition(op, ty, &rhs_expr, self.options)
        {
            self.add_violation(
                PropertyKind::DivisionByZero,
                is_zero,
                &format!("division by zero in {}", self.func.name),
                node,
            );
        }

        // Compute result.
        let result = self.eval_binop(op, ty, &lhs_expr, &rhs_expr);
        if let Some(result_id) = node.results.first() {
            self.bind(*result_id, result);
        }

        // A float op on an INTEGER type is ill-typed IR; eval_binop havocs the
        // result ("float_on_int"), so fail closed rather than let the
        // unconstrained value silently feed an obligation.
        if binop_is_floating_point(op) {
            self.add_unsupported_semantics(
                format!("floating-point operation {op:?} on integer type {ty:?}"),
                node,
            );
        }
        // A rotate whose operands are not same-width bit-vectors has no exact
        // encoding; eval_binop havocs it ("rotate_unencodable"), so fail closed
        // exactly as for float-on-int.
        if integer_rotate_is_unencodable(op, ty, &lhs_expr, &rhs_expr) {
            self.add_unsupported_semantics(
                format!("rotate {op:?} without a same-width bit-vector encoding on {ty:?}"),
                node,
            );
        }
    }

    /// Translate an Alloca instruction.
    ///
    /// Creates a symbolic memory region backed by an SMT array. The array maps
    /// 64-bit offsets to elements of the allocated type.
    fn translate_alloca(&mut self, ty: &Ty, count: Option<&ValueId>, node: &InstrNode) {
        let result_id = match node.results.first() {
            Some(id) => *id,
            None => return,
        };

        // Create the base pointer for this allocation.
        let ptr_expr = self.fresh_symbolic("alloca_ptr", &Ty::Ptr);
        self.bind(result_id, ptr_expr.clone());

        // Create the symbolic memory array: Array(BV64, element_sort).
        let element_sort = ty_to_sort(ty);
        let array_sort = Sort::array(Sort::bitvec(64), element_sort.clone());
        let array_name = format!("mem_{}", self.next_sym_id);
        self.next_sym_id += 1;
        let array_expr = Expr::var(&array_name, array_sort.clone());
        self.decls.push(Decl::constant(&array_name, array_sort));

        // Determine element count.
        let elem_count = match count {
            Some(count_val) => {
                // Dynamic count — we don't know the value statically.
                let _count_expr = self.resolve(*count_val, &Ty::I64);
                self.add_unsupported_semantics("dynamic alloca count", node);
                None
            }
            None => Some(1u64),
        };

        self.memory_regions.insert(
            result_id,
            MemoryRegion {
                array: array_expr,
                element_sort,
                count: elem_count,
                base_ptr: ptr_expr,
                ty: ty.clone(),
            },
        );
    }

    /// Translate a GEP (GetElementPtr) instruction.
    ///
    /// Computes `base + sum(indices * element_size)` as a bitvector address.
    /// If the base pointer has a known memory region, records the offset for
    /// later Load/Store resolution.
    fn translate_gep(
        &mut self,
        pointee_ty: &Ty,
        base: ValueId,
        indices: &[ValueId],
        node: &InstrNode,
    ) {
        let base_expr = self.resolve(base, &Ty::Ptr);
        let result_id = match node.results.first() {
            Some(id) => *id,
            None => return,
        };

        // Compute the byte offset: sum of each index * element_size.
        let elem_size = pointee_ty.bit_width_with(HOST_POINTER_BITS).unwrap_or(8) as u64 / 8;
        let elem_size_expr = Expr::bitvec_const(elem_size.max(1), 64);

        let mut total_offset = Expr::bitvec_const(0u64, 64);
        for idx_val in indices {
            let idx_expr = self.resolve(*idx_val, &Ty::I64);
            let byte_offset = idx_expr.bvmul(elem_size_expr.clone());
            total_offset = total_offset.bvadd(byte_offset);
        }

        // Result pointer = base + offset.
        let result_expr = base_expr.bvadd(total_offset);

        self.bind(result_id, result_expr);

        // Record the GEP result for memory region resolution.
        if !indices.is_empty() {
            let mut elem_offset = Expr::bitvec_const(0u64, 64);
            for idx_val in indices {
                let idx_expr = self.resolve(*idx_val, &Ty::I64);
                elem_offset = elem_offset.bvadd(idx_expr);
            }
            self.gep_results.insert(result_id, (base, elem_offset));
        }

        // Bounds check for the GEP result.
        if self.options.check_memory_bounds {
            if let Some((region, base_offset)) = self.resolve_memory_region(base) {
                if let Some(count) = region.count {
                    let final_offset = if !indices.is_empty() {
                        let mut elem_offset = Expr::bitvec_const(0u64, 64);
                        for idx_val in indices {
                            let idx_expr = self.resolve(*idx_val, &Ty::I64);
                            elem_offset = elem_offset.bvadd(idx_expr);
                        }
                        base_offset.bvadd(elem_offset)
                    } else {
                        base_offset
                    };
                    let count_expr = Expr::bitvec_const(count, 64);
                    let out_of_bounds = final_offset.bvuge(count_expr);
                    self.add_violation(
                        PropertyKind::OutOfBounds,
                        out_of_bounds,
                        &format!("GEP out of bounds in {}", self.func.name),
                        node,
                    );
                }
            }
        }
    }

    /// Translate a Load instruction with array-based memory model.
    ///
    /// If the pointer traces back to a known memory region (Alloca), performs
    /// an array `select` at the computed offset. Otherwise falls back to a
    /// fresh symbolic value with bounds checking.
    fn translate_load(&mut self, ty: &Ty, ptr: ValueId, node: &InstrNode) {
        let _ptr_expr = self.resolve(ptr, &Ty::Ptr);

        // Try to resolve to a known memory region.
        let region_info = self
            .resolve_memory_region(ptr)
            .map(|(r, off)| (r.array.clone(), r.element_sort.clone(), r.count, off));

        if let Some((array, _elem_sort, count, offset)) = region_info {
            // Bounds check. Bare InBounds metadata is not trusted here.
            if self.options.check_memory_bounds {
                if let Some(n) = count {
                    let count_expr = Expr::bitvec_const(n, 64);
                    let out_of_bounds = offset.clone().bvuge(count_expr);
                    self.add_violation(
                        PropertyKind::OutOfBounds,
                        out_of_bounds,
                        &format!("memory load out of bounds in {}", self.func.name),
                        node,
                    );
                }
            }

            // Array select: read from memory[offset].
            let result = array.select(offset);
            if let Some(result_id) = node.results.first() {
                self.bind(*result_id, result);
            }
        } else {
            // No known region — fall back to symbolic with bounds check.
            if self.options.check_memory_bounds {
                let bounds_ok = self.fresh_symbolic("bounds_ok", &Ty::Bool);
                let bounds_fail = bounds_ok.not();
                self.add_violation(
                    PropertyKind::OutOfBounds,
                    bounds_fail,
                    &format!("memory load out of bounds in {}", self.func.name),
                    node,
                );
            }

            let result = self.fresh_symbolic("load_result", ty);
            if let Some(result_id) = node.results.first() {
                self.bind(*result_id, result);
            }
        }
    }

    /// Translate a Store instruction with array-based memory model.
    ///
    /// If the pointer traces back to a known memory region, performs an array
    /// `store` at the computed offset, updating the region's array expression.
    fn translate_store(&mut self, ty: &Ty, ptr: ValueId, value: ValueId, node: &InstrNode) {
        let _ptr_expr = self.resolve(ptr, &Ty::Ptr);
        let val_expr = self.resolve(value, ty);

        // Try to find the region key for this pointer.
        let region_key = self.find_region_key_for_ptr(ptr);

        if let Some(key) = region_key {
            let offset = self
                .resolve_memory_region(ptr)
                .map(|(_, off)| off)
                .unwrap_or_else(|| Expr::bitvec_const(0u64, 64));
            let count = self.memory_regions.get(&key).and_then(|r| r.count);

            // Bounds check. Bare InBounds metadata is not trusted here.
            if self.options.check_memory_bounds {
                if let Some(n) = count {
                    let count_expr = Expr::bitvec_const(n, 64);
                    let out_of_bounds = offset.clone().bvuge(count_expr);
                    self.add_violation(
                        PropertyKind::OutOfBounds,
                        out_of_bounds,
                        &format!("memory store out of bounds in {}", self.func.name),
                        node,
                    );
                }
            }

            // Array store: memory[offset] = value (a no-op on paths that do
            // not execute the current block).
            //
            // A value of a COMPOUND type is one 64-bit placeholder element in
            // this model, but its bytes span more than one index: a lane `GEP`
            // into a compound cell (memory checks off) reads index `k >= 1`.
            // Writing only `offset` would leave those indices holding what the
            // store overwrote, a stale read and a false proof, so a compound
            // store lands on a FRESH array: the written element is exact and
            // every other index is unknown afterwards.
            let original = self
                .memory_regions
                .get(&key)
                .expect("resolved memory region key must exist")
                .array
                .clone();
            let base = if ty_is_compound_placeholder(ty) {
                let sort = original.sort().clone();
                let name = format!("mem_store_spans_{}", self.next_sym_id);
                self.next_sym_id += 1;
                self.decls.push(Decl::constant(&name, sort.clone()));
                Expr::var(&name, sort)
            } else {
                original.clone()
            };
            let stored_array = base.store(offset, val_expr);
            let new_array = self.guard_array_update(stored_array, original);
            self.memory_regions
                .get_mut(&key)
                .expect("resolved memory region key must be mutable")
                .array = new_array;
        } else {
            // No known region — emit bounds check only.
            if self.options.check_memory_bounds {
                let bounds_ok = self.fresh_symbolic("bounds_ok", &Ty::Bool);
                let bounds_fail = bounds_ok.not();
                self.add_violation(
                    PropertyKind::OutOfBounds,
                    bounds_fail,
                    &format!("memory store out of bounds in {}", self.func.name),
                    node,
                );
            }
        }
    }

    /// Translate a Return instruction, generating postcondition VCs.
    ///
    /// Checks the function's proof annotations for postcondition-related proofs.
    fn translate_return(&mut self, values: &[ValueId], node: &InstrNode) {
        let ret_exprs: Vec<Expr> = if let Some(func_ty) =
            self.module.func_types.get(self.func.ty.as_usize())
        {
            values.iter().zip(func_ty.returns.iter()).map(|(v, ty)| self.resolve(*v, ty)).collect()
        } else {
            values.iter().map(|v| self.resolve(*v, &Ty::I64)).collect()
        };

        // Generate VCs from function-level postcondition annotations.
        for proof in &self.func.proofs {
            match proof {
                ProofAnnotation::BoundedOutput { lo, hi } => {
                    for (i, ret_expr) in ret_exprs.iter().enumerate() {
                        let ret_ty = self
                            .module
                            .func_types
                            .get(self.func.ty.as_usize())
                            .and_then(|func_ty| func_ty.returns.get(i));
                        let out_of_range = ret_ty.and_then(|ret_ty| {
                            bounded_output_out_of_range(ret_ty, ret_expr, *lo, *hi)
                        });
                        match out_of_range {
                            Some(out_of_range) => {
                                self.add_violation(
                                    PropertyKind::Postcondition,
                                    out_of_range,
                                    &format!(
                                        "postcondition BoundedOutput[{lo}, {hi}] violated for return value {i} in {}",
                                        self.func.name
                                    ),
                                    node,
                                );
                            }
                            // The annotated bounds have no exact encoding
                            // against this return type (float-typed return,
                            // fractional/out-of-range f64 bound, or an
                            // untyped return). Previously a float-typed
                            // return was checked with a SIGNED BITVECTOR
                            // compare over raw IEEE bits — wrong semantics
                            // that could falsely prove or falsely refute the
                            // postcondition — and a width-less return was
                            // silently SKIPPED (an unchecked, silently
                            // dropped obligation). Both now fail closed.
                            None => {
                                self.add_unsupported_semantics(
                                    format!(
                                        "BoundedOutput[{lo}, {hi}] postcondition without exact \
                                         integer semantics for return value {i}"
                                    ),
                                    node,
                                );
                            }
                        }
                    }
                }
                ProofAnnotation::Pure | ProofAnnotation::Terminates => {
                    // No return VC needed for these.
                }
                _ => {}
            }
        }
    }

    /// Translate a Call instruction with interprocedural analysis.
    ///
    /// Direct module calls create fresh symbolic return values. Bare proof
    /// annotations on the callee are not trusted as production assumptions.
    /// Unknown callees fail closed.
    fn translate_call(&mut self, callee: FuncId, args: &[ValueId], node: &InstrNode) {
        let callee_func = self.module.functions.iter().find(|f| f.id == callee);

        let callee_func = match callee_func {
            Some(f) => f,
            None => {
                self.add_unsupported_semantics(
                    format!("unknown direct call target {callee:?}"),
                    node,
                );
                // External function — bind fresh symbolic result.
                if let Some(result_id) = node.results.first() {
                    let result = self.fresh_symbolic("call_result", &Ty::I64);
                    self.bind(*result_id, result);
                }
                return;
            }
        };

        self.symbolic_call(callee_func, args, node);
    }

    /// Create a symbolic return value for a direct call without trusting unchecked proofs.
    fn symbolic_call(&mut self, callee: &Function, args: &[ValueId], node: &InstrNode) {
        let ret_ty = self
            .module
            .func_types
            .get(callee.ty.as_usize())
            .and_then(|ft| ft.returns.first())
            .unwrap_or(&Ty::I64);

        let result_expr = self.fresh_symbolic(&format!("call_{}", callee.name), ret_ty);

        if let Some(result_id) = node.results.first() {
            self.bind(*result_id, result_expr.clone());
        }

        // Resolve argument expressions for side-effect contributions.
        let callee_func_ty = self.module.func_types.get(callee.ty.as_usize());
        for (i, arg_val) in args.iter().enumerate() {
            let arg_ty = callee_func_ty.and_then(|ft| ft.params.get(i)).unwrap_or(&Ty::I64);
            let _arg_expr = self.resolve(*arg_val, arg_ty);
        }
    }

    /// Translate an AtomicRMW instruction.
    ///
    /// For sequential BMC: load old, compute new, store new.
    fn translate_atomic_rmw(
        &mut self,
        op: trust_ir::inst::AtomicRMWOp,
        ty: &Ty,
        ptr: ValueId,
        value: ValueId,
        node: &InstrNode,
    ) {
        let val_expr = self.resolve(value, ty);

        // Load old value from memory.
        let region_info =
            self.resolve_memory_region(ptr).map(|(r, off)| (r.array.clone(), r.count, off));

        let loaded = if let Some((array, _count, offset)) = &region_info {
            array.clone().select(offset.clone())
        } else {
            self.fresh_symbolic("atomic_rmw_old", ty)
        };

        if let Some(result_id) = node.results.first() {
            self.bind(*result_id, loaded.clone());
        }

        // Compute the new value.
        //
        // `Xchg` moves bits without interpreting them — exact for every type.
        // The arithmetic/bitwise/min-max ops below use BITVECTOR semantics,
        // which are only the instruction's semantics on INTEGER types: on a
        // float type `Add` would be IEEE addition (rounding, NaN/∞, -0.0) and
        // `Max`/`Min` IEEE order, none of which `bvadd`/`bvsgt` compute. Havoc
        // the stored value and fail closed for non-integer element types so
        // wrong-bit results can neither be stored back nor decide obligations.
        let new_val = match op {
            trust_ir::inst::AtomicRMWOp::Xchg => val_expr,
            _ if !ty.is_integer() => {
                self.add_unsupported_semantics(
                    format!("atomic read-modify-write {op:?} on non-integer type {ty:?}"),
                    node,
                );
                self.fresh_symbolic("atomic_rmw_unmodeled", ty)
            }
            trust_ir::inst::AtomicRMWOp::Add => loaded.clone().bvadd(val_expr),
            trust_ir::inst::AtomicRMWOp::Sub => loaded.clone().bvsub(val_expr),
            trust_ir::inst::AtomicRMWOp::And => loaded.clone().bvand(val_expr),
            trust_ir::inst::AtomicRMWOp::Or => loaded.clone().bvor(val_expr),
            trust_ir::inst::AtomicRMWOp::Xor => loaded.clone().bvxor(val_expr),
            trust_ir::inst::AtomicRMWOp::Max => {
                let cond = loaded.clone().bvsgt(val_expr.clone());
                Expr::ite(cond, loaded.clone(), val_expr)
            }
            trust_ir::inst::AtomicRMWOp::Min => {
                let cond = loaded.clone().bvslt(val_expr.clone());
                Expr::ite(cond, loaded.clone(), val_expr)
            }
            trust_ir::inst::AtomicRMWOp::UMax => {
                let cond = loaded.clone().bvugt(val_expr.clone());
                Expr::ite(cond, loaded.clone(), val_expr)
            }
            trust_ir::inst::AtomicRMWOp::UMin => {
                let cond = loaded.clone().bvult(val_expr.clone());
                Expr::ite(cond, loaded.clone(), val_expr)
            }
        };

        // Store the new value back (a no-op on paths that do not execute the
        // current block).
        if let Some((_, _count, offset)) = region_info {
            let region_key = self.find_region_key_for_ptr(ptr);
            if let Some(key) = region_key {
                let region =
                    self.memory_regions.get(&key).expect("resolved memory region key must exist");
                let stored_array = region.array.clone().store(offset, new_val);
                let new_array = self.guard_array_update(stored_array, region.array.clone());
                self.memory_regions
                    .get_mut(&key)
                    .expect("resolved memory region key must be mutable")
                    .array = new_array;
            }
        }
    }

    /// Translate a CmpXchg instruction.
    ///
    /// Semantics: if *ptr == expected, store desired and return (expected, true).
    /// Otherwise return (*ptr, false).
    fn translate_cmpxchg(
        &mut self,
        ty: &Ty,
        ptr: ValueId,
        expected: ValueId,
        desired: ValueId,
        strength: CmpXchgStrength,
        node: &InstrNode,
    ) {
        let expected_expr = self.resolve(expected, ty);
        let desired_expr = self.resolve(desired, ty);

        // Load current value.
        let current = if let Some((region, offset)) = self.resolve_memory_region(ptr) {
            region.array.clone().select(offset)
        } else {
            self.fresh_symbolic("cmpxchg_current", ty)
        };

        // Compare: success if current == expected.
        //
        // Hardware compare-exchange compares RAW BITS, so bitvector equality
        // is the exact success semantics — including for floats, where the
        // hardware comparison is bitwise too (a CAS does NOT match -0.0
        // against +0.0, and DOES match identical NaN payloads; float values
        // carry exact IEEE bit patterns in this encoding). It is only exact
        // when the modeled bits themselves are: aggregate/vector values may
        // be opaque placeholders, so their bit equality is meaningless —
        // havoc the success flag and fail closed for those types.
        let bit_exact_ty = is_eq_comparable_ty(ty) || ty.is_float();
        let success_cond = if bit_exact_ty {
            current.clone().eq(expected_expr.clone())
        } else {
            self.add_unsupported_semantics(
                format!("compare-exchange over a type without exact modeled bits ({ty:?})"),
                node,
            );
            self.fresh_symbolic("cmpxchg_success", &Ty::Bool)
        };
        // A WEAK compare-exchange (trust-ir v48, `CmpXchg { weak: true }`,
        // Rust's `compare_exchange_weak`) may fail SPURIOUSLY: when the
        // comparison holds it may still leave memory untouched and report
        // failure, and it never succeeds when the comparison fails. That is
        // exactly `equal AND an unconstrained choice`, so the choice is a fresh
        // Bool the solver quantifies over. Modeling it as the strong instruction
        // would prove a program that relies on a weak exchange succeeding.
        let success_cond = match strength {
            CmpXchgStrength::Strong => success_cond,
            CmpXchgStrength::Weak => {
                let may_succeed = self.fresh_symbolic("cmpxchg_weak_may_succeed", &Ty::Bool);
                success_cond.and(may_succeed)
            }
        };

        // Result value: if success then expected (== current) else current.
        let result_val = Expr::ite(success_cond.clone(), expected_expr, current.clone());

        // Bind results: (value, success_flag).
        let mut results = node.results.iter();
        if let Some(r) = results.next() {
            self.bind(*r, result_val);
        }
        if let Some(r) = results.next() {
            self.bind(*r, success_cond.clone());
        }

        // On success, conditionally store the desired value.
        let region_key = self.find_region_key_for_ptr(ptr);
        if let Some(key) = region_key {
            let offset = self
                .resolve_memory_region(ptr)
                .map(|(_, off)| off)
                .unwrap_or_else(|| Expr::bitvec_const(0u64, 64));
            let region =
                self.memory_regions.get(&key).expect("resolved memory region key must exist");
            let stored_array = region.array.clone().store(offset, desired_expr);
            let exchanged = Expr::ite(success_cond, stored_array, region.array.clone());
            // The exchange is also a no-op on paths that do not execute the
            // current block.
            let new_array = self.guard_array_update(exchanged, region.array.clone());
            self.memory_regions
                .get_mut(&key)
                .expect("resolved memory region key must be mutable")
                .array = new_array;
        }
    }

    /// Find the memory region key for a pointer (helper for mutation).
    fn find_region_key_for_ptr(&self, ptr: ValueId) -> Option<ValueId> {
        if self.memory_regions.contains_key(&ptr) {
            return Some(ptr);
        }
        if let Some((base_id, _)) = self.gep_results.get(&ptr) {
            if self.memory_regions.contains_key(base_id) {
                return Some(*base_id);
            }
            if let Some((base_base_id, _)) = self.gep_results.get(base_id) {
                if self.memory_regions.contains_key(base_base_id) {
                    return Some(*base_base_id);
                }
            }
        }
        None
    }

    /// Evaluate a binary operation to produce a symbolic result expression.
    fn eval_binop(&mut self, op: BinOp, ty: &Ty, lhs: &Expr, rhs: &Expr) -> Expr {
        let lhs = &normalize_expr_to_ty(lhs, ty);
        let rhs = &normalize_expr_to_ty(rhs, ty);
        if ty.is_integer() {
            match op {
                BinOp::Add => lhs.clone().bvadd(rhs.clone()),
                BinOp::Sub => lhs.clone().bvsub(rhs.clone()),
                BinOp::Mul => mul_by_power_of_two_as_shift(lhs, rhs)
                    .unwrap_or_else(|| lhs.clone().bvmul(rhs.clone())),
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
                // trust-ir WS3.20 rotates: TOTAL, amount reduced modulo the
                // width — encoded EXACTLY (see `bv_rotate`). Unencodable
                // operands havoc, and translate_integer_binop fails closed on
                // exactly that case (`integer_rotate_is_unencodable`).
                BinOp::RotL | BinOp::RotR => bv_rotate(lhs, rhs, matches!(op, BinOp::RotL))
                    .unwrap_or_else(|| self.fresh_symbolic("rotate_unencodable", ty)),
                // Float ops on integer type — ill-typed IR, return fresh symbolic
                // (the callers flag this fail-closed; see translate_integer_binop).
                BinOp::FAdd
                | BinOp::FSub
                | BinOp::FMul
                | BinOp::FDiv
                | BinOp::FRem
                | BinOp::FMin
                | BinOp::FMax
                | BinOp::FCopySign => self.fresh_symbolic("float_on_int", ty),
                // Trust: the BOOLEAN connectives (trust-ir 4b06918) on an INTEGER
                // type are ill-typed IR -- trust-ir's own validator admits
                // BAnd/BOr/BXor on Bool (or bool-vector) only. Treated exactly as
                // float-on-int above: a fresh symbolic, which is unconstrained and
                // therefore never silently unsound, with the callers flagging it
                // fail-closed. NOT mapped onto bvand/bvor/bvxor: that would give an
                // ill-typed program a plausible bit-level reading instead of
                // rejecting it.
                BinOp::BAnd | BinOp::BOr | BinOp::BXor => {
                    self.fresh_symbolic("bool_connective_on_int", ty)
                }
            }
        } else if matches!(ty, Ty::Bool) {
            // `And`/`Or`/`Xor` on a `Bool`-typed value are LOGICAL connectives,
            // not bitvector ops — model them precisely (Xor over booleans is
            // inequality), mirroring translate_chc::eval_binop. Falls back to a
            // fresh symbolic only on a sort mismatch (never silently unsound:
            // a fresh bool is unconstrained).
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
                // Trust: the DEDICATED boolean connectives (trust-ir 4b06918) -- the
                // same logical semantics as the `And`/`Or`/`Xor` arms above, which
                // MIR reaches only via opcode overloading. Given explicit arms rather
                // than left to the catch-all below, which would havoc them to a fresh
                // symbolic and lose the very precision these opcodes exist to express.
                BinOp::BAnd => lhs
                    .clone()
                    .try_and(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                BinOp::BOr => lhs
                    .clone()
                    .try_or(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                // Xor over booleans IS inequality, exactly as the `Xor` arm above.
                BinOp::BXor => lhs
                    .clone()
                    .try_ne(rhs.clone())
                    .unwrap_or_else(|_| self.fresh_symbolic("binop_result", ty)),
                // Every other op on `Bool` is ill-typed: havoc, and the caller
                // (translate_node's BinOp arm) fails closed because only
                // the boolean connectives count as `modeled_precisely`. Listed, not `_`, so a
                // new `BinOp` must be placed here before this compiles.
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
            // Float or other types: return a fresh symbolic. Callers fail
            // closed on these (see the BinOp arm of translate_node) — in
            // particular a floating-point result is NEVER given bit-level
            // arithmetic semantics.
            self.fresh_symbolic("binop_result", ty)
        }
    }

    /// Evaluate an integer comparison.
    ///
    /// Both operands are normalized to `ty`'s bitvector width before the
    /// comparison so that mixed-width inputs (e.g. an extended index
    /// against a constant bound) do not flow into AY with mismatched
    /// sorts.
    ///
    /// Returns `None` — the caller must havoc the result AND fail closed —
    /// when the comparison has no exact bit-level semantics for `ty`,
    /// mirroring `translate_chc::eval_icmp`'s type gates:
    /// - float types: an integer compare over IEEE-754 bit patterns is NOT
    ///   IEEE comparison (-0.0 == +0.0 but different bits; NaN != NaN but
    ///   identical bits; sign-magnitude order is not two's-complement order),
    ///   and float constants now carry their exact bit patterns, so a bit
    ///   compare would confidently decide the WRONG predicate;
    /// - non-eq-comparable types (aggregates, fat pointers, unit): their
    ///   modeled bits are opaque placeholders, so bit equality over them is
    ///   meaningless and could falsely decide an obligation.
    fn eval_icmp(
        &mut self,
        op: trust_ir::inst::ICmpOp,
        ty: &Ty,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Option<Expr> {
        if ty.is_float() {
            return None;
        }
        let lhs = &normalize_expr_to_ty(lhs, ty);
        let rhs = &normalize_expr_to_ty(rhs, ty);
        // A comparison whose operands resolve to DIFFERENT sorts (e.g. a Bool operand
        // against an Int-typed compare — produced by an aggregate-/discriminant-derived
        // or otherwise malformed comparison) would panic inside `Expr::eq`/`bv*` ("same
        // sort" assert). HAVOC the boolean result instead of ICE-ing: the comparison
        // outcome is left unconstrained (sound over-approximation), mirroring the CHC
        // translator's `eval_icmp`, which returns `None` on the same mismatch.
        if lhs.sort() != rhs.sort() {
            return Some(self.fresh_symbolic("icmp_sort_mismatch", &Ty::Bool));
        }
        use trust_ir::inst::ICmpOp;
        match op {
            ICmpOp::Eq if is_eq_comparable_ty(ty) => Some(lhs.clone().eq(rhs.clone())),
            ICmpOp::Ne if is_eq_comparable_ty(ty) => Some(lhs.clone().eq(rhs.clone()).not()),
            ICmpOp::Ult if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvult(rhs.clone())),
            ICmpOp::Ule if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvule(rhs.clone())),
            ICmpOp::Ugt if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvugt(rhs.clone())),
            ICmpOp::Uge if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvuge(rhs.clone())),
            ICmpOp::Slt if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvslt(rhs.clone())),
            ICmpOp::Sle if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvsle(rhs.clone())),
            ICmpOp::Sgt if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvsgt(rhs.clone())),
            ICmpOp::Sge if is_ordered_scalar_ty(ty) => Some(lhs.clone().bvsge(rhs.clone())),
            _ => None,
        }
    }
}

/// Translate a single function to a BmcVc.
pub(super) fn translate_valid_function(
    func: &Function,
    module: &Module,
    options: &TranslateOptions,
) -> BmcVc {
    let translator = FuncTranslator::new(func, module, options);
    translator.translate()
}

/// Shared query configuration for ordinary VCs and module-input refusals.
pub(super) fn query_for_options(options: &TranslateOptions) -> BmcQuery {
    let mut query = BmcQuery::new();
    if let Some(logic) = &options.logic {
        query = query.with_logic(logic.clone());
    }
    if let Some(timeout) = options.timeout_ms {
        query = query.with_timeout(timeout);
    }
    query.with_model()
}

/// Returns `true` when `expr` is the literal boolean constant `true`.
fn expr_is_true(expr: &Expr) -> bool {
    *expr == Expr::true_()
}

/// Conjoin a guard with a condition, eliding the conjunction when either
/// side is the literal `true` (keeps straight-line VCs byte-identical to the
/// unguarded encoding).
fn and_guard(guard: &Expr, condition: Expr) -> Expr {
    if expr_is_true(guard) {
        condition
    } else if expr_is_true(&condition) {
        guard.clone()
    } else {
        guard.clone().and(condition)
    }
}

/// `guard => body`, eliding the implication when the guard is literally true.
fn implied_under_guard(guard: &Expr, body: Expr) -> Expr {
    if expr_is_true(guard) { body } else { guard.clone().implies(body) }
}

/// Encode a switch case constant as an expression matching the selector's
/// sort. Returns `None` when the constant has no exact encoding against the
/// selector (shared by the BMC and CHC lowerings).
/// The unsupported-semantics reason that names a tensor-region construct
/// (`crate::tensor_region`).
fn tensor_region_semantics(construct: crate::TensorConstruct) -> String {
    format!("{construct} (the trust-ir tensor region has no SMT value model)")
}

pub(crate) fn switch_case_expr(
    case: &trust_ir::constant::Constant,
    selector: &Expr,
) -> Option<Expr> {
    use trust_ir::constant::Constant;
    if selector.sort().is_bool() {
        return match case {
            Constant::Bool(value) => Some(Expr::bool_const(*value)),
            _ => None,
        };
    }

    let width = selector.sort().bitvec_width()?;
    match case {
        Constant::Int(value) => Some(Expr::bitvec_const(*value, width)),
        _ => None,
    }
}

/// Normalize an expression's bitvector width to the width of a trust_ir type.
pub(crate) fn normalize_expr_to_ty(expr: &Expr, ty: &Ty) -> Expr {
    let target_sort = ty_to_sort(ty);
    let Some(dst_width) = target_sort.bitvec_width() else {
        return expr.clone();
    };
    let Some(src_width) = expr.sort().bitvec_width() else {
        return expr.clone();
    };
    if src_width == dst_width {
        expr.clone()
    } else if ty.is_float() {
        // A width-mismatched FLOAT value has no bit-level normalization:
        // f32↔f64 conversion re-biases the exponent and shifts the mantissa —
        // it is NOT zero-extension or truncation of the bit pattern. Return
        // the expression unchanged so the caller's sort checks fail closed
        // (e.g. bind_block_params' mismatched-sort violation) instead of
        // silently fabricating wrong float bits.
        expr.clone()
    } else if src_width < dst_width {
        if ty.is_signed() {
            expr.clone().sign_extend(dst_width - src_width)
        } else {
            expr.clone().zero_extend(dst_width - src_width)
        }
    } else {
        expr.clone().extract(dst_width - 1, 0)
    }
}

/// A type with no SMT value carrier: geometry-only storage, or a tensor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnsupportedSort {
    AddressableStorage,
    /// trust-ir v67 `Ty::Tensor(elem, rank)`: extents and a row-major element
    /// sequence that no bit-vector, Boolean or uninterpreted sort denotes
    /// (`crate::tensor_region`).
    Tensor,
}

impl UnsupportedSort {
    pub(crate) fn message(self) -> &'static str {
        match self {
            Self::AddressableStorage => {
                "addressable storage is allocation geometry, not a modeled SMT value"
            }
            Self::Tensor => "Ty::Tensor (the trust-ir tensor region) has no modeled SMT value",
        }
    }
}

/// Public translators reject unsupported module types before allocating any
/// symbols. Keep the checked mapping available to classify the refusal without
/// inventing a numeric or uninterpreted carrier for uninitialized storage.
pub(crate) fn checked_ty_to_sort(ty: &Ty) -> Result<Sort, UnsupportedSort> {
    Ok(match ty {
        Ty::Bool => Sort::bool(),
        Ty::I8 => Sort::bitvec(8),
        Ty::I16 => Sort::bitvec(16),
        Ty::I32 => Sort::bitvec(32),
        Ty::I64 => Sort::bitvec(64),
        Ty::I128 => Sort::bitvec(128),
        // trust-ir v25 B1 scalars: pointer-width ints at HOST_POINTER_BITS
        // (the file's existing 64-bit convention); char as its 32-bit
        // carrier. Ty::Error never survives validate_module upstream —
        // model as an unconstrained 1-bit vector is WRONG; fail loudly.
        Ty::Isize | Ty::Usize => Sort::bitvec(64),
        Ty::Char => Sort::bitvec(32),
        Ty::Error => unreachable!("Ty::Error is rejected by validate_module"),
        Ty::Storage(_) => return Err(UnsupportedSort::AddressableStorage),
        // trust-ir v67 `Ty::Tensor`: no placeholder sort is invented for it. A
        // 64-bit carrier would let a contraction, map, view, gather or scatter
        // result flow as an unconstrained word with no extent or bounds
        // obligation, so the module input refuses every tensor occurrence
        // before translation, as it refuses Storage (`crate::tensor_region`).
        Ty::Tensor(..) => return Err(UnsupportedSort::Tensor),
        Ty::F16 => Sort::bitvec(16), // Model floats as bitvectors for now.
        Ty::F32 => Sort::bitvec(32),
        Ty::F64 => Sort::bitvec(64),
        Ty::Vector(elem, lanes) => elem
            .bit_width_with(HOST_POINTER_BITS)
            .and_then(|elem_width| elem_width.checked_mul(*lanes))
            .filter(|width| *width > 0)
            .map(Sort::bitvec)
            .unwrap_or_else(|| Sort::bitvec(64)),
        Ty::Ptr => Sort::bitvec(64),
        Ty::U8 => Sort::bitvec(8),
        Ty::U16 => Sort::bitvec(16),
        Ty::U32 => Sort::bitvec(32),
        Ty::U64 => Sort::bitvec(64),
        Ty::U128 => Sort::bitvec(128),
        Ty::FatPtr(_)
        | Ty::Ref(_)
        | Ty::RefMut(_)
        | Ty::PtrConst(_)
        | Ty::PtrMut(_)
        | Ty::Rc(_) => Sort::bitvec(64),
        Ty::Unit | Ty::Never => Sort::bool(),
        Ty::Struct(_)
        | Ty::Array(_, _)
        | Ty::Tuple(_)
        | Ty::Enum(_)
        | Ty::Func(_)
        | Ty::Set(_, _)
        | Ty::Sequence(_)
        | Ty::Record(_)
        | Ty::Closure(_)
        // v30 refinement types: treat the carrier as uninterpreted like the
        // other compound placeholders. The refinement PREDICATE is deliberately
        // NOT assumed — dropping it only weakens the hypothesis set (proofs
        // get harder, never falsely easier), and obligations that need refined
        // semantics fail closed downstream as unsupported. Adopted fail-closed
        // per the v30 plan-of-record (same posture as trust-cg dbb3d7db).
        | Ty::Refine(_, _)
        // trust-ir d1f4a2f nominal dialect types: no implicit scalar or pointer
        // representation, and a Core consumer must require explicit checked
        // legalization before it may interpret one. They take the SAME 64-bit
        // placeholder sort as the other compound placeholders above -- this is
        // a carrier, not a claim about layout. What keeps it sound is not the
        // sort but the fences around it: trust-ir's validate_nominal_instruction_types
        // refuses Const/Cast/Alloca/memory ops over a nominal type, every bmc
        // arithmetic/compare path is allow-listed on scalar types, and
        // const_to_expr below returns None for a Dialect-typed constant so
        // this lane fails closed even when handed an unvalidated module.
        | Ty::Dialect(_) => {
            // Compound types: use uninterpreted sort as placeholder.
            Sort::bitvec(64)
        }
        // trust-ir amendment S: a level-R type (`NoExt`) has no extension.
        Ty::Ext(e) => e.unreachable(),
        // trust-ir v43 `Ty::Handle`: an OPAQUE runtime handle, one pointer word
        // wide, whose identity is the exact `(name, runtime)` pair. It gets a
        // TRUE uninterpreted sort keyed on that pair -- deliberately NOT the
        // 64-bit placeholder the nominal dialect types above take. Two reasons,
        // both about what the solver is allowed to do with it:
        //
        //  1. IDENTITY. `Handle(A)` is never equal to `Handle(B)` of a
        //     different runtime, and never equal to `Ptr`; width is the only
        //     thing a handle shares with a pointer. Under a shared
        //     `bitvec(64)` all of them collapse into ONE sort, so every
        //     sort-equality fence in this crate -- `normalize_expr_to_ty`'s
        //     caller checks, translate_chc's `*coerced.sort() ==
        //     ty_to_sort(src_ty)`, its block-parameter binding and its
        //     call-argument `expected` check -- would silently ACCEPT a
        //     cross-runtime or handle/pointer substitution. Those checks are
        //     what matters here precisely because this module never calls
        //     `validate_module` itself (same reasoning as `const_to_expr`
        //     below). Keying the sort on `(name, runtime)` makes the fences
        //     that already exist do the discrimination, at no new cost.
        //  2. NO INVENTED VALUES. A `bitvec(64)` variable ranges over 2^64
        //     CONCRETE literals and admits arithmetic, comparison and
        //     concat/extract, so a solver could fabricate a handle -- and then
        //     relate it to an equal-width pointer -- when the format says the
        //     ONLY origin of a handle value is a call to a bodyless `External`
        //     declaration pinned in `trust_ir_build::validate::
        //     TRUSTED_HANDLE_RUNTIMES`. An uninterpreted sort has no literals
        //     and no constructors: a handle term can only be related to other
        //     handle terms already in the formula, which IS the
        //     "produced only by a pinned entry point" semantics.
        //
        // No theory is attached, on purpose: `trust_bignum::Nat`'s arithmetic
        // is a trusted-base row the consumer links against, not something to
        // model here, so an obligation that needs handle VALUES fails closed
        // downstream as unsupported rather than being proved against a wrong
        // model. What keeps the carrier sound is the upstream fence:
        // trust-ir's `validate_nominal_instruction_types` decides handles
        // FIRST and admits exact-typed TRANSPORT only (copy, select,
        // exact-signature call/invoke/return/branch edge) -- a strict subset
        // of the dialect rule, with no `DialectOp` and no pointer-like
        // indirect callee -- and refuses varargs, so a handle can reach this
        // translation only through bit-preserving plumbing. Since trust-ir
        // bf7ee706 (WS3.7) that plumbing includes a SEALED stack slot: an
        // `Alloca` at a handle type (or a struct/tuple of handle lanes) whose
        // pointer and borrows are used only by exact-typed `Store`s and
        // `Load`s, every load dominated by a store. It adds no constructor:
        // here a handle-typed slot is an array over this same sort, so a load
        // returns the term a store wrote or an unconstrained one of the sort,
        // never a literal; the CHC lane keeps no cell for it (a handle is not
        // a precise stack scalar), so its loads are fresh; the `Borrow` /
        // `EndBorrow` of the MIR spill shape fail closed in both lanes; and
        // the driver's proof-grade gate refuses the `Alloca` by name
        // (`single_cell_alloca_rejection`: not a scalar or aggregate cell).
        //
        // `Sort::uninterpreted` is the same mapping this workspace already
        // gives trust-vc's opaque sorts (`SortMeta::Opaque` in
        // trust-mc-trust-vc-ingest/src/sort_map.rs). The name mirrors `Ty`'s
        // own Display spelling so a counterexample stays readable; it is
        // injective because neither `name` nor `runtime` may contain `<`,
        // `>`, `,` or a space (`HandleTy::validate`).
        Ty::Handle(handle) => Sort::uninterpreted(handle_sort_name(handle)),
    })
}

pub(crate) fn ty_to_sort(ty: &Ty) -> Sort {
    checked_ty_to_sort(ty)
        .expect("ModuleInput rejects addressable storage and tensors before SMT translation")
}

/// The uninterpreted-sort symbol for a v43 opaque runtime handle.
///
/// Injective in `(name, runtime)`: `HandleTy::validate` restricts `name` to
/// `[A-Za-z0-9_]+` and `runtime` to `::`-separated segments of the same
/// charset, so none of the punctuation used here can occur inside either
/// field. Two runtimes therefore can never share a sort.
pub(crate) fn handle_sort_name(handle: &trust_ir::ty::HandleTy) -> String {
    format!("handle<{}, {}>", handle.name, handle.runtime)
}

/// Convert a trust_ir constant to a ay Expr.
///
/// Returns `None` when the constant has NO exact bit-level encoding (a float
/// constant that cannot be encoded bit-exactly, or a malformed vector
/// constant). Callers MUST fail closed on `None` — bind a fresh symbolic and
/// emit an unsupported-semantics obligation — never substitute placeholder
/// bits: a constant with wrong bits silently corrupts every downstream
/// obligation that depends on its value (false proofs AND false refutations),
/// whereas a havoc + fail-closed VC is loud and sound.
///
/// Aggregate-family constants (`Aggregate`/`Array`/`Splat`/…/`PhantomData`) keep the
/// historical opaque placeholder: their *bits* are never value-inspected —
/// every consumer that could turn them into a verdict (`ExtractField`/
/// `ExtractElement`, `ICmp` via the eq/order type gates, `CmpXchg` via its
/// type gate, `BoundedOutput` via its integer gate) independently fails
/// closed, so the placeholder can flow only through bit-preserving plumbing
/// (store/load, select, block-parameter binding).
pub(crate) fn const_to_expr(ty: &Ty, value: &trust_ir::constant::Constant) -> Option<Expr> {
    use trust_ir::constant::Constant;
    // Storage never denotes an initialized constant, including inline
    // compounds. Public module admission additionally resolves table types.
    let mut storage = false;
    ty.visit_types(|child| storage |= matches!(child, Ty::Storage(_)));
    if storage {
        return None;
    }
    // Trust: a nominal dialect type has no bit pattern the schema grants, so no
    // constant of that type has an exact encoding. trust-ir's validator refuses
    // such constants upstream (validate_nominal_instruction_types), but this
    // module never calls validate_module itself, so fail closed here as well:
    // callers MUST havoc the result and emit an unsupported-semantics
    // obligation on None.
    if matches!(ty, Ty::Dialect(_)) {
        return None;
    }
    // Trust (trust-ir v43): NO constant constructs an opaque runtime handle.
    // Without this guard the `Constant::Int` / `Constant::U128` arms below
    // would take `Ty::Handle`'s `bit_width_with` -- one pointer word, the only
    // property it shares with `Ptr` -- and hand back a 64-bit literal, i.e.
    // FABRICATE the one thing the format reserves to a pinned external entry
    // point, in the wrong sort to boot. trust-ir's validator refuses such a
    // constant upstream (`validate_nominal_instruction_types` admits no
    // `Const` at handle type), but this module never calls `validate_module`
    // itself, so fail closed here too: callers MUST havoc the result and emit
    // an unsupported-semantics obligation on `None`.
    if matches!(ty, Ty::Handle(_)) {
        return None;
    }
    // trust-ir v67-v70 tensor region: a tensor has no bit pattern in this
    // lowering (`UnsupportedSort::Tensor`), so no constant of a type that
    // holds one has an exact encoding. The module input refuses every tensor
    // occurrence first; fail closed here too, so a caller that bypassed it
    // havocs the result and emits an unsupported-semantics obligation.
    if crate::tensor_region::ty_holds_tensor(ty) {
        return None;
    }
    match value {
        Constant::Int(v) => {
            let width = ty.bit_width_with(HOST_POINTER_BITS).unwrap_or(64);
            Some(Expr::bitvec_const(*v, width))
        }
        // Trust (trust-ir v25): a byte-array constant has no scalar SMT
        // model — same exact-bits-or-nothing rule as floats (fail closed).
        Constant::Bytes { .. } => None,
        // trust-ir v49 `Uninit` is an UNWRITTEN aggregate lane, not a value:
        // nothing may read it, and trust-ir-build's validator admits it only
        // as a direct element of a struct/tuple `Aggregate`. As a whole
        // constant it has no bits at all, so there is nothing exact to encode
        // (fail closed). Inside an `Aggregate` it rides the opaque placeholder
        // below, whose bits are never inspected; the proof-grade admission gate
        // in trust-mc-driver refuses a `Const` that carries one, because a read
        // of the lane is undefined behaviour this lowering cannot see.
        Constant::Uninit => None,
        // Trust (trust-ir v24): the 128-bit-faithful unsigned carrier —
        // canonical iff value > i128::MAX. At width 128 the two's-complement
        // reinterpretation carries the EXACT bit pattern (same float lesson:
        // exact bits or no model at all); a canonical U128 under any
        // narrower declared type is malformed, so fail closed (None).
        Constant::U128(v) => {
            let width = ty.bit_width_with(HOST_POINTER_BITS).unwrap_or(64);
            if width == 128 {
                Some(Expr::bitvec_const(*v as i128, 128))
            } else {
                None
            }
        }
        // Trust (0-unknown campaign, float-constant soundness hazard): a float
        // constant must carry its EXACT IEEE-754 bit pattern. The previous
        // placeholder (`bitvec_const(0, width)`) modeled every float constant
        // as +0.0 — WRONG BITS — so any obligation whose verdict depended on
        // the constant's value could be falsely proved or falsely refuted.
        Constant::Float(v) => float_const_bits(ty, *v),
        Constant::Bool(b) => Some(Expr::bool_const(*b)),
        // A vector constant either packs exactly (every lane bit-exact) or has
        // no model at all — the old zero-bits fallback was the same wrong-bits
        // hazard as the float placeholder.
        Constant::Vector(elems) => vector_const_to_expr(ty, elems),
        Constant::Aggregate(_)
        | Constant::Array(_)
        // trust-ir v50 `Splat { elem, len }` is the ONE canonical spelling of a
        // uniform array literal `[elem; len]` (SPEC_RATIFICATIONS §3.1): the
        // same value a `Constant::Array` of `len` equal elements denotes, so it
        // takes the same opaque placeholder — a spelling must not change what
        // this lowering does. Nothing here reads `elem` or walks `len`, so it
        // costs O(1) whatever the length. (translate_chc's `Const` arm models a
        // trackable splat's lanes exactly before it ever reaches this.)
        | Constant::Splat { .. }
        | Constant::Sequence(_)
        | Constant::Set(_)
        | Constant::Record(_)
        | Constant::Closure { .. }
        | Constant::FnDef(_)
        // SymbolAddr is a link-time-only relocatable pointer (`&symbol +
        // addend`) with no value the verifier can model; treat it as an
        // opaque pointer-sized placeholder like FnDef.
        | Constant::SymbolAddr { .. }
        | Constant::PhantomData => {
            // Aggregate constants: opaque placeholder (see doc comment for why
            // this cannot decide an obligation).
            Some(Expr::bitvec_const(0u64, 64))
        }
        // trust-ir v70 `TensorBlob { digest, dims }`: a tensor whose elements
        // are bytes of the module's blob table, outside every function body.
        // It has no bits here whatever type it is spelled at (validation admits
        // it only at an integer `Ty::Tensor`, refused above), so fail closed.
        Constant::TensorBlob { .. } => None,
        // trust-ir amendment S: a level-R constant (`NoExt`) has no extension.
        Constant::Ext(e) => e.unreachable(),
    }
}

/// Exact IEEE-754 bit pattern for a float constant, or `None` (fail closed).
///
/// `Constant::Float` carries an `f64` payload whose wire format is
/// deliberately bit-exact (`{ "bits": u64 }` — see trust-ir `constant.rs`:
/// "if an f64 payload round-trips with even one ULP of drift, the constant
/// is corrupted and any proof about it becomes unsound").
///
/// - `F64`: the payload IS the value — encode `v.to_bits()`. Every pattern,
///   including NaN payloads and the -0.0 / +0.0 sign distinction, is
///   preserved exactly.
/// - `F32`: the bridge stores an exactly-widened f32 (`Constant::f32(v)` is
///   `Float(v as f64)`, and f32→f64 widening is exact and bit-injective; the
///   bridge additionally guarantees a non-NaN payload for F32). Demote with
///   `v as f32` and VERIFY the round-trip: for a non-NaN payload that is
///   exactly a widened f32, round-to-nearest demotion is the identity on the
///   original f32, so `f64::from(demoted).to_bits() == v.to_bits()` holds and
///   — by injectivity of widening — certifies that `demoted` is the UNIQUE
///   f32 whose widening is the payload. Any payload that fails the check
///   (not exactly representable in f32, ±∞ overflow from a finite payload,
///   or a NaN whose platform-dependent demotion picked a different payload)
///   has no certified 32-bit encoding: return `None` so the caller fails
///   closed instead of encoding wrong bits. The check runs on the demoted
///   value actually produced, so even Rust's licensed NaN-payload
///   non-determinism in `as` casts cannot slip an unverified pattern through.
/// - `F16`: no stable Rust representation to compute bits with — `None`.
/// - non-float destination type: ill-typed IR — `None`.
fn float_const_bits(ty: &Ty, v: f64) -> Option<Expr> {
    match ty {
        Ty::F64 => Some(Expr::bitvec_const(v.to_bits(), 64)),
        Ty::F32 => {
            let demoted = v as f32;
            (f64::from(demoted).to_bits() == v.to_bits())
                .then(|| Expr::bitvec_const(u64::from(demoted.to_bits()), 32))
        }
        _ => None,
    }
}

fn vector_const_to_expr(ty: &Ty, elems: &[trust_ir::constant::Constant]) -> Option<Expr> {
    let Ty::Vector(elem_ty, lanes) = ty else {
        return None;
    };
    if *lanes == 0 || elems.len() != *lanes as usize {
        return None;
    }

    let elem_width = elem_ty.bit_width_with(HOST_POINTER_BITS)?;
    if elem_width == 0 {
        return None;
    }

    let mut lane_exprs = elems
        .iter()
        .map(|elem| vector_lane_const_to_bv(elem_ty, elem, elem_width))
        .collect::<Option<Vec<_>>>()?
        .into_iter()
        .rev();
    let first = lane_exprs.next()?;
    Some(lane_exprs.fold(first, |acc, lane| acc.concat(lane)))
}

fn vector_lane_const_to_bv(
    ty: &Ty,
    value: &trust_ir::constant::Constant,
    width: u32,
) -> Option<Expr> {
    use trust_ir::constant::Constant;
    match (ty, value) {
        (Ty::Bool, Constant::Bool(value)) => Some(Expr::bitvec_const(u64::from(*value), width)),
        (ty, Constant::Int(value)) if ty.is_integer() => Some(Expr::bitvec_const(*value, width)),
        // Float lanes pack their EXACT IEEE-754 bit pattern (the old zero-bits
        // lane was the same wrong-bits hazard as the scalar float placeholder).
        // The lane width is cross-checked against the packed width so an
        // inconsistent element type fails closed rather than mis-packing.
        (ty, Constant::Float(value)) if ty.is_float() => {
            let lane = float_const_bits(ty, *value)?;
            (lane.sort().bitvec_width() == Some(width)).then_some(lane)
        }
        _ => None,
    }
}

/// Human-readable name for a binary operation.
pub(crate) fn op_name(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "add",
        BinOp::Sub => "sub",
        BinOp::Mul => "mul",
        BinOp::UDiv => "udiv",
        BinOp::SDiv => "sdiv",
        BinOp::URem => "urem",
        BinOp::SRem => "srem",
        BinOp::FAdd => "fadd",
        BinOp::FSub => "fsub",
        BinOp::FMul => "fmul",
        BinOp::FDiv => "fdiv",
        BinOp::FRem => "frem",
        BinOp::FMin => "fmin",
        BinOp::FMax => "fmax",
        BinOp::And => "and",
        BinOp::Or => "or",
        BinOp::Xor => "xor",
        BinOp::Shl => "shl",
        BinOp::LShr => "lshr",
        BinOp::AShr => "ashr",
        BinOp::BAnd => "band",
        BinOp::BOr => "bor",
        BinOp::BXor => "bxor",
        BinOp::RotL => "rotl",
        BinOp::RotR => "rotr",
        BinOp::FCopySign => "fcopysign",
    }
}

/// Text mnemonic of a unary operation, as trust-ir spells it.
///
/// EXHAUSTIVE on purpose — no wildcard — so a new `UnOp` is a compile error
/// here until someone decides how the BMC lane models it or refuses it by
/// this name.
pub(crate) fn unop_name(op: UnOp) -> &'static str {
    match op {
        UnOp::Neg => "neg",
        UnOp::Not => "not",
        UnOp::CtPop => "ctpop",
        UnOp::CtLz => "ctlz",
        UnOp::CtTz => "cttz",
        UnOp::BSwap => "bswap",
        UnOp::BitReverse => "bitreverse",
        UnOp::FNeg => "fneg",
        UnOp::FAbs => "fabs",
        UnOp::FSqrt => "fsqrt",
        UnOp::FFloor => "ffloor",
        UnOp::FCeil => "fceil",
        UnOp::FTrunc => "ftrunc",
    }
}

/// Is `op` a floating-point operation?
///
/// EXHAUSTIVE on purpose — no wildcard — so a new `BinOp` cannot compile until it
/// is classified here. Both lanes' float fail-closed checks (float-typed binops,
/// and the ill-typed float-op-on-an-integer `float_on_int` havoc) read this one
/// table instead of each carrying its own list that a new float op could miss.
pub(crate) fn binop_is_floating_point(op: BinOp) -> bool {
    match op {
        BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax
        | BinOp::FCopySign => true,
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::UDiv
        | BinOp::SDiv
        | BinOp::URem
        | BinOp::SRem
        | BinOp::And
        | BinOp::Or
        | BinOp::Xor
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr
        | BinOp::BAnd
        | BinOp::BOr
        | BinOp::BXor
        | BinOp::RotL
        | BinOp::RotR => false,
    }
}

/// EXACT bit-vector encoding of trust-ir's TOTAL integer rotates
/// (`BinOp::RotL` / `BinOp::RotR`, WS3.20).
///
/// trust-ir defines `rotl(x, n) = (x << k | x >> (w - k)) mod 2^w` with
/// `k = n mod w`, `n` read as the UNSIGNED bits of the amount (the reference
/// interpreter's `rotate_at_width`, Lean `semIntBinOp .RotL`); `rotr` is the
/// mirror. There is no out-of-range case and therefore no obligation. The
/// encoding is the same function over bit-vectors:
///
/// * `k` is `n & (w - 1)` when `w` is a power of two (every TrustIR integer
///   width is) and `n urem w` otherwise — both equal `n mod w` over the
///   unsigned reading;
/// * `k == 0` is the identity, selected by an explicit `ite` so the encoding
///   never depends on a backend's reading of a shift by the full width;
/// * otherwise both shift amounts `k` and `w - k` lie in `1..w`.
///
/// `lhs`/`rhs` must already be normalized to the operation type. Returns `None`
/// (the caller havocs AND fails closed) unless both are bit-vectors of one width.
pub(crate) fn bv_rotate(lhs: &Expr, rhs: &Expr, left: bool) -> Option<Expr> {
    let width = lhs.sort().bitvec_width()?;
    if width == 0 || rhs.sort().bitvec_width()? != width {
        return None;
    }
    let amount = if width.is_power_of_two() {
        rhs.clone().bvand(Expr::bitvec_const(i128::from(width - 1), width))
    } else {
        rhs.clone().bvurem(Expr::bitvec_const(i128::from(width), width))
    };
    let complement = Expr::bitvec_const(i128::from(width), width).bvsub(amount.clone());
    let (toward, around) = if left {
        (lhs.clone().bvshl(amount.clone()), lhs.clone().bvlshr(complement))
    } else {
        (lhs.clone().bvlshr(amount.clone()), lhs.clone().bvshl(complement))
    };
    let is_identity = amount.eq(Expr::bitvec_const(0u64, width));
    Some(Expr::ite(is_identity, lhs.clone(), toward.bvor(around)))
}

/// `true` exactly when `op` is a rotate that `bv_rotate` cannot encode for these
/// operands, i.e. when `eval_binop` havocked its result. The integer-binop arms
/// of both lanes fail closed on it, as they do on `float_on_int`.
pub(crate) fn integer_rotate_is_unencodable(op: BinOp, ty: &Ty, lhs: &Expr, rhs: &Expr) -> bool {
    matches!(op, BinOp::RotL | BinOp::RotR)
        && bv_rotate(&normalize_expr_to_ty(lhs, ty), &normalize_expr_to_ty(rhs, ty), true).is_none()
}

/// Map a checked-arithmetic `OverflowOp` to its underlying integer `BinOp`.
///
/// `CheckedBinaryOp` in MIR only ever produces add/sub/mul overflow checks, so
/// this is total over `OverflowOp`.
pub(crate) fn overflow_op_to_binop(op: OverflowOp) -> BinOp {
    match op {
        OverflowOp::AddOverflow => BinOp::Add,
        OverflowOp::SubOverflow => BinOp::Sub,
        OverflowOp::MulOverflow => BinOp::Mul,
    }
}

/// Lower `a * K` as `a << log2(K)` when `K` is a compile-time power-of-two
/// bit-vector constant. `a * 2^k == a << k` (mod `2^w`) for every `k`, so this
/// is EXACT — but the bit-blaster treats a constant shift as a bit relabeling
/// instead of building a full multiplier circuit, which makes the strict UNSAT
/// certificate for constant-scaled byte assembly (`trust-endian`/`trust-radix64`,
/// whose every factor is `256^i` / `64^i` = a power of two) small enough to seal.
/// `None` for a non-constant or non-power-of-two factor (caller falls back to
/// `bvmul`). Both factor orders are handled; the shift amount is a same-width
/// constant. Limited to the value fitting `u128` (widths up to 64 here).
fn mul_by_power_of_two_as_shift(lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    for (var, konst) in [(lhs, rhs), (rhs, lhs)] {
        let ExprValue::BitVecConst { value, width } = konst.value() else {
            continue;
        };
        let Ok(v) = value.to_string().parse::<u128>() else {
            continue;
        };
        if v.is_power_of_two() {
            let k = i128::from(v.trailing_zeros());
            return Some(var.clone().bvshl(Expr::bitvec_const(k, *width)));
        }
    }
    None
}

pub(crate) fn integer_binop_no_overflow_condition(
    op: BinOp,
    ty: &Ty,
    lhs: &Expr,
    rhs: &Expr,
    options: &TranslateOptions,
) -> Option<Expr> {
    if !ty.is_integer() {
        return None;
    }

    // Capture the shift amount at its NATIVE width before normalization: truncating a wide
    // shift amount to `ty` could mask an out-of-range shift (unsound), so the shift case
    // below compares the ORIGINAL `rhs`.
    let rhs_orig = rhs;
    let lhs = &normalize_expr_to_ty(lhs, ty);
    let rhs = &normalize_expr_to_ty(rhs, ty);

    // EXHAUSTIVE on purpose (no wildcard): every `BinOp` states here whether it
    // can carry an overflow / shift-range obligation at all, so a new op must be
    // decided before this compiles instead of silently reaching the `_ => None`
    // of the per-signedness table below.
    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::SDiv
        | BinOp::SRem
        | BinOp::Shl
        | BinOp::LShr
        | BinOp::AShr => {}
        // TOTAL on integers: unsigned division/remainder (their div-by-zero is
        // `integer_binop_div_by_zero_condition`), the bitwise ops, and the
        // WS3.20 rotates, whose amount is reduced MODULO the width — unlike the
        // shifts there is no out-of-range amount, hence no obligation.
        BinOp::UDiv
        | BinOp::URem
        | BinOp::And
        | BinOp::Or
        | BinOp::Xor
        | BinOp::RotL
        | BinOp::RotR => return None,
        // Ill-typed on an integer type: `eval_binop` havocs these and the
        // integer-binop arms fail closed (`binop_is_floating_point`, and the
        // boolean connectives are rejected by trust-ir's validator).
        BinOp::FAdd
        | BinOp::FSub
        | BinOp::FMul
        | BinOp::FDiv
        | BinOp::FRem
        | BinOp::FMin
        | BinOp::FMax
        | BinOp::FCopySign
        | BinOp::BAnd
        | BinOp::BOr
        | BinOp::BXor => return None,
    }

    match (op, ty.is_signed()) {
        (BinOp::Add, true) if options.check_signed_overflow => {
            Some(lhs.clone().bvadd_no_overflow_signed(rhs.clone()))
        }
        (BinOp::Sub, true) if options.check_signed_overflow => {
            Some(lhs.clone().bvsub_no_overflow_signed(rhs.clone()))
        }
        (BinOp::Mul, true) if options.check_signed_overflow => {
            Some(lhs.clone().bvmul_no_overflow_signed(rhs.clone()))
        }
        (BinOp::SDiv | BinOp::SRem, true) if options.check_signed_overflow => {
            Some(lhs.clone().bvsdiv_no_overflow(rhs.clone()))
        }
        (BinOp::Add, false) if options.check_unsigned_overflow => {
            Some(lhs.clone().bvadd_no_overflow_unsigned(rhs.clone()))
        }
        (BinOp::Sub, false) if options.check_unsigned_overflow => {
            Some(lhs.clone().bvsub_no_underflow_unsigned(rhs.clone()))
        }
        (BinOp::Mul, false) if options.check_unsigned_overflow => {
            Some(lhs.clone().bvmul_no_overflow_unsigned(rhs.clone()))
        }
        // Trust (7th false-proof, found by soundness_oracle::shift_discharge_soundness):
        // `a << s` / `a >> s` PANIC in Rust when the shift amount `s >= bit width`
        // ("attempt to shift left/right with overflow"). The encoder lowered shifts to a
        // total `bvshl`/`bvlshr`/`bvashr` with NO obligation, so `a << s` with an
        // out-of-range `s` was proved SAFE while it traps. No-overflow ⟺ `s < width`,
        // compared at the amount's native width (un-normalized) so a wide amount cannot be
        // truncated into range.
        (BinOp::Shl | BinOp::LShr | BinOp::AShr, _)
            if options.check_signed_overflow || options.check_unsigned_overflow =>
        {
            let ty_width = ty.bit_width_with(HOST_POINTER_BITS)?;
            let amount_width = rhs_orig.sort().bitvec_width()?;
            let width_const = Expr::bitvec_const(i128::from(ty_width), amount_width);
            Some(rhs_orig.clone().bvult(width_const))
        }
        _ => None,
    }
}

/// Encode the `BoundedOutput { lo, hi }` out-of-range condition for one
/// return value, or `None` when the annotation has no exact semantics against
/// the return type (the caller MUST fail closed on `None`).
///
/// The trust-ir annotation carries `f64` bounds. A VC is emitted only when:
/// - the return type is an INTEGER type. A float-typed return must NOT be
///   compared with bitvector order over its raw IEEE-754 bit pattern:
///   sign-magnitude float order is not two's-complement order (all negative
///   floats order-invert, -0.0/+0.0 split, NaN is unordered), so the old
///   `bvslt`/`bvsgt` encoding could falsely prove or falsely refute the
///   postcondition;
/// - both bounds are exactly integer-valued (`f64 → i128 → f64` bit
///   round-trip). Truncating a fractional bound checks a DIFFERENT
///   postcondition than annotated (e.g. `lo = 0.5` truncated to `0` accepts
///   a returned `0` that violates the real bound);
/// - both bounds fit the return type's value range. `bitvec_const` would
///   silently wrap an out-of-range bound to a different value.
///
/// The comparisons match the return type's signedness (`bvult`/`bvugt` for
/// unsigned types): a signed compare over an unsigned return misreads values
/// with the top bit set as negative and can falsely refute an in-range value.
pub(crate) fn bounded_output_out_of_range(
    ret_ty: &Ty,
    ret_expr: &Expr,
    lo: f64,
    hi: f64,
) -> Option<Expr> {
    if !ret_ty.is_integer() {
        return None;
    }
    let width = ret_ty.bit_width_with(HOST_POINTER_BITS)?;
    let lo_int = exact_f64_to_i128(lo)?;
    let hi_int = exact_f64_to_i128(hi)?;
    if !int_fits_ty(lo_int, ret_ty, width) || !int_fits_ty(hi_int, ret_ty, width) {
        return None;
    }
    let lo_expr = Expr::bitvec_const(lo_int, width);
    let hi_expr = Expr::bitvec_const(hi_int, width);
    let (too_low, too_high) = if ret_ty.is_signed() {
        (ret_expr.clone().bvslt(lo_expr), ret_expr.clone().bvsgt(hi_expr))
    } else {
        (ret_expr.clone().bvult(lo_expr), ret_expr.clone().bvugt(hi_expr))
    };
    Some(too_low.or(too_high))
}

/// `v` as an `i128` if the conversion is exact (bit round-trip), else `None`.
///
/// Rejects non-finite values, fractional values, values outside i128 range
/// (`as` saturates, breaking the round-trip), and `-0.0` (round-trips to
/// `+0.0` with different bits — rejected for a uniform "bit-exact or fail
/// closed" rule rather than special-cased).
fn exact_f64_to_i128(v: f64) -> Option<i128> {
    if !v.is_finite() {
        return None;
    }
    let int = v as i128;
    ((int as f64).to_bits() == v.to_bits()).then_some(int)
}

/// Whether `v` is within the value range of integer type `ty` of `width` bits.
fn int_fits_ty(v: i128, ty: &Ty, width: u32) -> bool {
    if ty.is_signed() {
        if width >= 128 {
            return true;
        }
        let min = -(1i128 << (width - 1));
        let max = (1i128 << (width - 1)) - 1;
        v >= min && v <= max
    } else {
        if v < 0 {
            return false;
        }
        if width >= 128 {
            return true;
        }
        (v as u128) < (1u128 << width)
    }
}

/// Types whose modeled bit patterns support EXACT equality semantics
/// (`x == y` ⟺ same bits ⟺ same value): booleans, integers, and thin
/// pointers. Floats are deliberately excluded — IEEE equality is not bit
/// equality — as are aggregates/fat pointers, whose modeled bits are opaque
/// placeholders. Shared by both the BMC and typed-CHC lanes.
pub(crate) fn is_eq_comparable_ty(ty: &Ty) -> bool {
    matches!(ty, Ty::Bool) || is_ordered_scalar_ty(ty)
}

/// Types whose modeled bit patterns support EXACT bitvector ordering
/// semantics. Floats are excluded: IEEE order is sign-magnitude, not
/// two's-complement. Shared by both the BMC and typed-CHC lanes.
pub(crate) fn is_ordered_scalar_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::Isize
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Usize
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
    )
}

pub(crate) fn integer_binop_div_by_zero_condition(
    op: BinOp,
    ty: &Ty,
    rhs: &Expr,
    options: &TranslateOptions,
) -> Option<Expr> {
    if !options.check_div_by_zero
        || !ty.is_integer()
        || !matches!(op, BinOp::SDiv | BinOp::UDiv | BinOp::SRem | BinOp::URem)
    {
        return None;
    }

    let width = ty.bit_width_with(HOST_POINTER_BITS)?;
    let rhs = normalize_expr_to_ty(rhs, ty);
    Some(rhs.eq(Expr::bitvec_const(0u64, width)))
}

#[cfg(test)]
mod expr_fidelity_tests {
    //! Structural fidelity: the LIVE encoder builds exactly the obligation EXPRESSION the
    //! clean proofs model + prove sound. This ties the modeled clean `Expr` AST
    //! (expr_obligation_semantics.lean / whole_program_expr_contract.lean) to the real
    //! `ay_bindings::ExprValue`, closing the "the proofs are over modeled, not literal,
    //! datatypes" gap for the comparison obligations — at the level of the actual AST node.
    use super::{
        TranslateOptions, integer_binop_div_by_zero_condition, integer_binop_no_overflow_condition,
    };
    use ay_bindings::{Expr, ExprValue, Sort};
    use trust_ir::inst::BinOp;
    use trust_ir::ty::Ty;

    /// The clean proof `shiftObligationExpr = Not(BvUlt operand width)` is sound. This proves
    /// the live `integer_binop_no_overflow_condition(Shl, ...)` actually returns that
    /// `BvUlt(amount, width)` no-overflow check (whose negation is the shift obligation) — the
    /// 7th-false-proof fix, now structurally pinned to the clean-proven AST.
    #[test]
    fn shift_no_overflow_condition_is_bvult() {
        let opts = TranslateOptions::default();
        let lhs = Expr::var("a", Sort::bitvec(32));
        let amount = Expr::var("s", Sort::bitvec(32));
        let cond = integer_binop_no_overflow_condition(BinOp::Shl, &Ty::U32, &lhs, &amount, &opts)
            .expect("Shl MUST get a no-overflow obligation (the shift-overflow fix)");
        assert!(
            matches!(cond.value(), ExprValue::BvULt(_, _)),
            "shift no-overflow condition must be a `BvULt(amount, width)` check (the structure \
             clean's shiftObligationExpr proves sound)"
        );
    }

    /// Two-polarity at the structural level: div-by-zero builds an EQUALITY, not a BvULt — so
    /// the shift assertion above is specific to the shift AST, not vacuous.
    #[test]
    fn div_by_zero_condition_is_not_bvult() {
        let opts = TranslateOptions::default();
        let rhs = Expr::var("d", Sort::bitvec(32));
        let cond = integer_binop_div_by_zero_condition(BinOp::UDiv, &Ty::U32, &rhs, &opts)
            .expect("UDiv MUST get a div-by-zero obligation");
        assert!(
            !matches!(cond.value(), ExprValue::BvULt(_, _)),
            "div-by-zero condition is `divisor == 0` (an equality), not a BvULt"
        );
    }

    /// FIDELITY for the OVERFLOW arms: the live encoder emits ay's BV no-overflow PRIMITIVES
    /// for checked add/sub/mul — the dedicated SMT nodes ay's solver decides, exactly the
    /// trust boundary named in clean's `overflow_trust_boundary.lean` (`ayNoOverflow`). This
    /// pins that boundary to the real code: the overflow obligation IS the ay primitive (not
    /// a comparison AST), so the clean proof's modeling of it as a trusted primitive is faithful.
    #[test]
    fn arithmetic_overflow_conditions_are_the_ay_primitives() {
        let opts = TranslateOptions::default();
        let a = Expr::var("a", Sort::bitvec(32));
        let b = Expr::var("b", Sort::bitvec(32));
        let add = integer_binop_no_overflow_condition(BinOp::Add, &Ty::U32, &a, &b, &opts)
            .expect("Add MUST get a no-overflow obligation");
        assert!(
            matches!(add.value(), ExprValue::BvAddNoOverflowUnsigned(_, _)),
            "unsigned add overflow obligation must be the ay BvAddNoOverflowUnsigned primitive"
        );
        let sub = integer_binop_no_overflow_condition(BinOp::Sub, &Ty::U32, &a, &b, &opts)
            .expect("Sub MUST get a no-underflow obligation");
        assert!(
            matches!(sub.value(), ExprValue::BvSubNoUnderflowUnsigned(_, _)),
            "unsigned sub underflow obligation must be the ay BvSubNoUnderflowUnsigned primitive"
        );
        let mul = integer_binop_no_overflow_condition(BinOp::Mul, &Ty::U32, &a, &b, &opts)
            .expect("Mul MUST get a no-overflow obligation");
        assert!(
            matches!(mul.value(), ExprValue::BvMulNoOverflowUnsigned(_, _)),
            "unsigned mul overflow obligation must be the ay BvMulNoOverflowUnsigned primitive"
        );
    }
}
