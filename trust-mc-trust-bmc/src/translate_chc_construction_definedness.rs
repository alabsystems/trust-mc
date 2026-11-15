// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Conservative source-SSA definedness for the new complete field constructor.
//!
//! A fresh SMT term is not evidence that an operand is initialized. In
//! particular, scalar `Undef` and a retained `Uninit` lane must not cross the
//! interpreter's consuming `MakeAggregate` boundary. This analysis supplies no
//! value facts: unsupported definitions, memory reads and cycles simply refuse.

use super::*;

const MAX_DEFINEDNESS_WORK: usize = 16_384;
pub(super) const MAX_DEFINEDNESS_DEPTH: usize = 64;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
enum QueryKind {
    Transport,
    Initialized,
    Cell,
    CellTransport,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Query {
    kind: QueryKind,
    function: FuncId,
    value: ValueId,
    path: Vec<u32>,
    defined: Option<Vec<bool>>,
    transport: Option<Vec<bool>>,
    assumptions: Vec<(FuncId, ValueId)>,
    transport_assumptions: Vec<(FuncId, ValueId)>,
    reference_assumptions: Vec<(FuncId, Vec<bool>)>,
}

struct FunctionIndex<'m> {
    entry: BlockId,
    parameters: BTreeMap<ValueId, (BlockId, usize, &'m Ty)>,
    definitions: BTreeMap<ValueId, &'m InstrNode>,
    types: BTreeMap<ValueId, Ty>,
    incoming: BTreeMap<BlockId, Vec<&'m [ValueId]>>,
    source_order: std::cell::OnceCell<bool>,
    dominators: std::cell::OnceCell<trust_ir::analysis::DominatorTree>,
    valid: bool,
}

/// Translation-local facts over ONE immutable source module. This index and
/// its exact-context memo never cross module/translation lifetimes.
pub(super) struct Analysis<'m> {
    module: &'m Module,
    indices: RefCell<BTreeMap<FuncId, std::rc::Rc<FunctionIndex<'m>>>>,
    proved: RefCell<BTreeSet<Query>>,
    initialized_cells: RefCell<BTreeSet<(FuncId, ValueId)>>,
    transported_cells: RefCell<BTreeSet<(FuncId, ValueId)>>,
    source_references: Option<&'m crate::SourceReferenceFacts<'m>>,
    reference_root: Option<FuncId>,
    reference_calls: std::rc::Rc<RefCell<Vec<(FuncId, Vec<bool>)>>>,
    reference_readonly: RefCell<BTreeSet<FuncId>>,
}

/// An owned stack handle avoids borrowing the mutable translator during a
/// nested summary. Every return/unwind restores the preceding invocation.
pub(super) struct ReferenceCallScope {
    calls: std::rc::Rc<RefCell<Vec<(FuncId, Vec<bool>)>>>,
    previous_len: usize,
}

impl Drop for ReferenceCallScope {
    fn drop(&mut self) {
        self.calls.borrow_mut().truncate(self.previous_len);
    }
}

impl<'m> Analysis<'m> {
    pub(super) fn new(module: &'m Module) -> Self {
        Self {
            module,
            indices: RefCell::new(BTreeMap::new()),
            proved: RefCell::new(BTreeSet::new()),
            initialized_cells: RefCell::new(BTreeSet::new()),
            transported_cells: RefCell::new(BTreeSet::new()),
            source_references: None,
            reference_root: None,
            reference_calls: std::rc::Rc::new(RefCell::new(Vec::new())),
            reference_readonly: RefCell::new(BTreeSet::new()),
        }
    }

    pub(super) fn with_source_references(
        module: &'m Module,
        root: FuncId,
        facts: &'m crate::SourceReferenceFacts<'m>,
    ) -> Self {
        let mut result = Self::new(module);
        if facts.matches_module(module) {
            result.source_references = Some(facts);
            result.reference_root = Some(root);
        }
        result
    }

    fn reference_assumptions(&self) -> Vec<(FuncId, Vec<bool>)> {
        self.reference_calls.borrow().clone()
    }

    pub(super) fn enter_reference_arguments(
        &self,
        function: FuncId,
        initialized: Vec<bool>,
    ) -> Option<ReferenceCallScope> {
        self.source_references?;
        let previous_len = self.reference_calls.borrow().len();
        self.reference_calls.borrow_mut().push((function, initialized));
        Some(ReferenceCallScope { calls: self.reference_calls.clone(), previous_len })
    }

    /// Requirements of the callee are discharged from the CALLER's actual
    /// provenance. A source parameter fact on the callee cannot seed itself.
    pub(super) fn reference_arguments(
        &self,
        caller: &Function,
        callee: &Function,
        args: &[ValueId],
        entry_defined: Option<&[bool]>,
    ) -> Vec<bool> {
        let Some(entry) = callee.block(callee.entry) else { return Vec::new() };
        let Some(facts) = self.source_references else { return vec![false; entry.params.len()] };
        entry
            .params
            .iter()
            .enumerate()
            .map(|(position, (parameter, _))| {
                let Some(pointee) = facts.parameter(callee.id, *parameter) else { return false };
                let Some(actual) = args.get(position) else { return false };
                let mut work = MAX_DEFINEDNESS_WORK;
                self.pointer_initialized_at(
                    caller,
                    *actual,
                    pointee,
                    entry_defined,
                    MAX_DEFINEDNESS_DEPTH,
                    &mut work,
                ) || self.block_local_actual_initialized(
                    caller,
                    callee.id,
                    args,
                    *actual,
                    pointee,
                    entry_defined,
                    &mut work,
                )
            })
            .collect()
    }

    /// The whole-cell proof deliberately rejects escaping calls. For an actual
    /// at its FIRST escape, prove initialization at that exact call instead:
    /// allocation, aliases, stores and the call must be in one source block;
    /// no earlier escape, mismatched write or poison may precede it. This proves
    /// no post-call initialization and supplies no loaded numeric value.
    fn block_local_actual_initialized(
        &self,
        caller: &Function,
        callee: FuncId,
        args: &[ValueId],
        actual: ValueId,
        pointee: &Ty,
        entry_defined: Option<&[bool]>,
        work: &mut usize,
    ) -> bool {
        let Some(index) = self.index(caller.id) else { return false };
        if !index.valid {
            return false;
        }
        let Some(root) = allocation_root(&index, actual, MAX_DEFINEDNESS_DEPTH) else {
            return false;
        };
        if !matches!(index.definitions.get(&root).map(|node| &node.inst),
            Some(Inst::Alloca { ty, count: None, align: None }) if ty == pointee)
        {
            return false;
        }
        let aliases: BTreeSet<_> = index
            .definitions
            .keys()
            .copied()
            .filter(|value| allocation_root(&index, *value, MAX_DEFINEDNESS_DEPTH) == Some(root))
            .collect();
        let mut found_call = false;
        for block in &caller.blocks {
            let mut allocated_here = false;
            let mut initialized = false;
            let mut clean = true;
            for node in &block.body {
                if *work == 0 {
                    return false;
                }
                *work -= 1;
                if node.results.contains(&root) {
                    allocated_here = true;
                }
                if matches!(&node.inst, Inst::Call { callee: target, args: actuals }
                    if *target == callee && actuals.as_slice() == args)
                {
                    found_call = true;
                    if !allocated_here || !clean || !initialized {
                        return false;
                    }
                }
                let mut uses = Vec::new();
                if collect_inst_value_uses(&node.inst, &mut uses) {
                    return false;
                }
                if !uses.iter().any(|value| aliases.contains(value)) {
                    continue;
                }
                match &node.inst {
                    Inst::Store { ty, ptr, value, volatile: false, align: None }
                        if allocated_here
                            && *ptr == root
                            && ty == pointee
                            && !aliases.contains(value) =>
                    {
                        initialized = defined_at(
                            self,
                            self.module,
                            caller,
                            *value,
                            &[],
                            entry_defined,
                            MAX_DEFINEDNESS_DEPTH,
                            work,
                        );
                    }
                    Inst::Load { ty, ptr, volatile: false, align: None }
                        if ty == pointee && aliases.contains(ptr) && initialized => {}
                    inst if transparent_pointer_alias(inst)
                        .is_some_and(|value| aliases.contains(&value)) => {}
                    // Including the current call: no later call may reuse this
                    // pre-call fact after the address has escaped.
                    _ => clean = false,
                }
            }
        }
        found_call
    }

    fn reference_call_is_valid(
        &self,
        caller: &Function,
        callee: FuncId,
        args: &[ValueId],
        entry_defined: Option<&[bool]>,
    ) -> bool {
        let Some(facts) = self.source_references else { return true };
        let Some(callee) = self.module.function_by_id(callee) else { return true };
        // A checked context cannot contain entry-parameter facts for a
        // declaration with no entry. Its existing unsupported/total-call model
        // remains responsible for that call, without inventing a requirement.
        let Some(entry) = callee.block(callee.entry) else { return true };
        let actuals = self.reference_arguments(caller, callee, args, entry_defined);
        entry.params.iter().enumerate().all(|(position, (value, _))| {
            facts.parameter(callee.id, *value).is_none()
                || actuals.get(position).copied().unwrap_or(false)
        })
    }

    fn pointer_initialized_at(
        &self,
        function: &Function,
        pointer: ValueId,
        pointee: &Ty,
        entry_defined: Option<&[bool]>,
        depth: usize,
        work: &mut usize,
    ) -> bool {
        if depth == 0 || *work == 0 {
            return false;
        }
        *work -= 1;
        let Some(facts) = self.source_references else { return false };
        let Some(index) = self.index(function.id) else { return false };
        if !index.valid || index.types.get(&pointer) != Some(&Ty::Ptr) {
            return false;
        }
        if let Some((block, position, _)) = index.parameters.get(&pointer) {
            if *block != function.entry
                || facts.parameter(function.id, pointer) != Some(pointee)
                || index.incoming.get(block).is_some_and(|edges| !edges.is_empty())
                || !self.reference_memory_preserved(function, depth, work, &mut BTreeSet::new())
            {
                return false;
            }
            return self
                .reference_calls
                .borrow()
                .iter()
                .rev()
                .find(|(callee, _)| *callee == function.id)
                .map_or(self.reference_root == Some(function.id), |(_, flags)| {
                    flags.get(*position).copied().unwrap_or(false)
                });
        }
        let Some(node) = index.definitions.get(&pointer) else { return false };
        match &node.inst {
            Inst::Copy { operand, .. }
            | Inst::Borrow { ptr: operand }
            | Inst::BorrowMut { ptr: operand } => self.pointer_initialized_at(
                function,
                *operand,
                pointee,
                entry_defined,
                depth - 1,
                work,
            ),
            Inst::Alloca { ty, count: None, align: None } if ty == pointee => cell_is_initialized(
                self,
                self.module,
                function,
                pointer,
                entry_defined,
                depth,
                work,
            ),
            // No raw cast, global, unknown memory, interior offset or constant
            // address inherits the entry-reference premise.
            _ => false,
        }
    }

    /// An entry pointee premise is not a permanent memory invariant. This
    /// initial domain requires transitive frame-local/read-only effects:
    /// parameter/global writes, opaque calls, cycles and unmodeled effects
    /// refuse. Stores are permitted only to exact whole local allocations.
    /// Checking the whole body is conservative when a write follows the load.
    fn reference_memory_preserved(
        &self,
        function: &Function,
        depth: usize,
        work: &mut usize,
        visiting: &mut BTreeSet<FuncId>,
    ) -> bool {
        if self.reference_readonly.borrow().contains(&function.id) {
            return true;
        }
        if depth == 0 || *work == 0 || function.blocks.is_empty() || !visiting.insert(function.id) {
            return false;
        }
        let result = (|| {
            let Some(index) = self.index(function.id) else { return false };
            if !index.valid {
                return false;
            }
            for node in function.blocks.iter().flat_map(|block| &block.body) {
                if *work == 0 {
                    return false;
                }
                *work -= 1;
                match &node.inst {
                    Inst::Store { ty, ptr, volatile: false, align: None, .. } => {
                        let Some(root) = allocation_root(&index, *ptr, depth) else { return false };
                        if !matches!(index.definitions.get(&root).map(|node| &node.inst),
                            Some(Inst::Alloca { ty: allocated, count: None, align: None }) if allocated == ty)
                        {
                            return false;
                        }
                        let mut alias = *ptr;
                        let mut left = depth;
                        while alias != root {
                            if left == 0 {
                                return false;
                            }
                            left -= 1;
                            let Some(parent) = index
                                .definitions
                                .get(&alias)
                                .and_then(|node| transparent_pointer_alias(&node.inst))
                            else {
                                return false;
                            };
                            alias = parent;
                        }
                    }
                    Inst::Store { .. } | Inst::Load { volatile: true, .. } => return false,
                    Inst::Call { callee, .. } => {
                        let Some(callee) = self.module.function_by_id(*callee) else {
                            return false;
                        };
                        if !self.reference_memory_preserved(callee, depth - 1, work, visiting) {
                            return false;
                        }
                    }
                    Inst::Cast { op, .. } if !matches!(op, CastOp::IntToPtr) => {}
                    Inst::MakeAggregate {
                        ty: Ty::Struct(_) | Ty::Tuple(_), variant: None, ..
                    } => {}
                    Inst::BinOp { .. }
                    | Inst::UnOp { .. }
                    | Inst::Overflow { .. }
                    | Inst::ICmp { .. }
                    | Inst::FCmp { .. }
                    | Inst::Load { volatile: false, .. }
                    | Inst::Alloca { .. }
                    | Inst::GEP { .. }
                    | Inst::Br { .. }
                    | Inst::CondBr { .. }
                    | Inst::Switch { .. }
                    | Inst::Return { .. }
                    | Inst::ExtractField { .. }
                    | Inst::InsertField { .. }
                    | Inst::ExtractElement { .. }
                    | Inst::InsertElement { .. }
                    | Inst::ArraySplat { .. }
                    | Inst::Const { .. }
                    | Inst::NullPtr
                    | Inst::Undef { .. }
                    | Inst::Assume { .. }
                    | Inst::Assert { .. }
                    | Inst::Unreachable
                    | Inst::Copy { .. }
                    | Inst::Select { .. } => {}
                    // Same conservative pure-effect families as the existing
                    // frame-local fence; no unknown instruction is read-only.
                    _ => return false,
                }
            }
            true
        })();
        visiting.remove(&function.id);
        if result {
            self.reference_readonly.borrow_mut().insert(function.id);
        }
        result
    }

    fn source_load_initialized(
        &self,
        function: &Function,
        result: ValueId,
        path: &[u32],
        entry_defined: Option<&[bool]>,
        depth: usize,
        work: &mut usize,
    ) -> bool {
        let Some(facts) = self.source_references else { return false };
        let Some(fact) = facts.load(function.id, result, path) else { return false };
        self.pointer_initialized_at(
            function,
            fact.pointer,
            &fact.pointee,
            entry_defined,
            depth,
            work,
        )
    }

    /// Initialization of opaque reference VALUE bits only. Deliberately never
    /// queried by pointer_initialized_at: this establishes no pointee fact.
    fn source_reference_value_initialized(&self, function: FuncId, result: ValueId) -> bool {
        self.source_references
            .is_some_and(|facts| facts.reference_value(function, result).is_some())
    }

    /// The live source seam's certificate that this exact marked `Undef` stands
    /// for an initialized value (`SourceInitializedValueFact`). Selects only the
    /// initialized reading of the fresh value; it never constrains the value.
    fn source_initialized_value(&self, function: FuncId, result: ValueId) -> bool {
        self.source_references
            .is_some_and(|facts| facts.initialized_value(function, result).is_some())
    }

    /// The live source seam's certificate that this exact by-value ENTRY
    /// parameter is initialized in every lane (`SourceInitializedParameterFact`).
    /// Read only for a root translation; it never constrains the value.
    fn source_initialized_parameter(&self, function: FuncId, value: ValueId) -> bool {
        self.source_references
            .is_some_and(|facts| facts.initialized_parameter(function, value).is_some())
    }

    pub(super) fn matches_function(&self, function: &Function) -> bool {
        self.module.function_by_id(function.id).is_some_and(|source| source == function)
    }

    fn index(&self, id: FuncId) -> Option<std::rc::Rc<FunctionIndex<'m>>> {
        if let Some(index) = self.indices.borrow().get(&id) {
            return Some(index.clone());
        }
        let function = self.module.function_by_id(id)?;
        let mut index = FunctionIndex {
            entry: function.entry,
            parameters: BTreeMap::new(),
            definitions: BTreeMap::new(),
            types: BTreeMap::new(),
            incoming: BTreeMap::new(),
            source_order: std::cell::OnceCell::new(),
            dominators: std::cell::OnceCell::new(),
            valid: true,
        };
        for block in &function.blocks {
            for (position, (value, ty)) in block.params.iter().enumerate() {
                if index.parameters.insert(*value, (block.id, position, ty)).is_some() {
                    index.valid = false;
                }
                index.types.insert(*value, ty.clone());
            }
            for node in &block.body {
                for (value, ty) in node.results.iter().zip(node.result_tys(self.module)) {
                    index.types.insert(*value, ty);
                }
                for value in &node.results {
                    if index.definitions.insert(*value, node).is_some() {
                        index.valid = false;
                    }
                }
            }
            if let Some(terminator) = block.body.last() {
                for edge in terminator.inst.successor_edges() {
                    index.incoming.entry(edge.target).or_default().push(edge.args);
                }
            }
        }
        index.valid &= index.parameters.keys().all(|value| !index.definitions.contains_key(value));
        let index = std::rc::Rc::new(index);
        self.indices.borrow_mut().insert(id, index.clone());
        Some(index)
    }

    fn prove(&self, query: Query, compute: impl FnOnce() -> bool) -> bool {
        if self.proved.borrow().contains(&query) {
            return true;
        }
        let result = compute();
        // Never cache a budget/cycle/unknown refusal as if it were a source
        // property. Only actually established facts are reused.
        if result {
            self.proved.borrow_mut().insert(query);
        }
        result
    }

    /// Recurrence induction requires actual reachable, well-ordered SSA. Reuse
    /// the canonical CFG dominator tree; malformed/unmodelled CFG stays closed.
    /// This establishes no type, value, proof or source-authority fact.
    fn recurrence_source_is_ordered(&self, function: &Function, block: BlockId) -> bool {
        let Some(index) = self.index(function.id) else { return false };
        let tree =
            index.dominators.get_or_init(|| trust_ir::analysis::DominatorTree::new(function));
        if !tree.is_reachable(block) {
            return false;
        }
        *index.source_order.get_or_init(|| {
            let mut blocks = BTreeMap::new();
            let mut sites = BTreeMap::new();
            for block in &function.blocks {
                if blocks.insert(block.id, block).is_some() {
                    return false;
                }
                for (value, _) in &block.params {
                    sites.insert(*value, (block.id, 0));
                }
                for (position, node) in block.body.iter().enumerate() {
                    for value in &node.results {
                        sites.insert(*value, (block.id, position + 1));
                    }
                }
            }
            if !blocks.contains_key(&function.entry) {
                return false;
            }
            for block in &function.blocks {
                let Some(terminator) = block.body.last() else { return false };
                if !terminator.inst.is_terminator() {
                    return false;
                }
                for edge in terminator.inst.successor_edges() {
                    if !blocks
                        .get(&edge.target)
                        .is_some_and(|target| target.params.len() == edge.args.len())
                    {
                        return false;
                    }
                    let target = blocks.get(&edge.target).unwrap();
                    if edge
                        .args
                        .iter()
                        .zip(&target.params)
                        .any(|(value, (_, ty))| index.types.get(value) != Some(ty))
                    {
                        return false;
                    }
                }
                for (position, node) in block.body.iter().enumerate() {
                    if node.inst.is_terminator() && position + 1 != block.body.len() {
                        return false;
                    }
                    if matches!(node.inst, Inst::Invoke { .. }) {
                        return false;
                    }
                    let mut uses = Vec::new();
                    if collect_inst_value_uses(&node.inst, &mut uses) {
                        return false;
                    }
                    for used in uses {
                        let Some((defined_block, defined_position)) = sites.get(&used) else {
                            return false;
                        };
                        if *defined_block == block.id {
                            if *defined_position >= position + 1 {
                                return false;
                            }
                        } else if !tree.strictly_dominates(*defined_block, block.id) {
                            return false;
                        }
                    }
                }
            }
            true
        })
    }
}

/// Decompose only pure, initializedness-preserving update syntax. Encountering
/// the target phi is a hypothetical induction step, never a proof: callers
/// MUST also check every external operand and a real nonrecursive incoming seed.
fn recurrence_inputs(
    module: &Module,
    index: &FunctionIndex<'_>,
    value: ValueId,
    target: ValueId,
    depth: usize,
) -> Option<(bool, Vec<ValueId>)> {
    if depth == 0 {
        return None;
    }
    if value == target {
        return Some((true, Vec::new()));
    }
    // A block parameter with ONE incoming edge is a forwarding identity, not
    // another induction hypothesis. Keep all multi-predecessor phis separate.
    if let Some((block, position, _)) = index.parameters.get(&value)
        && *block != index.entry
        && let Some(incoming) = index.incoming.get(block)
        && incoming.len() == 1
    {
        return recurrence_inputs(module, index, *incoming[0].get(*position)?, target, depth - 1);
    }
    let Some(node) = index.definitions.get(&value) else { return Some((false, vec![value])) };
    let has_type = |value, ty: &Ty| index.types.get(&value) == Some(ty);
    let inputs: Vec<_> = match &node.inst {
        Inst::Copy { ty, operand } | Inst::UnOp { ty, operand, .. } if has_type(*operand, ty) => {
            vec![*operand]
        }
        Inst::Cast { src_ty, dst_ty, operand, .. }
            if has_type(*operand, src_ty) && initialized_cast_shape(module, src_ty, dst_ty) =>
        {
            vec![*operand]
        }
        Inst::BinOp { ty, lhs, rhs, .. }
        | Inst::ICmp { ty, lhs, rhs, .. }
        | Inst::FCmp { ty, lhs, rhs, .. }
        | Inst::Overflow { ty, lhs, rhs, .. }
            if has_type(*lhs, ty) && has_type(*rhs, ty) =>
        {
            vec![*lhs, *rhs]
        }
        Inst::Select { ty, cond, then_val, else_val }
            if has_type(*cond, &Ty::Bool) && has_type(*then_val, ty) && has_type(*else_val, ty) =>
        {
            vec![*cond, *then_val, *else_val]
        }
        Inst::ArraySplat { ty: Ty::Array(elem, _), value }
            if module.types.get(elem.as_usize()).is_some_and(|ty| has_type(*value, ty)) =>
        {
            vec![*value]
        }
        Inst::InsertElement { ty: ty @ Ty::Array(elem, _), array, index: subscript, value }
            if module.types.get(elem.as_usize()).is_some_and(|ty| has_type(*value, ty))
                && has_type(*array, ty)
                && index.types.get(subscript).is_some_and(Ty::is_integer) =>
        {
            vec![*array, *subscript, *value]
        }
        Inst::ExtractElement { .. } | Inst::ExtractField { .. } => {
            return Some((false, vec![value]));
        }
        Inst::MakeAggregate { ty, variant: None, fields } => {
            let matches = match ty {
                Ty::Array(elem, len) => {
                    u64::try_from(fields.len()).ok() == Some(*len)
                        && module
                            .types
                            .get(elem.as_usize())
                            .is_some_and(|ty| fields.iter().all(|value| has_type(*value, ty)))
                }
                _ => aggregate_field_tys_of(module, ty).is_some_and(|types| {
                    types.len() == fields.len()
                        && fields.iter().zip(types).all(|(value, ty)| has_type(*value, &ty))
                }),
            };
            if !matches {
                return None;
            }
            fields.clone()
        }
        _ => return Some((false, vec![value])),
    };
    let mut recursive = false;
    let mut external = Vec::new();
    for input in inputs {
        let (recur, mut leaves) = recurrence_inputs(module, index, input, target, depth - 1)?;
        recursive |= recur;
        external.append(&mut leaves);
    }
    Some((recursive, external))
}

pub(super) fn supported_type(module: &Module, ty: &Ty) -> bool {
    fn visit(module: &Module, ty: &Ty, depth: usize) -> bool {
        if depth == 0 {
            return false;
        }
        match ty {
            Ty::FatPtr(_) => false,
            Ty::Array(_, 0) | Ty::Unit => true,
            Ty::Array(elem, _) => {
                module.types.get(elem.as_usize()).is_some_and(|elem| visit(module, elem, depth - 1))
            }
            _ => match aggregate_field_tys_of(module, ty) {
                Some(fields) => fields.iter().all(|field| visit(module, field, depth - 1)),
                None => is_scalar_field_ty(ty),
            },
        }
    }
    visit(module, ty, MAX_DEFINEDNESS_DEPTH)
}

pub(super) fn contains_opaque(binding: &CallSummaryBinding) -> bool {
    match binding {
        CallSummaryBinding::OpaqueFatPtr(_) | CallSummaryBinding::Uninit(_) => true,
        CallSummaryBinding::Scalar(_) => false,
        CallSummaryBinding::Aggregate(value) => value.fields.iter().any(contains_opaque),
        CallSummaryBinding::Array(value) => value.lanes.as_deref().is_some_and(contains_opaque),
    }
}

/// Scalar entry arguments cannot carry top-level poison across the canonical
/// call boundary. Aggregate arguments may still transport unwritten lanes, so in
/// a callee summary (`entry_defined: Some(..)`) only checked actual-argument flags
/// establish their recursive initialization. At the root (`entry_defined: None`)
/// one aggregate is granted from its declared type alone: an entry parameter of
/// `[e; n]` over a value-domain element (`root_parameter_is_a_value_domain_array`),
/// because a root parameter ranges over its type's value domain (trust-ir
/// SPEC_RATIFICATIONS §13) and no program value of that type has a poison lane.
/// An opaque/fresh summary binding never establishes any of these flags.
pub(super) fn value_is_defined(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    value: ValueId,
    entry_defined: Option<&[bool]>,
) -> bool {
    let mut work = MAX_DEFINEDNESS_WORK;
    if !std::ptr::eq(analysis.module, module) {
        return false;
    }
    defined_at(
        analysis,
        module,
        function,
        value,
        &[],
        entry_defined,
        MAX_DEFINEDNESS_DEPTH,
        &mut work,
    )
}

/// Canonical call/return transport rejects TOP-LEVEL poison, while a legitimate
/// partial aggregate may travel without claiming its lanes are initialized.
/// `entry_defined` is separate from `entry_transport`: only a checked actual
/// supplies recursive initialization inside a summary.
pub(super) fn value_is_transportable(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    value: ValueId,
    entry_defined: Option<&[bool]>,
    entry_transport: Option<&[bool]>,
) -> bool {
    let mut work = MAX_DEFINEDNESS_WORK;
    if !std::ptr::eq(analysis.module, module) {
        return false;
    }
    transport_at(
        analysis,
        module,
        function,
        value,
        entry_defined,
        entry_transport,
        MAX_DEFINEDNESS_DEPTH,
        &mut work,
    )
}

fn transport_at(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    value: ValueId,
    entry_defined: Option<&[bool]>,
    entry_transport: Option<&[bool]>,
    depth: usize,
    work: &mut usize,
) -> bool {
    let assumptions = analysis.initialized_cells.borrow().iter().copied().collect();
    let transport_assumptions = analysis.transported_cells.borrow().iter().copied().collect();
    analysis.prove(
        Query {
            kind: QueryKind::Transport,
            function: function.id,
            value,
            path: Vec::new(),
            defined: entry_defined.map(<[bool]>::to_vec),
            transport: entry_transport.map(<[bool]>::to_vec),
            assumptions,
            transport_assumptions,
            reference_assumptions: analysis.reference_assumptions(),
        },
        || {
            if depth == 0 || *work == 0 {
                return false;
            }
            *work -= 1;
            let depth = depth - 1;
            macro_rules! transport {
                ($value:expr) => {
                    transport_at(
                        analysis,
                        module,
                        function,
                        $value,
                        entry_defined,
                        entry_transport,
                        depth,
                        work,
                    )
                };
            }
            let Some(index) = analysis.index(function.id) else { return false };
            if !index.valid {
                return false;
            }
            if let Some((block, position, _)) = index.parameters.get(&value) {
                let mut found = *block == function.entry;
                let mut seed = found;
                let mut recurrent = false;
                if found
                    && entry_transport
                        .is_some_and(|flags| !flags.get(*position).copied().unwrap_or(false))
                {
                    return false;
                }
                for args in index.incoming.get(block).into_iter().flatten() {
                    found = true;
                    let Some(arg) = args.get(*position) else { return false };
                    let Some((recurs, leaves)) =
                        recurrence_inputs(module, &index, *arg, value, depth)
                    else {
                        return false;
                    };
                    if recurs {
                        recurrent = true;
                        if !analysis.recurrence_source_is_ordered(function, *block)
                            || !leaves.iter().all(|leaf| transport!(*leaf))
                        {
                            return false;
                        }
                    } else {
                        if !transport!(*arg) {
                            return false;
                        }
                        seed = true;
                    }
                }
                return found && (!recurrent || seed);
            }
            let Some(node) = index.definitions.get(&value) else { return false };
            match &node.inst {
                Inst::Const { ty: ty @ Ty::Enum(_), value } => {
                    dataless_enum::constant_tag(module, ty, value).is_some()
                }
                Inst::Const {
                    ty: Ty::Struct(_) | Ty::Tuple(_),
                    value: Constant::Aggregate(fields),
                } => fields.iter().all(|field| {
                    matches!(field, Constant::Uninit) || constant_at(field, &[], depth)
                }),
                Inst::Const { value, .. } => constant_at(value, &[], depth),
                // A certified initialized fresh value is transportable at every
                // type the record admits (never `Ptr`: the constructor refuses it).
                Inst::Undef { .. } if analysis.source_initialized_value(function.id, value) => true,
                Inst::Undef { ty: Ty::Ptr } => {
                    analysis.source_reference_value_initialized(function.id, value)
                }
                Inst::Copy { operand, .. } => transport!(*operand),
                Inst::InsertField { aggregate, value, .. } => {
                    transport!(*aggregate) && transport!(*value)
                }
                Inst::MakeAggregate { ty: ty @ Ty::Enum(_), variant, fields } => {
                    dataless_enum::variant_tag(module, ty, *variant, fields).is_some()
                }
                Inst::MakeAggregate { fields, .. } => fields.iter().all(|field| transport!(*field)),
                Inst::ArraySplat { value, .. } => transport!(*value),
                Inst::InsertElement { array, index, value, .. } => {
                    transport!(*array) && transport!(*index) && transport!(*value)
                }
                Inst::BinOp { lhs, rhs, .. }
                | Inst::ICmp { lhs, rhs, .. }
                | Inst::FCmp { lhs, rhs, .. }
                | Inst::Overflow { lhs, rhs, .. } => transport!(*lhs) && transport!(*rhs),
                Inst::UnOp { operand, .. } => transport!(*operand),
                Inst::Cast { src_ty, dst_ty, operand, .. } => {
                    initialized_cast_shape(module, src_ty, dst_ty)
                        && if is_scalar_field_ty(src_ty) {
                            transport!(*operand)
                        } else {
                            defined_at(
                                analysis,
                                module,
                                function,
                                *operand,
                                &[],
                                entry_defined,
                                depth,
                                work,
                            )
                        }
                }
                Inst::Select { cond, then_val, else_val, .. } => {
                    transport!(*cond) && transport!(*then_val) && transport!(*else_val)
                }
                Inst::NullPtr | Inst::GlobalAddr { .. } => true,
                Inst::DialectOp(op) if is_thread_local_addr(op) => true,
                Inst::Alloca { count, .. } => count.is_none_or(|count| transport!(count)),
                Inst::GEP { base, indices, .. } => {
                    transport!(*base) && indices.iter().all(|index| transport!(*index))
                }
                Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => transport!(*ptr),
                // This establishes only that a produced pointer can be transported;
                // existing borrow-permission/access/escape checks still govern its use.
                Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => transport!(*ptr),
                Inst::PtrFromParts { data, metadata, .. } => {
                    transport!(*data) && transport!(*metadata)
                }
                Inst::ExtractElement { array, index, .. } => array_lane_is_initialized(
                    analysis,
                    module,
                    function,
                    *array,
                    *index,
                    &[],
                    false,
                    entry_defined,
                    entry_transport,
                    depth,
                    work,
                ),
                Inst::Load { ptr, volatile: false, .. } => {
                    (transport!(*ptr)
                        && analysis.source_load_initialized(
                            function,
                            value,
                            &[],
                            entry_defined,
                            depth,
                            work,
                        ))
                        || cell_is_transportable(
                            analysis,
                            module,
                            function,
                            *ptr,
                            entry_defined,
                            depth,
                            work,
                        )
                }
                Inst::Call { callee, args } => {
                    if !args.iter().all(|arg| transport!(*arg)) {
                        return false;
                    }
                    let Some(callee) = module.function_by_id(*callee) else { return false };
                    // CONDITIONAL value property: a successfully returning canonical
                    // Call checks its return signature, including top-level poison.
                    // This proves no safety/termination or recursive initialization.
                    // The common guard below checks each Return before lowering it,
                    // so callee errors cannot disappear into this transport fact.
                    module.func_types.get(callee.ty.as_usize()).is_some_and(|ty| {
                        node.results.len() == ty.returns.len() && node.results.contains(&value)
                    })
                }
                // Arithmetic/projections need actual initialization, not merely an
                // aggregate carrier. Unknown memory, effects and recursive cycles refuse.
                _ => defined_at(analysis, module, function, value, &[], entry_defined, depth, work),
            }
        },
    )
}

/// Supported content-inspecting operations, matching canonical interpretation.
/// Copy/phi/nonvolatile Store transport values; they do not inspect their bits.
/// This SAME guard runs before ordinary and summary dispatch, including dead
/// results. Existing unsupported instruction-family refusals are unchanged.
pub(super) fn consumption_is_valid(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    node: &InstrNode,
    entry_defined: Option<&[bool]>,
    entry_transport: Option<&[bool]>,
) -> bool {
    if dataless_enum::refused_operation(&node.inst) {
        return false;
    }
    let valid = |value| {
        value_is_transportable(analysis, module, function, value, entry_defined, entry_transport)
    };
    let zero_count = |value| {
        analysis.index(function.id).is_some_and(|index| {
            matches!(index.definitions.get(&value).map(|node| &node.inst),
            Some(Inst::Const { ty, value: Constant::Int(0) }) if ty.is_integer())
        })
    };
    match &node.inst {
        Inst::Alloca { ty, count, align } => {
            if align.is_some_and(|align| align == 0 || !align.is_power_of_two()) {
                return false;
            }
            let Some(count) = count else { return true };
            if !valid(*count) {
                return false;
            }
            let Some(index) = analysis.index(function.id) else { return false };
            let Some(InstrNode {
                inst: Inst::Const { ty: count_ty, value: Constant::Int(raw) },
                ..
            }) = index.definitions.get(count).copied()
            else {
                return false;
            };
            if !count_ty.is_integer() {
                return false;
            }
            let Some(bits) = count_ty.bit_width_with(HOST_POINTER_BITS) else { return false };
            let mask = if bits == 128 { u128::MAX } else { (1u128 << bits) - 1 };
            let count = (*raw as u128) & mask;
            if count == 0 || (count_ty.is_signed() && count & (1u128 << (bits - 1)) != 0) {
                return false;
            }
            let Ok(count) = u64::try_from(count) else { return false };
            let Ok(layout) = module.ty_layout_shape(ty) else { return false };
            layout
                .size_bits
                .checked_add(7)
                .map(|bits| bits / 8)
                .is_some_and(|size| size.checked_mul(count).is_some())
        }
        // Canonical aggregate Undef faults at definition, even when discarded.
        // The one exception is a site the live source seam certified as an
        // initialized fresh value: it stands for a defined value, not poison.
        Inst::Undef { ty } => {
            scalar_poison_type(ty)
                || matches!(node.results.as_slice(), [result]
                    if analysis.source_initialized_value(function.id, *result))
        }
        Inst::BinOp { lhs, rhs, .. }
        | Inst::ICmp { lhs, rhs, .. }
        | Inst::FCmp { lhs, rhs, .. }
        | Inst::Overflow { lhs, rhs, .. } => valid(*lhs) && valid(*rhs),
        Inst::UnOp { operand, .. } | Inst::Cast { operand, .. } => valid(*operand),
        Inst::Assert { cond, .. }
        | Inst::Assume { cond }
        | Inst::CondBr { cond, .. }
        | Inst::Select { cond, .. } => valid(*cond),
        Inst::Switch { value, .. } => valid(*value),
        Inst::ExtractField { .. } => node.results.first().is_some_and(|result| valid(*result)),
        Inst::InsertField { aggregate, value, .. } => valid(*aggregate) && valid(*value),
        Inst::ExtractElement { array, index, .. } => valid(*array) && valid(*index),
        Inst::InsertElement { array, index, value, .. } => {
            valid(*array) && valid(*index) && valid(*value)
        }
        Inst::MakeAggregate { ty: ty @ Ty::Enum(_), variant, fields } => {
            dataless_enum::variant_tag(module, ty, *variant, fields).is_some()
        }
        Inst::MakeAggregate { fields, .. } => fields.iter().all(|field| valid(*field)),
        Inst::ArraySplat { value, .. } => valid(*value),
        Inst::Call { callee, args } => {
            args.iter().all(|arg| valid(*arg))
                && analysis.reference_call_is_valid(function, *callee, args, entry_defined)
        }
        Inst::Return { values } => values.iter().all(|value| valid(*value)),
        Inst::Load { ty, ptr, volatile, .. } => {
            valid(*ptr)
                && ((!*volatile && scalar_poison_type(ty))
                    || (!*volatile
                        && node.results.as_slice().first().is_some_and(|result| {
                            let mut work = MAX_DEFINEDNESS_WORK;
                            node.results.len() == 1
                                && analysis.source_load_initialized(
                                    function,
                                    *result,
                                    &[],
                                    entry_defined,
                                    MAX_DEFINEDNESS_DEPTH,
                                    &mut work,
                                )
                        }))
                    || {
                        let mut work = MAX_DEFINEDNESS_WORK;
                        cell_is_transportable(
                            analysis,
                            module,
                            function,
                            *ptr,
                            entry_defined,
                            MAX_DEFINEDNESS_DEPTH,
                            &mut work,
                        )
                    })
        }
        Inst::Store { ty, ptr, value, volatile, .. } => {
            valid(*ptr)
                && if *volatile {
                    value_is_defined(analysis, module, function, *value, entry_defined)
                } else {
                    value_is_storable(
                        analysis,
                        module,
                        function,
                        *value,
                        ty,
                        entry_defined,
                        entry_transport,
                        MAX_DEFINEDNESS_DEPTH,
                    )
                }
        }
        Inst::MemSet { dst, byte, bytes } => {
            // Canonical interpretation inspects count AND fill before the
            // zero-byte shortcut, but does not inspect the pointer on it.
            valid(*bytes) && valid(*byte) && (zero_count(*bytes) || valid(*dst))
        }
        Inst::MemCopy { dst, src, bytes, .. } => {
            valid(*bytes) && (zero_count(*bytes) || (valid(*dst) && valid(*src)))
        }
        Inst::GEP { base, indices, .. } => {
            valid(*base) && indices.iter().all(|index| valid(*index))
        }
        Inst::Borrow { ptr } | Inst::BorrowMut { ptr } => valid(*ptr),
        Inst::PtrData { ptr, .. } | Inst::PtrMetadata { ptr, .. } => valid(*ptr),
        Inst::PtrFromParts { data, metadata, .. } => valid(*data) && valid(*metadata),
        _ => true,
    }
}

/// Unknown partial records can be encoded only through canonical Struct/Tuple
/// unwritten-lane handling. An Array/Closure around an unwritten value does not
/// inherit that record mechanism and needs actual recursive initialization.
fn partial_record_type(module: &Module, ty: &Ty, depth: usize) -> bool {
    if depth == 0 {
        return false;
    }
    if scalar_poison_type(ty) || matches!(ty, Ty::FatPtr(_) | Ty::Unit) {
        return true;
    }
    if !matches!(ty, Ty::Struct(_) | Ty::Tuple(_)) {
        return false;
    }
    aggregate_field_tys_of(module, ty).is_some_and(|fields| {
        fields.iter().all(|field| partial_record_type(module, field, depth - 1))
    })
}

fn value_is_storable(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    value: ValueId,
    ty: &Ty,
    entry_defined: Option<&[bool]>,
    entry_transport: Option<&[bool]>,
    depth: usize,
) -> bool {
    if depth == 0 {
        return false;
    }
    if scalar_poison_type(ty) {
        return true;
    } // Non-strict scalar poison transport.
    if value_is_defined(analysis, module, function, value, entry_defined) {
        return true;
    }
    if partial_record_type(module, ty, depth)
        && value_is_transportable(analysis, module, function, value, entry_defined, entry_transport)
    {
        return true;
    }
    let Some(index) = analysis.index(function.id) else { return false };
    let Some(node) = index.definitions.get(&value) else { return false };
    match &node.inst {
        Inst::Const {
            ty: declared @ (Ty::Struct(_) | Ty::Tuple(_)),
            value: Constant::Aggregate(fields),
        } if declared == ty => fields
            .iter()
            .all(|field| matches!(field, Constant::Uninit) || constant_at(field, &[], depth - 1)),
        Inst::Copy { operand, .. } => value_is_storable(
            analysis,
            module,
            function,
            *operand,
            ty,
            entry_defined,
            entry_transport,
            depth - 1,
        ),
        Inst::InsertField { ty: declared, aggregate, field, value: inserted } if declared == ty => {
            let Some(fields) = aggregate_field_tys_of(module, ty) else { return false };
            fields.get(*field as usize).is_some_and(|field_ty| {
                value_is_storable(
                    analysis,
                    module,
                    function,
                    *aggregate,
                    ty,
                    entry_defined,
                    entry_transport,
                    depth - 1,
                ) && value_is_storable(
                    analysis,
                    module,
                    function,
                    *inserted,
                    field_ty,
                    entry_defined,
                    entry_transport,
                    depth - 1,
                )
            })
        }
        _ => false,
    }
}

/// Exact canonical nonstrict scalar-poison carrier roster. Every other Load
/// faults on uninitialized covered bytes at definition, even if discarded.
fn scalar_poison_type(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::I8
            | Ty::I16
            | Ty::I32
            | Ty::I64
            | Ty::I128
            | Ty::U8
            | Ty::U16
            | Ty::U32
            | Ty::U64
            | Ty::U128
            | Ty::Isize
            | Ty::Usize
            | Ty::Char
            | Ty::F16
            | Ty::F32
            | Ty::F64
            | Ty::Bool
            | Ty::Ptr
            | Ty::PtrConst(_)
            | Ty::PtrMut(_)
            | Ty::Ref(_)
            | Ty::RefMut(_)
            | Ty::Rc(_)
    )
}

/// A root translation's entry parameter is a verification input, universally
/// quantified over its type's VALUE DOMAIN (trust-ir SPEC_RATIFICATIONS §13). A
/// value of `[e; n]` holds a value of `e` in every lane, so such a parameter is
/// initialized exactly as a scalar root parameter is. The rule is deliberately
/// narrow: `n >= 1`, the parameter is the function's own declared parameter at
/// `position`, and `e` is (recursively) an element whose every bit pattern is a
/// value of the SMT sort that carries it: an integer, `Bool` (SMT Bool) or a float.
/// `Char` (a 32-bit carrier wider than its domain), pointer-likes (provenance the
/// carrier does not hold), fat pointers and every struct, tuple, enum, closure or
/// record element keep the old refusal. A callee's parameter is NOT a root input
/// (its definedness comes only from its caller's actual arguments), and an
/// embedder-built argument with poison lanes lies outside the domain this models.
fn root_parameter_is_a_value_domain_array(
    module: &Module,
    function: &Function,
    position: usize,
    param_ty: &Ty,
) -> bool {
    fn value_domain_array(module: &Module, ty: &Ty, depth: usize) -> bool {
        let Ty::Array(elem, len) = ty else { return false };
        if depth == 0 || *len == 0 {
            return false;
        }
        let Some(elem) = module.types.get(elem.as_usize()) else { return false };
        matches!(
            elem,
            Ty::I8
                | Ty::I16
                | Ty::I32
                | Ty::I64
                | Ty::I128
                | Ty::U8
                | Ty::U16
                | Ty::U32
                | Ty::U64
                | Ty::U128
                | Ty::Isize
                | Ty::Usize
                | Ty::Bool
                | Ty::F16
                | Ty::F32
                | Ty::F64
        ) || value_domain_array(module, elem, depth - 1)
    }
    module
        .func_types
        .get(function.ty.as_usize())
        .and_then(|signature| signature.params.get(position))
        .is_some_and(|declared| declared == param_ty)
        && value_domain_array(module, param_ty, MAX_DEFINEDNESS_DEPTH)
}

/// A write of the exact same immutable SSA index establishes that selected
/// lane even when unrelated lanes are unknown. Bounds/type obligations remain
/// in the existing element model; no SMT index equality or entry-array
/// initializedness is assumed here.
fn array_lane_is_initialized(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    array: ValueId,
    subscript: ValueId,
    path: &[u32],
    recursive: bool,
    entry_defined: Option<&[bool]>,
    entry_transport: Option<&[bool]>,
    depth: usize,
    work: &mut usize,
) -> bool {
    if depth == 0 || *work == 0 {
        return false;
    }
    *work -= 1;
    let Some(index) = analysis.index(function.id) else { return false };
    if let Some(node) = index.definitions.get(&array) {
        match &node.inst {
            Inst::Copy { operand, .. } => {
                return array_lane_is_initialized(
                    analysis,
                    module,
                    function,
                    *operand,
                    subscript,
                    path,
                    recursive,
                    entry_defined,
                    entry_transport,
                    depth - 1,
                    work,
                );
            }
            Inst::InsertElement { array: prior, index: written, value, .. }
                if *written == subscript =>
            {
                return transport_at(
                    analysis,
                    module,
                    function,
                    *prior,
                    entry_defined,
                    entry_transport,
                    depth - 1,
                    work,
                ) && transport_at(
                    analysis,
                    module,
                    function,
                    subscript,
                    entry_defined,
                    entry_transport,
                    depth - 1,
                    work,
                ) && if recursive {
                    defined_at(
                        analysis,
                        module,
                        function,
                        *value,
                        path,
                        entry_defined,
                        depth - 1,
                        work,
                    )
                } else {
                    transport_at(
                        analysis,
                        module,
                        function,
                        *value,
                        entry_defined,
                        entry_transport,
                        depth - 1,
                        work,
                    )
                };
            }
            _ => {}
        }
    }
    defined_at(analysis, module, function, array, &[], entry_defined, depth - 1, work)
        && transport_at(
            analysis,
            module,
            function,
            subscript,
            entry_defined,
            entry_transport,
            depth - 1,
            work,
        )
}

/// Prove full initialization from the actual finite write chain without
/// enumerating an array's declared length. Only the latest write to each
/// exact constant index counts; all writes must transport valid operands.
fn array_fully_written(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    mut value: ValueId,
    entry_defined: Option<&[bool]>,
    depth: usize,
    work: &mut usize,
) -> bool {
    let Some(index) = analysis.index(function.id) else { return false };
    let Some(Ty::Array(_, len)) = index.types.get(&value) else { return false };
    let mut covered = BTreeSet::new();
    let mut left = depth;
    while left != 0 && *work != 0 {
        left -= 1;
        *work -= 1;
        let Some(node) = index.definitions.get(&value) else { return false };
        match &node.inst {
            Inst::Copy { operand, .. } => value = *operand,
            Inst::InsertElement { array, index: written, value: inserted, .. } => {
                if !transport_at(
                    analysis,
                    module,
                    function,
                    *array,
                    entry_defined,
                    None,
                    left,
                    work,
                ) || !transport_at(
                    analysis,
                    module,
                    function,
                    *written,
                    entry_defined,
                    None,
                    left,
                    work,
                ) || !transport_at(
                    analysis,
                    module,
                    function,
                    *inserted,
                    entry_defined,
                    None,
                    left,
                    work,
                ) {
                    return false;
                }
                let Some(InstrNode { inst: Inst::Const { ty, value: constant }, .. }) =
                    index.definitions.get(written).copied()
                else {
                    return false;
                };
                if !ty.is_integer() {
                    return false;
                }
                let Some(expression) = const_to_expr(ty, constant) else { return false };
                let Some(raw) = bitvec_const_value(&expression) else { return false };
                let Some(width) = ty.bit_width_with(HOST_POINTER_BITS) else { return false };
                if ty.is_signed() && raw & (1u128 << (width - 1)) != 0 {
                    return false;
                }
                let Ok(lane) = u64::try_from(raw) else { return false };
                if lane >= *len {
                    return false;
                }
                if covered.insert(lane)
                    && !defined_at(
                        analysis,
                        module,
                        function,
                        *inserted,
                        &[],
                        entry_defined,
                        left,
                        work,
                    )
                {
                    return false;
                }
                if u64::try_from(covered.len()).ok() == Some(*len) {
                    return true;
                }
                value = *array;
            }
            _ => {
                return defined_at(
                    analysis,
                    module,
                    function,
                    value,
                    &[],
                    entry_defined,
                    left,
                    work,
                );
            }
        }
    }
    false
}

/// Resolve only source-SSA addresses derived from the same owned allocation.
/// This establishes no range, alignment, value, permission or escape fact.
fn allocation_root(index: &FunctionIndex<'_>, value: ValueId, depth: usize) -> Option<ValueId> {
    if depth == 0 {
        return None;
    }
    let node = index.definitions.get(&value)?;
    match &node.inst {
        Inst::Alloca { count: None, align: None, .. } => Some(value),
        Inst::GEP { base, .. } => allocation_root(index, *base, depth - 1),
        inst => allocation_root(index, transparent_pointer_alias(inst)?, depth - 1),
    }
}

/// A complete typed store initializes its fields, not padding. Reads in this
/// lane must retain exact logical pointee types; byte copies additionally need
/// a dense source image so unwritten padding cannot become a destination value.
fn pointee_type(
    module: &Module,
    index: &FunctionIndex<'_>,
    ptr: ValueId,
    depth: usize,
) -> Option<Ty> {
    if depth == 0 {
        return None;
    }
    match &index.definitions.get(&ptr)?.inst {
        Inst::Alloca { ty, count: None, align: None } => Some(ty.clone()),
        Inst::GEP { base, pointee_ty, indices, .. } if indices.len() == 1 => {
            let base_ty = pointee_type(module, index, *base, depth - 1)?;
            if let Ty::Array(elem, _) = base_ty {
                return (module.types.get(elem.as_usize())? == pointee_ty)
                    .then(|| pointee_ty.clone());
            }
            let Inst::Const { value: Constant::Int(lane), .. } =
                &index.definitions.get(&indices[0])?.inst
            else {
                return None;
            };
            let offset = u64::try_from(*lane)
                .ok()?
                .checked_mul(module.ty_layout_shape(pointee_ty).ok()?.size_bits)?;
            let layout = module.ty_layout_shape(&base_ty).ok()?;
            let fields = match layout.kind {
                trust_ir::TyLayoutKind::Struct { fields, .. }
                | trust_ir::TyLayoutKind::Tuple { fields }
                | trust_ir::TyLayoutKind::Closure { captures: fields, .. } => fields,
                _ => return None,
            };
            let types = aggregate_field_tys_of(module, &base_ty)?;
            if types.len() != fields.len() {
                return None;
            }
            let mut ranges = Vec::new();
            let mut found = false;
            for (field, ty) in fields.iter().zip(types) {
                let start = field.offset_bits?;
                let size = module.ty_layout_shape(&ty).ok()?.size_bits;
                let end = start.checked_add(size)?;
                if end > layout.size_bits {
                    return None;
                }
                found |= start == offset && ty == *pointee_ty;
                if size != 0 {
                    ranges.push((start, end));
                }
            }
            ranges.sort_unstable();
            if ranges.windows(2).any(|pair| pair[0].1 > pair[1].0) {
                return None;
            }
            found.then(|| pointee_ty.clone())
        }
        inst => pointee_type(module, index, transparent_pointer_alias(inst)?, depth - 1),
    }
}

/// An already initialized integer-only image has no invalid bit patterns.
/// Writing a defined integer wholly within that allocation preserves typed
/// initializedness even when the value model cannot identify a field lane.
/// This never initializes a cell, maps a value to a field, or admits Bool,
/// Char, enum, pointer, array, or opaque representations.
fn integer_image(module: &Module, ty: &Ty, depth: usize) -> bool {
    if depth == 0 {
        return false;
    }
    if ty.is_integer() {
        return true;
    }
    if !matches!(ty, Ty::Struct(_) | Ty::Tuple(_)) {
        return false;
    }
    aggregate_field_tys_of(module, ty)
        .is_some_and(|fields| fields.iter().all(|field| integer_image(module, field, depth - 1)))
}

/// Extent and alignment, not field identity: the interpreter synthesizes a
/// declaration-order aggregate layout when ALL struct metadata is absent.
/// Match that documented integer-only case; partial/contradictory descriptors
/// never fall back. No Rust ABI/layout claim follows from this calculation.
fn integer_image_extent(module: &Module, ty: &Ty, depth: usize) -> Option<(u64, u64)> {
    if depth == 0 || !integer_image(module, ty, depth) {
        return None;
    }
    if let Ok(layout) = module.ty_layout_shape(ty)
        && let Some(align) = layout.align_bits
        && layout.size_bits % 8 == 0
        && align != 0
        && align % 8 == 0
        && (align / 8).is_power_of_two()
    {
        return Some((layout.size_bits / 8, align / 8));
    }
    let Ty::Struct(id) = ty else { return None };
    let definition = module.struct_def(*id)?;
    if definition.size.is_some()
        || definition.align.is_some()
        || definition.fields.iter().any(|field| field.offset.is_some())
    {
        return None;
    }
    let mut size = 0u64;
    let mut align = 1u64;
    for field in &definition.fields {
        let (field_size, field_align) = integer_image_extent(module, &field.ty, depth - 1)?;
        size = size.checked_add(field_align - 1)? & !(field_align - 1);
        size = size.checked_add(field_size)?;
        align = align.max(field_align);
    }
    Some((size.checked_add(align - 1)? & !(align - 1), align))
}

fn constant_byte_offset(
    module: &Module,
    index: &FunctionIndex<'_>,
    root: ValueId,
    ptr: ValueId,
    depth: usize,
) -> Option<u64> {
    if depth == 0 {
        return None;
    }
    if ptr == root {
        return Some(0);
    }
    let inst = &index.definitions.get(&ptr)?.inst;
    if let Some(parent) = transparent_pointer_alias(inst) {
        return constant_byte_offset(module, index, root, parent, depth - 1);
    }
    let Inst::GEP { base, pointee_ty, indices, .. } = inst else { return None };
    let size = module.ty_layout_shape(pointee_ty).ok()?.size_bits;
    if size % 8 != 0 {
        return None;
    }
    let mut offset = constant_byte_offset(module, index, root, *base, depth - 1)?;
    for value in indices {
        let Inst::Const { ty, value: Constant::Int(lane) } = &index.definitions.get(value)?.inst
        else {
            return None;
        };
        if !ty.is_integer() {
            return None;
        }
        let lane = u64::try_from(*lane).ok()?;
        offset = offset.checked_add((size / 8).checked_mul(lane)?)?;
    }
    Some(offset)
}

fn integer_write_preserves_initialized_image(
    module: &Module,
    index: &FunctionIndex<'_>,
    root: ValueId,
    allocated: &Ty,
    store: &Inst,
    depth: usize,
) -> bool {
    let Inst::Store { ty: stored, ptr, volatile: false, align: None, .. } = store else {
        return false;
    };
    if !stored.is_integer()
        || !integer_image(module, allocated, depth)
        || !matches!(
            index.definitions.get(&root).map(|node| &node.inst),
            Some(Inst::Alloca { ty, count: None, align: None }) if ty == allocated
        )
    {
        return false;
    }
    let Some(offset) = constant_byte_offset(module, index, root, *ptr, depth) else {
        return false;
    };
    let (Some((allocated, allocation_alignment)), Ok(stored)) =
        (integer_image_extent(module, allocated, depth), module.ty_layout_shape(stored))
    else {
        return false;
    };
    let Some(alignment_bits) = stored.align_bits else { return false };
    if alignment_bits == 0 || alignment_bits % 8 != 0 {
        return false;
    }
    let natural_alignment = alignment_bits / 8;
    // Bounds and initialized bytes do not establish alignment. Both the
    // original allocation and this exact byte offset must guarantee the
    // canonical Store's natural alignment. Explicit alignment claims retain
    // their separate refusal instead of donating a stronger guarantee here.
    if !natural_alignment.is_power_of_two()
        || allocation_alignment % natural_alignment != 0
        || offset % natural_alignment != 0
    {
        return false;
    }
    stored.size_bits != 0
        && stored.size_bits % 8 == 0
        && offset.checked_add(stored.size_bits / 8).is_some_and(|end| end <= allocated)
}

fn initialized_cast_shape(module: &Module, source: &Ty, destination: &Ty) -> bool {
    let admissible = |ty: &Ty| {
        if pointer_newtype_field_path(ty, module, POINTER_NEWTYPE_FUEL)
            .is_some_and(|path| !path.is_empty())
        {
            // A dense image alone does not prove the bounded pointer carrier's
            // alignment and footprint (for example, repr(packed)).
            default_pointer_carrier(module, ty)
        } else {
            is_scalar_field_ty(ty) || dense_storage(module, ty, MAX_DEFINEDNESS_DEPTH)
        }
    };
    admissible(source) && admissible(destination)
}

/// Preserve the EXISTING logical one-pointer newtype model for canonical
/// all-None synthesized layouts. A structural pointer path alone is NOT a
/// footprint proof: independently derive size/alignment, reject gaps/tail
/// padding, over-aligned ZSTs and partial/invalid declarations. This supplies
/// no Rust-ABI, canonical aggregate-Bitcast execution or byte/refinement claim.
fn default_pointer_carrier(module: &Module, ty: &Ty) -> bool {
    if !pointer_newtype_field_path(ty, module, POINTER_NEWTYPE_FUEL)
        .is_some_and(|path| !path.is_empty())
    {
        return false;
    }
    matches!(pointer_footprint(module, ty, POINTER_NEWTYPE_FUEL),
        Some((size, align, true)) if size == u64::from(HOST_POINTER_BITS / 8) && align == size)
}

fn pointer_footprint(module: &Module, ty: &Ty, fuel: u32) -> Option<(u64, u64, bool)> {
    if fuel == 0 {
        return None;
    }
    let word = u64::from(HOST_POINTER_BITS / 8);
    let layout = module.ty_layout_shape(ty).ok();
    if is_thin_pointer_ty(ty) {
        let layout = layout?;
        return (layout.size_bits == word * 8 && layout.align_bits == Some(word * 8))
            .then_some((word, word, true));
    }
    if let Some(layout) = &layout
        && layout.size_bits == 0
    {
        let align = layout.align_bits?.checked_div(8)?;
        return (align != 0 && align.is_power_of_two() && align <= word)
            .then_some((0, align, false));
    }
    if let Ty::Array(elem, 0) = ty {
        let (_, align, _) =
            pointer_footprint(module, module.types.get(elem.as_usize())?, fuel - 1)?;
        return (align <= word).then_some((0, align, false));
    }
    let (fields, synthesized) = match ty {
        Ty::Struct(id) => {
            let declaration = module.struct_def(*id)?;
            let synthesized = declaration.size.is_none()
                && declaration.align.is_none()
                && declaration.fields.iter().all(|field| field.offset.is_none());
            if !synthesized && layout.is_none() {
                return None;
            }
            (
                declaration.fields.iter().map(|field| field.ty.clone()).collect::<Vec<_>>(),
                synthesized,
            )
        }
        Ty::Tuple(fields) => {
            let synthesized = module.tuple_layout_descriptor(ty).ok()?.is_none();
            if !synthesized && layout.is_none() {
                return None;
            }
            (fields.clone(), synthesized)
        }
        _ => return None,
    };
    let mut size = 0u64;
    let mut align = 1u64;
    let mut has_word = false;
    for field in &fields {
        let (field_size, field_align, field_word) = pointer_footprint(module, field, fuel - 1)?;
        if field_align == 0
            || !field_align.is_power_of_two()
            || field_align > word
            || (has_word && field_word)
        {
            return None;
        }
        has_word |= field_word;
        let aligned = size.checked_add(field_align - 1)? & !(field_align - 1);
        if aligned != size {
            return None;
        }
        size = aligned.checked_add(field_size)?;
        align = align.max(field_align);
    }
    let rounded = size.checked_add(align - 1)? & !(align - 1);
    if rounded != size {
        return None;
    }
    if !synthesized {
        let layout = layout?;
        if layout.size_bits != size.checked_mul(8)?
            || layout.align_bits != Some(align.checked_mul(8)?)
            || !dense_storage(module, ty, MAX_DEFINEDNESS_DEPTH)
        {
            return None;
        }
    }
    Some((size, align, has_word))
}

fn dense_storage(module: &Module, ty: &Ty, depth: usize) -> bool {
    if depth == 0 {
        return false;
    }
    let Ok(layout) = module.ty_layout_shape(ty) else { return false };
    match &layout.kind {
        trust_ir::TyLayoutKind::Scalar(_) | trust_ir::TyLayoutKind::ThinPointer => true,
        trust_ir::TyLayoutKind::Unit => layout.size_bits == 0,
        trust_ir::TyLayoutKind::Array { elem, stride_bits, .. } => {
            module.types.get(elem.as_usize()).is_some_and(|ty| {
                module.ty_layout_shape(ty).is_ok_and(|layout| layout.size_bits == *stride_bits)
                    && dense_storage(module, ty, depth - 1)
            })
        }
        trust_ir::TyLayoutKind::Struct { fields, .. }
        | trust_ir::TyLayoutKind::Tuple { fields }
        | trust_ir::TyLayoutKind::Closure { captures: fields, .. } => {
            let Some(types) = aggregate_field_tys_of(module, ty) else { return false };
            if types.len() != fields.len() {
                return false;
            }
            let mut ranges = Vec::new();
            for (field, ty) in fields.iter().zip(&types) {
                let (Some(start), Ok(layout)) = (field.offset_bits, module.ty_layout_shape(ty))
                else {
                    return false;
                };
                let Some(end) = start.checked_add(layout.size_bits) else { return false };
                if !dense_storage(module, ty, depth - 1) {
                    return false;
                }
                ranges.push((start, end));
            }
            ranges.sort_unstable();
            let mut end = 0;
            for (start, next) in ranges {
                if start != end {
                    return false;
                }
                end = next;
            }
            end == layout.size_bits
        }
        _ => false,
    }
}

/// A call may lose all VALUE precision while preserving initializedness only
/// when its exact original body cannot write memory or retain an address.
/// Keep this deliberately small: no nested calls, stores, opaque operations,
/// returns of an address, or external bodies acquire such a fact.
fn memory_inert_void_callee(module: &Module, id: FuncId) -> bool {
    let Some(function) = module.function_by_id(id) else { return false };
    let Some(signature) = module.func_types.get(function.ty.as_usize()) else { return false };
    !function.blocks.is_empty()
        && signature.returns.is_empty()
        && function.blocks.iter().flat_map(|block| &block.body).all(|node| {
            matches!(node.inst,
            Inst::Return { ref values } if values.is_empty())
        })
}

struct CellAssumption<'a> {
    cells: &'a RefCell<BTreeSet<(FuncId, ValueId)>>,
    key: (FuncId, ValueId),
}

/// One full logical field written through an exact single-step source address.
/// A zero/guessed offset or overlapping declaration cannot seed initialization.
fn direct_stored_field(
    module: &Module,
    index: &FunctionIndex<'_>,
    root: ValueId,
    allocated: &Ty,
    mut ptr: ValueId,
    stored: &Ty,
    depth: usize,
) -> Option<usize> {
    let mut left = depth;
    while left > 0 {
        left -= 1;
        let inst = &index.definitions.get(&ptr)?.inst;
        if let Some(parent) = transparent_pointer_alias(inst) {
            ptr = parent;
            continue;
        }
        let Inst::GEP { base, pointee_ty, indices, .. } = inst else { return None };
        if indices.len() != 1
            || pointee_ty != stored
            || pointee_type(module, index, ptr, depth).as_ref() != Some(stored)
        {
            return None;
        }
        let mut base = *base;
        while base != root && left > 0 {
            left -= 1;
            base = transparent_pointer_alias(&index.definitions.get(&base)?.inst)?;
        }
        if base != root {
            return None;
        }
        let Inst::Const { value: Constant::Int(lane), .. } =
            &index.definitions.get(&indices[0])?.inst
        else {
            return None;
        };
        let offset = u64::try_from(*lane)
            .ok()?
            .checked_mul(module.ty_layout_shape(stored).ok()?.size_bits)?;
        let fields = match module.ty_layout_shape(allocated).ok()?.kind {
            trust_ir::TyLayoutKind::Struct { fields, .. }
            | trust_ir::TyLayoutKind::Tuple { fields }
            | trust_ir::TyLayoutKind::Closure { captures: fields, .. } => fields,
            _ => return None,
        };
        let types = aggregate_field_tys_of(module, allocated)?;
        let mut selected =
            fields.iter().zip(types).enumerate().filter_map(|(position, (field, ty))| {
                (field.offset_bits == Some(offset) && ty == *stored).then_some(position)
            });
        let selected_field = selected.next()?;
        return selected.next().is_none().then_some(selected_field);
    }
    None
}
impl Drop for CellAssumption<'_> {
    fn drop(&mut self) {
        self.cells.borrow_mut().remove(&self.key);
    }
}

/// Canonical E3b whole-cell moves preserve the unwritten-lane record of an
/// exact typed Struct/Tuple Store. This is TRANSPORT, not initialized bytes.
/// No byte/field write, escaped pointer or unmodelled callee may borrow it;
/// MemCopy does not transfer that record. Every actual consuming field still
/// needs independent recursive initializedness from its original source.
fn cell_is_transportable(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    ptr: ValueId,
    entry_defined: Option<&[bool]>,
    depth: usize,
    work: &mut usize,
) -> bool {
    if cell_is_initialized(analysis, module, function, ptr, entry_defined, depth, work) {
        return true;
    }
    if depth == 0 || *work == 0 {
        return false;
    }
    *work -= 1;
    let Some(index) = analysis.index(function.id) else { return false };
    if !index.valid {
        return false;
    }
    let Some(root) = allocation_root(&index, ptr, depth) else { return false };
    let mut whole = ptr;
    let mut left = depth;
    while whole != root && left != 0 {
        left -= 1;
        let Some(node) = index.definitions.get(&whole) else { return false };
        let Some(parent) = transparent_pointer_alias(&node.inst) else { return false };
        whole = parent;
    }
    if whole != root {
        return false;
    }
    let key = (function.id, root);
    if analysis.transported_cells.borrow().contains(&key) {
        return true;
    }
    let Some(InstrNode { inst: Inst::Alloca { ty: allocated, .. }, .. }) =
        index.definitions.get(&root).copied()
    else {
        return false;
    };
    if !matches!(allocated, Ty::Struct(_) | Ty::Tuple(_)) {
        return false;
    }
    let query = Query {
        kind: QueryKind::CellTransport,
        function: function.id,
        value: root,
        path: Vec::new(),
        defined: entry_defined.map(<[bool]>::to_vec),
        transport: None,
        assumptions: analysis.initialized_cells.borrow().iter().copied().collect(),
        transport_assumptions: analysis.transported_cells.borrow().iter().copied().collect(),
        reference_assumptions: analysis.reference_assumptions(),
    };
    analysis.prove(query, || {
        let aliases: BTreeSet<_> = index
            .definitions
            .keys()
            .copied()
            .filter(|value| allocation_root(&index, *value, depth) == Some(root))
            .collect();
        let mut initialization = function.clone();
        for node in initialization.blocks.iter_mut().flat_map(|block| &mut block.body) {
            match &mut node.inst {
                Inst::Load { ty, ptr, .. } if aliases.contains(ptr) && ty == allocated => {
                    *ptr = root
                }
                Inst::Store { ty, ptr, .. } if aliases.contains(ptr) && ty == allocated => {
                    *ptr = root
                }
                _ => {}
            }
        }
        if !promoted_cell_is_definitely_initialized(&initialization, root.index()) {
            return false;
        }
        analysis.transported_cells.borrow_mut().insert(key);
        let _assumption = CellAssumption { cells: &analysis.transported_cells, key };
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            let mut uses = Vec::new();
            if collect_inst_value_uses(&node.inst, &mut uses) {
                return false;
            }
            if !uses.iter().any(|value| aliases.contains(value)) {
                continue;
            }
            match &node.inst {
                Inst::Load { ty, ptr, .. }
                    if aliases.contains(ptr)
                        && ty == allocated
                        && pointee_type(module, &index, *ptr, depth).as_ref() == Some(ty) => {}
                Inst::Store { ty, ptr, value, volatile: false, .. }
                    if aliases.contains(ptr)
                        && ty == allocated
                        && !aliases.contains(value)
                        && pointee_type(module, &index, *ptr, depth).as_ref() == Some(ty)
                        && transport_at(
                            analysis,
                            module,
                            function,
                            *value,
                            entry_defined,
                            None,
                            depth - 1,
                            work,
                        ) => {}
                inst if transparent_pointer_alias(inst)
                    .is_some_and(|value| aliases.contains(&value)) => {}
                Inst::Call { callee, args }
                    if args.iter().any(|value| aliases.contains(value))
                        && memory_inert_void_callee(module, *callee) => {}
                _ => return false,
            }
        }
        true
    })
}

/// Initialization is an inductive SOURCE-memory fact, separate from the SMT
/// value carried by the existing memory model. A full original-type Store
/// seeds every load on every live incoming path; all subsequent writes must
/// preserve initialized bytes. The scoped hypothesis is introduced only after
/// that CFG check, and is part of every memo key. It supplies no value facts.
fn cell_is_initialized(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    ptr: ValueId,
    entry_defined: Option<&[bool]>,
    depth: usize,
    work: &mut usize,
) -> bool {
    if depth == 0 || *work == 0 {
        return false;
    }
    *work -= 1;
    let Some(index) = analysis.index(function.id) else { return false };
    if !index.valid {
        return false;
    }
    let Some(root) = allocation_root(&index, ptr, depth) else { return false };
    let key = (function.id, root);
    if analysis.initialized_cells.borrow().contains(&key) {
        return true;
    }
    let query = Query {
        kind: QueryKind::Cell,
        function: function.id,
        value: root,
        path: Vec::new(),
        defined: entry_defined.map(<[bool]>::to_vec),
        transport: None,
        assumptions: analysis.initialized_cells.borrow().iter().copied().collect(),
        transport_assumptions: analysis.transported_cells.borrow().iter().copied().collect(),
        reference_assumptions: analysis.reference_assumptions(),
    };
    analysis.prove(query, || {
        let Some(InstrNode { inst: Inst::Alloca { ty: allocated, .. }, .. }) =
            index.definitions.get(&root).copied()
        else {
            return false;
        };
        let aliases: BTreeSet<_> = index
            .definitions
            .keys()
            .copied()
            .filter(|value| allocation_root(&index, *value, depth) == Some(root))
            .collect();
        // Normalize only LOAD aliases in a temporary ANALYSIS copy. Only exact
        // whole-object stores seed the existing all-path initialization proof;
        // an interior/partial store cannot initialize the whole allocation.
        let mut initialization = function.clone();
        for block in &mut initialization.blocks {
            let mut local_allocation = false;
            let mut stored_fields = BTreeSet::new();
            let fields = aggregate_field_tys_of(module, allocated).map(|fields| fields.len());
            for node in &mut block.body {
                if node.results.contains(&root) {
                    local_allocation = true;
                    stored_fields.clear();
                }
                if local_allocation
                    && let Inst::Store { ty, ptr, value, .. } = &node.inst
                    && let Some(field) =
                        direct_stored_field(module, &index, root, allocated, *ptr, ty, depth)
                {
                    stored_fields.insert(field);
                    if fields.is_some_and(|count| count != 0 && count == stored_fields.len()) {
                        // Abstract MUST-initialization event only, not executable
                        // source IR: every full original field was written since
                        // this allocation in this block. All stored values are
                        // independently checked below before the fact is retained.
                        node.inst = Inst::Store {
                            ty: allocated.clone(),
                            ptr: root,
                            value: *value,
                            volatile: false,
                            align: None,
                        };
                    }
                }
                match &mut node.inst {
                    Inst::Load { ptr, .. } if aliases.contains(ptr) => *ptr = root,
                    Inst::MemCopy { src, .. } if aliases.contains(src) => {
                        // A byte-source initialization claim is needed at the copy,
                        // not merely at some later typed Load.
                        node.inst = Inst::Load {
                            ty: allocated.clone(),
                            ptr: root,
                            volatile: false,
                            align: None,
                        };
                    }
                    Inst::Store { ty, ptr, .. } if *ptr == root && ty != allocated => return false,
                    _ => {}
                }
            }
        }
        if !promoted_cell_is_definitely_initialized(&initialization, root.index()) {
            return false;
        }
        analysis.initialized_cells.borrow_mut().insert(key);
        let _assumption = CellAssumption { cells: &analysis.initialized_cells, key };
        for node in function.blocks.iter().flat_map(|block| &block.body) {
            let mut uses = Vec::new();
            if collect_inst_value_uses(&node.inst, &mut uses) {
                return false;
            }
            if !uses.iter().any(|value| aliases.contains(value)) {
                continue;
            }
            let initialized = |value, work: &mut usize| {
                defined_at(analysis, module, function, value, &[], entry_defined, depth - 1, work)
            };
            match &node.inst {
                // A strict read does not modify initializedness. This says
                // nothing about its value/effect/admission, which retain the
                // existing separate volatile/alignment refusals.
                Inst::Load { ty, ptr, .. }
                    if aliases.contains(ptr)
                        && pointee_type(module, &index, *ptr, depth).as_ref() == Some(ty) => {}
                Inst::Store { ty, ptr, value, volatile: false, .. }
                    if aliases.contains(ptr)
                        && !aliases.contains(value)
                        && (pointee_type(module, &index, *ptr, depth).as_ref() == Some(ty)
                            || integer_write_preserves_initialized_image(
                                module, &index, root, allocated, &node.inst, depth,
                            ))
                        && initialized(*value, work) => {}
                Inst::GEP { base, indices, .. }
                    if aliases.contains(base)
                        && indices.iter().all(|value| initialized(*value, work)) => {}
                inst if transparent_pointer_alias(inst)
                    .is_some_and(|value| aliases.contains(&value)) => {}
                Inst::MemSet { dst, byte, bytes }
                    if aliases.contains(dst)
                        && initialized(*byte, work)
                        && initialized(*bytes, work) => {}
                Inst::MemCopy { dst, src, bytes, .. }
                    if (aliases.contains(dst) || aliases.contains(src))
                        && initialized(*bytes, work)
                        && pointee_type(module, &index, *src, depth)
                            .is_some_and(|ty| dense_storage(module, &ty, depth))
                        && cell_is_initialized(
                            analysis,
                            module,
                            function,
                            *src,
                            entry_defined,
                            depth - 1,
                            work,
                        ) => {}
                Inst::Call { callee, args }
                    if args.iter().any(|value| aliases.contains(value))
                        && memory_inert_void_callee(module, *callee) => {}
                _ => return false,
            }
        }
        true
    })
}

fn constant_at(value: &Constant, path: &[u32], depth: usize) -> bool {
    if depth == 0 || matches!(value, Constant::Uninit) {
        return false;
    }
    if let Some((field, rest)) = path.split_first() {
        return match value {
            Constant::Aggregate(fields) | Constant::Array(fields) => {
                fields.get(*field as usize).is_some_and(|field| constant_at(field, rest, depth - 1))
            }
            _ => false,
        };
    }
    value.children().all(|child| constant_at(child, &[], depth - 1))
}

fn defined_at(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    value: ValueId,
    path: &[u32],
    entry_defined: Option<&[bool]>,
    depth: usize,
    work: &mut usize,
) -> bool {
    let assumptions = analysis.initialized_cells.borrow().iter().copied().collect();
    let transport_assumptions = analysis.transported_cells.borrow().iter().copied().collect();
    analysis.prove(
        Query {
            kind: QueryKind::Initialized,
            function: function.id,
            value,
            path: path.to_vec(),
            defined: entry_defined.map(<[bool]>::to_vec),
            transport: None,
            assumptions,
            transport_assumptions,
            reference_assumptions: analysis.reference_assumptions(),
        },
        || {
            if depth == 0 || *work == 0 {
                return false;
            }
            *work -= 1;
            let depth = depth - 1;
            macro_rules! check {
                ($value:expr, $path:expr) => {
                    defined_at(
                        analysis,
                        module,
                        function,
                        $value,
                        $path,
                        entry_defined,
                        depth,
                        work,
                    )
                };
            }

            let Some(index) = analysis.index(function.id) else { return false };
            if !index.valid {
                return false;
            }
            if let Some((block, position, param_ty)) = index.parameters.get(&value) {
                // Every predecessor edge is checked, including loop/back edges. An
                // entry parameter's initialized input does not justify a cyclic phi.
                let mut found = *block == function.entry;
                let mut seed = found;
                let mut recurrent = false;
                if found {
                    let initialized = match entry_defined {
                        Some(flags) => flags.get(*position).copied().unwrap_or(false),
                        None => {
                            (is_scalar_field_ty(param_ty) && path.is_empty())
                                || aggregate_field_tys_of(module, param_ty)
                                    .is_some_and(|fields| fields.is_empty())
                                || (path.is_empty()
                                    && root_parameter_is_a_value_domain_array(
                                        module, function, *position, param_ty,
                                    ))
                                // A ROOT parameter the live source seam certified
                                // initialized in every lane (a fieldless enum's
                                // discriminant): any lane path of its type.
                                || (analysis.source_initialized_parameter(function.id, value)
                                    && initialized_value_path(module, param_ty, path))
                        }
                    };
                    if !initialized {
                        return false;
                    }
                }
                // Index retains every canonical incoming edge, including unwind.
                for args in index.incoming.get(block).into_iter().flatten() {
                    found = true;
                    let Some(arg) = args.get(*position) else { return false };
                    let Some((recurs, leaves)) =
                        recurrence_inputs(module, &index, *arg, value, depth)
                    else {
                        return false;
                    };
                    if recurs {
                        recurrent = true;
                        if !path.is_empty()
                            || !analysis.recurrence_source_is_ordered(function, *block)
                            || !leaves.iter().all(|leaf| check!(*leaf, &[]))
                        {
                            return false;
                        }
                    } else {
                        if !check!(*arg, path) {
                            return false;
                        }
                        seed = true;
                    }
                }
                return found && (!recurrent || seed);
            }
            let Some(node) = index.definitions.get(&value) else { return false };
            match &node.inst {
                Inst::Const { ty: ty @ Ty::Enum(_), value } => {
                    (path.is_empty() || path == [0])
                        && dataless_enum::constant_tag(module, ty, value).is_some()
                }
                Inst::MakeAggregate { ty: ty @ Ty::Enum(_), variant, fields } => {
                    (path.is_empty() || path == [0])
                        && dataless_enum::variant_tag(module, ty, *variant, fields).is_some()
                }
                Inst::Const { value, .. } => constant_at(value, path, depth),
                Inst::Copy { operand, .. } => check!(*operand, path),
                Inst::ExtractField { aggregate, field, .. } => {
                    let mut source_path = vec![*field];
                    source_path.extend_from_slice(path);
                    check!(*aggregate, &source_path)
                }
                Inst::InsertField { ty, aggregate, field, value: inserted } => {
                    if !transportable_carrier(
                        analysis,
                        module,
                        function,
                        *aggregate,
                        entry_defined,
                        depth,
                        work,
                    ) || !check!(*inserted, &[])
                    {
                        return false;
                    }
                    if let Some((selected, rest)) = path.split_first() {
                        if selected == field {
                            check!(*inserted, rest)
                        } else {
                            check!(*aggregate, path)
                        }
                    } else {
                        aggregate_field_tys_of(module, ty).is_some_and(|fields| {
                            (0..fields.len()).all(|index| check!(value, &[index as u32]))
                        })
                    }
                }
                Inst::MakeAggregate { variant: None, fields, .. } => {
                    // Even a projection of a good lane cannot bypass consumption of
                    // another poison operand when the constructor itself executes.
                    if !fields.iter().all(|field| check!(*field, &[])) {
                        return false;
                    }
                    if let Some((field, rest)) = path.split_first() {
                        fields.get(*field as usize).is_some_and(|field| check!(*field, rest))
                    } else {
                        true
                    }
                }
                Inst::Select { cond, then_val, else_val, .. } => {
                    check!(*cond, &[]) && check!(*then_val, path) && check!(*else_val, path)
                }
                Inst::BinOp { lhs, rhs, .. }
                | Inst::ICmp { lhs, rhs, .. }
                | Inst::Overflow { lhs, rhs, .. } => {
                    path.is_empty() && check!(*lhs, &[]) && check!(*rhs, &[])
                }
                Inst::UnOp { operand, .. } => path.is_empty() && check!(*operand, &[]),
                Inst::Cast { src_ty, dst_ty, operand, .. } => {
                    path.is_empty()
                        && initialized_cast_shape(module, src_ty, dst_ty)
                        && check!(*operand, &[])
                }
                Inst::ArraySplat { value, .. } => path.is_empty() && check!(*value, &[]),
                Inst::ExtractElement { array, index, .. } => array_lane_is_initialized(
                    analysis,
                    module,
                    function,
                    *array,
                    *index,
                    path,
                    true,
                    entry_defined,
                    None,
                    depth,
                    work,
                ),
                Inst::InsertElement { array, index, value: inserted, .. } => {
                    path.is_empty()
                        && ((check!(*array, &[]) && check!(*index, &[]) && check!(*inserted, &[]))
                            || array_fully_written(
                                analysis,
                                module,
                                function,
                                value,
                                entry_defined,
                                depth,
                                work,
                            ))
                }
                Inst::NullPtr => path.is_empty(),
                // Every logical lane of a certified initialized fresh value is
                // initialized; a path must still select a lane of its type.
                Inst::Undef { ty } if analysis.source_initialized_value(function.id, value) => {
                    initialized_value_path(module, ty, path)
                }
                Inst::Undef { ty: Ty::Ptr } => {
                    path.is_empty()
                        && analysis.source_reference_value_initialized(function.id, value)
                }
                Inst::Load { ptr, volatile: false, .. } => {
                    analysis.source_load_initialized(
                        function,
                        value,
                        path,
                        entry_defined,
                        depth,
                        work,
                    ) || cell_is_initialized(
                        analysis,
                        module,
                        function,
                        *ptr,
                        entry_defined,
                        depth,
                        work,
                    )
                }
                Inst::Call { callee, args } => {
                    // A poison argument faults at the call even when the callee never
                    // uses it. Returning an unrelated constant cannot erase that use.
                    if !args.iter().all(|arg| {
                        transport_at(
                            analysis,
                            module,
                            function,
                            *arg,
                            entry_defined,
                            None,
                            depth,
                            work,
                        )
                    }) {
                        return false;
                    }
                    let argument_defined: Vec<bool> =
                        args.iter().map(|arg| check!(*arg, &[])).collect();
                    let Some(callee) = module.function_by_id(*callee) else { return false };
                    let reference_arguments =
                        analysis.reference_arguments(function, callee, args, entry_defined);
                    let _reference_scope =
                        analysis.enter_reference_arguments(callee.id, reference_arguments);
                    let Some(result_index) =
                        node.results.iter().position(|result| *result == value)
                    else {
                        return false;
                    };
                    let mut found = false;
                    for node in callee.blocks.iter().flat_map(|block| &block.body) {
                        if let Inst::Return { values } = &node.inst {
                            found = true;
                            if !values.get(result_index).is_some_and(|result| {
                                defined_at(
                                    analysis,
                                    module,
                                    callee,
                                    *result,
                                    path,
                                    Some(&argument_defined),
                                    depth,
                                    work,
                                )
                            }) {
                                return false;
                            }
                        }
                    }
                    found
                }
                // This is deliberately narrower than the value model. In particular a
                // Load's fresh result, Undef and a cyclic phi do not prove initialization.
                _ => false,
            }
        },
    )
}

/// Whether `path` selects a lane inside `ty`'s logical field tree (the empty
/// path selects the whole value). A malformed path selects nothing.
fn initialized_value_path(module: &Module, ty: &Ty, path: &[u32]) -> bool {
    if path.len() > MAX_DEFINEDNESS_DEPTH {
        return false;
    }
    let mut selected = ty.clone();
    for field in path {
        let Some(fields) = aggregate_field_tys_of(module, &selected) else { return false };
        let Some(next) = fields.get(*field as usize) else { return false };
        selected = next.clone();
    }
    true
}

/// A direct partial aggregate constant is a legitimate builder carrier;
/// aggregate `Inst::Undef` is not (the interpreter refuses it at definition).
fn transportable_carrier(
    analysis: &Analysis<'_>,
    module: &Module,
    function: &Function,
    value: ValueId,
    entry_defined: Option<&[bool]>,
    depth: usize,
    work: &mut usize,
) -> bool {
    if depth == 0 || *work == 0 {
        return false;
    }
    *work -= 1;
    let Some(index) = analysis.index(function.id) else { return false };
    if !index.valid {
        return false;
    }
    let node = index.definitions.get(&value);
    match node.map(|node| &node.inst) {
        Some(Inst::Const {
            ty: Ty::Struct(_) | Ty::Tuple(_),
            value: Constant::Aggregate(fields),
        }) => fields
            .iter()
            .all(|field| matches!(field, Constant::Uninit) || constant_at(field, &[], depth - 1)),
        Some(Inst::Copy { operand, .. }) => transportable_carrier(
            analysis,
            module,
            function,
            *operand,
            entry_defined,
            depth - 1,
            work,
        ),
        Some(Inst::InsertField { aggregate, value, .. }) => {
            transportable_carrier(
                analysis,
                module,
                function,
                *aggregate,
                entry_defined,
                depth - 1,
                work,
            ) && defined_at(analysis, module, function, *value, &[], entry_defined, depth - 1, work)
        }
        _ => transport_at(analysis, module, function, value, entry_defined, None, depth - 1, work),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::{FieldDef, StructDef, StructId, StructRepr};
    use trust_ir_build::ModuleBuilder;

    fn pointer_carrier_round_trip() -> Module {
        let mut builder = ModuleBuilder::new("pointer_footprint");
        for (id, fields) in [
            (0, vec![]),
            (1, vec![Ty::Struct(StructId::new(0)), Ty::Ptr]),
            (2, vec![Ty::Struct(StructId::new(1)), Ty::Unit]),
        ] {
            builder.add_struct(StructDef {
                id: StructId::new(id),
                name: format!("Carrier{id}"),
                fields: fields
                    .into_iter()
                    .enumerate()
                    .map(|(i, ty)| FieldDef { name: format!("field{i}"), ty, offset: None })
                    .collect(),
                size: None,
                align: None,
                repr: StructRepr::Rust,
                origin: None,
            });
        }
        let signature = builder.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        let mut function = builder.function("round_trip", signature);
        let entry = function.create_block();
        function.set_entry(entry);
        function.switch_to_block(entry);
        let input = function.add_block_param(entry, Ty::U64);
        let carrier = Ty::Struct(StructId::new(2));
        let packed = function.cast(CastOp::Bitcast, Ty::U64, carrier.clone(), input);
        let unpacked = function.cast(CastOp::Bitcast, carrier, Ty::U64, packed);
        function.ret(vec![unpacked]);
        function.build();
        builder.build().expect("canonical logical carrier fixture")
    }

    #[test]
    fn logical_pointer_carriers_require_an_exact_word_footprint() {
        // This is the existing logical bit-carrier model, not an aggregate
        // Bitcast execution or Rust-ABI/byte-refinement claim. The canonical
        // interpreter does not currently execute aggregate Bitcast.
        let synthesized = pointer_carrier_round_trip();
        let mut declared = synthesized.clone();
        declared.structs[0].size = Some(0);
        declared.structs[0].align = Some(1);
        let carrier = &mut declared.structs[1];
        carrier.size = Some(8);
        carrier.align = Some(8);
        for field in &mut carrier.fields {
            field.offset = Some(0);
        }
        for (label, module) in [("synthesized", &synthesized), ("declared", &declared)] {
            assert!(
                default_pointer_carrier(module, &Ty::Struct(StructId::new(2))),
                "{label}: {:?}",
                pointer_footprint(module, &Ty::Struct(StructId::new(2)), POINTER_NEWTYPE_FUEL)
            );
            let out = trust_ir_function_to_chc_translation_output(
                module,
                FuncId::new(0),
                &TranslateOptions::default(),
            )
            .unwrap();
            assert!(out.diagnostics.is_empty(), "{:?}", out.diagnostics);
        }

        let mut tail = declared.clone();
        tail.structs[1].size = Some(16);
        let mut leading = tail.clone();
        leading.structs[1].fields[1].offset = Some(8);
        let mut overaligned = tail.clone();
        overaligned.structs[1].align = Some(16);
        let mut packed = declared.clone();
        packed.structs[1].repr = StructRepr::Packed(1);
        packed.structs[1].align = Some(1);
        let mut partial = declared.clone();
        partial.structs[1].align = None;
        let mut zst = synthesized.clone();
        zst.structs[0].size = Some(0);
        zst.structs[0].align = Some(16);
        let mut reordered = declared.clone();
        reordered.structs[1].size = Some(16);
        reordered.structs[1].fields[0].ty = Ty::U64;
        reordered.structs[1].fields[1].offset = Some(8);
        for (label, module) in [
            ("tail padding", tail),
            ("leading padding", leading),
            ("overaligned", overaligned),
            ("packed", packed),
            ("partial declaration", partial),
            ("overaligned ZST", zst),
            ("reordered non-newtype", reordered),
        ] {
            assert!(!default_pointer_carrier(&module, &Ty::Struct(StructId::new(2))), "{label}");
            let out = trust_ir_function_to_chc_translation_output(
                &module,
                FuncId::new(0),
                &TranslateOptions::default(),
            )
            .unwrap();
            let validation = trust_ir_build::validate_module(&module);
            if !validation.is_empty() {
                for error in validation {
                    assert!(
                        matches!(
                            error,
                            trust_ir_build::ValidationError::CastLayoutUnsupported { .. }
                        ),
                        "{label}: {error:?}"
                    );
                    crate::tests::assert_canonical_refusal(&module, "lacks valid layout evidence");
                }
            } else {
                assert!(
                    !out.diagnostics.is_empty(),
                    "{label} must retain its cast/consumption refusal"
                );
            }
        }
    }

    #[test]
    fn nested_opaque_summary_tokens_are_found_before_materialization() {
        let scalar = CallSummaryBinding::Scalar(Expr::bitvec_const(7u64, 64));
        assert!(!contains_opaque(&CallSummaryBinding::Aggregate(CallSummaryAggregate {
            fields: vec![scalar],
        })));
        let token = CallSummaryBinding::OpaqueFatPtr(FatPtrKind::ContainerVtable);
        let nested = CallSummaryBinding::Aggregate(CallSummaryAggregate {
            fields: vec![CallSummaryBinding::Array(CallSummaryArray {
                len: 2,
                lanes: Some(Box::new(CallSummaryBinding::Aggregate(CallSummaryAggregate {
                    fields: vec![token],
                }))),
            })],
        });
        assert!(contains_opaque(&nested));
    }
}
