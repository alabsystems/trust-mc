// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// StatementCodegen definition and construction (converted from include!() per #2595).

use super::{DiscrScrutinee, Env, IncomingEdge, VariantFact};
use crate::codegen_ay::context::AYCtx;
use crate::codegen_ay::stubs::StubRegistry;
use crate::kani_middle::tuple_usage::TupleUsageAnalysis;
use ay_bindings::Expr;
use rustc_public::mir::Body;
use rustc_public::ty::{RigidTy, Span, TyKind};
use tracing::debug;
use trust_mc_core::SourceLocation;

/// One stage of a recorded `Filter`/`Map` iterator-adapter chain.
///
/// `Iterator::filter` / `Iterator::map` wrap an inner iterator in a single-field
/// (`fld_iter`) datatype value that DROPS the per-element closure. To soundly
/// model a terminal `sum`/`fold`/`try_fold` over such a chain we must recover the
/// closures, so the adapter stubs record them here keyed by the adapter's base
/// SSA name. The terminal stub replays the stages element-wise (mirroring
/// `codegen_iter_all_any`), failing closed whenever the recorded stage count does
/// not match the wrapper depth of the adapter value (an incomplete chain).
#[derive(Clone)]
pub(in crate::codegen_ay) struct AdapterStage {
    pub(in crate::codegen_ay) kind: AdapterStageKind,
    pub(in crate::codegen_ay) closure_ty: rustc_public::ty::Ty,
    pub(in crate::codegen_ay) closure_value: Expr,
    /// SSA base name of the closure operand at the point the stage was recorded,
    /// when it is a `Copy`/`Move` place. Lets the terminal `sum`/`fold` replay
    /// graft the closure's captured-reference pointees (`collect_nested_arg_ref_pointees`)
    /// onto the inlined predicate's receiver base — the same capture-pointee graft
    /// `codegen_iter_all_any` performs — so a closure that captures a `&T` (e.g.
    /// `|term| eval_term(term, assignment)` capturing `assignment: &[bool]`)
    /// derefs the REAL caller data instead of a fresh symbolic. `None` for a
    /// constant closure operand (no captures to graft).
    pub(in crate::codegen_ay) closure_arg_base: Option<std::sync::Arc<str>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(in crate::codegen_ay) enum AdapterStageKind {
    Filter,
    Map,
}

/// Handles translation of MIR statements and terminators to AY constraints.
pub(in crate::codegen_ay) struct StatementCodegen<'a, 'tcx, 't> {
    pub(super) ctx: &'a mut AYCtx<'tcx, 't>,
    pub(super) body: &'a Body,
    pub(super) ssa_version: std::collections::HashMap<std::sync::Arc<str>, u32>,
    pub(super) stub_registry: StubRegistry,
    /// Path conditions for each basic block.
    pub(super) block_path_conditions: std::collections::HashMap<usize, Option<Expr>>,
    /// Current path condition being used for assertions.
    pub(super) current_path_condition: Option<Expr>,
    /// Current environment mapping base SSA names to expressions.
    pub(super) current_env: Env,
    /// Incoming edges for each block (edge predicate + predecessor env).
    pub(super) incoming_edges: std::collections::HashMap<usize, Vec<IncomingEdge>>,
    /// Tracks reference pointees for Deref resolution.
    pub(super) ref_pointees: std::collections::BTreeMap<std::sync::Arc<str>, std::sync::Arc<str>>,
    /// Tracks locals that have gone out of scope (StorageDead).
    pub(super) dead_locals: std::collections::HashSet<usize>,
    /// Counter for generating unique synthetic pointee names (#366).
    pub(super) synthetic_pointee_counter: u32,
    /// Tracks flattened tuples: base_name -> field expressions.
    pub(super) flattened_tuples: std::collections::HashMap<std::sync::Arc<str>, Vec<Expr>>,
    /// Tuple usage analysis for flattening eligibility (#414).
    pub(super) tuple_usage: TupleUsageAnalysis,
    /// Tracks heap-allocated values for Box<T> deref resolution (#1112).
    pub(super) heap_pointees: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    /// Tracks the source root local for raw pointer casts from Box (#1210).
    pub(super) ptr_source_map: std::collections::HashMap<std::sync::Arc<str>, std::sync::Arc<str>>,
    /// Stable address symbols for AddressOf/Ref rvalues (#1124).
    pub(super) addr_symbols: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    /// Stable metadata symbols for AddressOf/Ref rvalues on wide pointers (#1129).
    pub(super) addr_metadata_symbols: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    /// Current source span for property location tracking (#1164).
    pub(super) current_span: Option<Span>,
    /// Tracks HashMap len symbols for len/is_empty invariant (#1315).
    pub(super) hashmap_len_symbols: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    /// Tracks map bases for BTreeMap Entry operations (#1622).
    pub(super) entry_map_bases: std::collections::HashMap<std::sync::Arc<str>, std::sync::Arc<str>>,
    /// Tracks keys for BTreeMap Entry operations (#1622).
    pub(super) entry_keys: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    /// Caches concrete expressions bound to SSA variables (#3107).
    /// When `bind_ssa_result` creates `Var(ssa_name) == concrete_expr`,
    /// this maps `ssa_name → concrete_expr` so downstream consumers
    /// (e.g., `try_extract_layout_fields`) can resolve through Var indirection.
    pub(super) ssa_concrete_values: std::collections::HashMap<String, Expr>,
    /// Stub-created indexed references for write propagation. Part of #3392.
    /// Maps pointee_base → (container_env_key, index_expr) for stub-dispatched
    /// IndexMut paths where the pointee name doesn't use `_idx_by_` convention.
    pub(super) stub_indexed_refs:
        std::collections::HashMap<std::sync::Arc<str>, (std::sync::Arc<str>, Expr)>,
    /// Tracks immutable `[value; N]` arrays whose element is a datatype.
    /// This lets field projections avoid native AY's incomplete datatype-array path.
    pub(super) repeat_array_values: std::collections::HashMap<std::sync::Arc<str>, (Expr, u64)>,
    /// Pre-resolved fn_ptr callees from a parent (caller) scope.
    /// When the BMC mini-inliner inlines a function that receives a fn_ptr as a
    /// parameter, the ClosureFnPointer/ReifyFnPointer cast lives in the caller,
    /// not in the callee. This field carries the resolution from the caller's
    /// body scan so the nested fn_ptr resolver can find the callee.
    pub(super) parent_fn_ptr_callees: Vec<(rustc_public::mir::mono::Instance, bool)>,
    /// Recorded `Filter`/`Map` adapter closure chains keyed by the adapter's base
    /// SSA name, so a terminal `sum`/`fold`/`try_fold` can replay them
    /// element-wise (see `AdapterStage`). Per-body (NOT inherited across inlines):
    /// the filter/map/sum of a single `.iter().filter(..).map(..).sum()` chain all
    /// run in the same body's `StatementCodegen`.
    pub(super) adapter_closures: std::collections::HashMap<std::sync::Arc<str>, Vec<AdapterStage>>,
    /// SwitchInt→variant bridge (Effort 2, #3017): a `Rvalue::Discriminant(P)` assigned
    /// to a bare local, keyed by that local's index, so the following `SwitchInt` on it
    /// can pin the active variant. Reset at each block-0 entry (per function / inline).
    pub(super) discr_of_local: std::collections::HashMap<usize, DiscrScrutinee>,
    /// SwitchInt→variant bridge: variant facts live at the CURRENT program point,
    /// carried on edges and merged by INTERSECTION at block entry.
    pub(super) current_variant_facts: Vec<VariantFact>,
    /// SwitchInt→variant bridge: per-target facts staged by the current `SwitchInt`
    /// terminator, consumed by `record_outgoing_edge`. Cleared at every terminator.
    pub(super) pending_edge_variant_facts: std::collections::HashMap<usize, Vec<VariantFact>>,
    /// SwitchInt→variant bridge: the field-read place + projection offset for the
    /// in-flight `apply_post_deref_projections` call, so its `Field` arm can compute
    /// the parent-enum place key. Set (only when facts are live) immediately before
    /// the call and CONSUMED (taken) at the top of that function — never stale.
    pub(super) bridge_enum_read: Option<(rustc_public::mir::Place, usize)>,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Create a new statement codegen context.
    pub(in crate::codegen_ay) fn new(
        ctx: &'a mut AYCtx<'tcx, 't>,
        body: &'a Body,
        tuple_usage: TupleUsageAnalysis,
    ) -> Self {
        // Initialize memory model for heap operations (#24).
        ctx.init_memory();
        let mut codegen = Self {
            ctx,
            body,
            ssa_version: std::collections::HashMap::new(),
            stub_registry: StubRegistry::new(),
            block_path_conditions: std::collections::HashMap::new(),
            current_path_condition: None,
            current_env: Env::new(),
            incoming_edges: std::collections::HashMap::new(),
            ref_pointees: std::collections::BTreeMap::new(),
            dead_locals: std::collections::HashSet::new(),
            synthetic_pointee_counter: 0,
            flattened_tuples: std::collections::HashMap::new(),
            tuple_usage,
            heap_pointees: std::collections::HashMap::new(),
            ptr_source_map: std::collections::HashMap::new(),
            addr_symbols: std::collections::HashMap::new(),
            addr_metadata_symbols: std::collections::HashMap::new(),
            current_span: None,
            hashmap_len_symbols: std::collections::HashMap::new(),
            entry_map_bases: std::collections::HashMap::new(),
            entry_keys: std::collections::HashMap::new(),
            ssa_concrete_values: std::collections::HashMap::new(),
            stub_indexed_refs: std::collections::HashMap::new(),
            repeat_array_values: std::collections::HashMap::new(),
            parent_fn_ptr_callees: Vec::new(),
            adapter_closures: std::collections::HashMap::new(),
            discr_of_local: std::collections::HashMap::new(),
            current_variant_facts: Vec::new(),
            pending_edge_variant_facts: std::collections::HashMap::new(),
            bridge_enum_read: None,
        };
        // Initialize synthetic pointees for reference-type arguments (#407).
        codegen.init_reference_arguments();
        codegen
    }

    /// Initialize synthetic pointee variables for function arguments that are reference types.
    fn init_reference_arguments(&mut self) {
        use std::fmt::Write;
        let fn_name = self.ctx.current_fn_name().to_owned();

        for (idx, local_decl) in self.body.arg_locals().iter().enumerate() {
            let local_idx = idx + 1;
            let arg_ty = local_decl.ty;

            if let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = arg_ty.kind() {
                let ref_base = crate::codegen_ay::names::local_name(&fn_name, local_idx);
                // Part of #2267: pre-allocate instead of format!().
                let pointee_base = {
                    let mut s = String::with_capacity(fn_name.len() + 18);
                    s.push_str(&fn_name);
                    s.push_str("::arg_pointee_");
                    let _ = write!(s, "{}", local_idx);
                    s
                };

                if let Some(pointee_sort) = Self::infer_sort_from_ty(pointee_ty) {
                    // Part of #2267: push_str instead of format!().
                    let pointee_name = {
                        let mut s = String::with_capacity(pointee_base.len() + 2);
                        s.push_str(&pointee_base);
                        s.push_str("_0");
                        s
                    };
                    let pointee_var = self.ctx.declare_var(&pointee_name, pointee_sort);

                    debug!(
                        "init_reference_arguments: {} -> {} (sort: {:?})",
                        ref_base,
                        pointee_base,
                        pointee_ty.kind()
                    );
                    let pointee_arc: std::sync::Arc<str> = std::sync::Arc::from(pointee_base);
                    self.env_update(std::sync::Arc::clone(&pointee_arc), pointee_var);
                    self.ref_pointees.insert(std::sync::Arc::from(ref_base), pointee_arc);
                } else {
                    debug!(
                        "init_reference_arguments: could not infer sort for pointee of arg {} (type: {:?})",
                        local_idx,
                        pointee_ty.kind()
                    );
                }
            }
        }
    }

    /// Convert the current span to a `SourceLocation` (#1164).
    pub(super) fn current_source_location(&self) -> Option<SourceLocation> {
        self.current_span.map(|span| {
            let lines = span.get_lines();
            let filename = span.get_filename();
            let mut loc = SourceLocation::new(filename, lines.start_line as u32)
                .with_column(lines.start_col as u32);
            if let Some(fn_ctx) = self.ctx.current_fn() {
                loc = loc.with_function(fn_ctx.name.as_str());
            }
            loc
        })
    }
}
