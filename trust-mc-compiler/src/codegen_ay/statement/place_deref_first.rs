// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Leading-deref resolution for place translation.
//!
//! Extracted from `place.rs` as part of #2246 decomposition.

use std::sync::Arc;

use super::place_post_deref::DerefProjectionResult;
use super::{Expr, IntoOption, LayoutOf, Place, ProjectionElem, RigidTy, StatementCodegen, TyKind};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::rustc_public_bridge::IndexedVal;
use tracing::{debug, warn};

/// Result of the deref-first path in `codegen_place`.
pub(super) enum DerefFirstResult {
    /// First projection is not Deref - caller should try other paths.
    NotDeref,
    /// Deref resolved to an expression.
    Resolved(Expr),
    /// Deref path was taken but no resolution path matched (no `ctx.unsupported` was called).
    /// Caller should fall through to generic resolution (env lookup, flattened tuples, etc.).
    Unresolved,
    /// Deref path encountered an unsupported projection (`ctx.unsupported` was called).
    /// Caller should return `None`.
    Unsupported,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Recover symbolic non-bitvec values tracked by the memory model.
    ///
    /// Returns `None` only when the expected type is byte-addressed (bitvec/bool).
    /// Non-bitvec loads must resolve through tracked symbolic stores; otherwise this
    /// fails closed to avoid unsound byte-memory fallbacks.
    #[must_use]
    #[allow(clippy::panic)] // Fail-closed for unsound non-bitvec byte-memory deref paths
    fn recover_symbolic_non_bitvec_load(
        &mut self,
        addr: Expr,
        expected_ty: rustc_public::ty::Ty,
    ) -> Option<Expr> {
        let expected_sort = Self::infer_sort_from_ty(expected_ty)?;
        if expected_sort.is_bitvec() || expected_sort.is_bool() {
            return None;
        }

        let symbolic_value_opt = self.ctx.load_symbolic_memory_value(addr.clone()).or_else(|| {
            // Part of #4101: When the direct symbolic store lookup fails, the load
            // address may be a copy of the original address through an SSA chain
            // (e.g., raw pointer extracted from NonNull/Container wrappers). Scan
            // addr_symbols to find stored addresses with matching symbolic values
            // and build an ITE that selects the correct value when addresses match.
            let candidates: Vec<_> = self
                .addr_symbols
                .values()
                .filter_map(|known_addr| {
                    let val = self.ctx.load_symbolic_memory_value(known_addr.clone())?;
                    if val.sort() == &expected_sort {
                        Some((known_addr.clone(), val))
                    } else {
                        None
                    }
                })
                .collect();
            if candidates.is_empty() {
                return None;
            }
            debug!(
                "recover_symbolic_non_bitvec_load: direct lookup failed, {} addr_symbol candidates with matching sort",
                candidates.len()
            );
            // Build ITE chain: ite(addr==a1, v1, ite(addr==a2, v2, ..., fresh))
            let fallback_name = self.ctx.fresh_name("symbolic_deref_fallback");
            let mut result = self.ctx.declare_var(&fallback_name, expected_sort.clone());
            for (known_addr, stored_val) in candidates.iter().rev() {
                let cond = addr.clone().eq(known_addr.clone());
                result = Expr::ite(cond, stored_val.clone(), result);
            }
            Some(result)
        });
        let Some(symbolic_value) = symbolic_value_opt else {
            warn!(
                addr = ?addr,
                expected_sort = ?expected_sort,
                "recover_symbolic_non_bitvec_load: missing symbolic store, using unconstrained fallback"
            );
            self.ctx.unsupported_with_fallback(
                "non_bitvec_deref_untracked",
                format!("addr={addr:?}, expected_sort={expected_sort:?}"),
            );
            let fresh_name = self.ctx.fresh_name("untracked_symbolic_deref");
            return Some(self.ctx.declare_var(&fresh_name, expected_sort));
        };
        assert!(
            symbolic_value.sort() == &expected_sort,
            "raw pointer symbolic load sort mismatch at addr {:?}: expected {:?}, found {:?}",
            addr,
            expected_sort,
            symbolic_value.sort()
        );
        Some(symbolic_value)
    }

    /// Handle the deref-first path: when the first projection is Deref.
    ///
    /// Tries resolution in order:
    /// 1. ref_pointees lookup (direct env, derived, synthesized)
    /// 2. heap_pointees lookup (direct key, ptr_source_map)
    /// 3. Raw pointer memory load (with byte-offset field projections)
    ///
    /// Returns `NotDeref` if first projection isn't Deref, allowing the caller
    /// to proceed with non-deref paths.
    pub(super) fn codegen_place_deref_first(&mut self, place: &Place) -> DerefFirstResult {
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return DerefFirstResult::NotDeref;
        }

        // Use ssa_base_name_for_prefix(0) for consistency with generic Deref handling
        let ref_base = self.ssa_base_name_for_prefix(place, 0);

        // Try direct lookup, then attempt to derive mapping if missing (#697).
        let pointee_base_opt = self.ref_pointees.get(ref_base.as_str()).cloned().or_else(|| {
            self.ensure_ref_pointee_for_place(place);
            self.ref_pointees.get(ref_base.as_str()).cloned()
        });

        if let Some(pointee_base) = pointee_base_opt {
            debug!("codegen_place Deref: ref_base={}, pointee_base={}", ref_base, pointee_base);
            // INTERIOR-MUTABILITY FAIL-CLOSE, part 1 of 2: MULTI-payload wrappers.
            //
            // The unified naming that lets the fail-close stand down further below
            // holds only when the payload is a SINGLE-payload chain
            // (`unsafe_cell_is_single_payload`) — `Cell`/`UnsafeCell`, and a struct
            // wrapping exactly one of them. `RefCell` is `{ borrow, value }`, two
            // non-ZST fields, so the erased-wrapper identity refuses it, its payload
            // keeps a separate name, and its write escapes into a synthetic
            // `arg_pointee` slot. MEASURED: `RefCell::new(7);
            // c.replace_with(|&mut old| old + 2); assert!(*c.as_ptr() == 7)` is
            // UNFALSIFIABLE without this guard. So those keep the blanket havoc they
            // have always had, at the position they have always had it.
            if self.base_name_is_interior_mutable(pointee_base.as_ref())
                && !self.base_name_unsafe_cell_is_single_payload(pointee_base.as_ref())
                && let Some(sort) = self
                    .infer_sort_from_place(place)
                    .or_else(|| self.env_lookup(pointee_base.as_ref()).map(|e| e.sort().clone()))
            {
                let fresh = self.ctx.fresh_name("cell_read_havoc");
                let havoc = self.ctx.declare_var(&fresh, sort);
                self.ctx.unsupported_with_fallback(
                    "Interior-mutable (Cell/UnsafeCell) read through shared reference",
                    format!("multi-payload interior-mutable read of {pointee_base}"),
                );
                self.record_violation_guarded(
                    Expr::bool_const(true),
                    "unsound_interior_mutable_read",
                );
                debug!("codegen_place Deref: multi-payload interior-mutable read -> havoc");
                return DerefFirstResult::Resolved(havoc);
            }
            // Get the pointee's value from the environment
            if let Some(pointee_expr) = self.env_lookup(pointee_base.as_ref()) {
                debug!(
                    "codegen_place Deref: found pointee_expr (sort={:?}) in env for {}",
                    pointee_expr.sort(),
                    pointee_base
                );
                if place.projection.len() == 1 {
                    return DerefFirstResult::Resolved(pointee_expr.clone());
                }
                // #3133: Try piecewise env lookup for flattened Options before
                // applying post-deref projections (which can't handle Downcast on BV64).
                if let Some(piecewise_expr) =
                    self.try_piecewise_env_lookup(&pointee_base, &place.projection[1..])
                {
                    debug!(
                        "codegen_place Deref: piecewise env resolved {}, sort={:?}",
                        pointee_base,
                        piecewise_expr.sort()
                    );
                    return DerefFirstResult::Resolved(piecewise_expr);
                }
                let pointee_expr = pointee_expr.clone();
                self.stage_bridge_enum_read(place, 1);
                return match self.apply_post_deref_projections(
                    pointee_expr,
                    &place.projection[1..],
                    true,  // strict
                    false, // hard failure
                    "Deref projection",
                ) {
                    DerefProjectionResult::Success(expr) => DerefFirstResult::Resolved(expr),
                    DerefProjectionResult::Fallthrough | DerefProjectionResult::Unsupported => {
                        DerefFirstResult::Unsupported
                    }
                };
            }

            debug!(
                "codegen_place Deref: env_lookup FAILED for pointee_base={}, trying fallback",
                pointee_base
            );
            // Fallback: try to resolve derived pointee names (#468).
            if let Some(pointee_expr) = self.ensure_derived_pointee_in_env(pointee_base.as_ref()) {
                debug!(
                    "codegen_place Deref: fallback resolved {} (sort={:?})",
                    pointee_base,
                    pointee_expr.sort()
                );
                if place.projection.len() == 1 {
                    return DerefFirstResult::Resolved(pointee_expr);
                }
                // #3133: Piecewise env lookup for flattened Options.
                if let Some(piecewise_expr) =
                    self.try_piecewise_env_lookup(&pointee_base, &place.projection[1..])
                {
                    return DerefFirstResult::Resolved(piecewise_expr);
                }
                self.stage_bridge_enum_read(place, 1);
                return match self.apply_post_deref_projections(
                    pointee_expr,
                    &place.projection[1..],
                    false, // lenient
                    false, // hard failure
                    "Deref fallback projection",
                ) {
                    DerefProjectionResult::Success(expr) => DerefFirstResult::Resolved(expr),
                    DerefProjectionResult::Fallthrough | DerefProjectionResult::Unsupported => {
                        DerefFirstResult::Unsupported
                    }
                };
            }

            // INTERIOR-MUTABILITY FAIL-CLOSE, part 2 of 2: single-payload wrappers
            // whose value NOTHING above could resolve.
            //
            // This guard used to sit BEFORE the `env_lookup` above and override a
            // value the model already held. That was the right call while the
            // payload had two names: `Cell::set`'s `ptr::write` landed in the env
            // slot `<base>_field_0` while `Cell::get` read `<base>`, so the store
            // was invisible and `get()` returned the CONSTRUCTION value — a false
            // PROOF the blanket havoc converted into a sound FAILED/INCONCLUSIVE.
            //
            // That split is gone: `erased_wrapper_field_sort` now names the
            // `Cell`/`UnsafeCell` payload after the wrapper on BOTH sides, and the
            // BMC mini-inliner carries SSA versions in and publishes a callee's
            // writes to caller storage back out (`inline_body`). Construction,
            // `Cell::get`, `Cell::set`/`replace`, the `UnsafeCell::get` raw-pointer
            // store and `as_ptr` now all name ONE slot, so a resolved value here is
            // the value the program last WROTE, not a stale snapshot. Overriding it
            // would only discard a correct answer. MEASURED in both directions:
            // `c.set(9); assert!(c.get() == 7)` FAILS and `assert!(c.get() == 9)`
            // SUCCEEDS; with the guard in its old position the first was
            // INCONCLUSIVE (an UNSAT VC — a PROOF of the false claim, kept off the
            // console only by AY's strict proof self-check) and the second FAILED.
            //
            // What remains is the case the havoc is actually FOR: nothing resolved,
            // so the next step is `synthesize_pointee_expr`, an unconstrained value
            // minted with no record that the interior-mutable contents were never
            // tracked. Keep the fresh-per-read havoc AND the canonical fallback pair
            // here so that read is demoted rather than silently trusted. Fresh per
            // read (never `env_update`d) is deliberate: two `get()`s of an untracked
            // `&Cell` must be independent, or `assert(x == y)` re-proves itself.
            if self.base_name_is_interior_mutable(pointee_base.as_ref())
                && let Some(sort) = self.infer_sort_from_place(place)
            {
                let fresh = self.ctx.fresh_name("cell_read_havoc");
                let havoc = self.ctx.declare_var(&fresh, sort);
                self.ctx.unsupported_with_fallback(
                    "Interior-mutable (Cell/UnsafeCell) read through shared reference",
                    format!("untracked Cell::get of {pointee_base}"),
                );
                self.record_violation_guarded(
                    Expr::bool_const(true),
                    "unsound_interior_mutable_read",
                );
                debug!("codegen_place Deref: untracked interior-mutable read -> havoc");
                return DerefFirstResult::Resolved(havoc);
            }

            // Last resort: synthesize a fresh symbolic pointee value.
            // Construct a minimal Place with just [Deref] instead of cloning the full Place.
            let deref_place =
                Place { local: place.local, projection: place.projection[..1].to_vec() };
            if let Some(pointee_expr) =
                self.synthesize_pointee_expr(pointee_base.as_ref(), &deref_place)
            {
                if place.projection.len() == 1 {
                    return DerefFirstResult::Resolved(pointee_expr);
                }
                self.stage_bridge_enum_read(place, 1);
                return match self.apply_post_deref_projections(
                    pointee_expr,
                    &place.projection[1..],
                    false, // lenient
                    false, // hard failure
                    "Deref synthesized projection",
                ) {
                    DerefProjectionResult::Success(expr) => DerefFirstResult::Resolved(expr),
                    DerefProjectionResult::Fallthrough | DerefProjectionResult::Unsupported => {
                        DerefFirstResult::Unsupported
                    }
                };
            }
        } else {
            debug!("codegen_place Deref: ref_base={} NOT FOUND in ref_pointees", ref_base);

            let ref_place = Place { local: place.local, projection: Vec::new() };
            if let Some(pointee_expr) = self.try_ref_pointee_from_env_value(&ref_base, &ref_place) {
                debug!(
                    "codegen_place Deref: recovered pointee from env value for {} (sort={:?})",
                    ref_base,
                    pointee_expr.sort()
                );
                if place.projection.len() == 1 {
                    return DerefFirstResult::Resolved(pointee_expr);
                }
                self.stage_bridge_enum_read(place, 1);
                return match self.apply_post_deref_projections(
                    pointee_expr,
                    &place.projection[1..],
                    false, // lenient
                    true, // fall through to generic projection chain for unsupported post-deref ops
                    "Deref env-value projection",
                ) {
                    DerefProjectionResult::Success(expr) => DerefFirstResult::Resolved(expr),
                    DerefProjectionResult::Fallthrough => DerefFirstResult::Unresolved,
                    DerefProjectionResult::Unsupported => DerefFirstResult::Unsupported,
                };
            }

            // #1112: Check heap_pointees for Box<T> and other heap-allocated values.
            let heap_key = self.ssa_base_name(place);
            if let Some(heap_value) = self.heap_pointees.get(heap_key.as_str()).cloned() {
                debug!(
                    "codegen_place Deref: found in heap_pointees[{}] (sort={:?})",
                    heap_key,
                    heap_value.sort()
                );
                return DerefFirstResult::Resolved(heap_value);
            }

            // Also try ptr_source_map to resolve raw ptr back to source Box (#1039).
            let ptr_heap_key = self.root_ssa_base_name(place);
            let direct_value = self.heap_pointees.get(ptr_heap_key.as_str()).cloned();
            // #3159: Follow ptr_source_map chain transitively to find
            // heap_pointees entry. Unsized coercions create multi-hop
            // pointer chains that single-hop resolution misses.
            // Part of #2267: Use Arc<str> for chain_key to avoid per-iteration
            // String allocation. ptr_source_map values are Arc<str>, so
            // reassignment is a move (zero-cost) instead of .to_string() copy.
            let mut chain_key: Arc<str> = Arc::from(ptr_heap_key.as_str());
            let mut chain_value = None;
            for _ in 0..8 {
                if let Some(next) = self.ptr_source_map.get(&*chain_key).cloned() {
                    if let Some(val) = self.heap_pointees.get(&*next).cloned() {
                        chain_value = Some(val);
                        break;
                    }
                    chain_key = next;
                } else {
                    break;
                }
            }
            // #3739: When ptr_source_map chain terminates without a heap_pointees
            // hit, try symbolic_memory_stores at the terminal's env address.
            // Multi-level Box nesting (e.g., Box<Box<dyn FnOnce>>) stores the
            // inner content in symbolic_memory_stores under the allocation addr,
            // not in heap_pointees.
            if chain_value.is_none() {
                if let Some(terminal_addr) = self.env_lookup(&chain_key).cloned() {
                    if terminal_addr.sort().is_bitvec() {
                        // Address is a bitvec pointer — look up symbolic memory.
                        if let Some(sym_val) = self.ctx.load_symbolic_memory_value(terminal_addr) {
                            debug!(
                                "codegen_place Deref: ptr_source_map chain terminal {} -> symbolic store (sort={:?})",
                                chain_key,
                                sym_val.sort()
                            );
                            chain_value = Some(sym_val);
                        }
                    } else {
                        // Non-bitvec (e.g., Datatype) — the env value IS the
                        // symbolic content for the inner Box, use it directly.
                        debug!(
                            "codegen_place Deref: ptr_source_map chain terminal {} -> env value (sort={:?})",
                            chain_key,
                            terminal_addr.sort()
                        );
                        chain_value = Some(terminal_addr);
                    }
                }
            }
            let heap_value_opt = chain_value.or(direct_value);
            if let Some(heap_value) = heap_value_opt {
                debug!(
                    "codegen_place Deref: found in heap_pointees[{}] (ptr base, sort={:?})",
                    ptr_heap_key,
                    heap_value.sort()
                );
                if place.projection.len() == 1 {
                    return DerefFirstResult::Resolved(heap_value);
                }
                self.stage_bridge_enum_read(place, 1);
                if let DerefProjectionResult::Success(expr) = self.apply_post_deref_projections(
                    heap_value,
                    &place.projection[1..],
                    false, // lenient
                    true,  // fallthrough on failure
                    "Deref heap_pointees projection",
                ) {
                    return DerefFirstResult::Resolved(expr);
                }
                // fall through to raw pointer / memory load handlers
            }
        }

        // Deref but no tracked pointee: check if this is a raw pointer deref (#24).
        // Construct minimal Place instead of cloning full projection Vec.
        let ptr_place = Place { local: place.local, projection: vec![] };
        if let Some(ptr_ty) = ptr_place.ty(self.body.locals()).into_option()
            && let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ptr_ty.kind()
        {
            // #1210: Check heap_pointees first for ADT types stored symbolically.
            let ptr_heap_key = self.root_ssa_base_name(&ptr_place);
            if let Some(heap_value) = self.heap_pointees.get(ptr_heap_key.as_str()).cloned() {
                debug!(
                    "codegen_place raw ptr: found heap_pointees[{}] (sort={:?})",
                    ptr_heap_key,
                    heap_value.sort()
                );
                if place.projection.len() == 1 {
                    return DerefFirstResult::Resolved(heap_value);
                }
                self.stage_bridge_enum_read(place, 1);
                if let DerefProjectionResult::Success(expr) = self.apply_post_deref_projections(
                    heap_value,
                    &place.projection[1..],
                    false, // lenient
                    true,  // fallthrough on failure
                    "Deref raw ptr heap projection",
                ) {
                    return DerefFirstResult::Resolved(expr);
                }
                // fall through to byte memory load
            }

            // Handle projections after Deref (e.g., (*ptr).field) by computing byte offset
            if place.projection.len() > 1 {
                let mut total_offset: usize = 0;
                let mut current_ty = pointee_ty;
                let mut final_field_ty = pointee_ty;
                let mut all_fields = true;

                for proj in place.projection.iter().skip(1) {
                    if let ProjectionElem::Field(field_idx, field_ty) = proj {
                        let layout = LayoutOf::new(current_ty);
                        if let Some(offset) = layout.field_offset(*field_idx) {
                            total_offset += offset;
                            current_ty = *field_ty;
                            final_field_ty = *field_ty;
                        } else {
                            debug!(
                                "codegen_place: cannot compute field offset for field {}",
                                *field_idx
                            );
                            all_fields = false;
                            break;
                        }
                    } else {
                        // external enum: ProjectionElem
                        debug!("codegen_place: unsupported projection after Deref: {:?}", proj);
                        all_fields = false;
                        break;
                    }
                }

                if all_fields
                    && let Some(ptr_expr) = self.codegen_place(&ptr_place)
                    && let Some(field_size) = LayoutOf::new(final_field_ty).size_of()
                {
                    let addr = if total_offset > 0 {
                        ptr_expr.bvadd(Expr::bitvec_const(total_offset as i64, POINTER_WIDTH))
                    } else {
                        ptr_expr
                    };
                    if let Some(symbolic) =
                        self.recover_symbolic_non_bitvec_load(addr.clone(), final_field_ty)
                    {
                        debug!(
                            "codegen_place: raw ptr symbolic deref + field, offset={}, sort={:?}",
                            total_offset,
                            symbolic.sort()
                        );
                        return DerefFirstResult::Resolved(symbolic);
                    }
                    let loaded = self.ctx.load_memory_bytes(addr, field_size as u32);
                    let loaded = if matches!(final_field_ty.kind(), TyKind::RigidTy(RigidTy::Bool))
                    {
                        loaded.ne(Expr::bitvec_const(0, 8))
                    } else {
                        loaded
                    };
                    debug!(
                        "codegen_place: raw ptr deref + field, offset={}, size={}",
                        total_offset, field_size
                    );
                    return DerefFirstResult::Resolved(loaded);
                }
            } else {
                // Raw pointer deref with no additional projections - load from memory
                if let Some(ptr_expr) = self.codegen_place(&ptr_place)
                    && let Some(size) = LayoutOf::new(pointee_ty).size_of()
                {
                    if let Some(symbolic) =
                        self.recover_symbolic_non_bitvec_load(ptr_expr.clone(), pointee_ty)
                    {
                        debug!("codegen_place: raw ptr symbolic deref, sort={:?}", symbolic.sort());
                        return DerefFirstResult::Resolved(symbolic);
                    }
                    let loaded = self.ctx.load_memory_bytes(ptr_expr, size as u32);
                    let loaded = if matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Bool)) {
                        loaded.ne(Expr::bitvec_const(0, 8))
                    } else {
                        loaded
                    };
                    debug!("codegen_place: raw ptr deref, loaded {} bytes from memory", size);
                    return DerefFirstResult::Resolved(loaded);
                }
            }
        }

        // Deref was first projection but couldn't resolve through any path
        DerefFirstResult::Unresolved
    }

    /// Try to resolve remaining projections via piecewise env lookup (#3133).
    ///
    /// For flattened Options (stored as BV64 + piecewise keys), projections like
    /// `[Downcast(1), Field(0)]` can't be applied on the BV64 expression directly.
    /// Instead, construct the full piecewise key name (e.g., `{base}_variant_1_field_0`)
    /// and look it up in the env.
    fn try_piecewise_env_lookup(
        &self,
        base_name: &str,
        remaining_projections: &[ProjectionElem],
    ) -> Option<Expr> {
        use std::fmt::Write;
        // Only attempt piecewise lookup if remaining projections contain Downcast.
        if !remaining_projections.iter().any(|p| matches!(p, ProjectionElem::Downcast(..))) {
            return None;
        }
        // Part of #2267: pre-allocate with capacity instead of to_string().
        let mut piecewise_name =
            String::with_capacity(base_name.len() + remaining_projections.len() * 15);
        piecewise_name.push_str(base_name);
        for proj in remaining_projections {
            match proj {
                ProjectionElem::Downcast(variant_idx) => {
                    let _ = write!(piecewise_name, "_variant_{}", variant_idx.to_index());
                }
                ProjectionElem::Field(field, _) => {
                    let _ = write!(piecewise_name, "_field_{}", field);
                }
                _ => return None, // Unsupported projection in piecewise lookup
            }
        }
        let result = self.env_lookup(&piecewise_name).cloned();
        debug!(
            "piecewise lookup '{}' -> {}",
            piecewise_name,
            if result.is_some() { "FOUND" } else { "NOT FOUND" }
        );
        result
    }
}
