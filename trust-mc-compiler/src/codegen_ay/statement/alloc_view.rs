// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Allocation views of pointer terms, for Kani's same-allocation obligation
//! (default BMC lane).
//!
//! Kani's pointer-offset models (library/kani_core/src/models.rs `offset`,
//! `ptr_offset_from`) raise `safety_check(same_allocation(p, q))`: both
//! pointers inside ONE allocation, one-past-the-end included. The BMC lane
//! used to decide it as `p / HEAP_STRIDE == q / HEAP_STRIDE`, a 1 MiB region,
//! which is neither sound nor precise for a stack local: a pointer 160 bytes
//! past a 16-byte `u128` was "the same allocation" (a missed bug), and a
//! one-past-the-end pointer could land in the next region (a false failure
//! certified `Genuine`).
//!
//! # The rule
//!
//! An address symbol minted for a place with no `Deref` projection is
//! REGISTERED with the byte position of that place inside its root local and
//! the local's size ([`AllocView`]). A pointer term resolves to an allocation
//! when walking it back — through SSA definitions, `+`/`-` of an offset, an
//! `ite` whose arms agree, and `fld_ptr` of a fat-pointer constructor — reaches
//! exactly one registered symbol. For a resolved pointer `p` of symbol `S`
//! with view `(offset, extent)`, the allocation base is `S - offset` and
//!
//! ```text
//! in_bounds(p) := (p - (S - offset)) <=u extent
//! ```
//!
//! is exact, because registration also asserts `S >= offset` and
//! `S - offset + extent <= usize::MAX` (the allocation, one-past-the-end
//! included, does not wrap). Two pointers are in the same allocation iff they
//! resolve to the same root local and both are in bounds; different root
//! locals are different allocations.
//!
//! A pointer that does not resolve is an allocation the encoder cannot NAME.
//! Its site keeps the old region predicate and records
//! `offset_provenance_unresolved`, which demotes a proof that leaned on it.

use std::sync::Arc;

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};

use super::StatementCodegen;
use crate::codegen_ay::context::AllocView;
use crate::rustc_public_bridge::IndexedVal;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

/// Deepest term walk [`StatementCodegen::resolve_alloc`] performs.
const MAX_ALLOC_WALK: usize = 64;

/// The fresh placeholder an SSA merge uses for "not assigned on this path".
fn is_ssa_init_placeholder(e: &Expr) -> bool {
    matches!(e.value(), ExprValue::Var { name } if name.contains("__ssa_init_"))
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// The byte position of `place` inside its root local and that local's
    /// size, when `place` has no `Deref` and every projection has a
    /// layout-known offset. `None` otherwise.
    pub(super) fn alloc_view_of_place(&mut self, place: &Place) -> Option<AllocView> {
        let root_ty = self.body.locals().get(place.local)?.ty;
        let extent = u128::try_from(LayoutOf::new(root_ty).size_of()?).ok()?;
        let mut ty = root_ty;
        let mut offset: u128 = 0;
        let mut variant: Option<usize> = None;
        for proj in &place.projection {
            match proj {
                ProjectionElem::Field(idx, field_ty) => {
                    let layout = LayoutOf::new(ty);
                    let field_offset = match variant.take() {
                        Some(v) => layout.variant_field_offset(v, *idx)?,
                        None => layout.field_offset(*idx)?,
                    };
                    offset = offset.checked_add(u128::try_from(field_offset).ok()?)?;
                    ty = *field_ty;
                }
                ProjectionElem::Downcast(v) => variant = Some(v.to_index()),
                ProjectionElem::Index(index_local) => {
                    let TyKind::RigidTy(RigidTy::Array(elem, _)) = ty.kind() else {
                        return None;
                    };
                    let index_place = Place { local: *index_local, projection: vec![] };
                    let index_expr = self.codegen_place(&index_place)?;
                    let index =
                        u128::try_from(self.const_on_defined_path(&index_expr, MAX_ALLOC_WALK)?)
                            .ok()?;
                    let elem_size = u128::try_from(LayoutOf::new(elem).size_of()?).ok()?;
                    offset = offset.checked_add(index.checked_mul(elem_size)?)?;
                    ty = elem;
                }
                ProjectionElem::ConstantIndex { offset: index, from_end: false, .. } => {
                    let TyKind::RigidTy(RigidTy::Array(elem, _)) = ty.kind() else {
                        return None;
                    };
                    let elem_size = u128::try_from(LayoutOf::new(elem).size_of()?).ok()?;
                    offset = offset.checked_add(u128::from(*index).checked_mul(elem_size)?)?;
                    ty = elem;
                }
                _ => return None,
            }
        }
        if variant.is_some() {
            return None;
        }
        let size = u128::try_from(LayoutOf::new(ty).size_of()?).ok()?;
        if offset.checked_add(size)? > extent {
            return None;
        }
        let root: Arc<str> = self.ssa_base_name_for_prefix(place, 0).into();
        Some(AllocView { root, offset, extent })
    }

    /// A cached address symbol is being REUSED for `place`. Address symbols are
    /// cached by base name, and `a[i]`'s name (`_idx_by_<local>`) does not change
    /// when `i` does, so that reuse may denote a different element: if the view
    /// no longer matches the registered one, the symbol stops naming an
    /// allocation (resolution fails, the site is recorded as unresolved) rather
    /// than vouching for the wrong element. Every other base name denotes one
    /// fixed place, including a reuse through `&raw *r` whose `r` resolves to
    /// it (measured: poisoning that reuse left `ptr.wrapping_add(10)
    /// .offset_from(ptr)` unresolved on offset-bounds-check/offset_from.rs).
    pub(super) fn revalidate_alloc_view(&mut self, addr: &Expr, place: &Place, base_name: &str) {
        let ExprValue::Var { name } = addr.value() else {
            return;
        };
        if !base_name.contains("_idx_by_") {
            return;
        }
        let Some(registered) = self.ctx.alloc_views.get(name).cloned() else {
            return;
        };
        let current = if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            // Reached through `&raw *r`: rebuild `local_M[local_N]` from the name,
            // the only index shape whose view can be re-derived here; anything
            // else stays fail-closed (poisoned).
            self.idx_place_from_base_name(base_name).and_then(|p| self.alloc_view_of_place(&p))
        } else {
            self.alloc_view_of_place(place)
        };
        if current.as_ref() != Some(&registered) {
            self.ctx.alloc_views.remove(name);
            self.ctx.alloc_views_poisoned.insert(name.clone());
        }
    }

    /// `<current fn>::local_M_idx_by_N` as the place `local_M[local_N]`.
    fn idx_place_from_base_name(&self, base_name: &str) -> Option<Place> {
        let rest = base_name.strip_prefix(self.ctx.current_fn_name())?.strip_prefix("::local_")?;
        let (array, index) = rest.split_once("_idx_by_")?;
        let array: usize = array.parse().ok()?;
        let index: usize = index.parse().ok()?;
        Some(Place { local: array, projection: vec![ProjectionElem::Index(index)] })
    }

    /// `Some(leaves)` when `base + count * size` is decidable from constants:
    /// `count` is constant on its defined path and `src` is exactly `symbol`
    /// there. `leaves` is whether the result is outside `[base, base+extent]`;
    /// an overflowing byte count is outside by definition.
    fn const_offset_leaves_view(
        &self,
        src: &Expr,
        count: &Expr,
        symbol: &Expr,
        view: &AllocView,
        pointee_size: usize,
    ) -> Option<bool> {
        let k = self.const_on_defined_path(count, MAX_ALLOC_WALK)?;
        if !self.is_symbol_on_defined_path(src, symbol, MAX_ALLOC_WALK) {
            return None;
        }
        if k == 0 {
            return Some(false);
        }
        let start = i128::try_from(view.offset).ok()?;
        let extent = i128::try_from(view.extent).ok()?;
        let Some(end) = k.checked_mul(pointee_size as i128).and_then(|b| start.checked_add(b)) else {
            return Some(true);
        };
        Some(end < 0 || end > extent)
    }

    /// `e` denotes `symbol` itself on every path where `e` is defined.
    fn is_symbol_on_defined_path(&self, e: &Expr, symbol: &Expr, depth: usize) -> bool {
        if e == symbol {
            return true;
        }
        let Some(depth) = depth.checked_sub(1) else {
            return false;
        };
        match e.value() {
            ExprValue::Var { name } if !name.contains("__ssa_init_") => self
                .ssa_concrete_values
                .get(name)
                .is_some_and(|def| self.is_symbol_on_defined_path(def, symbol, depth)),
            ExprValue::Ite { then_expr, else_expr, .. } => {
                if is_ssa_init_placeholder(else_expr) {
                    self.is_symbol_on_defined_path(then_expr, symbol, depth)
                } else if is_ssa_init_placeholder(then_expr) {
                    self.is_symbol_on_defined_path(else_expr, symbol, depth)
                } else {
                    self.is_symbol_on_defined_path(then_expr, symbol, depth)
                        && self.is_symbol_on_defined_path(else_expr, symbol, depth)
                }
            }
            _ => false,
        }
    }

    /// The constant an index local holds on every path where it is DEFINED.
    ///
    /// An index assigned under a path condition is `ite(pc, 3, <__ssa_init_>)`:
    /// the placeholder arm is the value on paths where the local was never
    /// assigned, and MIR's definite-initialization rule means no `a[i]` reads
    /// `i` there. `const_i128` cannot see through the `ite`, so `&a[i]` taken
    /// after a bounds check was never registered and every `offset_from` on it
    /// stayed unresolved (kani/PointerOffset/offset_from.rs, measured on the
    /// after2 bundle: `local_9_0 = ite(local_6_0, 3, local_9__ssa_init_..)`).
    fn const_on_defined_path(&self, e: &Expr, depth: usize) -> Option<i128> {
        let depth = depth.checked_sub(1)?;
        match e.value() {
            ExprValue::Var { name } if !name.contains("__ssa_init_") => {
                match self.ssa_concrete_values.get(name) {
                    Some(def) => self.const_on_defined_path(def, depth),
                    None => self.const_i128(e),
                }
            }
            ExprValue::Ite { then_expr, else_expr, .. } => {
                if is_ssa_init_placeholder(else_expr) {
                    self.const_on_defined_path(then_expr, depth)
                } else if is_ssa_init_placeholder(then_expr) {
                    self.const_on_defined_path(else_expr, depth)
                } else {
                    let t = self.const_on_defined_path(then_expr, depth)?;
                    (self.const_on_defined_path(else_expr, depth)? == t).then_some(t)
                }
            }
            _ => self.const_i128(e),
        }
    }

    /// Register `addr` (the stable address symbol of `place`) as a view of its
    /// root allocation, and assert the facts the in-bounds predicate needs.
    ///
    /// The facts are about the address symbol alone (it is fresh, and every
    /// other constraint on it is an unconditional validity fact too), so they
    /// are asserted unconditionally: they cannot restrict a program input.
    pub(super) fn register_alloc_view(&mut self, addr: &Expr, place: &Place) {
        let ExprValue::Var { name } = addr.value() else {
            return;
        };
        if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
            || self.ctx.alloc_views_poisoned.contains(name)
            || self.ctx.alloc_views.contains_key(name)
        {
            return;
        }
        let Some(view) = self.alloc_view_of_place(place) else {
            return;
        };
        let max = if POINTER_WIDTH >= 128 { u128::MAX } else { (1u128 << POINTER_WIDTH) - 1 };
        let Some(room) = max.checked_sub(view.extent) else {
            return;
        };
        let offset = Expr::bitvec_const(view.offset, POINTER_WIDTH);
        let base = addr.clone().bvsub(offset.clone());
        // The allocation starts at or above 0 ...
        self.ctx.assert(addr.clone().bvuge(offset));
        // ... and it, one-past-the-end included, does not wrap.
        self.ctx.assert(base.clone().bvule(Expr::bitvec_const(room, POINTER_WIDTH)));
        // One-past-the-end shares the region of the first byte, so the region
        // predicate other checks still use agrees with this one.
        if let Ok(extent) = u64::try_from(view.extent) {
            self.ctx.heap_constrain_within_region(base.clone(), extent.saturating_add(1));
        }
        // Two views of one local name one allocation.
        if let Some((sibling_base, _)) = self.ctx.alloc_roots.get(&view.root).cloned() {
            self.ctx.assert(base.eq(sibling_base));
        } else {
            // Two live locals are two allocations, and allocations do not
            // overlap. Without this the solver placed `&mut a` and `&mut b` at
            // ONE address, so a write through the first was read back through
            // the second (kani/Intrinsics/Atomic/Unstable/AtomicAdd, certified
            // Genuine). A zero-sized allocation overlaps nothing, and both
            // disjuncts hold for it. Sound: the constraint is about fresh
            // address symbols only, and Rust guarantees it for every pair of
            // simultaneously live allocations; for a local re-created in a
            // loop the symbol is reused, so no pair is ever the same object.
            let end = base.clone().bvadd(Expr::bitvec_const(view.extent, POINTER_WIDTH));
            let others: Vec<(Expr, u128)> = self.ctx.alloc_roots.values().cloned().collect();
            for (other_base, other_extent) in others {
                let other_end =
                    other_base.clone().bvadd(Expr::bitvec_const(other_extent, POINTER_WIDTH));
                self.ctx.assert(end.clone().bvule(other_base).or(other_end.bvule(base.clone())));
            }
            self.ctx.alloc_roots.insert(Arc::clone(&view.root), (base, view.extent));
        }
        self.ctx.alloc_views.insert(name.clone(), view);
    }

    /// Store the ROOT local's current value at the allocation base of `addr`,
    /// when `addr` is a registered view of a projected (non-root) place.
    pub(super) fn materialize_root_of_projected_view(&mut self, addr: &Expr, place: &Place) {
        if place.projection.is_empty()
            || place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
        {
            return;
        }
        let ExprValue::Var { name } = addr.value() else {
            return;
        };
        let Some(view) = self.ctx.alloc_views.get(name).cloned() else {
            return;
        };
        let root_place = Place { local: place.local, projection: vec![] };
        let Some(root_value) = self.codegen_place(&root_place) else {
            return;
        };
        let Some(root_ty) = self.body.locals().get(place.local).map(|d| d.ty) else {
            return;
        };
        let base = addr.clone().bvsub(Expr::bitvec_const(view.offset, POINTER_WIDTH));
        if !self.try_materialize_array_to_memory(&base, &root_value, root_ty) {
            self.store_typed_value_to_memory(base, root_value, root_ty);
        }
    }

    /// The registered symbol a pointer term is derived from, and its view.
    pub(super) fn resolve_alloc(&self, ptr: &Expr) -> Option<(Expr, AllocView)> {
        self.resolve_alloc_walk(ptr, MAX_ALLOC_WALK)
    }

    fn resolve_alloc_walk(&self, e: &Expr, depth: usize) -> Option<(Expr, AllocView)> {
        let depth = depth.checked_sub(1)?;
        match e.value() {
            ExprValue::Var { name } => {
                if let Some(view) = self.ctx.alloc_views.get(name) {
                    return Some((e.clone(), view.clone()));
                }
                // A merge (phi) variable resolves through its ite; every arm must
                // name the same allocation (the `Ite` arm below).
                let def = self
                    .ssa_concrete_values
                    .get(name)
                    .or_else(|| self.ctx.alloc_phi_defs.get(name))?;
                self.resolve_alloc_walk(def, depth)
            }
            ExprValue::BvAdd(a, b) => {
                match (self.resolve_alloc_walk(a, depth), self.resolve_alloc_walk(b, depth)) {
                    (Some(r), None) | (None, Some(r)) => Some(r),
                    _ => None,
                }
            }
            ExprValue::BvSub(a, _) => self.resolve_alloc_walk(a, depth),
            ExprValue::Ite { then_expr, else_expr, .. } => {
                // A `__ssa_init_` placeholder arm is the value on paths where
                // the local was never assigned; no check reads the pointer
                // there, so the defined arm decides.
                if is_ssa_init_placeholder(else_expr) {
                    return self.resolve_alloc_walk(then_expr, depth);
                }
                if is_ssa_init_placeholder(then_expr) {
                    return self.resolve_alloc_walk(else_expr, depth);
                }
                let t = self.resolve_alloc_walk(then_expr, depth)?;
                let f = self.resolve_alloc_walk(else_expr, depth)?;
                (t.0 == f.0 && t.1 == f.1).then_some(t)
            }
            ExprValue::DatatypeSelector { selector_name, expr, .. }
                if selector_name == "fld_ptr" =>
            {
                let built = self.follow_ssa_defs(expr, depth);
                let ExprValue::DatatypeConstructor { args, .. } = built.value() else {
                    return None;
                };
                let fields = &built.sort().datatype_sort()?.constructors.first()?.fields;
                let idx = fields.iter().position(|f| f.name == "fld_ptr")?;
                self.resolve_alloc_walk(args.get(idx)?, depth)
            }
            _ => None,
        }
    }

    /// Follow `ssa_concrete_values` definitions only (never the CURRENT env
    /// value of a base, which may postdate the term).
    fn follow_ssa_defs(&self, e: &Expr, depth: usize) -> Expr {
        let mut cur = e.clone();
        for _ in 0..depth {
            let ExprValue::Var { name } = cur.value() else { break };
            let Some(def) = self.ssa_concrete_values.get(name) else { break };
            cur = def.clone();
        }
        cur
    }

    /// `p` lies inside the allocation of `(symbol, view)`, one-past-the-end
    /// included. `p` must be pointer width.
    pub(super) fn alloc_in_bounds(p: &Expr, symbol: &Expr, view: &AllocView) -> Expr {
        let base = symbol.clone().bvsub(Expr::bitvec_const(view.offset, POINTER_WIDTH));
        p.clone().bvsub(base).bvule(Expr::bitvec_const(view.extent, POINTER_WIDTH))
    }

    /// Kani's `same_allocation(p, q)` for two pointer-width terms whose
    /// UNCOERCED operands are `p_src` / `q_src`. `None` when either allocation
    /// cannot be named.
    pub(super) fn same_allocation_exact(
        &self,
        p_src: &Expr,
        p: &Expr,
        q_src: &Expr,
        q: &Expr,
    ) -> Option<Expr> {
        let (ps, pv) = self.resolve_alloc(p_src)?;
        let (qs, qv) = self.resolve_alloc(q_src)?;
        if pv.root != qv.root {
            return Some(Expr::bool_const(false));
        }
        Some(Self::alloc_in_bounds(p, &ps, &pv).and(Self::alloc_in_bounds(q, &qs, &qv)))
    }
}

/// Kani's wording for the `ptr::offset` allocation obligation (kani_core models.rs).
const OFFSET_MUST_SAME_ALLOCATION: &str =
    "Offset result and original pointer must point to the same allocation";

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// The same-allocation obligation of a CHECKED pointer offset
    /// (`ptr::offset` / `add` / `sub`, the `Offset` model, MIR `BinOp::Offset`):
    /// for a non-zero count of a non-zero-sized pointee, the base and the
    /// result must both lie in the base's allocation.
    ///
    /// `src` is the UNCOERCED base operand term (what [`Self::resolve_alloc`]
    /// walks); `ptr` is its pointer-width form; `count` the element count.
    /// An allocation that cannot be named falls back to the slice-view check
    /// in `copy_shadow.rs`, and when that cannot decide either the site is
    /// recorded as `offset_provenance_unresolved`.
    pub(super) fn emit_offset_same_allocation_check(
        &mut self,
        src: &Expr,
        ptr: &Expr,
        count: &Expr,
        pointee_size: usize,
    ) {
        if pointee_size == 0 {
            return;
        }
        let resolved = if ptr.sort().bitvec_width() == Some(POINTER_WIDTH)
            && count.sort().bitvec_width().is_some()
        {
            self.resolve_alloc(src)
        } else {
            None
        };
        let Some((symbol, view)) = resolved else {
            if !self.emit_offset_object_bounds_check(ptr, count, pointee_size) {
                self.ctx.bmc_offset_provenance_unresolved("ptr_offset");
            }
            return;
        };
        // Decided at codegen when the count is a constant and the base IS the
        // registered symbol (no displacement): the obligation is then a fact
        // about constants. Folding it keeps the query as small as the program:
        // `(&a[1] as *const i32).offset(isize::MAX)` stated symbolically made
        // ay give up (`resourceout` after 15 s, 4.8 GB) on a query it answered
        // in 4 s without the check (expected/pointer-overflow/main.rs,
        // measured on the after2 bundle).
        if let Some(leaves) = self.const_offset_leaves_view(src, count, &symbol, &view, pointee_size)
        {
            if leaves {
                self.record_violation_guarded_with_message(
                    Expr::bool_const(true),
                    "ptr_offset_same_alloc",
                    Some(OFFSET_MUST_SAME_ALLOCATION.to_string()),
                );
            }
            return;
        }
        let count = Self::coerce_to_width_typed(count.clone(), POINTER_WIDTH, true);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let size = Expr::bitvec_const(pointee_size as u128, POINTER_WIDTH);
        let result = ptr.clone().bvadd(count.clone().bvmul(size));
        let in_bounds = Self::alloc_in_bounds(ptr, &symbol, &view)
            .and(Self::alloc_in_bounds(&result, &symbol, &view));
        let violation = count.eq(zero).not().and(in_bounds.not());
        self.record_violation_guarded_with_message(
            violation,
            "ptr_offset_same_alloc",
            Some(OFFSET_MUST_SAME_ALLOCATION.to_string()),
        );
    }
}
