// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC null-pointer-dereference obligation for raw pointer derefs.
//!
//! Soundness gap closure: MIR does not always emit
//! `Assert(NullPointerDereference)` for `unsafe { *p }` on a raw pointer —
//! e.g. `let p: *const u32 = ptr::null(); unsafe { *p }` has no MIR-level
//! null assert on current nightlies (the assert is folded away or never
//! materialized). The BMC path closes this at codegen time in
//! `statement::place_deref::emit_raw_ptr_deref_checks` by recording a
//! `null_pointer_check` violation guarded on `ptr == 0`. The CHC path had no
//! equivalent: a null raw-pointer deref simply loaded an unconstrained value
//! from the memory array (Mem level) or recorded a sound fallback (Reg/Ptr
//! level), so harnesses with a reachable null deref verified as PROOF.
//!
//! A previous attempt (c24a352db, reverted in 558ded3d8) wired the check into
//! `emit_assignment_safety_checks`, but that hook only runs when rvalue
//! translation *succeeds* — precisely the deref-bail cases never reached it.
//! This implementation instead emits the obligation from the TOP of the
//! deref-resolution cascade (`try_resolve_deref_cascade`) and from the top of
//! the projection-assignment (deref-store) path, so the `ptr != 0` obligation
//! is staged on `heap_state.pending_checks` regardless of whether the deref
//! later Resolves, stays Unresolved (memory path), or Bails.
//!
//! `pending_checks` entries are positive conditions that must HOLD; the rule
//! generator (`emit_error_rule_for_condition_shared`) negates them into
//! `state ∧ ¬cond → error()`, which is the CHC analog of the BMC violation
//! record. Pushing `ptr != 0` therefore makes `ptr == 0` reach `error()`.
//!
//! False-positive control (#3094-class): references (`&T`, `&mut T`), `Box`,
//! and other language-guaranteed-non-null bases are excluded by the RawPtr
//! type gate, and raw pointers that are provably non-null (stack addresses,
//! known heap allocations, promoted constants, and ref/alloc/static-derived
//! pointers traced through the global assignment map — the same whitelist
//! used by `should_skip_reg_pointer_assert`) are skipped.

use std::collections::{HashMap, HashSet};

use ay_bindings::Expr;
use rustc_public::mir::{
    AggregateKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{ConstantKind, IntTy, RigidTy, TyKind, UintTy};
use tracing::debug;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Stage a `ptr != 0` memory-safety obligation for a leading raw-pointer
    /// dereference in `place` (`*p`, `(*p).field`, `(*p)[i]`, `*p = v`, ...).
    ///
    /// The obligation is pushed onto `heap_state.pending_checks`, which the
    /// block encoder drains into per-block error rules (fail-closed: the
    /// solver must prove `ptr != 0` on every path that reaches the deref).
    ///
    /// No-op when:
    /// - memory safety checks are disabled,
    /// - the place does not start with a `Deref` projection,
    /// - the base local is not a raw pointer (`&T`/`&mut T`/`Box` are
    ///   language-guaranteed non-null),
    /// - the pointer is provably non-null (see
    ///   [`Self::raw_ptr_local_provably_non_null`]),
    /// - the pointer's SSA value cannot be resolved or is not bitvector-sorted
    ///   (those encodings have no uniform null representation; their deref
    ///   paths already record sound fallbacks).
    pub(in crate::codegen_ay::chc) fn emit_raw_ptr_null_deref_check(
        &mut self,
        place: &Place,
        modified_locals: &HashSet<usize>,
    ) {
        if !self.memory_safety_checks {
            return;
        }
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return;
        }
        let local_idx: usize = place.local;
        let Some(local_decl) = self.body.locals().get(local_idx) else {
            return;
        };
        if !matches!(local_decl.ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(_, _))) {
            // References and Box are non-null by language guarantee; their
            // derefs must not pick up spurious obligations (#3094).
            return;
        }
        if self.raw_ptr_local_provably_non_null(local_idx) {
            debug!(local_idx, "CHC: raw ptr deref provably non-null — skipping null check");
            return;
        }

        // Resolve the pointer's current SSA value: in-block expression env for
        // already-modified locals, otherwise the relation state variable.
        // Mirrors the base-expression resolution in translate_place_with_deref.
        let ptr_expr = if modified_locals.contains(&local_idx) {
            self.encode
                .local_expr_env
                .get(&local_idx)
                .cloned()
                .or_else(|| self.resolve_local_expr(local_idx, modified_locals))
        } else {
            self.resolve_local_expr(local_idx, modified_locals)
        };
        let Some(ptr_expr) = ptr_expr else {
            debug!(local_idx, "CHC: raw ptr null check — pointer value unresolvable, skipping");
            return;
        };
        let Some(width) = ptr_expr.sort().bitvec_width() else {
            debug!(local_idx, "CHC: raw ptr null check — non-bitvector pointer sort, skipping");
            return;
        };

        // Provably non-null BY VALUE: a split pointer whose obj_id lane
        // (`extract(63,32)`) is a NONZERO CONSTANT occupies the high 32 bits, so
        // `concat(id, off) != 0` is a tautology on every path regardless of the
        // (possibly symbolic) offset lane. This is the value-level complement to
        // the provenance whitelist above: it catches stack/static/promoted/
        // computed addresses whose resolved SSA value is a constant-obj_id split
        // pointer but whose provenance the trace lost through casts/arithmetic —
        // and, crucially, avoids ever building a `concat(nonzero, x) != 0` rule
        // that ay's simplifier may not discharge cheaply (residual-sat gap),
        // which is a dominant source of the null-obligation query bloat that
        // pushes safe harnesses past the timeout. obj_id 0 is the reserved null
        // sentinel, so requiring `id != 0` never skips a possibly-null pointer;
        // non-64-bit or symbolic-obj_id pointers yield `None` and fall through to
        // the emitted check (fail-open to the obligation).
        if let Some((obj_id_expr, _offset)) = self.split_pointer(&ptr_expr) {
            if Self::const_obj_id_u32(&obj_id_expr).is_some_and(|id| id != 0) {
                debug!(
                    local_idx,
                    "CHC: raw ptr deref has constant nonzero obj_id — skipping null check"
                );
                return;
            }
        }

        // Positive polarity: the condition that must HOLD. The error-rule
        // generator negates it (error fires on ptr == 0). Same semantics as
        // BMC's null_pointer_check (which records `ptr == 0` as a violation).
        let zero = Expr::bitvec_const(0u64, width);
        let check = ptr_expr.eq(zero).not();
        if self.heap_state.pending_checks.contains(&check) {
            // The same deref can be translated more than once per block
            // (speculative/retry paths); one obligation is enough.
            return;
        }
        debug!(local_idx, width, "CHC: staged raw ptr null-deref obligation (ptr != 0)");
        self.heap_state.pending_checks.push(check);
    }

    /// Whitelist of "provably non-null" raw-pointer sources, mirroring the
    /// `should_skip_reg_pointer_assert` suppression machinery (#3094) plus the
    /// deref-cascade's own resolution facts:
    ///
    /// - stack-address-backed pointers (`&local as *const T` with a concrete
    ///   stack region id),
    /// - pointers tied to a known heap allocation (`obj_id != 0`; obj_id 0 is
    ///   the null sentinel and is filtered at the propagation layer since
    ///   8fb72021a — cross-checked here as defense-in-depth),
    /// - promoted-constant references (`const_ref_values` /
    ///   `const_ref_discriminants`),
    /// - ref-derived / alloc-derived / static-derived pointers traced through
    ///   the global assignment map (`place_depends_on_ref_target`).
    fn raw_ptr_local_provably_non_null(&self, local_idx: usize) -> bool {
        // Soundness (conditionally-null pointers): a raw pointer that is assigned
        // a NULL value on ANY path is not provably non-null — even when another
        // path assigns a reference/allocation. Without this guard, a pointer like
        // `if c { null() } else { &z }` trips the ref-target whitelist below (via
        // the `&z` branch) and the null-deref obligation is silently elided on the
        // `null()` branch. This is the obligation that must fire once a ZST address
        // comparison is modeled as nondeterministic. (zst/main.rs missed_bug.)
        if self.raw_ptr_local_has_null_assignment(local_idx) {
            debug!(local_idx, "CHC: raw ptr has a null-producing assignment — not skipping");
            return false;
        }
        if self.known_stack_addr_expr(local_idx).is_some() {
            return true;
        }
        if self.known_alloc_ids.get(&local_idx).copied().is_some_and(|obj_id| obj_id != 0) {
            return true;
        }
        if self.ref_resolution.const_ref_values.contains_key(&local_idx)
            || self.ref_resolution.const_ref_discriminants.contains_key(&local_idx)
        {
            return true;
        }
        // Chain-trace last: O(depth) walk over the memoized (built-once) global
        // assignment map. Part of the null-provenance perf fix. The depth bound
        // only limits how far a non-null base case can be REACHED — a deeper walk
        // can prove MORE derefs non-null (skipping a needless obligation) and can
        // never fabricate a non-null proof (it returns true only on a genuine
        // ref/alloc/static base), so raising it is sound and monotone in the safe
        // direction. 32 covers the long inlined copy-cast chains that std/Kani
        // harness expansion produces; `visited` still bounds total work.
        let global_assignments = self.global_assignment_map();
        let mut visited = HashSet::new();
        let base_place = Place { local: local_idx, projection: vec![] };
        self.place_depends_on_ref_target(&base_place, global_assignments, &mut visited, 32)
    }

    /// True when `local_idx` receives a NULL pointer value on some assignment
    /// path (directly, or transitively through a copy/cast of a null-valued
    /// local). Used to VETO the provably-non-null whitelist: a pointer that can
    /// be null must keep its null-deref obligation.
    ///
    /// O(1) membership test against the memoized null-taint set (see
    /// [`Self::compute_null_tainted_locals`]).
    fn raw_ptr_local_has_null_assignment(&self, local_idx: usize) -> bool {
        self.null_tainted_locals().contains(&local_idx)
    }

    /// Memoized set of null-tainted locals for the current body. Computed once
    /// (a pure function of `self.body`) and cached; every subsequent
    /// `raw_ptr_local_has_null_assignment` query is an O(1) set lookup instead
    /// of a recursive whole-body scan. Part of the null-provenance perf fix.
    fn null_tainted_locals(&self) -> &HashSet<usize> {
        self.null_tainted_locals_cache.get_or_init(|| self.compute_null_tainted_locals())
    }

    /// Single-pass computation of the set of locals that hold a NULL pointer on
    /// some assignment path — the whole-body reachability the old recursive
    /// `local_null_assign_rec` computed per query.
    ///
    /// Detection semantics are identical to the old scan (same candidate
    /// operands, same `::null`/`::null_mut` recognition, same projection-empty
    /// guards); only the algorithm changes:
    /// 1. One scan of every block collects, for all locals at once:
    ///    - DIRECT null seeds: locals whose address operand is a null constant
    ///      (`operand_is_null_ptr_const`) or whose defining Call terminator is
    ///      `::null`/`::null_mut`;
    ///    - copy/cast taint edges `src → dst`: when `dst`'s address operand is a
    ///      projection-empty `Copy`/`Move` of `src`, `dst` is null iff `src` is.
    /// 2. A transitive closure propagates taint from the seeds along the edges.
    ///
    /// Candidate address operands per rvalue (a raw pointer is null iff its data
    /// operand is zero): `Use`/`Cast` — the operand itself; `Aggregate(RawPtr,
    /// [data, meta])` — the first (data) field (how `std::ptr::null()`
    /// const-folds via `from_raw_parts(without_provenance(0), ())`).
    /// `AddressOf`/`Ref` are non-null by construction and contribute nothing.
    ///
    /// Full closure (vs. the old depth-8 cap) can only ADD taint on chains
    /// longer than 8 hops — the fail-closed direction (more null-deref
    /// obligations, never fewer), so no PROOF that the old code rejected can
    /// slip through.
    fn compute_null_tainted_locals(&self) -> HashSet<usize> {
        // Seeds: locals with a direct null-producing definition.
        let mut seeds: Vec<usize> = Vec::new();
        // Forward taint edges: edges[src] = locals tainted when `src` is tainted.
        let mut edges: HashMap<usize, Vec<usize>> = HashMap::new();

        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                if !lhs.projection.is_empty() {
                    continue;
                }
                let dst = lhs.local;
                let addr_op = match rvalue {
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => op,
                    Rvalue::Aggregate(AggregateKind::RawPtr(..), operands) => {
                        let Some(op) = operands.first() else {
                            continue;
                        };
                        op
                    }
                    _ => continue,
                };
                if self.operand_is_null_ptr_const(addr_op) {
                    seeds.push(dst);
                } else if let Operand::Copy(p) | Operand::Move(p) = addr_op
                    && p.projection.is_empty()
                {
                    edges.entry(p.local).or_default().push(dst);
                }
            }
            // `std::ptr::null()` / `null_mut()` are function calls whose
            // destination is the pointer local — scan Call terminators too.
            if let TerminatorKind::Call { func, destination, .. } = &bb.terminator.kind
                && destination.projection.is_empty()
                && self
                    .resolve_callee_path(func)
                    .is_some_and(|p| p.ends_with("::null") || p.ends_with("::null_mut"))
            {
                seeds.push(destination.local);
            }
        }

        // Transitive closure: propagate taint from seeds along the copy/cast edges.
        let mut tainted: HashSet<usize> = HashSet::new();
        let mut stack = seeds;
        while let Some(local) = stack.pop() {
            if !tainted.insert(local) {
                continue;
            }
            if let Some(dsts) = edges.get(&local) {
                stack.extend(dsts.iter().copied());
            }
        }
        tainted
    }

    /// True when `op` is a constant that evaluates to a zero pointer / integer.
    ///
    /// Cheap and side-effect-free (do NOT use `translate_constant` here — it
    /// allocates fresh CHC var declarations, and this runs inside a per-deref
    /// whole-body scan). Detects:
    /// - an integer/usize constant equal to 0 (`0 as *const T`,
    ///   `without_provenance(0)`, and zero address fields), and
    /// - a pointer-typed constant whose allocation is all-zero with no
    ///   provenance (a literal null pointer constant).
    fn operand_is_null_ptr_const(&self, op: &Operand) -> bool {
        let Operand::Constant(c) = op else {
            return false;
        };
        // `eval_target_usize` reads the constant as a pointer-sized (8-byte)
        // integer and ICEs ("expected int of size 8") on any other-sized const.
        // The one-pass null-taint scan reaches `Use`/`Cast` operands of EVERY
        // type (i32, i128, u8, ...), so only evaluate it for pointer-sized
        // integer constants — a null pointer's address is a usize/isize; a
        // non-pointer-sized integer is never a null pointer here.
        if matches!(
            c.const_.ty().kind(),
            TyKind::RigidTy(RigidTy::Uint(UintTy::Usize) | RigidTy::Int(IntTy::Isize))
        ) && matches!(c.const_.eval_target_usize(), Ok(0))
        {
            return true;
        }
        matches!(c.const_.ty().kind(), TyKind::RigidTy(RigidTy::RawPtr(..) | RigidTy::Ref(..)))
            && matches!(
                c.const_.kind(),
                ConstantKind::Allocated(alloc)
                    if alloc.provenance.ptrs.is_empty()
                        && !alloc.bytes.is_empty()
                        && alloc.bytes.iter().all(|b| *b == Some(0))
            )
    }
}
