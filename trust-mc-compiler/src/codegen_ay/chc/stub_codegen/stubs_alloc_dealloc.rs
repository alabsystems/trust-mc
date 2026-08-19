// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC heap deallocation implementation.
//!
//! Extracted from `stubs_alloc_heap_ops.rs` — Part of #4206.

use std::collections::HashSet;

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::CrateDef;
use rustc_public::mir::Operand;
use tracing::{debug, warn};

use super::types::POINTER_WIDTH;
use super::{AllocCallResult, ChcCtx, chc_fresh_name, codegen_expr_heap, declare_pending_var};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Index of the argument that carries the allocation's ADDRESS, decided by
    /// the Rust type the MIR gives it.
    ///
    /// # Why this is not a width test
    ///
    /// The allocator stubs see two shapes — `__rust_dealloc(ptr, size, align)` /
    /// `__rust_realloc(ptr, old_size, align, new_size)` and the trait methods
    /// `<Global as Allocator>::{deallocate,grow,shrink}(&self, ptr, ..)` — and
    /// have to decide which operand is the pointer that the free / move model is
    /// built on. Every candidate is `bv64` in the encoding: a `*mut u8`, a
    /// `&Global`, and a `usize` size are indistinguishable by width, which is how
    /// #3184 came to free the allocator reference.
    ///
    /// The Rust type answers it outright. A raw pointer, or a `NonNull` /
    /// `Unique` (the `Allocator` trait's pointer type), is the pointer; a
    /// reference is the receiver; everything else is neither. Only the first two
    /// positions are considered, because those are the only two either ABI puts
    /// the pointer in — a match further along would be a coincidence, not a
    /// convention.
    ///
    /// `None` means the pointer could not be identified, and every caller fails
    /// closed on it rather than guessing.
    pub(in crate::codegen_ay::chc) fn allocator_pointer_arg_idx(
        &self,
        args: &[Operand],
    ) -> Option<usize> {
        use rustc_public::ty::{RigidTy, TyKind};
        args.iter().take(2).position(|arg| {
            arg.ty(self.body.locals()).ok().is_some_and(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::RawPtr(..)) => true,
                TyKind::RigidTy(RigidTy::Adt(def, _)) => {
                    let name = def.name();
                    let trimmed = name.rsplit("::").next().unwrap_or(name.as_str());
                    matches!(trimmed, "NonNull" | "Unique")
                }
                _ => false, // external enum: TyKind
            })
        })
    }

    /// Translate `__rust_dealloc` to CHC constraints.
    ///
    /// Handles two calling conventions:
    /// - `__rust_dealloc(ptr, size, align)` — 3 bare args
    /// - `<Global as Allocator>::deallocate(&self, ptr, layout)` — trait method
    ///
    /// Per design:
    /// - Marks obj_valid[obj_id] = false (freed)
    /// - Part of #1173: Detect double-free by checking obj_valid[obj_id] == true first
    pub(in crate::codegen_ay::chc) fn translate_rust_dealloc(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<AllocCallResult> {
        self.translate_dealloc_object(args, modified_locals, false)
    }

    /// Translate `libc::free(ptr)` to CHC constraints.
    ///
    /// Same free model as [`Self::translate_rust_dealloc`] — obj_valid is
    /// cleared, the double-free and base-address obligations are emitted — with
    /// the two differences the C contract dictates:
    ///
    /// - `free` carries NO size/align: those are the allocator's record, not the
    ///   caller's. That is not an unresolved argument, so no sound-fallback is
    ///   recorded for it and the Rust-only size-mismatch obligation is not
    ///   applicable (it would compare the recorded size against nothing).
    /// - `free(NULL)` is a defined no-op, so every obligation is exempted on a
    ///   null pointer instead of reporting a double free.
    ///
    /// Part of #3175.
    pub(in crate::codegen_ay::chc) fn translate_libc_free(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<AllocCallResult> {
        self.translate_dealloc_object(args, modified_locals, true)
    }

    /// Shared free model behind `translate_rust_dealloc` / `translate_libc_free`.
    ///
    /// `libc_free` selects the C contract described on `translate_libc_free`;
    /// `false` reproduces the Rust deallocator contract byte-for-byte.
    fn translate_dealloc_object(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        libc_free: bool,
    ) -> Option<AllocCallResult> {
        // Address-vs-value: which argument is the FREED ADDRESS is read off the
        // Rust types in MIR, never off a width.
        //
        // Fix #3184 recorded that the width heuristic had already failed once —
        // `&Global` is a 64-bit pointer-width bitvec too, so the allocator
        // reference was freed instead of the allocation — and bolted a MIR-type
        // veto ABOVE the width test. Width still decided every remaining case:
        // with `__rust_dealloc(ptr, size, align)`, a `ptr` operand that failed to
        // translate (or translated to any non-`bv64` sort) fell through to the
        // `deallocate(&self, ptr, layout)` arm and named `size` — a VALUE — as
        // the address to free, shifting the `(size, align)` window with it.
        //
        // `allocator_pointer_arg_idx` replaces the test outright: a raw pointer
        // or a `NonNull`/`Unique` is the pointer, a reference (`&self`) is not,
        // and when no argument is pointer-typed the stub fails closed rather than
        // freeing whichever operand happened to be 64 bits wide.
        let Some(ptr_arg_idx) = self.allocator_pointer_arg_idx(args) else {
            warn!(
                "RustDealloc: no pointer-typed argument in MIR; falling back to unconstrained call"
            );
            self.record_sound_fallback_reason("dealloc_pointer_arg_unresolved");
            return None;
        };
        let size_align_start = ptr_arg_idx + 1;
        let ptr_expr = args
            .get(ptr_arg_idx)
            .and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));

        // Supports both:
        // - __rust_dealloc(ptr, size, align)
        // - std::alloc::dealloc(ptr, layout)
        // - <Global as Allocator>::deallocate(&self, ptr, layout)
        let raw_size_or_layout_expr = args
            .get(size_align_start)
            .and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));
        let raw_align_expr = args
            .get(size_align_start + 1)
            .and_then(|arg| self.resolve_layout_operand_expr(arg, modified_locals));
        // Part of #2758: Use symbolic fallback instead of returning None when
        // dealloc args can't be resolved. Returning None leaves obj_valid unchanged,
        // silently dropping use-after-free and double-free checks.
        let (size_expr, align_expr, args_resolved) = if let Some((size, align)) =
            raw_size_or_layout_expr.clone().and_then(Self::extract_layout_size_align)
        {
            // Part of #3841: Same concrete-layout recovery as translate_rust_alloc.
            if !matches!(size.value(), ExprValue::BitVecConst { .. }) {
                if let Some(layout_arg) = args.get(size_align_start) {
                    if let Some((s, a)) = self.trace_arg_to_layout_pair(layout_arg) {
                        debug!(
                            size = s,
                            align = a,
                            "translate_rust_dealloc: recovered concrete layout from trace"
                        );
                        (
                            Expr::bitvec_const(s as u128, POINTER_WIDTH),
                            Expr::bitvec_const(a as u128, POINTER_WIDTH),
                            true,
                        )
                    } else {
                        (size, align, true)
                    }
                } else {
                    (size, align, true)
                }
            } else {
                (size, align, true)
            }
        } else if let (Some(size_expr), Some(align_expr)) =
            (raw_size_or_layout_expr, raw_align_expr)
        {
            (size_expr, align_expr, true)
        } else if libc_free {
            // `free(ptr)` has no size/align by construction — nothing failed to
            // resolve, so this is NOT a fallback. `args_resolved = false` keeps
            // the size-mismatch obligation (which has no operand to compare
            // against here) unemitted; the placeholder size is never read.
            (
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                false,
            )
        } else {
            warn!(
                "RustDealloc: failed to resolve size/align arguments; \
                 using symbolic fallback to preserve obj_valid invalidation"
            );
            self.record_sound_fallback_reason("dealloc_args_unresolved");
            let symbolic_size =
                declare_pending_var(chc_fresh_name("__dealloc_size"), Sort::bitvec(64));
            let symbolic_align =
                declare_pending_var(chc_fresh_name("__dealloc_align"), Sort::bitvec(64));
            (symbolic_size, symbolic_align, false)
        };
        let size_32 = self.coerce_to_heap_bv32(size_expr.clone()).unwrap_or_else(|| {
            warn!(
                sort = ?size_expr.sort(),
                "RustDealloc: size expression is not a bitvec; using symbolic BV32 fallback"
            );
            self.record_sound_fallback_reason("dealloc_size_bv32_coercion_failed");
            declare_pending_var(chc_fresh_name("__dealloc_size32"), Sort::bitvec(32))
        });

        let mut heap_constraints = Vec::new();
        let mut safety_checks = Vec::new();
        // Only emit size/align validity checks when args were actually resolved.
        if args_resolved {
            safety_checks.extend(self.fits_in_bv32_check(&size_expr));
            safety_checks.extend(self.nonzero_bv_check(size_expr, POINTER_WIDTH));
            safety_checks.extend(self.power_of_two_bv_check(align_expr.clone(), POINTER_WIDTH));
            safety_checks.extend(self.nonzero_bv_check(align_expr, POINTER_WIDTH));
        }

        // `free(NULL)` is a defined no-op in C. Every obligation below is a
        // property of a REAL allocation, so each one is exempted on the null
        // pointer rather than reporting a double free on a legal call. Built
        // before the pointer is consumed; `None` for the Rust ABI, where a null
        // `__rust_dealloc` argument is undefined and must stay reportable.
        let null_ptr_exemption = if libc_free {
            ptr_expr.as_ref().and_then(|ptr| {
                let width = ptr.sort().bitvec_width()?;
                Some(ptr.clone().eq(Expr::bitvec_const(0u64, width)))
            })
        } else {
            None
        };

        if let Some(ptr) = ptr_expr {
            let (raw_obj_id_expr, raw_offset_expr) = match self.split_pointer(&ptr) {
                Some(parts) => parts,
                None => {
                    return Some(AllocCallResult {
                        result: None,
                        heap_constraints,
                        safety_checks,
                        alloc_obj_id: None,
                        transition_branches: Vec::new(),
                    });
                }
            };
            let resolved_alloc_id = Self::const_obj_id_u32(&raw_obj_id_expr)
                .or_else(|| args.get(ptr_arg_idx).and_then(|arg| self.trace_arg_to_alloc_id(arg)));
            let obj_id_expr = resolved_alloc_id
                .map(|obj_id| Expr::bitvec_const(obj_id as i128, 32))
                .unwrap_or_else(|| raw_obj_id_expr.clone());

            let obj_valid_in = codegen_expr_heap::obj_valid_in();
            let obj_valid_out = codegen_expr_heap::obj_valid_out();
            let obj_size_in = codegen_expr_heap::obj_size_in();
            let obj_size_out = codegen_expr_heap::obj_size_out();
            let known_recorded_size = resolved_alloc_id
                .and_then(|obj_id| self.heap_state.heap_alloc_size(obj_id))
                .map(|size| Expr::bitvec_const(size as u128, 32));
            let recorded_size = || {
                known_recorded_size
                    .clone()
                    .unwrap_or_else(|| obj_size_in.clone().select(obj_id_expr.clone()))
            };

            // Part of #1173: Double-free detection.
            // Part of #3655: Exempt unregistered allocations (obj_size[id]==0) from
            // the double-free check. String/Vec stubs create symbolic allocations
            // without registering obj_valid[id]=true. For these objects,
            // obj_valid[id] is solver-default (can be false), causing a false CTREX.
            // When obj_size[id]==0, the allocation was never registered via
            // exchange_malloc, so the double-free check is vacuous.
            let obj_valid_check = obj_valid_in.clone().select(obj_id_expr.clone());
            let unregistered_alloc = recorded_size().eq(Expr::bitvec_const(0u64, 32));
            safety_checks.push(Expr::or(unregistered_alloc, obj_valid_check));

            // Part of #1174: Validate dealloc size matches allocation size.
            // Part of #2769: Only emit when args were resolved. On symbolic fallback
            // (args_resolved == false), size_32 is unconstrained — the solver trivially
            // satisfies `obj_size[id] == <unconstrained>`, making the check vacuous.
            // Part of #3159: Exempt zero-size allocations from size check.
            // When obj_size[id] == 0 (dyn trait or ZST allocations where the
            // compile-time size is unresolvable), the mismatch is spurious.
            if args_resolved {
                let zero = Expr::bitvec_const(0u64, 32);
                let recorded_size = recorded_size();
                let is_zero_size = recorded_size.clone().eq(zero);
                let sizes_match = recorded_size.eq(size_32);
                safety_checks.push(Expr::or(is_zero_size, sizes_match));
            }

            // Require dealloc pointer to be base address (offset == 0).
            // Part of #3655: Also exempt unregistered allocations (obj_size==0).
            let offset_zero = raw_offset_expr.eq(Expr::bitvec_const(0, 32));
            let unregistered_offset = recorded_size().eq(Expr::bitvec_const(0u64, 32));
            safety_checks.push(Expr::or(unregistered_offset, offset_zero));

            // Deallocating a stack local is undefined behavior — the free
            // argument must be a dynamic (heap) object. When the dealloc
            // pointer's obj_id is PROVABLY a concrete stack-local id, emit a
            // fail-closed memory-safety violation ("free argument must be
            // dynamic object") instead of the anti-alias constraint below.
            //
            // Soundness: the old `obj_id != stack_id` anti-alias constraint,
            // applied to a concrete stack obj_id, makes the transition body
            // contradictory (stack_id != stack_id), rendering the post-dealloc
            // path infeasible so every downstream check verifies vacuously and
            // the UB is hidden. Recording the check as a memory-safety error
            // rule instead makes `error` reachable → FAILED.
            let ptr_obj_id_is_stack_local = resolved_alloc_id
                .is_some_and(|id| self.heap_state.local_idx_for_obj_id(id).is_some());
            if ptr_obj_id_is_stack_local {
                // `false` as a must-hold condition ⇒ `¬false = true` heads the
                // per-property memory-safety error rule (unconditionally
                // reachable whenever the dealloc block is reached).
                safety_checks.push(Expr::bool_const(false));
            } else {
                // Part of #3159: Prevent dealloc from aliasing with stack locals.
                // Stack locals are valid for the entire function lifetime — they are
                // never freed. Without this constraint, a symbolic dealloc pointer
                // (common for Box<dyn Trait> due to type-punned memory arrays breaking
                // the store/load chain during unsized casts) could be assigned an
                // obj_id matching a stack local, invalidating its obj_valid and causing
                // false CTREX on subsequent access checks.
                // These are HEAP CONSTRAINTS (transition body), not safety checks,
                // because safety checks become error rules that a symbolic pointer
                // trivially triggers. Transition constraints instead restrict which
                // obj_id values the solver may assign.
                for stack_obj_id in self.heap_state.stack_local_obj_ids() {
                    let stack_id_expr = Expr::bitvec_const(stack_obj_id as i128, 32);
                    heap_constraints.push(obj_id_expr.clone().eq(stack_id_expr).not());
                }
            }

            // Constraint: obj_valid__out = store(obj_valid, obj_id, false) (mark freed)
            // Last use of obj_id_expr — moved directly.
            let freed_constraint =
                obj_valid_out.eq(obj_valid_in.store(obj_id_expr, Expr::bool_const(false)));
            heap_constraints.push(freed_constraint);

            // Preserve size metadata on dealloc (explicitly carry forward obj_size).
            heap_constraints.push(obj_size_out.eq(obj_size_in));

            // Mark metadata arrays as modified (#1100 follow-up)
            self.mark_heap_metadata_modified();

            debug!("CHC: RustDealloc - marked heap object as freed with double-free check");
        }

        if let Some(is_null) = null_ptr_exemption {
            safety_checks =
                safety_checks.into_iter().map(|check| Expr::or(is_null.clone(), check)).collect();
        }

        Some(AllocCallResult {
            result: None, // dealloc returns ()
            heap_constraints,
            safety_checks,
            alloc_obj_id: None,
            transition_branches: Vec::new(),
        })
    }
}
