// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct `libc::{malloc, free, memset}` call handling for CHC.
//!
//! These three are foreign items, so without a model they reach the
//! undefined-foreign `error()` emission in `codegen_call.rs` and make every
//! harness that touches C allocation fail on a counterexample that names no
//! user assertion. They are not opaque, though: each has a contract that the
//! encoder ALREADY models for the Rust allocator, so the fix is to route them
//! to that model rather than to weaken the fail-closed net around them.
//!
//! - `malloc(size)` → the heap-object model with the callee's fixed alignment
//!   ([`ChcCtx::translate_libc_malloc`]): a fresh, non-null, uninitialized
//!   object of `size` bytes, registered in `obj_valid` / `obj_size`.
//! - `free(ptr)` → the deallocation model ([`ChcCtx::translate_libc_free`]):
//!   clears `obj_valid`, KEEPS the double-free and base-address obligations,
//!   and exempts the defined `free(NULL)` no-op.
//! - `memset(dst, c, n)` → an exact byte-fill of the destination object, and
//!   ONLY when the fill is exactly representable (see
//!   [`CallDispatchLibcMem::try_dispatch_call_libc_memset`]); every other shape
//!   returns `false` and keeps the existing fail-closed `error()`.
//!
//! Precedent for the shape of this module: `codegen_call_posix_memalign.rs`
//! (#3736), which models the one other direct libc allocation entry point.
//!
//! Part of #3175.

use ay_bindings::{Expr, Sort};
use tracing::debug;

use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::chc::codegen_ctx::types::AllocCallResult;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_rules::CodegenRules;

/// Largest `memset` span encoded as an exact fill. A fill is one store per cell
/// per overlay array, so the bound keeps the rule size linear in a small
/// constant; a longer span is not modelled at all (fail-closed `error()`)
/// rather than modelled partially, because a partial fill would leave the tail
/// bytes at their PRE-`memset` values — a stale read, which is the one failure
/// mode that can hide a bug.
const MAX_MEMSET_FILL_BYTES: usize = 64;

pub(in crate::codegen_ay::chc) trait CallDispatchLibcMem {
    fn try_dispatch_call_libc_mem(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
    fn try_dispatch_call_libc_malloc(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
    fn try_dispatch_call_libc_free(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
    fn try_dispatch_call_libc_memset(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchLibcMem for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_libc_mem(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        match callee_path.as_deref() {
            Some("libc::malloc") => self.try_dispatch_call_libc_malloc(dcx),
            Some("libc::free") => self.try_dispatch_call_libc_free(dcx),
            Some("libc::memset") => self.try_dispatch_call_libc_memset(dcx),
            _ => false,
        }
    }

    /// `libc::malloc(size) -> *mut c_void`.
    ///
    /// Emits the same transition the Rust allocator stub emits: the destination
    /// is bound to a fresh object's base address, the heap metadata store
    /// constraints ride the rule, and the allocation preconditions are emitted
    /// as error rules. The result is non-null by construction (object ids start
    /// above zero), which is what makes the `is_null()` guard in C-FFI code
    /// provable instead of a spurious counterexample.
    fn try_dispatch_call_libc_malloc(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            return false;
        };
        if dcx.args.len() != 1 {
            return false;
        }
        let dest_local: usize = dcx.destination.local;
        // Resolve the destination BEFORE allocating an object id, so a bail-out
        // cannot leave a registered-but-unreferenced allocation behind.
        if self.resolve_destination(dest_local).is_none() {
            return false;
        }

        let Some(alloc) = self.translate_libc_malloc(dcx.args, dcx.modified_locals) else {
            return false;
        };
        let AllocCallResult {
            result: Some(ptr_expr),
            heap_constraints,
            safety_checks,
            alloc_obj_id,
            transition_branches,
        } = alloc
        else {
            return false;
        };
        if !transition_branches.is_empty() {
            return false;
        }
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let dest_sort = dest_var.sort().clone();
        let Some(dest_eq) = self.make_coerced_eq_constraint(
            &dest_var,
            ptr_expr,
            &dest_sort,
            dest_local,
            "libc_malloc",
        ) else {
            return false;
        };

        if self.memory_safety_checks {
            for check in safety_checks {
                self.emit_error_rule_for_condition(
                    dcx.from_app,
                    check,
                    dcx.stmt_constraints,
                    dcx.bb_idx,
                );
            }
        }

        let mut constraints = vec![dest_eq];
        constraints.extend(heap_constraints);
        // MEMUB-24/25/27: malloc returns UNINITIALIZED bytes — the same shadow
        // effect `__rust_alloc` carries, not the zeroed one.
        self.append_alloc_shadow_constraints(StubKind::RustAlloc, alloc_obj_id, &mut constraints);
        self.emit_alloc_pending_checks(dcx.from_app, dcx.stmt_constraints, *target);
        self.record_alloc_dest(dest_local, alloc_obj_id);
        if let Some(obj_id) = alloc_obj_id {
            // Raw C storage: readers of this object go through the memory
            // arrays only, which is the precondition the `memset` fill below
            // relies on.
            self.heap_state.mark_c_malloc_obj(obj_id);
        }

        let out = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(dcx.from_app, *target, &out, dcx.stmt_constraints, constraints);
        debug!(obj_id = ?alloc_obj_id, "libc_mem: modeled direct libc::malloc call");
        true
    }

    /// `libc::free(ptr)`.
    ///
    /// The double-free / base-address obligations come from the shared free
    /// model and are emitted as error rules here, so a use-after-free or a
    /// double free stays reportable; only the size/align obligations that C's
    /// `free` does not carry are absent.
    fn try_dispatch_call_libc_free(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            return false;
        };
        if dcx.args.len() != 1 {
            return false;
        }
        let Some(dealloc) = self.translate_libc_free(dcx.args, dcx.modified_locals) else {
            return false;
        };
        let AllocCallResult { heap_constraints, safety_checks, transition_branches, .. } = dealloc;
        if !transition_branches.is_empty() {
            return false;
        }

        if self.memory_safety_checks {
            for check in safety_checks {
                self.emit_error_rule_for_condition(
                    dcx.from_app,
                    check,
                    dcx.stmt_constraints,
                    dcx.bb_idx,
                );
            }
        }
        self.emit_alloc_pending_checks(dcx.from_app, dcx.stmt_constraints, *target);

        // `free` returns `()`: no destination is written.
        let out = self.build_output_args(dcx.modified_locals, &[]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &out,
            dcx.stmt_constraints,
            heap_constraints,
        );
        debug!("libc_mem: modeled direct libc::free call");
        true
    }

    /// `libc::memset(dst, c, n) -> *mut c_void`.
    ///
    /// Encoded ONLY as an exact fill, under all of:
    /// - `c` and `n` are compile-time constants, and `n` is within
    ///   [`MAX_MEMSET_FILL_BYTES`];
    /// - `dst` resolves to an object created by the `libc::malloc` model — raw
    ///   C storage, whose only readers are the memory arrays this fill writes;
    /// - `n` equals the recorded size of that allocation, so the fill covers
    ///   the WHOLE object — no cell of the object keeps a pre-`memset` value,
    ///   and no cell outside it is touched (a wider cell straddling the end
    ///   would belong to no allocation in the split-pointer model).
    ///
    /// The remaining premise — that `dst` is that object's BASE and not an
    /// interior pointer into it — is not assumed from the provenance trace but
    /// emitted as an obligation, so a path that violates it reports instead of
    /// being encoded wrongly.
    ///
    /// Under those conditions the fill is written through the same region /
    /// type-overlay store paths an ordinary `*p = v` uses, so every reader of
    /// the object sees the filled bytes. Any other shape returns `false` and
    /// the caller's fail-closed `error()` stands: a partial or approximated
    /// fill could leave a stale value readable, which is strictly worse than
    /// reporting the call as unmodelled.
    fn try_dispatch_call_libc_memset(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            return false;
        };
        if dcx.args.len() != 3 {
            return false;
        }

        // The fill byte: C converts the `int` argument to `unsigned char`.
        let Some(fill_byte) = self
            .translate_operand_with_modified(&dcx.args[1], dcx.modified_locals)
            .and_then(|expr| ChcCtx::const_usize_from_expr(&expr))
            .map(|value| (value & 0xff) as u8)
        else {
            return false;
        };
        let Some(count) = self
            .translate_operand_with_modified(&dcx.args[2], dcx.modified_locals)
            .and_then(|expr| ChcCtx::const_usize_from_expr(&expr))
        else {
            return false;
        };
        if count == 0 || count > MAX_MEMSET_FILL_BYTES {
            return false;
        }

        // The destination object, which must be the allocation's BASE: the fill
        // below writes [base, base + n), so a destination at a non-zero offset
        // would be filled at the wrong addresses and its overrun hidden.
        let Some(dst_expr) =
            self.translate_operand_with_modified(&dcx.args[0], dcx.modified_locals)
        else {
            return false;
        };
        let obj_id = match Self::try_extract_constant_addr(&dst_expr) {
            // A constant address carries its offset explicitly — only offset 0
            // is the base, and a non-zero one is rejected outright (the alloc-id
            // trace below would answer with the same object and lose the offset).
            Some((obj_id, 0)) => obj_id,
            Some(_) => return false,
            // A symbolic address is resolved through the alloc-id trace, which
            // walks copy / move / cast hops only, so a hit names an allocation
            // this pointer IS the base of.
            None => match self.trace_arg_to_alloc_id(&dcx.args[0]) {
                Some(obj_id) => obj_id,
                None => return false,
            },
        };
        // Only a raw C allocation is filled here. Any other object has readers
        // the memory arrays do not serve, and writing the fill into the arrays
        // alone would leave those readers on the PRE-`memset` value — a proof
        // over stale data, which is the one outcome worse than the fail-closed
        // `error()` this returns to. Two such shapes are live in the encoder:
        // a stack local's address object (read through the local's state
        // VARIABLE, e.g. `memset(&mut x, 0, 4)`) and a collection's backing
        // buffer (read through the collection's logical data array, e.g.
        // `memset(v.as_mut_ptr(), 0, n)`).
        if !self.heap_state.is_c_malloc_obj(obj_id)
            || self.heap_state.local_idx_for_obj_id(obj_id).is_some()
        {
            return false;
        }
        // Whole-object gate: the recorded allocation size must equal the span.
        if self.heap_state.heap_alloc_size(obj_id) != u32::try_from(count).ok() {
            return false;
        }
        let dest_local: usize = dcx.destination.local;
        let Some((_, dest_var)) = self.resolve_destination(dest_local) else {
            return false;
        };
        let dest_sort = dest_var.sort().clone();
        if dst_expr.sort().bitvec_width() != Some(POINTER_WIDTH) {
            return false;
        }
        let Some(dest_eq) = self.make_coerced_eq_constraint(
            &dest_var,
            dst_expr.clone(),
            &dest_sort,
            dest_local,
            "libc_memset",
        ) else {
            return false;
        };

        // Every array a reader of this object can consult has to be filled; an
        // array left out would answer a post-`memset` read with its PRE-`memset`
        // contents. `None` means one of them cannot be filled cell-by-cell, so
        // the whole call is left unmodelled instead of partially modelled.
        let Some(fill_targets) = self.memset_fill_targets(obj_id) else {
            return false;
        };

        let base_addr =
            Expr::bitvec_const(i128::from(obj_id), 32).concat(Expr::bitvec_const(0, 32));

        // The fill is written at the object's BASE, so the encoding is faithful
        // only on paths where the destination pointer IS that base. The alloc-id
        // trace is provenance, not an offset proof — `known_alloc_ids` also
        // carries interior pointers (`&mut (*p).field` inherits the object) —
        // so the base identity is discharged as an obligation rather than
        // assumed: on any path where it fails, `error` is reachable and the
        // harness reports, exactly as the unmodelled call did before.
        self.emit_error_rule_for_condition(
            dcx.from_app,
            dst_expr.eq(base_addr.clone()),
            dcx.stmt_constraints,
            dcx.bb_idx,
        );

        // The written span is inside a live allocation exactly when the object
        // is still valid — `memset` after `free` must stay reportable. The
        // whole-object gate above already pins the span inside the allocation,
        // so the first byte's access checks carry the remaining obligation.
        if self.memory_safety_checks {
            let checks = self.heap_access_checks(
                base_addr.clone(),
                rustc_public::ty::Ty::unsigned_ty(rustc_public::ty::UintTy::U8),
            );
            if !checks.is_empty() {
                self.mark_heap_metadata_read();
            }
            for check in checks {
                self.emit_error_rule_for_condition(
                    dcx.from_app,
                    check,
                    dcx.stmt_constraints,
                    dcx.bb_idx,
                );
            }
        }

        // A store-to-load forward recorded before this call names a PRE-fill
        // value at an address the fill overwrites; drop the whole map before
        // writing so only this call's stores can be forwarded.
        self.heap_state.invalidate_store_forwards();
        self.emit_memset_fill_stores(&base_addr, count, fill_byte, &fill_targets);

        let mut constraints = vec![dest_eq];
        constraints.append(&mut self.heap_state.drain_store_chains(&self.diagnostics));
        // The returned pointer is the destination — the same allocation.
        self.known_alloc_ids.insert(dest_local, obj_id);

        let out = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(dcx.from_app, *target, &out, dcx.stmt_constraints, constraints);
        debug!(
            obj_id,
            count, fill_byte, "libc_mem: modeled direct libc::memset call as exact fill"
        );
        true
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Every memory array a reader of `obj_id` can consult: the object's region
    /// array and every type overlay array that exists at this point, each with
    /// the byte stride the fill walks it at.
    ///
    /// An array whose element sort has no byte image (a datatype or a nested
    /// array) is not skipped — skipping would leave its pre-`memset` entries
    /// readable. It is walked at a one-byte stride with unconstrained values
    /// instead, which is exact about WHICH cells changed and merely
    /// over-approximate about what they now hold.
    ///
    /// `None` only for a type key whose stores are stubbed out, which would
    /// silently drop the fill and record a fallback.
    ///
    /// An array created LATER cannot hold stale contents for this object: it
    /// starts as an unconstrained input, which is a sound over-approximation of
    /// the filled bytes.
    fn memset_fill_targets(&self, obj_id: u32) -> Option<Vec<MemsetFillTarget>> {
        let mut targets: Vec<MemsetFillTarget> = Vec::new();
        if let Some((_, _, region_sort)) = self.heap_state.get_region_array(obj_id) {
            let stride = memset_cell_bytes(&region_sort).unwrap_or(1);
            targets.push(MemsetFillTarget { type_key: None, elem_sort: region_sort, stride });
        }
        for type_key in self.sorted_type_array_keys() {
            if self.should_stub_spawn_type_array(type_key) {
                debug!(type_key, "libc_mem: memset refused — stubbed type array store");
                return None;
            }
            let (_, elem_sort) = &self.heap_state.type_arrays[type_key];
            let stride = memset_cell_bytes(elem_sort).unwrap_or(1);
            targets.push(MemsetFillTarget {
                type_key: Some(type_key.to_string()),
                elem_sort: elem_sort.clone(),
                stride,
            });
        }
        Some(targets)
    }

    /// Write `count` bytes of `fill_byte` from `base_addr` into every target,
    /// through the same region / type-array store paths an ordinary `*p = v`
    /// uses.
    ///
    /// A cell fully inside the span gets the exact replicated pattern. A cell
    /// only PARTIALLY inside it (an element sort wider than the remaining span)
    /// gets a fresh unconstrained value instead of being skipped — skipping
    /// would leave a pre-`memset` value readable through that array.
    fn emit_memset_fill_stores(
        &mut self,
        base_addr: &Expr,
        count: usize,
        fill_byte: u8,
        targets: &[MemsetFillTarget],
    ) {
        for target in targets {
            let MemsetFillTarget { type_key, elem_sort, stride } = target;
            let signed = type_key.as_deref().is_some_and(|key| key.starts_with('i'));
            for byte_offset in (0..count).step_by(*stride) {
                let value = if byte_offset + stride <= count {
                    Self::fill_value_for_sort(elem_sort, fill_byte)
                } else {
                    None
                }
                .unwrap_or_else(|| {
                    declare_pending_var(chc_fresh_name("__memset_opaque"), elem_sort.clone())
                });
                let addr = if byte_offset == 0 {
                    base_addr.clone()
                } else {
                    base_addr.clone().bvadd(Expr::bitvec_const(byte_offset as i128, POINTER_WIDTH))
                };
                match type_key {
                    None => self.try_store_to_region(&addr, &value, elem_sort, signed),
                    Some(key) => {
                        self.store_to_type_array(addr, value, key, elem_sort.clone(), signed);
                    }
                }
            }
        }
    }
}

/// The byte width of one cell of `elem_sort`, for stepping a fill across an
/// array. Bitvec and bool come from the shared allocator helper; a
/// floating-point cell is `exponent + significand` bits wide (f32 = 8 + 24,
/// f64 = 11 + 53). `None` for a sort with no byte image at all — a datatype, an
/// array, or an unbounded `Int` — whose array is then walked byte by byte with
/// unconstrained values.
fn memset_cell_bytes(elem_sort: &Sort) -> Option<usize> {
    ChcCtx::copyable_elem_bytes(elem_sort).or_else(|| {
        let bits = elem_sort.fp_exponent_bits()? + elem_sort.fp_significand_bits()?;
        (bits % 8 == 0).then(|| bits as usize / 8)
    })
}

/// One memory array the `memset` fill has to write, resolved before any rule is
/// emitted so an unfillable array aborts the model instead of half-writing it.
struct MemsetFillTarget {
    /// `None` is the object's region array; `Some(key)` a type overlay array.
    type_key: Option<String>,
    elem_sort: Sort,
    /// Byte distance between the cells the fill writes: the element width where
    /// the sort has one, and 1 (unconstrained values) where it does not.
    stride: usize,
}
