// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Copy/copy_nonoverlapping intrinsics (converted from include!() per #2595).

use super::{IntoOption, StatementCodegen};
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;
use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::Operand;
use rustc_public::ty::{Allocation, ConstantKind, RigidTy, Span, TyConstKind, TyKind};
use tracing::{debug, warn};

/// Bound on how far pointer expressions are peeled when resolving a root.
pub(in crate::codegen_ay::statement) const MAX_PTR_PEEL: usize = 64;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen copy_nonoverlapping intrinsic.
    ///
    /// Copies `count` elements from `src` to `dst`. Elements are typed T,
    /// so this copies `count * size_of::<T>()` bytes total.
    ///
    /// Part of #1478: Implement copy/copy_nonoverlapping intrinsics.
    ///
    /// Memory model:
    /// - For constant counts with small total bytes: unroll byte-by-byte
    /// - For symbolic counts: guarded unrolled copy (Part of #3104)
    ///
    /// Soundness: We trust the caller that src and dst don't overlap.
    /// Emit the byte-count overflow obligation shared by `copy`,
    /// `copy_nonoverlapping` and `write_bytes`.
    ///
    /// All three compute `count * size_of::<T>()` bytes, and all three are UB
    /// when that product overflows `usize` — rustc's own codegen emits exactly
    /// this check, with exactly this message.
    ///
    /// This obligation was previously not emitted **at all**, in either lane,
    /// which is why `intrinsics/copy/copy-overflow`, `copy-nonoverlapping/
    /// copy-overflow` and `write_bytes/overflow` all reported
    /// `VERIFICATION:- SUCCESSFUL` for programs whose whole purpose is to
    /// overflow that product. A missing obligation is the worst shape a
    /// checker can have: nothing is reported, so the run looks clean.
    ///
    /// It is not enough to notice the overflow while unrolling. The constant
    /// path computes the total with `saturating_mul`, so an overflowing count
    /// saturates to a huge-but-finite value, falls past the unroll limit, and
    /// leaves through the "large constant count" fallback — a path that
    /// abstains rather than failing, and therefore keeps the proof clean.
    /// Alignment of the pointee of a raw-pointer operand, when known.
    pub(super) fn pointee_align(&self, ptr: &Operand) -> Option<usize> {
        ptr.ty(self.body.locals()).into_option().and_then(|ty| {
            if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ty.kind() {
                LayoutOf::new(pointee_ty).align_of()
            } else {
                None
            }
        })
    }

    /// Emit the alignment obligation shared by `copy`, `copy_nonoverlapping`
    /// and `write_bytes`: every pointer operand must be aligned to
    /// `align_of::<T>()` of its pointee.
    ///
    /// None of the three emitted this, so four corpus tests whose entire
    /// purpose is to pass a deliberately misaligned pointer reported
    /// `VERIFICATION:- SUCCESSFUL` with a clean qualifier. The only checks
    /// those runs produced were "pointer arithmetic overflow" — the misaligned
    /// access itself was never an obligation at all.
    ///
    /// The deref path already does exactly this
    /// (`place_deref.rs`, label `alignment_check`), and the model already
    /// ASSERTS the same fact when it mints an address
    /// (`rvalue_address_of.rs`: `addr & (align-1) == 0`), so this obligation is
    /// stated in the same terms the model already reasons in rather than in a
    /// new scheme of its own.
    ///
    /// `count == 0` is exempt because rustc exempts it: a zero-length copy
    /// never dereferences, so its pointer need not be aligned.
    pub(super) fn emit_copy_alignment_check(
        &mut self,
        ptr: &Operand,
        count: &Operand,
        align: usize,
        role: &str,
    ) {
        // align_of == 1 can never be violated; emitting it would be noise on
        // every byte copy in the corpus.
        if align <= 1 {
            return;
        }
        let Some(ptr_expr) = self.codegen_operand(ptr) else {
            return;
        };
        let ptr_bv = self.coerce_to_ptr_width(ptr_expr);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let mask = Expr::bitvec_const((align - 1) as u128, POINTER_WIDTH);
        let misaligned = ptr_bv.bvand(mask).eq(zero.clone()).not();

        let violation = match self.try_eval_const_operand(count) {
            Some(0) => return,
            Some(_) => misaligned,
            None => {
                let Some(count_expr) = self.codegen_operand(count) else {
                    return;
                };
                let count_bv = self.coerce_to_ptr_width(count_expr);
                count_bv.eq(zero).not().and(misaligned)
            }
        };

        self.record_violation_guarded_with_message(
            violation,
            "alignment_check",
            Some(format!("`{role}` must be properly aligned")),
        );
    }

    /// Alignment obligation for a single-pointer intrinsic access
    /// (`volatile_load` / `volatile_store` and their `core::ptr` wrappers):
    /// the pointer must be aligned to `align_of` of its pointee.
    ///
    /// Same shape as `emit_copy_alignment_check` without the `count == 0`
    /// exemption — these intrinsics always dereference. `volatile_load` on a
    /// misaligned `*const u32` verified SUCCESSFUL before this obligation
    /// existed (tests/expected/intrinsics/volatile_load/unaligned). The
    /// `unaligned_volatile_load/store` variants are exempt by definition —
    /// callers must not emit this check for them.
    pub(super) fn emit_intrinsic_alignment_check(&mut self, ptr: &Operand, role: &str) {
        let Some(align) = self.pointee_align(ptr) else {
            return;
        };
        if align <= 1 {
            return;
        }
        let Some(ptr_expr) = self.codegen_operand(ptr) else {
            return;
        };
        let ptr_bv = self.coerce_to_ptr_width(ptr_expr);
        let zero = Expr::bitvec_const(0u128, POINTER_WIDTH);
        let mask = Expr::bitvec_const((align - 1) as u128, POINTER_WIDTH);
        let misaligned = ptr_bv.bvand(mask).eq(zero).not();
        self.record_violation_guarded_with_message(
            misaligned,
            "alignment_check",
            Some(format!("`{role}` must be properly aligned")),
        );
    }

    /// A structural key for the ROOT of a pointer expression, with SSA
    /// definitions followed so two spellings of the same root compare equal.
    fn pointer_root_key(&self, e: &Expr, depth: usize) -> String {
        if depth == 0 {
            return format!("{:?}", e.value());
        }
        match e.value() {
            ExprValue::Var { name } => match self.ssa_concrete_values.get(name) {
                Some(def) => self.pointer_root_key(def, depth - 1),
                None => format!("var:{name}"),
            },
            ExprValue::DatatypeSelector { datatype_name, selector_name, expr } => {
                format!(
                    "sel:{datatype_name}::{selector_name}({})",
                    self.pointer_root_key(expr, depth - 1)
                )
            }
            other => format!("{other:?}"),
        }
    }

    /// Peel constant byte offsets off a pointer expression, returning the root
    /// key and the accumulated offset. `None` when the shape is not a constant
    /// displacement from a single root.
    fn resolve_ptr_offset(&self, e: &Expr, depth: usize) -> Option<(String, i128)> {
        if depth == 0 {
            return None;
        }
        match e.value() {
            ExprValue::BvAdd(a, b) => match (self.const_i128(a), self.const_i128(b)) {
                (Some(k), None) => {
                    let (root, off) = self.resolve_ptr_offset(b, depth - 1)?;
                    Some((root, off.checked_add(k)?))
                }
                (None, Some(k)) => {
                    let (root, off) = self.resolve_ptr_offset(a, depth - 1)?;
                    Some((root, off.checked_add(k)?))
                }
                _ => None,
            },
            ExprValue::BvSub(a, b) => {
                let k = self.const_i128(b)?;
                let (root, off) = self.resolve_ptr_offset(a, depth - 1)?;
                Some((root, off.checked_sub(k)?))
            }
            ExprValue::Var { name } => match self.ssa_concrete_values.get(name) {
                Some(def) => self.resolve_ptr_offset(def, depth - 1),
                None => Some((self.pointer_root_key(e, MAX_PTR_PEEL), 0)),
            },
            _ => Some((self.pointer_root_key(e, MAX_PTR_PEEL), 0)),
        }
    }

    /// Evaluate an expression to a signed byte displacement, following SSA
    /// definitions. Values at or above 2^63 are read as negative so that a
    /// `wrapping_sub`-shaped constant becomes the small negative it denotes.
    pub(in crate::codegen_ay::statement) fn const_i128(&self, e: &Expr) -> Option<i128> {
        match e.value() {
            ExprValue::BitVecConst { value, width } => {
                let raw: i128 = value.to_string().parse().ok()?;
                if *width >= 64 {
                    let modulus = 1i128 << 64;
                    if raw >= (1i128 << 63) { Some(raw - modulus) } else { Some(raw) }
                } else {
                    Some(raw)
                }
            }
            ExprValue::Var { .. } => {
                // Through `follow_ssa`, not a bare map lookup: the env fallback
                // there is what resolves an INLINED callee's locals (a `&str`
                // slice's `fld_len` arrives as exactly such a Var), and the
                // equality test is the loop guard — an unresolvable Var comes
                // back unchanged.
                let followed = self.follow_ssa(e, MAX_PTR_PEEL);
                if followed == *e { None } else { self.const_i128(&followed) }
            }
            ExprValue::BvAdd(a, b) => self.const_i128(a)?.checked_add(self.const_i128(b)?),
            ExprValue::BvSub(a, b) => self.const_i128(a)?.checked_sub(self.const_i128(b)?),
            ExprValue::BvMul(a, b) => self.const_i128(a)?.checked_mul(self.const_i128(b)?),
            _ => None,
        }
    }

    /// Emit the non-overlap obligation for `copy_nonoverlapping`.
    ///
    /// Deliberately NOT emitted for `copy`, which is memmove and PERMITS
    /// overlap; adding it there would be a wrong answer, not a stricter one.
    ///
    /// # Why this abstains instead of comparing addresses
    ///
    /// The obvious encoding — `src < dst + n && dst < src + n` on the pointer
    /// values — is a tool-destroying false-positive generator, and it was
    /// measured as one before this was written. Distinct stack address symbols
    /// are mutually unconstrained in this model: `assert!(p != q)` for two
    /// distinct locals does not hold, so "these two regions overlap" is
    /// trivially satisfiable for
    ///
    ///     copy_nonoverlapping(src.as_ptr(), dst.as_mut_ptr(), 3)
    ///
    /// on two separate arrays — i.e. essentially every real copy in real code.
    /// A same-object guard built from the heap model's `obj_id` does NOT rescue
    /// it either, because `obj_id` is a function of those same free variables.
    /// The corpus would not have caught any of this: a 108-harness slice showed
    /// zero changed verdicts under the naive check, because the corpus copies
    /// are nearly all one-object cases.
    ///
    /// So this reasons only where the answer is not in the solver's gift: when
    /// both pointers peel to the SAME root, their difference is a concrete
    /// number of bytes and overlap is decided arithmetically. When the roots
    /// differ, or either side will not peel, it emits nothing. That is
    /// incomplete — an overlap between two separately-derived pointers is
    /// missed — but incompleteness here costs a missed bug, while the naive
    /// version costs every correct program.
    pub(super) fn emit_copy_nonoverlapping_overlap_check(
        &mut self,
        src: &Operand,
        dst: &Operand,
        count: &Operand,
        element_size: usize,
    ) {
        if element_size == 0 {
            return;
        }
        let (Some(src_val), Some(dst_val)) = (self.codegen_operand(src), self.codegen_operand(dst))
        else {
            return;
        };
        let src_bv = self.coerce_to_ptr_width(src_val);
        let dst_bv = self.coerce_to_ptr_width(dst_val);

        let Some((src_root, src_off)) = self.resolve_ptr_offset(&src_bv, MAX_PTR_PEEL) else {
            return;
        };
        let Some((dst_root, dst_off)) = self.resolve_ptr_offset(&dst_bv, MAX_PTR_PEEL) else {
            return;
        };
        // Different roots: the model cannot tell us how far apart they are, and
        // guessing is the failure mode described above.
        if src_root != dst_root {
            return;
        }

        let gap = (src_off - dst_off).unsigned_abs();
        let message = Some("memcpy src/dst overlap".to_string());
        let label = "copy_overlap_check";

        match self.try_eval_const_operand(count) {
            Some(0) => (),
            Some(count_val) => {
                let n = (count_val as u128).saturating_mul(element_size as u128);
                if gap < n {
                    self.record_violation_guarded_with_message(
                        Expr::bool_const(true),
                        label,
                        message,
                    );
                }
            }
            None => {
                // Symbolic count: the offsets are still concrete, so the only
                // symbolic term is n. Overlap iff n > |src_off - dst_off|.
                let Some(count_expr) = self.codegen_operand(count) else {
                    return;
                };
                let count_bv = self.coerce_to_ptr_width(count_expr);
                let elem = Expr::bitvec_const(element_size as u128, POINTER_WIDTH);
                let n = count_bv.bvmul(elem);
                let gap_expr = Expr::bitvec_const(gap, POINTER_WIDTH);
                self.record_violation_guarded_with_message(n.bvugt(gap_expr), label, message);
            }
        }
    }

    /// Byte extent of the object a pointer root denotes, when the root states
    /// it structurally.
    ///
    /// A slice/array reaches a copy site as `fld_ptr(Slice_T_mk(ptr, len, data))`.
    /// That constructor CARRIES the length, and the data array's element sort
    /// carries the element width, so `len * elem_bytes` is the object's extent —
    /// known exactly, at codegen time, without consulting the solver and without
    /// asking the provenance tables anything.
    ///
    /// This is what makes the region check safe. The alternative sources of
    /// object extent are both unusable here: `obj_size` is written only by
    /// `heap_alloc`, so a stack array has no entry and the query would be
    /// unconstrained; and `ref_pointees` is flow-insensitive last-writer-wins,
    /// so a pointer merged from two branches resolves to whichever arm was
    /// traversed last and the obligation then fails UB-free code.
    /// Follow an SSA variable to its defining expression.
    ///
    /// Two maps are consulted, because the value can live in either:
    /// `ssa_concrete_values` is keyed by the SSA name (`base_N`), while an
    /// INLINED callee's parameter is seeded by `seed_inline_params` through
    /// `assign_value_to_place`, which lands in `current_env` keyed by the BASE
    /// name. A `&str`'s `as_ptr` receiver is exactly that case: the Var is
    /// `...as_ptr#f0::local_2_0`, the Slice constructor sits in the env under
    /// `...as_ptr#f0::local_2`, and without the fallback the extent lookup
    /// misses an object whose length is right there.
    ///
    /// The suffix strip is the exact inverse of `ssa_name_from_base`
    /// (`{base}_{version}`), and the sort-equality guard rejects a base name
    /// that collided with an unrelated env entry — inheriting a wrong value
    /// here would silently mis-scale every extent computed from it.
    pub(in crate::codegen_ay::statement) fn follow_ssa(&self, e: &Expr, depth: usize) -> Expr {
        if depth == 0 {
            return e.clone();
        }
        match e.value() {
            ExprValue::Var { name } => {
                if let Some(def) = self.ssa_concrete_values.get(name) {
                    return self.follow_ssa(def, depth - 1);
                }
                if let Some((base, version)) = name.rsplit_once('_')
                    && version.parse::<u32>().is_ok()
                    && let Some(current) = self.env_lookup(base)
                    && current.sort() == e.sort()
                    && !matches!(current.value(), ExprValue::Var { name: n } if n == name)
                {
                    return self.follow_ssa(&current.clone(), depth - 1);
                }
                e.clone()
            }
            _ => e.clone(),
        }
    }

    /// The dereferenced object must contain the whole accessed range.
    ///
    /// The existing deref battery does not cover this. `heap_is_allocated`
    /// compares 1 MiB HEAP_STRIDE bucket identity, so a pointer twelve bytes
    /// past a twelve-byte stack array is still "in the same allocation" and
    /// passes; and `obj_size` is written only by `heap_alloc`, so a stack
    /// object has no recorded extent to compare against at all. The result was
    /// that `*ptr.add(3)` on a `[i32; 3]` produced no bounds obligation — the
    /// failure it did report came from `offset_result_overflow`, i.e. numeric
    /// wraparound of the address, which is a different question and fires on
    /// the LEGAL one-past-the-end computation rather than on the illegal read.
    ///
    /// Decided arithmetically or not at all, exactly like the copy-family
    /// region check: the root must state its own extent (a slice or Vec
    /// constructor carries `fld_len` and its element width) and the
    /// displacement from it must peel to a constant. Anything else emits
    /// nothing.
    ///
    /// That restraint is the whole design. Comparing the dereferenced address
    /// against a symbolic object base would be satisfiable for almost any
    /// program, because distinct stack address symbols are mutually
    /// unconstrained here — `assert!(p != q)` for two distinct live locals does
    /// not hold. A deref check that fired spuriously would be far worse than
    /// this one being incomplete: it sits on every pointer access in every
    /// harness.
    pub(in crate::codegen_ay::statement) fn emit_deref_object_bounds_check(
        &mut self,
        addr: &Expr,
        access_size: usize,
    ) {
        if access_size == 0 {
            return;
        }
        let Some((root, offset)) = self.resolve_ptr_root_expr(addr, MAX_PTR_PEEL) else {
            return;
        };
        let Some(extent) = self.root_object_extent(&root) else {
            return;
        };
        let message = Some("dereference failure: pointer outside object bounds".to_string());
        let label = "pointer_bounds_check";

        if offset < 0 {
            self.record_violation_guarded_with_message(Expr::bool_const(true), label, message);
            return;
        }
        if (offset as u128).saturating_add(access_size as u128) > extent {
            self.record_violation_guarded_with_message(Expr::bool_const(true), label, message);
        }
    }

    pub(in crate::codegen_ay::statement) fn root_object_extent(&self, root: &Expr) -> Option<u128> {
        let root = self.follow_ssa(root, MAX_PTR_PEEL);
        let ExprValue::DatatypeSelector { selector_name, expr, .. } = root.value() else {
            return None;
        };
        if selector_name != "fld_ptr" {
            return None;
        }
        // The selector's operand normally arrives as an SSA variable, not as the
        // constructor itself; follow the chain before matching.
        let built = self.follow_ssa(expr, MAX_PTR_PEEL);
        let ExprValue::DatatypeConstructor { args, .. } = built.value() else {
            return None;
        };
        // Read the fields BY NAME. Reading them positionally as
        // `[ptr, len, data]` is the three-field `Slice_T_mk` layout and is
        // wrong for `Vec_T_mk`, which has four — `(fld_ptr, fld_len, fld_cap,
        // fld_data)`. Under the positional read every Vec landed on `fld_cap`
        // where the data array was expected, `array_sort()` returned None, and
        // the extent silently came back unknown for every Vec in the corpus.
        let decl = &built.sort().datatype_sort()?.constructors.first()?.fields;
        let index_of = |want: &str| decl.iter().position(|f| f.name == want);
        let len = self.const_i128(args.get(index_of("fld_len")?)?)?;
        if len < 0 {
            return None;
        }
        let elem_bits =
            args.get(index_of("fld_data")?)?.sort().array_sort()?.element_sort.bitvec_width()?;
        let elem_bytes = u128::from(elem_bits) / 8;
        if elem_bytes == 0 {
            return None;
        }
        (len as u128).checked_mul(elem_bytes)
    }

    /// Emit the region-validity obligation: the whole `[ptr, ptr + n)` range
    /// must lie inside the object the pointer denotes.
    ///
    /// Only fires where the answer is arithmetic — a root that states its own
    /// extent and a concrete displacement from it. Anything else abstains,
    /// which costs a missed bug rather than a wrongly-rejected program.
    pub(super) fn emit_copy_region_validity_check(
        &mut self,
        ptr: &Operand,
        count: &Operand,
        element_size: usize,
        message: &str,
    ) {
        if element_size == 0 {
            return;
        }
        let Some(ptr_val) = self.codegen_operand(ptr) else {
            return;
        };
        let ptr_bv = self.coerce_to_ptr_width(ptr_val);
        let Some((root, offset)) = self.resolve_ptr_root_expr(&ptr_bv, MAX_PTR_PEEL) else {
            return;
        };
        let Some(extent) = self.root_object_extent(&root) else {
            return;
        };

        // A displacement before the object is out of range whatever the length.
        if offset < 0 {
            self.record_violation_guarded_with_message(
                Expr::bool_const(true),
                "region_validity_check",
                Some(message.to_string()),
            );
            return;
        }
        let offset = offset as u128;

        match self.try_eval_const_operand(count) {
            Some(0) => (),
            Some(count_val) => {
                let n = (count_val as u128).saturating_mul(element_size as u128);
                if offset.saturating_add(n) > extent {
                    self.record_violation_guarded_with_message(
                        Expr::bool_const(true),
                        "region_validity_check",
                        Some(message.to_string()),
                    );
                }
            }
            None => {
                // Symbolic count, concrete offset and extent: the range escapes
                // the object exactly when n > extent - offset.
                let room = extent.saturating_sub(offset);
                let Some(count_expr) = self.codegen_operand(count) else {
                    return;
                };
                let count_bv = self.coerce_to_ptr_width(count_expr);
                let elem = Expr::bitvec_const(element_size as u128, POINTER_WIDTH);
                let n = count_bv.bvmul(elem);
                let room_expr = Expr::bitvec_const(room, POINTER_WIDTH);
                self.record_violation_guarded_with_message(
                    n.bvugt(room_expr),
                    "region_validity_check",
                    Some(message.to_string()),
                );
            }
        }
    }

    /// As `resolve_ptr_offset`, but hands back the root expression itself.
    pub(in crate::codegen_ay::statement) fn resolve_ptr_root_expr(
        &self,
        e: &Expr,
        depth: usize,
    ) -> Option<(Expr, i128)> {
        if depth == 0 {
            return None;
        }
        match e.value() {
            ExprValue::BvAdd(a, b) => match (self.const_i128(a), self.const_i128(b)) {
                (Some(k), None) => {
                    let (r, off) = self.resolve_ptr_root_expr(b, depth - 1)?;
                    Some((r, off.checked_add(k)?))
                }
                (None, Some(k)) => {
                    let (r, off) = self.resolve_ptr_root_expr(a, depth - 1)?;
                    Some((r, off.checked_add(k)?))
                }
                _ => None,
            },
            ExprValue::BvSub(a, b) => {
                let k = self.const_i128(b)?;
                let (r, off) = self.resolve_ptr_root_expr(a, depth - 1)?;
                Some((r, off.checked_sub(k)?))
            }
            ExprValue::Var { name } => match self.ssa_concrete_values.get(name) {
                Some(def) => self.resolve_ptr_root_expr(def, depth - 1),
                None => Some((e.clone(), 0)),
            },
            _ => Some((e.clone(), 0)),
        }
    }

    pub(super) fn emit_copy_byte_count_overflow_check(
        &mut self,
        count: &Operand,
        element_size: usize,
        intrinsic: &str,
    ) {
        // A zero-sized element makes the product zero for every count, so
        // there is nothing to overflow. Guard explicitly: it is also the
        // divisor below.
        if element_size <= 1 {
            return;
        }
        let message =
            Some(format!("{intrinsic}: attempt to compute number in bytes which would overflow"));
        let label = "copy_byte_count_overflow";

        // The largest count whose byte product still fits in a usize.
        let max_count = (u128::from(u64::MAX) >> (64 - POINTER_WIDTH)) / element_size as u128;

        match self.try_eval_const_operand(count) {
            Some(count_val) => {
                // Constant count: decide it here rather than asking the solver.
                // Emitting a `false` violation for the safe case would still
                // create a discharged obligation, which is the honest shape —
                // but it also costs a check on every copy in every harness, so
                // only the overflowing case is recorded.
                if (count_val as u128) > max_count {
                    let always = Expr::bool_const(true);
                    self.record_violation_guarded_with_message(always, label, message);
                }
            }
            None => {
                // Symbolic count: `count * element_size` overflows exactly when
                // `count > usize::MAX / element_size`. Expressed as a compare
                // against a constant rather than a multiply-and-detect, so the
                // obligation stays linear.
                if let Some(count_expr) = self.codegen_operand(count) {
                    let count_bv = self.coerce_to_ptr_width(count_expr);
                    let limit = Expr::bitvec_const(max_count, POINTER_WIDTH);
                    self.record_violation_guarded_with_message(
                        count_bv.bvugt(limit),
                        label,
                        message,
                    );
                }
            }
        }
    }

    pub(super) fn codegen_copy_nonoverlapping(
        &mut self,
        src: &Operand,
        dst: &Operand,
        count: &Operand,
        span: Span,
    ) {
        // Get the element size from the src pointer type
        let element_size = src.ty(self.body.locals())
            .into_option()
            .and_then(|ty| {
                // src is a pointer *const T or *mut T - get the pointee type
                if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ty.kind() {
                    LayoutOf::new(pointee_ty).size_of()
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                // Warn when we can't determine element size - defaulting to 1 could be wrong
                warn!(
                    "codegen_copy_nonoverlapping: couldn't determine element size, defaulting to 1 byte"
                );
                1
            });

        // Try to get constant count
        let count_const = self.try_eval_const_operand(count);

        debug!(
            "codegen_copy_nonoverlapping: element_size={}, span={:?}, count_const={:?}, count={:?}",
            element_size, span, count_const, count
        );

        // UB when count * size_of::<T>() overflows a usize, regardless of what
        // the unroll below decides to do with the copy itself.
        self.emit_copy_byte_count_overflow_check(count, element_size, "copy_nonoverlapping");

        // Both operands must be aligned for the pointee type. Emitted here, not
        // inside the unroll, so the obligation exists on every tail — including
        // the large-count path that abstains from modelling the copy at all.
        if let Some(align) = self.pointee_align(src) {
            self.emit_copy_alignment_check(src, count, align, "src");
            self.emit_copy_alignment_check(dst, count, align, "dst");
        }

        // The whole copied range must lie inside each object.
        self.emit_copy_region_validity_check(
            src, count, element_size, "memcpy source region readable",
        );
        self.emit_copy_region_validity_check(
            dst, count, element_size, "memcpy destination region writeable",
        );

        // copy_nonoverlapping only: memmove (`codegen_copy`) permits overlap.
        self.emit_copy_nonoverlapping_overlap_check(src, dst, count, element_size);

        // Defer location formatting until an error path needs it (Part of #2267).
        let location = || format!("{:?}", span);

        // Get src and dst pointer expressions
        let (Some(src_val), Some(dst_val)) = (self.codegen_operand(src), self.codegen_operand(dst))
        else {
            self.ctx.unsupported("CopyNonOverlapping: failed to codegen pointers", location());
            return;
        };

        // Coerce to pointer width
        let src_ptr = self.coerce_to_ptr_width(src_val);
        let dst_ptr = self.coerce_to_ptr_width(dst_val);

        // Maximum bytes to unroll (avoid explosion for large copies)
        const MAX_UNROLL_BYTES: usize = 128;

        match count_const {
            Some(count_val) => {
                // Constant count - unroll the copy
                let total_bytes = count_val.saturating_mul(element_size);

                if total_bytes == 0 {
                    // Zero-byte copy is a no-op
                    debug!("codegen_copy_nonoverlapping: zero-byte copy, skipping");
                    return;
                }

                if total_bytes <= MAX_UNROLL_BYTES {
                    // Unroll byte-by-byte
                    debug!("codegen_copy_nonoverlapping: unrolling {} bytes", total_bytes);
                    for i in 0..total_bytes {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let src_addr = src_ptr.clone().bvadd(offset.clone());
                        let dst_addr = dst_ptr.clone().bvadd(offset);

                        // Load byte from src, store to dst
                        let byte = self.ctx.load_memory(src_addr);
                        self.ctx.store_memory(dst_addr, byte);
                    }
                } else {
                    // Too large to unroll - treat as unsupported with warning
                    self.ctx.unsupported_with_fallback(
                        "CopyNonOverlapping with large constant count",
                        format!(
                            "{} ({} bytes > {} limit)",
                            location(),
                            total_bytes,
                            MAX_UNROLL_BYTES
                        ),
                    );
                }
            }
            None => {
                // Symbolic count - guarded unrolled copy (Part of #3104).
                //
                // For each byte offset i in 0..MAX_UNROLL_BYTES, conditionally copy
                // src[i] to dst[i] when i < count * element_size. When the guard is
                // false, the destination byte is left unchanged.
                //
                // Soundness: correct for total_bytes <= MAX_UNROLL_BYTES. If the
                // solver explores paths where count * element_size > MAX_UNROLL_BYTES,
                // bytes beyond the limit are unchanged (truncation). For harnesses
                // with assume(count <= N) where N * element_size <= 128, this is
                // exact. Falls back to unsupported_with_fallback when even count=1
                // exceeds the limit (element_size > MAX_UNROLL_BYTES).
                if element_size > MAX_UNROLL_BYTES {
                    self.ctx.unsupported_with_fallback(
                        "CopyNonOverlapping with symbolic count (element too large for unroll)",
                        format!(
                            "{} (element_size={} > {} limit)",
                            location(),
                            element_size,
                            MAX_UNROLL_BYTES
                        ),
                    );
                    return;
                }
                let count_expr = self.codegen_operand(count);
                if let Some(count_bv) = count_expr {
                    let count_bv = self.coerce_to_ptr_width(count_bv);
                    let elem_size_bv = Expr::bitvec_const(element_size as u128, POINTER_WIDTH);
                    let total_bv = count_bv.bvmul(elem_size_bv);

                    debug!(
                        "codegen_copy_nonoverlapping: guarded unroll for symbolic count, \
                         element_size={}, max_bytes={}",
                        element_size, MAX_UNROLL_BYTES
                    );

                    for i in 0..MAX_UNROLL_BYTES {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        // Guard: total bytes > i (i.e., this byte is within the copy range)
                        let guard = total_bv.clone().bvugt(offset.clone());
                        let src_addr = src_ptr.clone().bvadd(offset.clone());
                        let dst_addr = dst_ptr.clone().bvadd(offset);

                        let src_byte = self.ctx.load_memory(src_addr);
                        let dst_byte = self.ctx.load_memory(dst_addr.clone());
                        // If guard: copy src byte; else: preserve dst byte
                        let value = Expr::ite(guard, src_byte, dst_byte);
                        self.ctx.store_memory(dst_addr, value);
                    }
                } else {
                    // Count operand failed to codegen - fall back to unsupported
                    self.ctx.unsupported_with_fallback(
                        "CopyNonOverlapping with symbolic count (operand codegen failed)",
                        location(),
                    );
                }
            }
        }
    }

    /// Codegen copy intrinsic (overlapping allowed).
    ///
    /// Copies `count` elements from `src` to `dst` with memmove semantics.
    /// Elements are typed T, so this copies `count * size_of::<T>()` bytes total.
    ///
    /// Part of #1479: Implement copy intrinsic for function call paths.
    ///
    /// Memory model:
    /// - For constant counts with small total bytes: load into temporaries, then store
    /// - For symbolic counts: two-phase guarded unrolled copy (Part of #3104)
    pub(super) fn codegen_copy(
        &mut self,
        src: &Operand,
        dst: &Operand,
        count: &Operand,
        span: Span,
    ) {
        // Get the element size from the src pointer type
        let element_size = src
            .ty(self.body.locals())
            .into_option()
            .and_then(|ty| {
                // src is a pointer *const T or *mut T - get the pointee type
                if let TyKind::RigidTy(RigidTy::RawPtr(pointee_ty, _)) = ty.kind() {
                    LayoutOf::new(pointee_ty).size_of()
                } else {
                    None
                }
            })
            .unwrap_or_else(|| {
                warn!("codegen_copy: couldn't determine element size, defaulting to 1 byte");
                1
            });

        // Try to get constant count
        let count_const = self.try_eval_const_operand(count);

        debug!(
            "codegen_copy: element_size={}, span={:?}, count_const={:?}, count={:?}",
            element_size, span, count_const, count
        );

        // UB when count * size_of::<T>() overflows a usize, regardless of what
        // the unroll below decides to do with the copy itself.
        self.emit_copy_byte_count_overflow_check(count, element_size, "copy");

        // Both operands must be aligned for the pointee type. Emitted here, not
        // inside the unroll, so the obligation exists on every tail — including
        // the large-count path that abstains from modelling the copy at all.
        if let Some(align) = self.pointee_align(src) {
            self.emit_copy_alignment_check(src, count, align, "src");
            self.emit_copy_alignment_check(dst, count, align, "dst");
        }

        // The whole copied range must lie inside each object.
        self.emit_copy_region_validity_check(
            src, count, element_size, "memmove source region readable",
        );
        self.emit_copy_region_validity_check(
            dst, count, element_size, "memmove destination region writeable",
        );

        // Defer location formatting until an error path needs it (Part of #2267).
        let location = || format!("{:?}", span);

        // Get src and dst pointer expressions
        let (Some(src_val), Some(dst_val)) = (self.codegen_operand(src), self.codegen_operand(dst))
        else {
            self.ctx.unsupported("Copy: failed to codegen pointers", location());
            return;
        };

        let src_ptr = self.coerce_to_ptr_width(src_val);
        let dst_ptr = self.coerce_to_ptr_width(dst_val);

        // Maximum bytes to unroll (avoid explosion for large copies)
        const MAX_UNROLL_BYTES: usize = 128;

        match count_const {
            Some(count_val) => {
                let total_bytes = count_val.saturating_mul(element_size);

                if total_bytes == 0 {
                    debug!("codegen_copy: zero-byte copy, skipping");
                    return;
                }

                if total_bytes <= MAX_UNROLL_BYTES {
                    debug!("codegen_copy: unrolling {} bytes", total_bytes);

                    let mut temp_bytes = Vec::with_capacity(total_bytes);
                    for i in 0..total_bytes {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let src_addr = src_ptr.clone().bvadd(offset);
                        let byte = self.ctx.load_memory(src_addr);
                        temp_bytes.push(byte);
                    }

                    for (i, byte) in temp_bytes.into_iter().enumerate() {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let dst_addr = dst_ptr.clone().bvadd(offset);
                        self.ctx.store_memory(dst_addr, byte);
                    }
                } else {
                    self.ctx.unsupported_with_fallback(
                        "Copy with large constant count",
                        format!(
                            "{} ({} bytes > {} limit)",
                            location(),
                            total_bytes,
                            MAX_UNROLL_BYTES
                        ),
                    );
                }
            }
            None => {
                // Symbolic count - guarded unrolled copy with overlap safety (Part of #3104).
                //
                // For overlapping copy (memmove semantics), load ALL source bytes first
                // into temporaries, then conditionally store to destination. This prevents
                // reads from seeing partially-written destination values.
                //
                // Soundness: see codegen_copy_nonoverlapping for truncation caveat.
                if element_size > MAX_UNROLL_BYTES {
                    self.ctx.unsupported_with_fallback(
                        "Copy with symbolic count (element too large for unroll)",
                        format!(
                            "{} (element_size={} > {} limit)",
                            location(),
                            element_size,
                            MAX_UNROLL_BYTES
                        ),
                    );
                    return;
                }
                let count_expr = self.codegen_operand(count);
                if let Some(count_bv) = count_expr {
                    let count_bv = self.coerce_to_ptr_width(count_bv);
                    let elem_size_bv = Expr::bitvec_const(element_size as u128, POINTER_WIDTH);
                    let total_bv = count_bv.bvmul(elem_size_bv);

                    debug!(
                        "codegen_copy: guarded unroll for symbolic count, \
                         element_size={}, max_bytes={}",
                        element_size, MAX_UNROLL_BYTES
                    );

                    // Phase 1: Load all source bytes into temporaries
                    let mut temp_bytes = Vec::with_capacity(MAX_UNROLL_BYTES);
                    for i in 0..MAX_UNROLL_BYTES {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let src_addr = src_ptr.clone().bvadd(offset);
                        temp_bytes.push(self.ctx.load_memory(src_addr));
                    }

                    // Phase 2: Conditionally store to destination
                    for (i, src_byte) in temp_bytes.into_iter().enumerate() {
                        let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                        let guard = total_bv.clone().bvugt(offset.clone());
                        let dst_addr = dst_ptr.clone().bvadd(offset);
                        let dst_byte = self.ctx.load_memory(dst_addr.clone());
                        let value = Expr::ite(guard, src_byte, dst_byte);
                        self.ctx.store_memory(dst_addr, value);
                    }
                } else {
                    self.ctx.unsupported_with_fallback(
                        "Copy with symbolic count (operand codegen failed)",
                        location(),
                    );
                }
            }
        }
    }

    /// Try to evaluate an operand as a constant usize.
    pub(super) fn try_eval_const_operand(&self, operand: &Operand) -> Option<usize> {
        match operand {
            Operand::Constant(const_op) => {
                let mir_const = &const_op.const_;
                let ty = mir_const.ty();

                // Helper to extract value from allocation based on type
                let extract_from_alloc =
                    |alloc: &Allocation, ty: rustc_public::ty::Ty| -> Option<usize> {
                        match ty.kind() {
                            TyKind::RigidTy(RigidTy::Uint(_)) => {
                                alloc.read_uint().into_option().and_then(|v| v.try_into().ok())
                            }
                            TyKind::RigidTy(RigidTy::Int(_)) => {
                                // Also handle signed integers (for completeness)
                                let v = alloc.read_int().into_option()?;
                                if v >= 0 { usize::try_from(v).ok() } else { None }
                            }
                            _ => None, // external enum: TyKind
                        }
                    };

                // Extract value from constant
                match mir_const.kind() {
                    ConstantKind::Allocated(alloc) => extract_from_alloc(alloc, ty),
                    ConstantKind::Ty(ty_const) => match ty_const.kind() {
                        TyConstKind::Value(value_ty, alloc) => extract_from_alloc(alloc, *value_ty),
                        _ => None, // external enum: TyConstKind
                    },
                    _ => None, // external enum: ConstantKind
                }
            }
            Operand::Copy(_) | Operand::Move(_) => {
                // Copy/Move operands are not constants
                None
            }
        }
    }
}

// write_bytes intrinsic moved to codegen_write_bytes.rs per #4206.
