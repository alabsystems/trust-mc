// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Heap allocation intrinsic handlers for AY codegen (#1100).
//!
//! REQUIRES/ENSURES contracts added per #1380, verified [M]55.
//!
//! Implements the AY heap allocation model (#1100):
//! - `__rust_alloc(size, align)` -> fresh pointer with validity tracking
//! - `__rust_alloc_zeroed(size, align)` -> fresh pointer with zero-initialized memory
//! - `__rust_dealloc(ptr, size, align)` -> marks allocation as invalid
//! - `__rust_realloc(ptr, old_size, align, new_size)` -> new allocation, old invalidated
//!
//! Layout helpers extracted to `alloc_layout.rs`.
//! Pointer/NonNull helpers extracted to `alloc_ptr.rs`.

use ay_bindings::{Expr, ExprValue};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::StatementCodegen;
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

/// Fallback pointer value when operand codegen fails.
/// 0x1000 is page-aligned (4KB boundary) and non-null, making it a safe
/// fallback that satisfies NonNull constraints and typical alignment requirements.
pub(super) const FALLBACK_PTR: u64 = 0x1000;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen `std::alloc::alloc` / `__rust_alloc`.
    ///
    /// Handles two calling conventions:
    /// - __rust_alloc: `fn(size: usize, align: usize) -> *mut u8`
    /// - std::alloc::alloc: `fn(layout: Layout) -> *mut u8`
    ///
    /// REQUIRES: args.len() >= 1 (size or Layout)
    /// ENSURES: destination receives a fresh non-null pointer
    /// ENSURES: ctx.heap tracks the new allocation
    pub(super) fn codegen_rust_alloc(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_rust_alloc: need at least 1 arg, got 0");
            return None;
        }

        // Extract size and align - handles both Layout struct and raw (size, align) args
        let (size, align) = self.extract_alloc_args(args);

        let size = self.coerce_to_ptr_width(size);
        let align = self.coerce_to_ptr_width(align);

        let ptr = self.ctx.heap_alloc(size, align);
        self.assign_value_to_place(destination, ptr);

        debug!("codegen_rust_alloc: allocated heap object");
        target
    }

    /// Codegen `std::alloc::alloc_zeroed` / `__rust_alloc_zeroed`.
    ///
    /// REQUIRES: args.len() >= 1 (size or Layout)
    /// ENSURES: destination receives a fresh non-null pointer
    /// ENSURES: ctx.heap tracks the new allocation (zeroed memory)
    /// ENSURES: all bytes in [ptr, ptr+size) are constrained to zero
    pub(super) fn codegen_rust_alloc_zeroed(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_rust_alloc_zeroed: need at least 1 arg, got 0");
            return None;
        }

        let (size, align) = self.extract_alloc_args(args);
        let size = self.coerce_to_ptr_width(size);
        let align = self.coerce_to_ptr_width(align);

        let ptr = self.ctx.heap_alloc(size.clone(), align);

        // Part of #3096: Zero the allocated memory in the BMC byte-addressed model.
        // The CHC path has add_bounded_zero_init_constraints, but the BMC path
        // previously delegated to plain alloc, leaving memory unconstrained.
        self.zero_init_alloc_memory(&ptr, &size);

        self.assign_value_to_place(destination, ptr);
        debug!("codegen_rust_alloc_zeroed: allocated and zeroed heap object");
        target
    }

    /// Zero-initialize allocated memory for alloc_zeroed (Part of #3096).
    ///
    /// Emits store_memory(ptr+i, 0) for each byte in the allocation.
    /// Requires concrete size for loop unrolling; symbolic sizes fall back
    /// to unconstrained memory (over-approximation).
    ///
    /// REQUIRES: ptr is a valid heap pointer from heap_alloc
    /// ENSURES: memory[ptr+i] == 0 for i in 0..min(size, MAX_ZERO_INIT_BYTES)
    fn zero_init_alloc_memory(&mut self, ptr: &Expr, size: &Expr) {
        /// Maximum bytes to zero-init in the BMC path.
        /// Matches MAX_REALLOC_COPY_BYTES for consistency.
        const MAX_ZERO_INIT_BYTES: usize = 128;

        let concrete_size = Self::try_extract_concrete_usize(size);
        debug!(
            ?concrete_size,
            size_value = ?size.value(),
            "zero_init_alloc_memory: size expression analysis (#3107)"
        );

        match concrete_size {
            Some(sz) if sz > 0 => {
                self.ctx.init_memory();
                let zero_bytes = sz.min(MAX_ZERO_INIT_BYTES);
                let zero = Expr::bitvec_const(0u64, 8);
                for i in 0..zero_bytes {
                    let offset = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                    let addr = ptr.clone().bvadd(offset);
                    self.ctx.store_memory(addr, zero.clone());
                }
                if sz > MAX_ZERO_INIT_BYTES {
                    self.ctx.unsupported_with_fallback(
                        "alloc_zeroed_large",
                        format!(
                            "alloc_zeroed: size {} exceeds zero-init limit {}; bytes {}..{} unconstrained",
                            sz, MAX_ZERO_INIT_BYTES, MAX_ZERO_INIT_BYTES, sz
                        ),
                    );
                }
            }
            _ => {
                self.ctx.unsupported_with_fallback(
                    "alloc_zeroed_symbolic_size",
                    "alloc_zeroed with symbolic/zero size: cannot unroll zero-init loop",
                );
            }
        }
    }

    /// Try to extract a concrete `usize` from a bitvec expression.
    ///
    /// Part of #3107: Handles expression patterns that arise from Layout field
    /// extraction and pointer width coercion. Without this, `Layout::new::<i32>()`
    /// produces expressions that `zero_init_alloc_memory` cannot resolve to a
    /// concrete size, causing alloc_zeroed to fall back to unconstrained memory.
    ///
    /// Handles:
    /// - Direct `BitVecConst` (simple constant)
    /// - `BvExtract` over `BitVecConst` (Layout packed as BV128, size extracted)
    /// - `BvZeroExtend` / `BvSignExtend` over `BitVecConst` (coerce_to_ptr_width)
    fn try_extract_concrete_usize(expr: &Expr) -> Option<usize> {
        match expr.value() {
            ExprValue::BitVecConst { value, .. } => u64::try_from(value).ok().map(|v| v as usize),
            ExprValue::BvExtract { high, low, expr: inner } => {
                if let ExprValue::BitVecConst { value, .. } = inner.value() {
                    let shifted = value >> (*low as usize);
                    let width = high - low + 1;
                    let mask = (num_bigint::BigInt::from(1) << (width as usize)) - 1;
                    let extracted = shifted & mask;
                    u64::try_from(&extracted).ok().map(|v| v as usize)
                } else {
                    None
                }
            }
            ExprValue::BvZeroExtend { expr: inner, .. }
            | ExprValue::BvSignExtend { expr: inner, .. } => {
                Self::try_extract_concrete_usize(inner)
            }
            _ => None,
        }
    }

    /// Codegen `std::alloc::dealloc` / `__rust_dealloc`.
    ///
    /// Handles two calling conventions:
    /// - __rust_dealloc: `fn(ptr: *mut u8, size: usize, align: usize)` (3 args)
    /// - std::alloc::dealloc: `fn(ptr: *mut u8, layout: Layout)` (2 args)
    ///
    /// REQUIRES: args.len() >= 1 (at least ptr)
    /// REQUIRES: args[0] is a valid allocated pointer
    /// ENSURES: ctx.heap marks the allocation as invalid
    pub(super) fn codegen_rust_dealloc(
        &mut self,
        args: &[Operand],
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.is_empty() {
            debug!("codegen_rust_dealloc: need at least 1 arg (ptr), got 0");
            return None;
        }

        let ptr = if let Some(p) = self.codegen_operand(&args[0]) {
            p
        } else {
            // If ptr codegen fails, we can't safely deallocate.
            // Fail-closed: signal untranslatable rather than silently skipping
            // dealloc, which could mask use-after-free bugs (#2497).
            debug!("codegen_rust_dealloc: failed to codegen ptr — fail-closed (#2497)");
            return None;
        };

        // Extract size and align based on calling convention
        let (size, align) = if args.len() >= 3 {
            // __rust_dealloc(ptr, size, align) form
            let size = self.codegen_operand(&args[1]).unwrap_or_else(|| {
                let name = self.ctx.fresh_name("dealloc_size");
                warn!("codegen_rust_dealloc: size codegen failed, using symbolic (#2455)");
                Expr::var(name, ptr_sort())
            });
            let align = match self.codegen_operand(&args[2]) {
                Some(a) => a,
                None => {
                    warn!(
                        "codegen_rust_dealloc: align operand resolution failed \
                         — skipping dealloc, over-approximation (#3302)"
                    );
                    return target;
                }
            };
            (size, align)
        } else if args.len() == 2 {
            // std::alloc::dealloc(ptr, layout) form - extract from Layout
            self.extract_dealloc_layout_args(&args[1])
        } else {
            // Only ptr provided — size unknown, use unconstrained symbolic (#2455)
            let name = self.ctx.fresh_name("dealloc_size");
            warn!("codegen_rust_dealloc: only ptr provided, using symbolic size (#2455)");
            let align_name = self.ctx.fresh_name("dealloc_align");
            (Expr::var(name, ptr_sort()), Expr::var(align_name, ptr_sort()))
        };

        let ptr = self.coerce_to_ptr_width(ptr);
        let size = self.coerce_to_ptr_width(size);
        let align = self.coerce_to_ptr_width(align);
        self.ctx.heap_dealloc(ptr, size, align);

        debug!("codegen_rust_dealloc: deallocated");
        target
    }

    /// Codegen `std::alloc::realloc` / `__rust_realloc`.
    ///
    /// __rust_realloc signature: `fn(ptr: *mut u8, old_size: usize, align: usize, new_size: usize) -> *mut u8`
    ///
    /// REQUIRES: args.len() >= 4 (ptr, old_size, align, new_size)
    /// REQUIRES: args[0] is a valid allocated pointer
    /// ENSURES: destination receives a fresh non-null pointer
    /// ENSURES: old allocation is invalidated
    /// ENSURES: ctx.heap tracks the new allocation
    pub(super) fn codegen_rust_realloc(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if args.len() < 4 {
            debug!(
                "codegen_rust_realloc: need 4 args (ptr, old_size, align, new_size), got {}",
                args.len()
            );
            return None;
        }

        let old_ptr = if let Some(p) = self.codegen_operand(&args[0]) {
            p
        } else {
            // Fail-closed: fabricating an allocation without deallocating old_ptr
            // would leave old_ptr valid, masking use-after-free (#2497).
            debug!("codegen_rust_realloc: failed to codegen old_ptr — fail-closed (#2497)");
            return None;
        };
        let old_size = self.codegen_operand(&args[1]).unwrap_or_else(|| {
            let name = self.ctx.fresh_name("realloc_old_size");
            warn!("codegen_rust_realloc: old_size codegen failed, using symbolic (#2455)");
            Expr::var(name, ptr_sort())
        });
        let align = self.codegen_operand(&args[2]).unwrap_or_else(|| {
            let name = self.ctx.fresh_name("realloc_align");
            warn!("codegen_rust_realloc: align codegen failed, using symbolic (#3723)");
            Expr::var(name, ptr_sort())
        });
        let new_size = self.codegen_operand(&args[3]).unwrap_or_else(|| {
            let name = self.ctx.fresh_name("realloc_new_size");
            warn!("codegen_rust_realloc: new_size codegen failed, using symbolic (#2455)");
            Expr::var(name, ptr_sort())
        });

        let old_ptr = self.coerce_to_ptr_width(old_ptr);
        let old_size = self.coerce_to_ptr_width(old_size);
        let align = self.coerce_to_ptr_width(align);
        let new_size = self.coerce_to_ptr_width(new_size);

        let new_ptr = self.ctx.heap_realloc(old_ptr, old_size, align, new_size);
        self.assign_value_to_place(destination, new_ptr);

        debug!("codegen_rust_realloc: reallocated");
        target
    }

    /// Extract size and align from allocation arguments.
    ///
    /// Handles two calling conventions:
    /// - Layout struct: extract `fld_size` and use default align
    /// - Raw (size, align): use directly
    fn extract_alloc_args(&mut self, args: &[Operand]) -> (Expr, Expr) {
        let first_arg = self.codegen_operand(&args[0]).unwrap_or_else(|| {
            let name = self.ctx.fresh_name("alloc_size");
            warn!("extract_alloc_args: codegen_operand failed, using symbolic size (#2455)");
            Expr::var(name, ptr_sort())
        });

        // Check if first arg is a Layout datatype and extract fields
        if let Some((size, align)) = self.try_extract_layout_fields(&first_arg) {
            return (size, align);
        }

        // Check if it's a different datatype that we couldn't extract from
        if first_arg.sort().is_datatype() {
            tracing::warn!(
                "extract_alloc_args: unexpected datatype {:?}, treating as raw size",
                first_arg.sort()
            );
        }

        // Raw (size, align) arguments
        let size = first_arg;
        let align = if args.len() > 1 {
            self.codegen_operand(&args[1]).unwrap_or_else(|| {
                let name = self.ctx.fresh_name("alloc_align");
                warn!("extract_alloc_args: align codegen failed, using symbolic (#3302)");
                Expr::var(name, ptr_sort())
            })
        } else {
            let name = self.ctx.fresh_name("alloc_align");
            warn!("extract_alloc_args: no align arg, using symbolic (#3302)");
            Expr::var(name, ptr_sort())
        };

        (size, align)
    }

    /// Extract size and align from a Layout operand for dealloc.
    fn extract_dealloc_layout_args(&mut self, layout_op: &Operand) -> (Expr, Expr) {
        let layout = self.codegen_operand(layout_op).unwrap_or_else(|| {
            let name = self.ctx.fresh_name("dealloc_layout_size");
            warn!("extract_dealloc_layout_args: codegen_operand failed, using symbolic (#2455)");
            Expr::var(name, ptr_sort())
        });

        if let Some((size, align)) = self.try_extract_layout_fields(&layout) {
            (size, align)
        } else {
            // Not a Layout, use as size with symbolic align (#3302)
            let name = self.ctx.fresh_name("dealloc_layout_align");
            warn!("extract_dealloc_layout_args: non-Layout operand, using symbolic align (#3302)");
            (layout, Expr::var(name, ptr_sort()))
        }
    }

    /// Try to extract fld_size and fld_align from a Layout datatype expression.
    ///
    /// Returns None if the expression is not a Layout datatype.
    ///
    /// When the Layout expression is a concrete `DatatypeConstructor` (e.g.,
    /// `Layout_mk(16, 4)`), directly returns the constructor arguments instead
    /// of wrapping in `DatatypeSelector`. This allows downstream consumers
    /// (like `zero_init_alloc_memory`) to see concrete BV values via `value()`.
    pub(super) fn try_extract_layout_fields(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        use ay_bindings::SortInner;

        if let SortInner::Datatype(dt) = expr.sort().inner()
            && dt.name == "Layout"
        {
            // Part of #3007: When the Layout is a concrete constructor application,
            // extract arguments directly to preserve concrete values for
            // zero_init_alloc_memory and other consumers that need BitVecConst.
            if let ExprValue::DatatypeConstructor { args, .. } = expr.value() {
                if args.len() >= 2 {
                    debug!("try_extract_layout_fields: direct constructor extraction (concrete)");
                    return Some((args[0].clone(), args[1].clone()));
                }
            }

            // Part of #3107: When the Layout is an SSA Var, look up the concrete
            // value that was bound in bind_ssa_result. This resolves the
            // DatatypeSelector-over-Var pattern that loses concrete field values.
            if let ExprValue::Var { name } = expr.value() {
                debug!(
                    "try_extract_layout_fields: Var name={name}, ssa_cache_len={}, has_key={}",
                    self.ssa_concrete_values.len(),
                    self.ssa_concrete_values.contains_key(name),
                );
                if let Some(concrete) = self.ssa_concrete_values.get(name) {
                    debug!(
                        "try_extract_layout_fields: cache hit, concrete value={:?}",
                        concrete.value()
                    );
                    if let ExprValue::DatatypeConstructor { args, .. } = concrete.value() {
                        if args.len() >= 2 {
                            debug!(
                                "try_extract_layout_fields: resolved Var {name} to concrete \
                                 constructor via ssa_concrete_values cache"
                            );
                            return Some((args[0].clone(), args[1].clone()));
                        }
                    }
                }
            } else {
                debug!(
                    "try_extract_layout_fields: Layout expr is NOT Var, value={:?}",
                    expr.value()
                );
            }

            // Fallback: use field_select (symbolic Layout)
            let bv_sort = ptr_sort();
            let size = expr.clone().field_select("Layout", "fld_size", bv_sort.clone());
            let align = expr.clone().field_select("Layout", "fld_align", bv_sort);

            debug!("try_extract_layout_fields: extracted fld_size and fld_align (selector)");
            return Some((size, align));
        }
        None
    }

    /// Coerce an expression to pointer width (64 bits).
    ///
    /// For bitvecs: zero-extend or truncate as needed.
    /// For Dyn_Trait fat pointers: extract the `fld_ptr` data pointer field.
    /// For non-bitvecs (datatypes, etc.): return a safe non-null aligned pointer
    /// to avoid type errors while staying safe.
    ///
    /// REQUIRES: expr is any valid AY expression
    /// ENSURES: result.sort().bitvec_width() == Some(POINTER_WIDTH)
    #[must_use]
    pub(super) fn coerce_to_ptr_width(&self, expr: Expr) -> Expr {
        if let Some(width) = expr.sort().bitvec_width() {
            if width < POINTER_WIDTH {
                return expr.zero_extend(POINTER_WIDTH - width);
            } else if width > POINTER_WIDTH {
                return expr.extract(POINTER_WIDTH - 1, 0);
            }
            expr
        } else {
            // Non-bitvec (datatype, etc.) - return safe non-null aligned fallback pointer.
            // This can happen when Layout extraction fails or unexpected sort is passed.
            tracing::warn!(
                "coerce_to_ptr_width: non-bitvec sort {:?}, using fallback ptr",
                expr.sort()
            );
            Expr::bitvec_const(FALLBACK_PTR, POINTER_WIDTH)
        }
    }
}
