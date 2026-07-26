// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Transparent wrapper handling for ADT aggregate construction.
//!
//! Split from codegen_stmt_aggregate_adt.rs per #3199.
//! Handles ManuallyDrop, MaybeUninit, UnsafeCell, Cell, NonZero,
//! NonNull, Unique, Box, Rc, and Arc — all transparent wrappers that return
//! the inner operand directly at the SMT level.

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::{debug, warn};

use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe};

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Try to translate an ADT aggregate as a transparent wrapper.
    ///
    /// Returns `Some(Some(expr))` if the ADT is a transparent wrapper and was translated,
    /// `Some(None)` if it is a wrapper but translation failed,
    /// `None` if it is not a transparent wrapper (caller should continue to main logic).
    ///
    /// Part of #912 / #2075: Pointer-wrapper ADTs are encoded as raw pointers (bv64)
    /// in translate_ty. Keep aggregate translation consistent by returning the pointer
    /// operand directly rather than building a datatype value.
    pub(in crate::codegen_ay::chc) fn try_translate_transparent_wrapper(
        &mut self,
        base_name: &str,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Option<Expr>> {
        // ManuallyDrop, MaybeUninit, UnsafeCell, Cell, NonZero — single-operand passthrough
        if base_name == "ManuallyDrop"
            || base_name == "MaybeUninit"
            || base_name == "UnsafeCell"
            || base_name == "Cell"
            || base_name == "NonZero"
            || base_name.starts_with("NonZero")
        {
            if operands.len() != 1 {
                warn!(
                    "translate_adt_aggregate: {} expected 1 operand, got {}",
                    base_name,
                    operands.len()
                );
                return Some(None);
            }
            let expr = self.translate_operand_with_modified(&operands[0], modified_locals);
            if expr.is_some() {
                debug!(
                    "translate_adt_aggregate: {} transparent wrapper -> returning operand directly",
                    base_name
                );
            }
            return Some(expr);
        }

        // NonNull, Unique, Box, Rc, Arc — pointer wrappers. Rc/Arc aggregates
        // include PhantomData/allocator operands in MIR, but the CHC model uses
        // only the first operand (the inner pointer) as the wrapper value.
        if base_name == "NonNull"
            || base_name == "Unique"
            || base_name == "Box"
            || base_name == "Rc"
            || base_name == "Arc"
        {
            if operands.len() == 1 {
                let Some(expr) =
                    self.translate_operand_with_modified(&operands[0], modified_locals)
                else {
                    return Some(None);
                };
                if !expr.sort().is_bitvec() {
                    warn!(
                        "translate_adt_aggregate: {} operand sort {:?} is not bitvec",
                        base_name,
                        expr.sort()
                    );
                    return Some(None);
                }
                let expr = coerce_bitvec_width_safe(expr, POINTER_WIDTH, SignExtension::ZeroExtend);
                debug!(
                    "translate_adt_aggregate: {} transparent wrapper -> returning operand directly",
                    base_name
                );
                return Some(Some(expr));
            } else if (base_name == "Rc" || base_name == "Arc") && operands.len() >= 2 {
                let Some(expr) =
                    self.translate_operand_with_modified(&operands[0], modified_locals)
                else {
                    return Some(None);
                };
                if !expr.sort().is_bitvec() {
                    warn!(
                        "translate_adt_aggregate: {} operand sort {:?} is not bitvec",
                        base_name,
                        expr.sort()
                    );
                    return Some(None);
                }
                let expr = coerce_bitvec_width_safe(expr, POINTER_WIDTH, SignExtension::ZeroExtend);
                debug!(
                    "translate_adt_aggregate: {} aggregate -> returning pointer, ignoring metadata fields",
                    base_name
                );
                return Some(Some(expr));
            } else if base_name == "Box" && operands.len() == 2 {
                // Box<T, A> can include allocator payload in MIR. We model Box as
                // pointer-only and ignore allocator metadata for now.
                let Some(expr) =
                    self.translate_operand_with_modified(&operands[0], modified_locals)
                else {
                    return Some(None);
                };
                if !expr.sort().is_bitvec() {
                    warn!(
                        "translate_adt_aggregate: Box operand sort {:?} is not bitvec",
                        expr.sort()
                    );
                    return Some(None);
                }
                let expr = coerce_bitvec_width_safe(expr, POINTER_WIDTH, SignExtension::ZeroExtend);
                debug!(
                    "translate_adt_aggregate: Box with 2 operands -> returning pointer, ignoring allocator field"
                );
                return Some(Some(expr));
            } else if base_name == "Unique" && operands.len() == 2 {
                // Unique<T> has 2 fields: NonNull<T> pointer and PhantomData<T> (zero-sized marker)
                let Some(expr) =
                    self.translate_operand_with_modified(&operands[0], modified_locals)
                else {
                    return Some(None);
                };
                if !expr.sort().is_bitvec() {
                    warn!(
                        "translate_adt_aggregate: Unique operand sort {:?} is not bitvec",
                        expr.sort()
                    );
                    return Some(None);
                }
                let expr = coerce_bitvec_width_safe(expr, POINTER_WIDTH, SignExtension::ZeroExtend);
                debug!(
                    "translate_adt_aggregate: Unique with 2 operands -> returning pointer, ignoring PhantomData"
                );
                return Some(Some(expr));
            }
            warn!(
                "translate_adt_aggregate: {} expected pointer in operand 0, got {} operands",
                base_name,
                operands.len()
            );
            return Some(None);
        }

        // Part of #4067: OnceBox — internal platform type mapped to ptr_sort()
        // in type translation. Contains a single AtomicPtr operand. Treat as
        // pointer-wrapper passthrough so aggregate construction doesn't fall back.
        if base_name == "OnceBox" {
            if operands.len() == 1 {
                let expr = self.translate_operand_with_modified(&operands[0], modified_locals);
                if let Some(expr) = expr {
                    let expr =
                        coerce_bitvec_width_safe(expr, POINTER_WIDTH, SignExtension::ZeroExtend);
                    debug!("translate_adt_aggregate: OnceBox -> returning pointer operand");
                    return Some(Some(expr));
                }
                return Some(None);
            }
            warn!("translate_adt_aggregate: OnceBox expected 1 operand, got {}", operands.len());
            return Some(None);
        }

        // Part of #4067: Mutex<T>, RwLock<T>, and ArcInner<T> are data-extract
        // wrappers where the last field holds the meaningful data.
        //
        // Mutex/RwLock: transparent in single-threaded verification. MIR-level
        // inlining expands Mutex::new into aggregates like
        // Aggregate(Mutex, [inner, poison, data]). Only data (UnsafeCell<T>) matters.
        //
        // ArcInner<T>: has (strong: AtomicUsize, weak: AtomicUsize, data: T). Arc is
        // a pointer wrapper — ArcInner is allocated on heap and data is the meaningful
        // content. Extracting last field avoids aggregate sort mismatch when the type
        // translator makes Mutex<T> transparent.
        if base_name == "Mutex" || base_name == "RwLock" || base_name == "ArcInner" {
            if operands.is_empty() {
                warn!("translate_adt_aggregate: {} expected >=1 operand, got 0", base_name);
                return Some(None);
            }
            // The data field is the last operand.
            let data_idx = operands.len() - 1;
            let expr = self.translate_operand_with_modified(&operands[data_idx], modified_locals);
            if expr.is_some() {
                debug!(
                    base_name,
                    data_idx,
                    "translate_adt_aggregate: data-extract wrapper -> extracting last field"
                );
            }
            return Some(expr);
        }

        // Not a transparent wrapper — caller should continue.
        None
    }
}
