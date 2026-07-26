// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String parsing stub handlers.
//!
//! Covers `StrFromUtf8` and `IntParse`. Both follow a concrete-fast-path
//! pattern: when the input bytes or &str are fully known at codegen time,
//! emit a precise `Result::Ok(value)` or `Result::Err`; otherwise fall back
//! to a symbolic (unconstrained) Result over-approximation.
//!
//! Split from `codegen_call_string.rs` (Part of #4071).

use std::collections::HashSet;

use ay_bindings::Expr;
use rustc_public::mir::Operand;
use tracing::debug;

use super::super::ChcCtx;
use super::super::codegen_call_coerce::CallCoerce;

/// Extension trait for String parsing stubs on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallStringParse {
    /// Handle `StrFromUtf8`: core::str::from_utf8(&[u8]) -> Result<&str, Utf8Error>.
    fn codegen_str_from_utf8(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );

    /// Handle `IntParse`: <integer as FromStr>::from_str(&str) -> Result<T, ParseIntError>.
    fn codegen_int_parse(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    );
}

impl<'tcx, 'body> CallStringParse for ChcCtx<'tcx, 'body> {
    fn codegen_str_from_utf8(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // core::str::from_utf8(&[u8]) -> Result<&str, Utf8Error> (#3708)
        // Concrete fast path: when the byte slice backing is fully known,
        // evaluate UTF-8 validity at codegen time and emit precise Ok/Err.
        // Keep the existing unconstrained Result as the symbolic fallback.
        let mut concrete_emitted = false;
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let dest_sort = dest_var.sort().clone();
            if let Some(slice) = self.try_resolve_concrete_byte_slice_arg(args, modified_locals)
                && let Some(ok_sort) = Self::result_ok_inner_sort(&dest_sort)
            {
                match String::from_utf8(slice.bytes.clone()) {
                    Ok(_) => {
                        if let Some(ok_payload) = self.build_slice_value_for_sort(&slice, &ok_sort)
                        {
                            if ok_sort.is_bitvec() {
                                self.record_slice_backing_local(dest_local, &slice);
                            }
                            if let Some(ok_result) =
                                self.build_result_ok_expr(ok_payload, &dest_sort)
                                && let Some(eq) = self.make_coerced_eq_constraint(
                                    &dest_var,
                                    ok_result,
                                    dest_var.sort(),
                                    dest_local,
                                    "codegen_call_string_core::StrFromUtf8::concrete_ok",
                                )
                            {
                                extra_constraints.push(eq);
                                concrete_emitted = true;
                                debug!(
                                    dest_local,
                                    len = ?slice.len,
                                    "StrFromUtf8: concrete Ok result"
                                );
                            }
                        }
                    }
                    Err(_) => {
                        if let Some(err_result) = self.build_result_err_expr(&dest_sort)
                            && let Some(eq) = self.make_coerced_eq_constraint(
                                &dest_var,
                                err_result,
                                dest_var.sort(),
                                dest_local,
                                "codegen_call_string_core::StrFromUtf8::concrete_err",
                            )
                        {
                            extra_constraints.push(eq);
                            concrete_emitted = true;
                            debug!(dest_local, "StrFromUtf8: concrete Err result");
                        }
                    }
                }
            }
        }
        if !concrete_emitted {
            debug!(dest_local, "StrFromUtf8: symbolic Result over-approximation");
        }
        extra_dests.push(dest_local);
    }

    fn codegen_int_parse(
        &mut self,
        dest_local: usize,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        extra_constraints: &mut Vec<Expr>,
        extra_dests: &mut Vec<usize>,
    ) {
        // <integer as FromStr>::from_str(&str) -> Result<T, ParseIntError> (#3676)
        // Part of #3692: When the &str argument is concretely known, parse at
        // codegen time and emit a precise Result::Ok(value) or Result::Err.
        let mut concrete_emitted = false;
        if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
            let dest_sort = dest_var.sort().clone();
            // Try to resolve the &str argument to concrete string content.
            if let Some(str_content) = self.try_resolve_concrete_str_arg(args, modified_locals) {
                // Determine target BV width from the Result's Ok type.
                if let Some(ok_sort) = Self::result_ok_inner_sort(&dest_sort) {
                    if let Some(bv_width) = ok_sort.bitvec_width() {
                        // Parse the string as a signed integer.
                        if let Ok(parsed) = str_content.parse::<i128>() {
                            let max = (1i128 << (bv_width - 1)) - 1;
                            let min = -(1i128 << (bv_width - 1));
                            if parsed >= min && parsed <= max {
                                let value_expr = Expr::bitvec_const(parsed, bv_width);
                                if let Some(ok_result) =
                                    self.build_result_ok_expr(value_expr, &dest_sort)
                                {
                                    if let Some(eq) = self.make_coerced_eq_constraint(
                                        &dest_var,
                                        ok_result,
                                        dest_var.sort(),
                                        dest_local,
                                        "codegen_call_string_core::IntParse::concrete_ok",
                                    ) {
                                        extra_constraints.push(eq);
                                        concrete_emitted = true;
                                        debug!(
                                            dest_local,
                                            %str_content,
                                            parsed,
                                            bv_width,
                                            "IntParse: concrete Ok result (#3692)"
                                        );
                                    }
                                }
                            }
                        }
                        // Parse failure or out-of-range: emit Result::Err.
                        if !concrete_emitted {
                            if let Some(err_result) = self.build_result_err_expr(&dest_sort) {
                                if let Some(eq) = self.make_coerced_eq_constraint(
                                    &dest_var,
                                    err_result,
                                    dest_var.sort(),
                                    dest_local,
                                    "codegen_call_string_core::IntParse::concrete_err",
                                ) {
                                    extra_constraints.push(eq);
                                    concrete_emitted = true;
                                    debug!(
                                        dest_local,
                                        %str_content,
                                        "IntParse: concrete Err result (#3692)"
                                    );
                                }
                            }
                        }
                    }
                }
            }
        }
        if !concrete_emitted {
            debug!(dest_local, "IntParse: symbolic Result over-approximation");
        }
        extra_dests.push(dest_local);
    }
}
