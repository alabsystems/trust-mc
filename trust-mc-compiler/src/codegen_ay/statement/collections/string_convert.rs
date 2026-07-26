// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! String conversion and equality operations for AY codegen.
//!
//! Extracted from `string.rs`. Handles:
//! - Equality: StringEq (quantified content comparison)
//! - Conversions: CowToString, DisplayToString, FmtFormat
//! - Helper: create_symbolic_string
//!
//! Part of #2246: Large file decomposition.

use crate::codegen_ay::names::{self, RUST_STRING_CONS, RUST_STRING_SORT, struct_sort};
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{bv8_sort, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::super::StatementCodegen;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen String conversion and equality operations.
    ///
    /// Delegated from `codegen_string_stub` for equality/conversion variants.
    pub(in super::super) fn codegen_string_convert_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        _callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{CowToString, DisplayToString, FmtFormat, StringEq};

        match stub_kind {
            StringEq => {
                // PartialEq::eq(&String, &String) -> bool or eq(&String, &str) -> bool
                // Part of #1753: Compare actual content, not just length.
                // Uses quantified formula: forall i. (i < len) -> l[i] == r[i]
                if args.len() < 2 {
                    warn!("String::eq requires 2 args (lhs, rhs) — fail-closed (#2497)");
                    // Part of #3211: Track constraint drop in demotion pipeline.
                    self.ctx.unsupported_with_fallback(
                        "string_eq_insufficient_args",
                        "String::eq requires 2 args",
                    );
                    return None;
                }

                let lhs_base = self.get_map_base_from_ref(&args[0]);
                let rhs_base = self.get_map_base_from_ref(&args[1]);
                let lhs = lhs_base
                    .as_ref()
                    .and_then(|b| self.env_lookup(b).cloned())
                    .or_else(|| self.codegen_operand(&args[0]));
                let rhs = rhs_base
                    .as_ref()
                    .and_then(|b| self.env_lookup(b).cloned())
                    .or_else(|| self.codegen_operand(&args[1]));

                if let (Some(l), Some(r)) = (lhs, rhs) {
                    let (Some(l_len), Some(r_len)) =
                        (self.string_like_len(&l), self.string_like_len(&r))
                    else {
                        warn!("StringEq: cannot extract string lengths — fail-closed (#2497)");
                        // Part of #3211: Track constraint drop in demotion pipeline.
                        self.ctx.unsupported_with_fallback(
                            "string_eq_missing_lengths",
                            "cannot extract string lengths",
                        );
                        return None;
                    };
                    let len_eq = l_len.clone().eq(r_len);

                    // Part of #1753: Content equality via fld_data array comparison
                    // forall i. (i < len) -> l_data[i] == r_data[i]
                    let data_sort = Sort::array(ptr_sort(), bv8_sort());
                    let l_data = l.field_select(RUST_STRING_SORT, "fld_data", data_sort.clone());
                    let r_data = r.field_select(RUST_STRING_SORT, "fld_data", data_sort);

                    // Create bound variable for quantified content comparison
                    let idx_name = self.ctx.fresh_name("str_eq_idx");
                    let idx_sort = ptr_sort();
                    let idx_var = Expr::var(&idx_name, idx_sort.clone());

                    // Compare elements at each index
                    let l_elem = l_data.select(idx_var.clone());
                    let r_elem = r_data.select(idx_var.clone());
                    let elems_eq = l_elem.eq(r_elem);

                    // Only indices less than length matter
                    let in_bounds = idx_var.bvult(l_len);
                    let body = in_bounds.implies(elems_eq);
                    let content_eq = Expr::forall(vec![(idx_name, idx_sort)], body);

                    let result = len_eq.and(content_eq);
                    self.assign_value_to_place(destination, result);
                } else {
                    // Fail-closed: operands could not be resolved (#2497)
                    warn!("StringEq: cannot resolve operands — fail-closed (#2497)");
                    return None;
                }
                target
            }

            CowToString => {
                // <Cow<str> as ToString>::to_string() -> String (#1691)
                // Cow<str> is already modeled as String by StringFromUtf8Lossy.
                // to_string() just passes through the value or clones it.
                debug!("CowToString: args.len()={}", args.len());
                if args.is_empty() {
                    warn!("Cow::to_string requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                // Try to get the underlying String value from the Cow
                let resolved = self.resolve_collection_base(&args[0]);
                debug!("CowToString: resolved={:?}", resolved.as_ref().map(|(b, _)| b));

                if let Some((_base, s)) = resolved {
                    // Cow is modeled as String - just pass through
                    self.assign_value_to_place(destination, s);
                } else {
                    // Fallback: create a new symbolic String
                    let string = self.create_symbolic_string("cow_to_string");
                    self.assign_value_to_place(destination, string);
                }
                target
            }

            DisplayToString => {
                // <T as ToString>::to_string() -> String (#1700, #1701)
                // Generic handler for Display types - returns symbolic String
                // This is an overapproximation: we don't model the Display::fmt impl
                debug!("DisplayToString: args.len()={}", args.len());
                if args.is_empty() {
                    warn!("DisplayToString: requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }
                // Note: args are ignored - we can't extract useful info from arbitrary Display types
                let string = self.create_symbolic_string("display_to_string");
                self.assign_value_to_place(destination, string);
                target
            }

            FmtFormat => {
                // std::fmt::format(Arguments) -> String (#1704)
                // The format! macro expands to this function.
                // Returns symbolic String - we don't model formatting logic.
                debug!("FmtFormat: args.len()={}", args.len());
                // args[0] is core::fmt::Arguments which we don't inspect
                let string = self.create_symbolic_string("fmt_format");
                self.assign_value_to_place(destination, string);
                target
            }

            _other => {
                // partial dispatch: StubKind
                warn!(
                    ?stub_kind,
                    "codegen_string_convert_stub: unexpected stub kind — update string.rs routing"
                );
                None
            }
        }
    }

    /// Create a symbolic String value with fresh variables.
    ///
    /// Used by CowToString, DisplayToString, FmtFormat, and other stubs that need
    /// to return a symbolic String without specific constraints.
    ///
    /// Part of #1700, #1704: DRY extraction for symbolic String creation.
    /// Part of #1632: Include fld_data array backing to match sort_inference.rs.
    #[must_use]
    pub(in super::super) fn create_symbolic_string(&mut self, prefix: &str) -> Expr {
        // String is backed by Vec<u8>, so fld_data is Array<usize, u8>
        let array_sort = Sort::array(ptr_sort(), bv8_sort());
        let string_sort = struct_sort(RUST_STRING_SORT, names::vec_fields(array_sort.clone()));
        let ptr_name = self.ctx.fresh_name_with_suffix(prefix, "ptr");
        let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());
        let len_name = self.ctx.fresh_name_with_suffix(prefix, "len");
        let len = self.ctx.declare_var(&len_name, ptr_sort());
        let cap_name = self.ctx.fresh_name_with_suffix(prefix, "cap");
        let cap = self.ctx.declare_var(&cap_name, ptr_sort());
        let data_name = self.ctx.fresh_name_with_suffix(prefix, "data");
        let data = self.ctx.declare_var(&data_name, array_sort);
        // Standard String invariant: cap >= len
        self.ctx.assert(cap.clone().bvuge(len.clone()));

        Expr::datatype_constructor(
            RUST_STRING_SORT,
            RUST_STRING_CONS,
            vec![ptr, len, cap, data],
            string_sort,
        )
    }
}
