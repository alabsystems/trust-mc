// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! String semantic model for AY codegen.
//!
//! String is modeled as a struct with (ptr, len, cap) fields,
//! similar to Vec but for UTF-8 string data.
//!
//! Part of #1312: Collection stubs implementation.
//! Part of #1354: Statement module refactoring.

#[path = "string_utf8.rs"]
mod string_utf8;

use crate::codegen_ay::names::{self, RUST_STRING_CONS, RUST_STRING_SORT, struct_sort};
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort, bv8_sort, ptr_sort};
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::super::StatementCodegen;

/// Extracted fields from a String datatype expression.
///
/// Extracts all 4 fields in one pass; clones `s` for each `field_select` call
/// since `field_select` consumes `self` (Expr wraps Arc, so clones are O(1)).
struct StringFields {
    ptr: Expr,
    len: Expr,
    cap: Expr,
    data: Expr,
    sort: Sort,
}

impl StringFields {
    /// Extract all 4 fields from a String datatype expression.
    ///
    /// `field_select` consumes `self`, so we clone for each call
    /// (Expr wraps Arc, O(1) clone).
    fn extract(s: Expr) -> Self {
        let sort = s.sort().clone();
        let ptr = s.clone().field_select(RUST_STRING_SORT, "fld_ptr", ptr_sort());
        let len = s.clone().field_select(RUST_STRING_SORT, "fld_len", ptr_sort());
        let cap = s.clone().field_select(RUST_STRING_SORT, "fld_cap", ptr_sort());
        let data_sort = Sort::array(ptr_sort(), bv8_sort());
        let data = s.field_select(RUST_STRING_SORT, "fld_data", data_sort);
        Self { ptr, len, cap, data, sort }
    }

    /// Reconstruct a String datatype from (possibly modified) fields.
    fn reconstruct(self) -> Expr {
        Expr::datatype_constructor(
            RUST_STRING_SORT,
            RUST_STRING_CONS,
            vec![self.ptr, self.len, self.cap, self.data],
            self.sort,
        )
    }
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    #[must_use]
    pub(in super::super) fn string_like_len(&self, expr: &Expr) -> Option<Expr> {
        if !expr.sort().is_datatype() {
            return None;
        }
        match expr.sort().datatype_name() {
            Some(RUST_STRING_SORT) => {
                Some(expr.clone().field_select(RUST_STRING_SORT, "fld_len", ptr_sort()))
            }
            Some("Slice") => Some(expr.clone().field_select("Slice", "fld_len", ptr_sort())),
            _ => None, // non-enum: Option<&str> (datatype_default_constructor)
        }
    }

    /// Codegen String operations (Part of #1312).
    ///
    /// String is modeled as a struct with (ptr, len, cap) fields.
    pub(in crate::codegen_ay::statement) fn codegen_string_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
        callee_path: &str,
    ) -> Option<BasicBlockIdx> {
        use StubKind::{
            CowToString, DisplayToString, FmtFormat, IntParse, StrFromUtf8, StringAsStr,
            StringClear, StringClone, StringContains, StringEndsWith, StringEq, StringFrom,
            StringFromUtf8Lossy, StringIntoBoxedStr, StringIsAscii, StringIsEmpty, StringLen,
            StringNew, StringPush, StringPushStr, StringStartsWith, StringTruncate,
        };

        debug!(?stub_kind, %callee_path, "codegen_string_stub");

        match stub_kind {
            StringNew => {
                // Part of #1632: Include fld_data array backing to match sort_inference.rs.
                // Use a canonical empty String so repeated String::new() calls compare equal.
                let byte_array = Sort::array(ptr_sort(), bv8_sort());
                let string_sort = struct_sort(RUST_STRING_SORT, names::vec_fields(byte_array));
                let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                let zero_byte = Expr::bitvec_const(0u8, 8);
                let data = Expr::const_array(ptr_sort(), zero_byte);
                let string = Expr::datatype_constructor(
                    RUST_STRING_SORT,
                    RUST_STRING_CONS,
                    vec![zero.clone(), zero.clone(), zero, data],
                    string_sort,
                );
                self.assign_value_to_place(destination, string);
                target
            }

            StringFrom => {
                // String::from may allocate and copy content, so keep len/cap/data symbolic.
                let array_sort = Sort::array(ptr_sort(), bv8_sort());
                let string_sort =
                    struct_sort(RUST_STRING_SORT, names::vec_fields(array_sort.clone()));

                let ptr_name = self.ctx.fresh_name("string_ptr");
                let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());
                let data_name = self.ctx.fresh_name("string_data");
                let data = self.ctx.declare_var(&data_name, array_sort);

                let len_name = self.ctx.fresh_name("string_len");
                let cap_name = self.ctx.fresh_name("string_cap");
                let len = self.ctx.declare_var(&len_name, ptr_sort());
                let cap = self.ctx.declare_var(&cap_name, ptr_sort());
                // cap and len used again in vec below — clone for assert
                self.ctx.assert(cap.clone().bvuge(len.clone()));

                let string = Expr::datatype_constructor(
                    RUST_STRING_SORT,
                    RUST_STRING_CONS,
                    vec![ptr, len, cap, data],
                    string_sort,
                );
                self.assign_value_to_place(destination, string);
                target
            }

            StringLen => {
                if args.is_empty() {
                    warn!("String::len requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, s)) = self.resolve_collection_base(&args[0]) {
                    if let Some(len) = self.string_like_len(&s) {
                        self.assign_value_to_place(destination, len);
                    } else {
                        let name = self.ctx.fresh_name("string_len");
                        let len = self.ctx.declare_var(&name, ptr_sort());
                        self.assign_value_to_place(destination, len);
                    }
                } else {
                    let name = self.ctx.fresh_name("string_len");
                    let len = self.ctx.declare_var(&name, ptr_sort());
                    self.assign_value_to_place(destination, len);
                }
                target
            }

            StringIsEmpty => {
                if args.is_empty() {
                    warn!("String::is_empty requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, s)) = self.resolve_collection_base(&args[0]) {
                    if let Some(len) = self.string_like_len(&s) {
                        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                        // len and zero: last use of each — no clone needed
                        let is_empty = len.eq(zero);
                        self.assign_value_to_place(destination, is_empty);
                    } else {
                        let name = self.ctx.fresh_name("string_is_empty");
                        let is_empty = self.ctx.declare_var(&name, bool_sort());
                        self.assign_value_to_place(destination, is_empty);
                    }
                } else {
                    let name = self.ctx.fresh_name("string_is_empty");
                    let is_empty = self.ctx.declare_var(&name, bool_sort());
                    self.assign_value_to_place(destination, is_empty);
                }
                target
            }

            // Part of #2125 Phase 2: String/str Bool predicates
            // Sound over-approximation: symbolic Bool (no character-level content model)
            StringContains | StringStartsWith | StringEndsWith | StringIsAscii => {
                let prefix = match stub_kind {
                    StringContains => "string_contains",
                    StringStartsWith => "string_starts_with",
                    StringEndsWith => "string_ends_with",
                    StringIsAscii => "string_is_ascii",
                    _other => {
                        // partial dispatch: StubKind
                        warn!(
                            ?_other,
                            "String predicate: unexpected stub in Contains|StartsWith|EndsWith|IsAscii arm"
                        );
                        return None;
                    }
                };
                let name = self.ctx.fresh_name(prefix);
                let result = self.ctx.declare_var(&name, bool_sort());
                self.assign_value_to_place(destination, result);
                target
            }

            StringPush | StringPushStr => {
                if args.is_empty() {
                    warn!("String::push requires at least 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((base, s)) = self.resolve_collection_base(&args[0]) {
                    // Guard against non-datatype String (same as vec_field_select fix)
                    if !s.sort().is_datatype() {
                        warn!(
                            "String::push: s has non-datatype sort {:?} — fail-closed (#2497)",
                            s.sort()
                        );
                        return None;
                    }
                    let fields = StringFields::extract(s);

                    // String::push(char) adds 1-4 bytes (UTF-8), push_str adds unknown bytes
                    // Use nondet increment constrained to >= 1 for push, >= 0 for push_str
                    let inc_name = self.ctx.fresh_name("string_push_len");
                    let increment = self.ctx.declare_var(&inc_name, ptr_sort());
                    if stub_kind == StringPush {
                        // char is 1-4 bytes in UTF-8
                        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
                        let four = Expr::bitvec_const(4u64, POINTER_WIDTH);
                        // increment used again below — clone for each assert
                        self.ctx.assert(increment.clone().bvuge(one));
                        self.ctx.assert(increment.clone().bvule(four));
                    }

                    // increment last use in this branch — no clone needed
                    let new_len = fields.len.bvadd(increment);

                    // Capacity grows as needed but never shrinks
                    let cap_name = self.ctx.fresh_name("string_cap");
                    let new_cap = self.ctx.declare_var(&cap_name, ptr_sort());
                    // new_cap used in struct below — clone; new_len used in struct below — clone
                    self.ctx.assert(new_cap.clone().bvuge(new_len.clone()));
                    // new_cap used in struct below — clone; fields.cap last use
                    self.ctx.assert(new_cap.clone().bvuge(fields.cap));

                    let new_string = StringFields {
                        ptr: fields.ptr,
                        len: new_len,
                        cap: new_cap,
                        data: fields.data,
                        sort: fields.sort,
                    }
                    .reconstruct();
                    self.env_update(base, new_string);
                }
                target
            }

            StringClear => {
                if args.is_empty() {
                    warn!("String::clear requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((base, s)) = self.resolve_collection_base(&args[0]) {
                    // Guard against non-datatype String
                    if !s.sort().is_datatype() {
                        warn!(
                            "String::clear: s has non-datatype sort {:?} — fail-closed (#2497)",
                            s.sort()
                        );
                        return None;
                    }
                    let fields = StringFields::extract(s);
                    let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                    let new_string = StringFields {
                        ptr: fields.ptr,
                        len: zero,
                        cap: fields.cap,
                        data: fields.data,
                        sort: fields.sort,
                    }
                    .reconstruct();
                    self.env_update(base, new_string);
                }
                target
            }

            StringClone => {
                if args.is_empty() {
                    warn!("String::clone requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, s)) = self.resolve_collection_base(&args[0]) {
                    self.assign_value_to_place(destination, s);
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            StringTruncate => {
                // String::truncate(&mut self, new_len: usize) - truncates in place
                // Part of #1610
                if args.len() < 2 {
                    warn!("String::truncate requires 2 args (self, new_len) — fail-closed (#2497)");
                    return None;
                }

                let resolved = self.resolve_collection_base(&args[0]);
                let new_len = self.codegen_operand(&args[1]);

                if let (Some((base, s)), Some(new_len)) = (resolved, new_len) {
                    // Guard against non-datatype String
                    if !s.sort().is_datatype() {
                        warn!(
                            "String::truncate: s has non-datatype sort {:?} — fail-closed (#2497)",
                            s.sort()
                        );
                        return None;
                    }
                    let fields = StringFields::extract(s);

                    // truncated_len = min(old_len, new_len) using ITE
                    // new_len used in ite — clone; fields.len used in ite — clone
                    let cond = new_len.clone().bvult(fields.len.clone());
                    // cond, new_len, fields.len: last use of each — no clone
                    let truncated_len = Expr::ite(cond, new_len, fields.len);

                    let new_string = StringFields {
                        ptr: fields.ptr,
                        len: truncated_len,
                        cap: fields.cap,
                        data: fields.data,
                        sort: fields.sort,
                    }
                    .reconstruct();
                    self.env_update(base, new_string);
                }
                target
            }

            StringFromUtf8Lossy => {
                // String::from_utf8_lossy(&[u8]) -> Cow<str>
                // Model: return String with symbolic length <= input_len
                // UTF-8 validation logic is abstracted; we model result conservatively.
                // Part of #1610, #1632: Include fld_data array backing
                let array_sort = Sort::array(ptr_sort(), bv8_sort());
                let string_sort =
                    struct_sort(RUST_STRING_SORT, names::vec_fields(array_sort.clone()));

                // Symbolic ptr, len, cap, data for the result
                let ptr_name = self.ctx.fresh_name("utf8_ptr");
                let ptr = self.ctx.declare_var(&ptr_name, ptr_sort());
                let len_name = self.ctx.fresh_name("utf8_len");
                let len = self.ctx.declare_var(&len_name, ptr_sort());
                let cap_name = self.ctx.fresh_name("utf8_cap");
                let cap = self.ctx.declare_var(&cap_name, ptr_sort());
                let data_name = self.ctx.fresh_name("utf8_data");
                let data = self.ctx.declare_var(&data_name, array_sort);

                // Constraint: cap >= len (standard invariant)
                // cap and len used again in vec below — clone for assert
                self.ctx.assert(cap.clone().bvuge(len.clone()));

                // If we have the input slice, constrain len <= input_len
                if let Some(input) = args.first().and_then(|arg| self.codegen_operand(arg)) {
                    // Slice is modeled as (fld_ptr, fld_len, fld_data) with name "Slice"
                    if let Some(input_len) = self.string_like_len(&input) {
                        // len used again in vec below — clone
                        self.ctx.assert(len.clone().bvule(input_len));
                    }
                }

                let string = Expr::datatype_constructor(
                    RUST_STRING_SORT,
                    RUST_STRING_CONS,
                    vec![ptr, len, cap, data],
                    string_sort,
                );
                self.assign_value_to_place(destination, string);
                target
            }

            StringAsStr => {
                // String::as_str(&self) -> &str
                // Returns a Slice view of the String's UTF-8 content (ptr, len, data).
                // Follows the VecAsSlice pattern. Part of #3582.
                if args.is_empty() {
                    warn!("String::as_str requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, s)) = self.resolve_collection_base(&args[0]) {
                    if s.sort().is_datatype() {
                        let fields = StringFields::extract(s);
                        // Build a Slice_bv8 from the String's (ptr, len, data).
                        let slice_name = names::slice_sort_name("bv8");
                        let ctor_name = names::cons_name(&slice_name);
                        let slice_sort = Self::slice_sort(bv8_sort());
                        let slice = Expr::datatype_constructor(
                            slice_name,
                            ctor_name,
                            vec![fields.ptr, fields.len, fields.data],
                            slice_sort,
                        );
                        self.assign_value_to_place(destination, slice);
                    } else {
                        self.codegen_symbolic_result(destination);
                    }
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            StringIntoBoxedStr => {
                // String::into_boxed_str(self) -> Box<str> (#3646)
                // Layout-preserving: return a Slice view (ptr, len, data) of the
                // source String's backing, same as StringAsStr. Box<str> is an
                // owned str slice, so the representation is identical for BMC.
                if args.is_empty() {
                    warn!("String::into_boxed_str requires 1 arg (self) — fail-closed (#2497)");
                    return None;
                }

                if let Some((_base, s)) = self.resolve_collection_base(&args[0]) {
                    if s.sort().is_datatype() {
                        let fields = StringFields::extract(s);
                        let slice_name = names::slice_sort_name("bv8");
                        let ctor_name = names::cons_name(&slice_name);
                        let slice_sort = Self::slice_sort(bv8_sort());
                        let slice = Expr::datatype_constructor(
                            slice_name,
                            ctor_name,
                            vec![fields.ptr, fields.len, fields.data],
                            slice_sort,
                        );
                        self.assign_value_to_place(destination, slice);
                    } else {
                        self.codegen_symbolic_result(destination);
                    }
                } else {
                    self.codegen_symbolic_result(destination);
                }
                target
            }

            StrFromUtf8 => self.codegen_str_from_utf8_stub(args, destination, target),

            IntParse => {
                // <integer as FromStr>::from_str(&str) -> Result<T, ParseIntError> (#3676)
                // Sound over-approximation: leave destination unconstrained.
                debug!("IntParse: symbolic Result over-approximation (BMC)");
                target
            }

            // Equality and conversion ops delegated to string_convert.rs
            StringEq | CowToString | DisplayToString | FmtFormat => {
                self.codegen_string_convert_stub(stub_kind, args, destination, target, callee_path)
            }

            // partial dispatch: StubKind — parent dispatcher (stub_dispatch.rs) routes only
            // String*/Cow*/Display*/Fmt* variants here; reaching this arm is a programming error.
            _other => {
                warn!(
                    ?_other,
                    "codegen_string_stub: unexpected stub — update stub_dispatch.rs routing"
                );
                None
            }
        }
    }
}
