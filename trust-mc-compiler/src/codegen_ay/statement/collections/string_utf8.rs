// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! UTF-8-specific String collection helpers.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use crate::codegen_ay::names;
use crate::codegen_ay::types::{
    SignExtension, bool_sort, bv8_sort, coerce_bitvec_width_safe, ptr_sort,
};

use super::super::vec_fields::VecFields;
use super::{StatementCodegen, StringFields};

struct ConcreteByteSlice {
    ptr: Expr,
    len: Expr,
    data: Expr,
    bytes: Vec<u8>,
}

/// The (ptr, len, cap, data) quadruple shared by the `String` and `Vec<u8>`
/// models. `String::from_utf8` / `String::into_bytes` are layout identities on
/// it — only the datatype sort changes.
struct OwnedBytes {
    ptr: Expr,
    len: Expr,
    cap: Expr,
    data: Expr,
}

/// Longest byte string the concrete UTF-8 fast path will decode at codegen time.
/// Same bound as the `str::from_utf8` stub above (`try_resolve_concrete_byte_slice`).
const MAX_CONCRETE_UTF8_BYTES: usize = 256;

/// Rewrite depth for `peel_concrete`: one level per SSA hop, selector, store
/// or arithmetic node. A 256-byte push-built Vec is a 256-deep store chain.
const MAX_CONCRETE_PEEL: usize = 4 * MAX_CONCRETE_UTF8_BYTES;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// `String::from_utf8(Vec<u8>) -> Result<String, FromUtf8Error>`.
    ///
    /// SOUNDNESS: three lanes, none of which can silently pick `Ok`:
    /// - concrete bytes (constant len ≤ 256, every byte readable from the
    ///   store chain): `std::str::from_utf8` decides at codegen time and the
    ///   result is exactly `Ok(String{ptr,len,cap,data})` or `Err(symbolic)`;
    /// - symbolic bytes: a fresh Bool chooses between `Ok(String carrying the
    ///   Vec's fields)` and `Err(symbolic)` — a strict superset of the real
    ///   behaviour, so a downstream `.unwrap()` yields a (possibly spurious)
    ///   CTREX rather than a false proof;
    /// - unresolvable receiver / sort: an unconstrained Result PLUS a recorded
    ///   fallback, so the verdict is demoted rather than reported clean.
    pub(in crate::codegen_ay::statement) fn codegen_string_from_utf8_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let Some(arg) = args.first() else {
            return self.string_bytes_fail_closed(
                "String::from_utf8",
                "no receiver argument",
                destination,
                target,
            );
        };
        let Some(result_sort) = self.infer_sort_from_place(destination) else {
            return self.string_bytes_fail_closed(
                "String::from_utf8",
                "destination Result sort not inferable",
                destination,
                target,
            );
        };
        let Some(ok_sort) = Self::result_variant_field_sort(&result_sort, "Ok") else {
            return self.string_bytes_fail_closed(
                "String::from_utf8",
                "destination Result has no single-field Ok constructor",
                destination,
                target,
            );
        };
        let Some(bytes) = self.resolve_owned_bytes_from_vec(arg) else {
            return self.string_bytes_fail_closed(
                "String::from_utf8",
                "receiver is not a resolvable Vec<u8> datatype",
                destination,
                target,
            );
        };
        let Some(ok_payload) = Self::build_owned_bytes_for_sort(&bytes, &ok_sort) else {
            return self.string_bytes_fail_closed(
                "String::from_utf8",
                "Ok payload sort is not the (ptr, len, cap, data) String model",
                destination,
                target,
            );
        };

        // Lane 1: concrete bytes — decide validity now. The length of a
        // push-built Vec is a `bvadd` chain, not a literal, so fold it.
        if let Some(len) = self.const_usize(&bytes.len)
            && len <= MAX_CONCRETE_UTF8_BYTES
            && let Some(raw) = self.try_extract_raw_bytes_from_array(&bytes.data, len)
        {
            let result_expr = match std::str::from_utf8(&raw) {
                Ok(_) => self.build_result_variant_expr(&result_sort, "Ok", ok_payload.clone()),
                Err(_) => self.build_symbolic_result_err_expr(&result_sort),
            };
            if let Some(result_expr) = result_expr {
                self.assign_value_to_place(destination, result_expr);
                debug!(len, "StringFromUtf8: concrete Result semantics (BMC)");
                return target;
            }
        }

        // Lane 2: symbolic bytes — nondeterministic Ok/Err, Ok carries the bytes.
        let (Some(ok_expr), Some(err_expr)) = (
            self.build_result_variant_expr(&result_sort, "Ok", ok_payload),
            self.build_symbolic_result_err_expr(&result_sort),
        ) else {
            return self.string_bytes_fail_closed(
                "String::from_utf8",
                "destination Result constructors not buildable",
                destination,
                target,
            );
        };
        let choice_name = self.ctx.fresh_name("string_from_utf8_is_ok");
        let choice = self.ctx.declare_var(&choice_name, bool_sort());
        self.ctx.bmc_sound_havoc("string_from_utf8_choice");
        self.assign_value_to_place(destination, Expr::ite(choice, ok_expr, err_expr));
        debug!("StringFromUtf8: symbolic nondet Ok/Err over-approximation (BMC)");
        target
    }

    /// `String::into_bytes(self) -> Vec<u8>`: layout identity.
    ///
    /// The String model IS the Vec<u8> model under a different datatype name,
    /// so the destination is the receiver's (ptr, len, cap, data) re-wrapped in
    /// the destination's Vec sort. Fails CLOSED (fallback demotion + symbolic
    /// destination) when the receiver is not a resolvable String datatype.
    pub(in crate::codegen_ay::statement) fn codegen_string_into_bytes_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let Some(arg) = args.first() else {
            return self.string_bytes_fail_closed(
                "String::into_bytes",
                "no receiver argument",
                destination,
                target,
            );
        };
        let Some(dest_sort) = self.infer_sort_from_place(destination) else {
            return self.string_bytes_fail_closed(
                "String::into_bytes",
                "destination Vec<u8> sort not inferable",
                destination,
                target,
            );
        };
        let Some((_base, s)) = self.resolve_collection_base(arg) else {
            return self.string_bytes_fail_closed(
                "String::into_bytes",
                "receiver String not resolvable",
                destination,
                target,
            );
        };
        if s.sort().datatype_name() != Some(names::RUST_STRING_SORT) {
            return self.string_bytes_fail_closed(
                "String::into_bytes",
                "receiver is not the String datatype",
                destination,
                target,
            );
        }
        let fields = StringFields::extract(s);
        let bytes =
            OwnedBytes { ptr: fields.ptr, len: fields.len, cap: fields.cap, data: fields.data };
        let Some(vec_expr) = Self::build_owned_bytes_for_sort(&bytes, &dest_sort) else {
            return self.string_bytes_fail_closed(
                "String::into_bytes",
                "destination sort is not the (ptr, len, cap, data) Vec model",
                destination,
                target,
            );
        };
        self.assign_value_to_place(destination, vec_expr);
        debug!("StringIntoBytes: layout identity String -> Vec<u8> (BMC)");
        target
    }

    /// Fail-closed exit shared by the two stubs above: record the fallback (so
    /// the verdict is demoted), leave the destination unconstrained, and keep
    /// the successor edge. Never `None` — the STRING_STUBS router turns `None`
    /// into `Diverge`, which would prune the path instead of failing closed.
    fn string_bytes_fail_closed(
        &mut self,
        construct: &'static str,
        detail: &'static str,
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        warn!(construct, detail, "fail-closed: symbolic destination + fallback demotion");
        self.ctx.unsupported_with_fallback(construct, detail);
        self.codegen_symbolic_result(destination);
        target
    }

    /// Resolve a by-value `Vec<u8>` operand to its (ptr, len, cap, data) fields.
    fn resolve_owned_bytes_from_vec(&mut self, operand: &Operand) -> Option<OwnedBytes> {
        let (_base, vec_expr) = self.resolve_collection_base(operand)?;
        let VecFields { ptr, len, cap, data, .. } = Self::extract_all_vec_fields(&vec_expr)?;
        // Only a byte array can back a String.
        let elem = data.sort().array_sort()?.element_sort.clone();
        if elem != bv8_sort() {
            return None;
        }
        Some(OwnedBytes { ptr, len, cap, data })
    }

    /// Re-wrap (ptr, len, cap, data) in `target_sort`'s single constructor,
    /// matching fields BY NAME so the String and Vec<u8> models can be
    /// exchanged without assuming field order. `None` when the sort is not a
    /// four-field (ptr, len, cap, data) datatype or the data sorts differ.
    fn build_owned_bytes_for_sort(bytes: &OwnedBytes, target_sort: &Sort) -> Option<Expr> {
        let dt = target_sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        if dt.constructors.len() != 1 || ctor.fields.len() != 4 {
            return None;
        }
        let fields: Option<Vec<Expr>> = ctor
            .fields
            .iter()
            .map(|field| {
                let value = match field.name.as_str() {
                    "fld_ptr" | "ptr" => bytes.ptr.clone(),
                    "fld_len" | "len" => bytes.len.clone(),
                    "fld_cap" | "cap" => bytes.cap.clone(),
                    "fld_data" | "data" => bytes.data.clone(),
                    _ => return None,
                };
                (*value.sort() == field.sort).then_some(value)
            })
            .collect();
        Some(Expr::datatype_constructor(&dt.name, &ctor.name, fields?, target_sort.clone()))
    }

    pub(in crate::codegen_ay::statement) fn codegen_str_from_utf8_stub(
        &mut self,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        if !args.is_empty()
            && let Some(slice) = self.try_resolve_concrete_byte_slice(&args[0])
            && let Some(result_sort) = self.infer_sort_from_place(destination)
            && let Some(ok_sort) = Self::result_variant_field_sort(&result_sort, "Ok")
        {
            let result_expr = match String::from_utf8(slice.bytes.clone()) {
                Ok(_) => self.build_slice_value_for_sort(&slice, &ok_sort).and_then(|ok_payload| {
                    self.build_result_variant_expr(&result_sort, "Ok", ok_payload)
                }),
                Err(_) => self.build_symbolic_result_err_expr(&result_sort),
            };
            if let Some(result_expr) = result_expr {
                self.assign_value_to_place(destination, result_expr);
                debug!("StrFromUtf8: concrete Result semantics (BMC)");
                return target;
            }
        }

        debug!("StrFromUtf8: symbolic Result over-approximation (BMC)");
        self.codegen_symbolic_result(destination);
        target
    }

    fn try_resolve_concrete_byte_slice(&mut self, operand: &Operand) -> Option<ConcreteByteSlice> {
        let (_base, slice_expr) = self.resolve_collection_base(operand)?;
        let (ptr, len, data) = Self::extract_slice_fields(&slice_expr)?;
        let len_usize = self.const_usize(&len)?;
        if len_usize > MAX_CONCRETE_UTF8_BYTES {
            return None;
        }
        let bytes = self.try_extract_raw_bytes_from_array(&data, len_usize)?;
        Some(ConcreteByteSlice { ptr, len, data, bytes })
    }

    /// A usize-valued expression folded to a constant: a literal, or a
    /// `bvadd`/`bvsub`/`bvmul` chain of literals (what `Vec::push` leaves in
    /// `fld_len` and in the store indices of a push-built Vec), after SSA
    /// variables and selectors have been peeled (`peel_concrete`).
    fn const_usize(&self, expr: &Expr) -> Option<usize> {
        let peeled = self.peel_concrete(expr, MAX_CONCRETE_PEEL);
        Self::extract_const_usize(&peeled)
            .or_else(|| self.const_i128(&peeled).and_then(|v| usize::try_from(v).ok()))
    }

    /// Rewrite `e` with every SSA variable replaced by its cached concrete
    /// definition and every selector-over-constructor folded. `Vec::push`
    /// leaves `bvadd(fld_len(Var), 1)` and `store(fld_data(Var), fld_len(Var),
    /// byte)` behind, where `Var` is the SSA alias of `Vec_mk(ptr, 0, 0,
    /// const_array(..))`; only once the alias is followed does the selector
    /// fold and the chain become a literal one. Every rewrite is an equality
    /// the SSA assertions already state — nothing is invented — and anything
    /// unresolvable is returned unchanged (the callers then decline).
    fn peel_concrete(&self, e: &Expr, depth: usize) -> Expr {
        if depth == 0 {
            return e.clone();
        }
        match e.value() {
            ExprValue::Var { .. } => {
                let followed =
                    self.follow_ssa(e, crate::codegen_ay::statement::codegen_copy::MAX_PTR_PEEL);
                if followed == *e { e.clone() } else { self.peel_concrete(&followed, depth - 1) }
            }
            ExprValue::DatatypeSelector { datatype_name, selector_name, expr } => {
                let inner = self.peel_concrete(expr, depth - 1);
                if inner == *expr {
                    return e.clone();
                }
                // The fold yields the constructor ARGUMENT, which is itself a
                // term over the previous SSA value (`Vec::push` rebuilds every
                // field from selectors of the old Vec) — peel it in turn.
                match inner.try_field_select(
                    datatype_name.as_str(),
                    selector_name.as_str(),
                    e.sort().clone(),
                ) {
                    Ok(folded) if folded != *e => self.peel_concrete(&folded, depth - 1),
                    _ => e.clone(),
                }
            }
            ExprValue::BvAdd(a, b) => {
                self.peel_concrete(a, depth - 1).bvadd(self.peel_concrete(b, depth - 1))
            }
            ExprValue::BvSub(a, b) => {
                self.peel_concrete(a, depth - 1).bvsub(self.peel_concrete(b, depth - 1))
            }
            ExprValue::Store { array, index, value } => self
                .peel_concrete(array, depth - 1)
                .store(self.peel_concrete(index, depth - 1), self.peel_concrete(value, depth - 1)),
            _ => e.clone(),
        }
    }

    fn extract_slice_fields(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
        let dt_name = expr.sort().datatype_name()?;
        let ptr = expr.clone().field_select(dt_name, "fld_ptr", ptr_sort());
        let len = expr.clone().field_select(dt_name, "fld_len", ptr_sort());
        let data_sort = Sort::array(ptr_sort(), bv8_sort());
        let data = expr.clone().field_select(dt_name, "fld_data", data_sort);
        Some((ptr, len, data))
    }

    fn extract_const_usize(expr: &Expr) -> Option<usize> {
        if let ExprValue::BitVecConst { value, .. } = expr.value() {
            u64::try_from(value).ok().map(|v| v as usize)
        } else {
            None
        }
    }

    /// Read the first `len` bytes of a store chain as concrete values.
    ///
    /// SOUNDNESS: returns `None` unless EVERY index below `len` is pinned to a
    /// literal — by a store with a foldable constant index and a literal byte
    /// (the newest store wins), or by a `const_array` whose default IS a
    /// literal. A `const_array` over a symbolic default (what `Vec::new` seeds)
    /// or a bare array variable leaves unseen bytes unconstrained, and
    /// treating them as anything concrete would decide UTF-8 validity for a
    /// byte the program never fixed. A store at a non-foldable index is
    /// likewise a decline: it may target one of the bytes below `len`.
    fn try_extract_raw_bytes_from_array(&self, data: &Expr, len: usize) -> Option<Vec<u8>> {
        let mut bytes = vec![0u8; len];
        let mut found = vec![false; len];
        let data = self.peel_concrete(data, MAX_CONCRETE_PEEL);
        let mut current = &data;
        loop {
            match current.value() {
                ExprValue::Store { array, index, value } => {
                    let idx = self.const_usize(index)?;
                    if idx < len && !found[idx] {
                        let ExprValue::BitVecConst { value: byte_val, .. } = value.value() else {
                            return None;
                        };
                        bytes[idx] = u8::try_from(byte_val.clone()).ok()?;
                        found[idx] = true;
                    }
                    current = array;
                }
                ExprValue::ConstArray { value, .. } => {
                    if found.iter().all(|seen| *seen) {
                        break;
                    }
                    let ExprValue::BitVecConst { value: byte_val, .. } = value.value() else {
                        return None;
                    };
                    let byte = u8::try_from(byte_val.clone()).ok()?;
                    for (idx, seen) in found.iter().enumerate() {
                        if !seen {
                            bytes[idx] = byte;
                        }
                    }
                    break;
                }
                ExprValue::Var { .. } => {
                    if found.iter().any(|seen| !seen) {
                        return None;
                    }
                    break;
                }
                _ => return None,
            }
        }
        Some(bytes)
    }

    fn result_variant_field_sort(result_sort: &Sort, bare_name: &str) -> Option<Sort> {
        let dt = result_sort.datatype_sort()?;
        let is_match: fn(&str) -> bool = match bare_name {
            "Ok" => names::is_ok_constructor,
            "Err" => names::is_err_constructor,
            _ => return None,
        };
        dt.constructors
            .iter()
            .find(|ctor| is_match(&ctor.name) && ctor.fields.len() == 1)
            .map(|ctor| ctor.fields[0].sort.clone())
    }

    fn build_result_variant_expr(
        &mut self,
        result_sort: &Sort,
        bare_name: &str,
        value: Expr,
    ) -> Option<Expr> {
        let dt = result_sort.datatype_sort()?;
        let is_match: fn(&str) -> bool = match bare_name {
            "Ok" => names::is_ok_constructor,
            "Err" => names::is_err_constructor,
            _ => return None,
        };
        let ctor =
            dt.constructors.iter().find(|ctor| is_match(&ctor.name) && ctor.fields.len() == 1)?;
        Some(Expr::datatype_constructor(&dt.name, &ctor.name, vec![value], result_sort.clone()))
    }

    fn build_symbolic_result_err_expr(&mut self, result_sort: &Sort) -> Option<Expr> {
        let err_sort = Self::result_variant_field_sort(result_sort, "Err")?;
        let name = self.ctx.fresh_name("utf8_err");
        let err = self.ctx.declare_var(&name, err_sort);
        self.ctx.bmc_sound_havoc("utf8_symbolic_err");
        self.build_result_variant_expr(result_sort, "Err", err)
    }

    fn build_slice_value_for_sort(
        &self,
        slice: &ConcreteByteSlice,
        target_sort: &Sort,
    ) -> Option<Expr> {
        if target_sort.is_array() {
            return Some(slice.data.clone());
        }
        if target_sort.is_bitvec() {
            let width = target_sort.bitvec_width()?;
            let ptr = if slice.ptr.sort().bitvec_width() == Some(width) {
                slice.ptr.clone()
            } else {
                coerce_bitvec_width_safe(slice.ptr.clone(), width, SignExtension::ZeroExtend)
            };
            return Some(ptr);
        }

        let dt = target_sort.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        let fields: Option<Vec<Expr>> = ctor
            .fields
            .iter()
            .map(|field| match field.name.as_str() {
                "fld_ptr" | "ptr" => Some(slice.ptr.clone()),
                "fld_len" | "len" => Some(slice.len.clone()),
                "fld_data" | "data" => Some(slice.data.clone()),
                _ => None,
            })
            .collect();
        Some(Expr::datatype_constructor(&dt.name, &ctor.name, fields?, target_sort.clone()))
    }
}
