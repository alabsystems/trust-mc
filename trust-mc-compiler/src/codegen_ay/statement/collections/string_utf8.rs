// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! UTF-8-specific String collection helpers.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::debug;

use crate::codegen_ay::names;
use crate::codegen_ay::types::{SignExtension, bv8_sort, coerce_bitvec_width_safe, ptr_sort};

use super::StatementCodegen;

struct ConcreteByteSlice {
    ptr: Expr,
    len: Expr,
    data: Expr,
    bytes: Vec<u8>,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
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
        let len_usize = Self::extract_const_usize(&len)?;
        if len_usize > 256 {
            return None;
        }
        let bytes = Self::try_extract_raw_bytes_from_array(&data, len_usize)?;
        Some(ConcreteByteSlice { ptr, len, data, bytes })
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

    fn try_extract_raw_bytes_from_array(data: &Expr, len: usize) -> Option<Vec<u8>> {
        let mut bytes = vec![0u8; len];
        let mut found = vec![false; len];
        let mut current = data;
        loop {
            match current.value() {
                ExprValue::Store { array, index, value } => {
                    if let ExprValue::BitVecConst { value: idx_val, .. } = index.value()
                        && let ExprValue::BitVecConst { value: byte_val, .. } = value.value()
                    {
                        if let (Ok(idx), Ok(byte)) =
                            (usize::try_from(idx_val.clone()), u8::try_from(byte_val.clone()))
                            && idx < len
                            && !found[idx]
                        {
                            bytes[idx] = byte;
                            found[idx] = true;
                        }
                    }
                    current = array;
                }
                ExprValue::ConstArray { value, .. } => {
                    if let ExprValue::BitVecConst { value: byte_val, .. } = value.value()
                        && let Ok(byte) = u8::try_from(byte_val.clone())
                    {
                        for (idx, seen) in found.iter().enumerate() {
                            if !seen {
                                bytes[idx] = byte;
                            }
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
