// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! BMC concrete filter_map replay for iterator collect.
//!
//! When `vec!["tofu", "93"].iter().filter_map(|s| s.parse::<i32>().ok()).collect()`
//! appears in MIR, this module extracts strings from array aggregates, evaluates
//! parsing at codegen time, and builds a concrete Vec with the results.
//!
//! Part of #3189: Missing MIR bodies for stdlib functions blocks CHC fn_inline handler.

use ay_bindings::Expr;
use rustc_public::mir::Place;
use tracing::debug;

use super::super::StatementCodegen;
use crate::codegen_ay::types::CtorFieldExt;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Try to build a concrete Vec from MIR filter_map(parse.ok()).collect() chains.
    ///
    /// Extracts string constants from MIR `[&str; N]` array aggregates,
    /// checks for a parse closure in the MIR body, evaluates parsing at codegen time,
    /// and builds a concrete Vec with the parsed results.
    ///
    /// Part of #3189: BMC concrete replay for parse.rs PROOF.
    #[must_use]
    pub(in crate::codegen_ay::statement) fn try_concrete_filter_map_collect_from_mir(
        &mut self,
        destination: &Place,
    ) -> Option<Expr> {
        use crate::codegen_ay::types::POINTER_WIDTH;
        use rustc_public::mir::{AggregateKind, Rvalue, StatementKind, TerminatorKind};
        use rustc_public::ty::{RigidTy, TyKind};

        // Step 1: Scan MIR body for [&str; N] array aggregates.
        let mut source_strs: Option<Vec<String>> = None;
        for bb in &self.body.blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(_, Rvalue::Aggregate(kind, operands)) = &stmt.kind else {
                    continue;
                };
                let AggregateKind::Array(elem_ty) = kind else {
                    continue;
                };
                if operands.is_empty() || operands.len() > 16 {
                    continue;
                }
                let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = elem_ty.kind() else {
                    continue;
                };
                if !matches!(inner.kind(), TyKind::RigidTy(RigidTy::Str)) {
                    continue;
                }
                let strs: Option<Vec<String>> = operands
                    .iter()
                    .map(|op| match op {
                        rustc_public::mir::Operand::Constant(c) => self.try_extract_str_constant(
                            &rustc_public::mir::Operand::Constant(c.clone()),
                        ),
                        rustc_public::mir::Operand::Move(place)
                        | rustc_public::mir::Operand::Copy(place) => {
                            Self::resolve_str_from_local_assign(&self.body.blocks, place.local)
                        }
                    })
                    .collect();
                if let Some(s) = strs {
                    source_strs = Some(s);
                    break;
                }
            }
            if source_strs.is_some() {
                break;
            }
        }
        let source_strs = source_strs?;

        // Step 2: Check MIR body for a filter_map call.
        let has_filter_map = self.body.blocks.iter().any(|bb| {
            if let TerminatorKind::Call { func: rustc_public::mir::Operand::Constant(c), .. } =
                &bb.terminator.kind
            {
                let path = format!("{:?}", c.const_.ty());
                return path.contains("filter_map");
            }
            false
        });
        if !has_filter_map {
            return None;
        }

        // Step 3: Infer the output element sort from the destination place.
        let dest_sort = self.infer_sort_from_place(destination)?;
        let vec_dt = dest_sort.datatype_sort()?;
        let data_field = vec_dt.constructors.first()?.field("fld_data")?;
        let elem_sort = data_field.sort.array_sort()?.element_sort.clone();
        let elem_width = elem_sort.bitvec_width()?;

        // Step 4: Parse strings at codegen time and build BV constants.
        let mut output_elems = Vec::new();
        for text in &source_strs {
            if let Ok(parsed) = text.parse::<i128>() {
                let max = (1i128 << (elem_width - 1)) - 1;
                let min = -(1i128 << (elem_width - 1));
                if parsed >= min && parsed <= max {
                    output_elems.push(Expr::bitvec_const(parsed, elem_width));
                }
            }
            // Non-parseable strings are filtered out (filter_map semantics).
        }

        // Step 5: Build a concrete Vec from the parsed elements.
        let idx_sort = crate::codegen_ay::types::ptr_sort();
        let default_name = self.ctx.fresh_name("filter_map_default");
        let default_elem = self.ctx.declare_var(&default_name, elem_sort.clone());
        let mut data = Expr::const_array(idx_sort, default_elem);
        for (i, elem) in output_elems.iter().enumerate() {
            let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
            data = data.store(idx, elem.clone());
        }
        let len = Expr::bitvec_const(output_elems.len() as u128, POINTER_WIDTH);

        // Allocate via heap model so the pointer is registered as valid.
        let elem_bv_width = elem_width as u64;
        let alloc_size = Expr::bitvec_const(
            (output_elems.len() as u128) * (elem_bv_width as u128 / 8),
            POINTER_WIDTH,
        );
        let align = Expr::bitvec_const(8u128, POINTER_WIDTH);
        let ptr = self.ctx.heap_alloc(alloc_size, align);

        let data_sort = data.sort().clone();
        let vec_sort_name = crate::codegen_ay::names::vec_sort_name(
            &crate::codegen_ay::names::sort_short_name(&elem_sort),
        );
        let vec_sort = crate::codegen_ay::names::struct_sort(
            vec_sort_name.clone(),
            crate::codegen_ay::names::vec_fields(data_sort),
        );
        let ctor_name = crate::codegen_ay::names::resolve_ctor_name(&vec_sort, &vec_sort_name);

        debug!(
            source_count = source_strs.len(),
            output_count = output_elems.len(),
            "try_concrete_filter_map_collect_from_mir: concrete Vec built (#3189)"
        );
        Some(Expr::datatype_constructor(
            vec_sort_name,
            ctor_name,
            vec![ptr, len.clone(), len, data],
            vec_sort,
        ))
    }

    /// Resolve a `&str` constant from a local's assignment in MIR.
    ///
    /// Scans all basic blocks for `Assign(local, Use(Constant(...)))` where the
    /// constant is a `&str`, and extracts the string bytes via provenance following.
    ///
    /// Part of #3189: handles `Move(_N)` operands in `[&str; N]` array aggregates
    /// where MIR optimizer hoisted one constant into a local.
    fn resolve_str_from_local_assign(
        blocks: &[rustc_public::mir::BasicBlock],
        local: usize,
    ) -> Option<String> {
        use rustc_public::mir::alloc::GlobalAlloc;
        use rustc_public::mir::{Operand, Rvalue, StatementKind};
        use rustc_public::ty::{ConstantKind, RigidTy, TyConstKind, TyKind};

        for bb in blocks {
            for stmt in &bb.statements {
                let StatementKind::Assign(place, rvalue) = &stmt.kind else {
                    continue;
                };
                if place.local != local {
                    continue;
                }
                let Rvalue::Use(Operand::Constant(c)) = rvalue else {
                    continue;
                };
                let mir_const = &c.const_;
                let ty = mir_const.ty();
                let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _)) = ty.kind() else {
                    continue;
                };
                if !matches!(pointee_ty.kind(), TyKind::RigidTy(RigidTy::Str)) {
                    continue;
                }
                let alloc = match mir_const.kind() {
                    ConstantKind::Allocated(alloc) => alloc.clone(),
                    ConstantKind::Ty(ty_const) => match ty_const.kind() {
                        TyConstKind::Value(_, alloc) => alloc.clone(),
                        _ => continue,
                    },
                    _ => continue,
                };
                let ptr_bytes = (crate::codegen_ay::types::POINTER_WIDTH / 8) as usize;
                let (_, prov) = alloc.provenance.ptrs.first()?;
                let GlobalAlloc::Memory(target) = GlobalAlloc::from(prov.0) else {
                    continue;
                };
                if alloc.bytes.len() < ptr_bytes * 2 {
                    continue;
                }
                let mut len_arr = [0u8; 8];
                for (i, opt_byte) in alloc.bytes[ptr_bytes..ptr_bytes * 2].iter().enumerate() {
                    len_arr[i] = (*opt_byte)?;
                }
                let len = u64::from_le_bytes(len_arr) as usize;
                if len == 0 || len > 256 || target.bytes.len() < len {
                    continue;
                }
                let bytes: Option<Vec<u8>> =
                    (0..len).map(|i| target.bytes.get(i).copied()?).collect();
                return String::from_utf8(bytes?).ok();
            }
        }
        None
    }
}
