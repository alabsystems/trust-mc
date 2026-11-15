// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The CHC translator's own tensor-region arms (`crate::tensor_region`).
//!
//! The module input refuses every module that stores a tensor construct
//! before any function is translated
//! (`tests::tensor_region::module_input_refuses_each_tensor_instruction_by_name_before_translation`).
//! These tests hand a tensor body straight to the translator, bypassing that
//! boundary, so the instruction arms themselves are what answer: each fails
//! closed with an unconditional error rule whose diagnostic names the
//! construct, and the value-use collector reports each conservatively.

use trust_ir::constant::Constant;
use trust_ir::{Inst, Ty};

use super::{
    ChcEncoding, TrustIrChcUnsupportedReason, collect_inst_value_uses,
    translate_function_with_encoding,
};
use crate::tests::tensor_region::{
    TENSOR_INSTRUCTIONS, bypassing_body, tensor, tensor_blob_module, tensor_blob_switch_module,
    tensor_instruction_module,
};
use crate::{SemanticsFamily, TensorConstruct, TranslateOptions};

#[test]
fn each_tensor_construct_fails_closed_by_name_in_both_encodings() {
    let mut cases: Vec<(TensorConstruct, trust_ir::Module)> = TENSOR_INSTRUCTIONS
        .iter()
        .map(|construct| (*construct, bypassing_body(tensor_instruction_module(*construct))))
        .collect();
    cases.push((TensorConstruct::TensorBlobConstant, bypassing_body(tensor_blob_module())));
    // A non-blob constant at a tensor type is named by its type.
    let mut typed = bypassing_body(tensor_blob_module());
    typed.functions[0].blocks[0].body[0].inst =
        Inst::Const { ty: tensor(Ty::I32, 0), value: Constant::Int(0) };
    cases.push((TensorConstruct::TensorType, typed));
    // A blob switch case, named rather than refused as a generic switch.
    cases.push((TensorConstruct::TensorBlobConstant, tensor_blob_switch_module()));

    let options = TranslateOptions::default();
    for (construct, module) in cases {
        for encoding in [ChcEncoding::Automatic, ChcEncoding::PerBlock] {
            let output =
                translate_function_with_encoding(&module.functions[0], &module, &options, encoding);
            assert!(output.module_input_refusal.is_none(), "the boundary is bypassed here");
            let named: Vec<_> = output
                .diagnostics
                .iter()
                .filter(|d| d.reason == TrustIrChcUnsupportedReason::TensorRegion(construct))
                .collect();
            assert_eq!(named.len(), 1, "{construct}: {:?}", output.diagnostics);
            assert_eq!(named[0].instruction_index, 0, "{construct}");
            assert!(named[0].result_values.len() <= 1, "{construct}");
            if construct != TensorConstruct::TensorType {
                assert_eq!(named[0].family, SemanticsFamily::Tensors, "{construct}");
            }
            assert!(
                named[0].reason.label().contains(&format!("{construct:?}")),
                "{construct}: {}",
                named[0].reason.label()
            );
            // The fail-closed error rule: the query target is reachable.
            assert!(
                output.vc.rules.iter().any(|rule| rule.head.name == "error"),
                "{construct}: an error rule must be emitted"
            );
        }
    }
}

#[test]
fn the_value_use_collector_reports_each_tensor_instruction_conservatively() {
    for construct in TENSOR_INSTRUCTIONS {
        let module = tensor_instruction_module(construct);
        let inst = &module.functions[0].blocks[0].body[0].inst;
        let mut uses = Vec::new();
        assert!(collect_inst_value_uses(inst, &mut uses), "{construct}: conservative");
    }
    // Control: an enumerable instruction is not conservative.
    let mut uses = Vec::new();
    assert!(!collect_inst_value_uses(
        &Inst::Copy { ty: Ty::U32, operand: trust_ir::ValueId::new(0) },
        &mut uses
    ));
    assert_eq!(uses, vec![trust_ir::ValueId::new(0)]);
}
