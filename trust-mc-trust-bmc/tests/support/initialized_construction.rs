// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Explicit test twins for the archived, obsolete Undef construction spelling.
//! The archived bytes remain unchanged and are independently tested as UB.
//! These twins preserve every evaluated field, result identity and later
//! instruction; they are not new compiler captures or proof authority.

pub fn complete_construction_twin(original: &trust_ir::Module) -> trust_ir::Module {
    use trust_ir::{Inst, Ty};
    let mut twin = original.clone();
    let mut replaced = 0;
    for function in &mut twin.functions {
        for block in &mut function.blocks {
            let mut at = 0;
            while at + 2 < block.body.len() {
                let Inst::Undef { ty } = &block.body[at].inst else {
                    at += 1;
                    continue;
                };
                let ty = ty.clone();
                let fields = match &ty {
                    Ty::Struct(id) => original.struct_def(*id).unwrap().fields.len(),
                    Ty::Tuple(fields) => fields.len(),
                    _ => panic!("unexpected archived Undef construction type {ty:?}"),
                };
                assert_eq!(fields, 2, "pin the actual two archived construction lanes");
                let mut previous = block.body[at].results[0];
                let mut values = Vec::new();
                for field in 0..fields {
                    let node = &block.body[at + 1 + field];
                    let Inst::InsertField { ty: actual, aggregate, field: lane, value } =
                        &node.inst
                    else {
                        panic!("archive no longer has contiguous complete field writes")
                    };
                    assert_eq!(actual, &ty);
                    assert_eq!(*aggregate, previous);
                    assert_eq!(*lane as usize, field);
                    assert!(node.proofs.is_empty(), "the twin must import no annotation");
                    values.push(*value);
                    previous = node.results[0];
                }
                let seed = &mut block.body[at];
                assert!(
                    seed.proofs.iter().all(|proof| matches!(
                        proof,
                        trust_ir::ProofAnnotation::FreshSymbolicHavoc
                    ))
                );
                seed.proofs.clear();
                seed.inst = Inst::MakeAggregate { ty: ty.clone(), variant: None, fields: values };
                let mut previous = seed.results[0];
                // Keep instruction positions and SSA IDs, so the unchanged
                // obligation-site roster still names the same later checks.
                for node in &mut block.body[at + 1..=at + fields] {
                    node.inst = Inst::Copy { ty: ty.clone(), operand: previous };
                    previous = node.results[0];
                }
                replaced += 1;
                at += fields + 1;
            }
        }
    }
    assert_eq!(replaced, 1, "each exact archived module contains one obsolete seed");
    let errors = trust_ir_build::validate_module(&twin);
    assert!(errors.is_empty(), "explicit initialized twin: {errors:?}");
    twin
}
