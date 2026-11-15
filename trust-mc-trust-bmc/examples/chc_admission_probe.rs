// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Emit the actual public CHC for a canonically invalid, path-hidden SSA use.
//! Diagnostic input only: this program neither solves nor grants authority.
//! It uses only APIs already present at public824 for exact before/after replay.

use trust_ir::{Inst, ValueId};
use trust_ir_build::{ModuleBuilder, validate_module};
use trust_mc_trust_bmc::{TranslateOptions, trust_ir_function_to_chc_vc};

fn main() {
    let mut mb = ModuleBuilder::new("chc_undefined_after_false_assumption");
    let ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("actual_subject", ty);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let no = fb.bool_const(false);
    fb.assume(no);
    let yes = fb.bool_const(true);
    fb.assert(yes);
    fb.ret(vec![]);
    fb.build();
    let mut module = mb.build().unwrap();
    let Inst::Assert { cond, .. } = &mut module.functions[0].blocks[0].body[3].inst else {
        panic!("actual assert fixture")
    };
    *cond = ValueId::new(999);
    let errors = validate_module(&module);
    assert!(!errors.is_empty(), "the exact reproducer must be invalid IR");
    eprintln!("canonical input errors: {errors:?}");
    let vc =
        trust_ir_function_to_chc_vc(&module, module.functions[0].id, &TranslateOptions::default())
            .expect("actual function selection exists");
    print!("{}", vc.to_horn_smt2());
}
