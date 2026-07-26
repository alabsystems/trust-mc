// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Test code: unwrap is acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// Tests deleted: test_relation_decl, test_nullary_relation, test_assume_bool_operand,
// test_assume_bitvector_operand, test_assume_int_operand, test_state_var_naming_convention
// Reason: #2312 — tested library types (RelationDecl, AY Expr, format!), not production codegen.

mod assigned_locals_and_goto;
mod basics;
mod classification_and_coerce_drop;
mod encode_block_output_invariants;
mod encode_block_statements;
mod mir_branching_pipeline;
mod mir_option_result;
mod mir_struct_pipeline;
mod primitive_cmp_and_bool_coercion;
mod raw_eq_and_coerce_eq;
mod resolve_bare_local;
mod rules_coverage;
mod store_paths;
mod translate_ty;
