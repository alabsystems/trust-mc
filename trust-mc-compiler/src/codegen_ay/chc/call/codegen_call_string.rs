// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! String core operation call handling.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.

mod codegen_call_string_backing;
mod codegen_call_string_conversion;
mod codegen_call_string_lifecycle;
mod codegen_call_string_nth;
mod codegen_call_string_parse;
mod codegen_call_string_raw_parts;
mod codegen_call_string_raw_parts_dst;
mod codegen_call_string_utf8;
mod codegen_call_string_whitespace;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use ay_bindings::Expr;

use crate::codegen_ay::names;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{POINTER_WIDTH, bool_sort};

use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use codegen_call_string_conversion::CallStringConversion;
use codegen_call_string_lifecycle::CallStringLifecycle;
use codegen_call_string_parse::CallStringParse;
use codegen_call_string_whitespace::CallStringWhitespace;
use tracing::{debug, warn};

/// Extension trait for String core operation call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallString {
    fn codegen_call_string_core(&mut self, cx: &ChcCallContext<'_>);
}

impl<'tcx, 'body> CallString for ChcCtx<'tcx, 'body> {
    /// Handle String core operation stubs (Part of #2196).
    ///
    /// String operations are modeled with tracked length and unconstrained content.
    /// Same pattern as Vec but with String-specific semantics.
    fn codegen_call_string_core(&mut self, cx: &ChcCallContext<'_>) {
        let stub = cx.stub;
        let args = cx.args;
        let destination = cx.destination;
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;
        let dest_local: usize = destination.local;
        debug!("string_core_stub stub={:?} dest={}", stub, dest_local);
        // Part of #2486: collect extras instead of stmt_constraints.to_vec().
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        // Resolve collection local for length tracking
        let collection_local = self.resolve_collection_local(args);

        match stub {
            StubKind::StringNew => {
                self.codegen_string_new(dest_local, &mut extra_constraints, &mut extra_dests);
            }
            StubKind::StringFromRawParts => {
                // String::from_raw_parts(ptr, len, cap) — Vec<u8> reinterpret.
                // Repackage the source Vec<u8> into a String so downstream
                // equality handlers can read the actual backing bytes.
                let repackaged = self
                    .resolve_string_from_raw_parts_source_local(args)
                    .or(collection_local)
                    .and_then(|vec_local| {
                        self.resolve_string_from_raw_parts_vec_fields(vec_local, modified_locals)
                    })
                    .and_then(|fields| {
                        let (_, dest_var) = self.resolve_destination(dest_local)?;
                        let dest_sort = dest_var.sort().clone();
                        let dt_name = dest_sort.datatype_name()?.to_owned();
                        self.ref_resolution
                            .const_ref_values
                            .insert(dest_local, fields.data.clone());
                        self.ref_resolution.subslice_len.insert(dest_local, fields.len.clone());
                        self.ref_resolution.subslice_offset.remove(&dest_local);
                        Some((
                            fields.len.clone(),
                            Expr::datatype_constructor(
                                &dt_name,
                                names::cons_name(&dt_name),
                                vec![fields.ptr, fields.len, fields.cap, fields.data],
                                dest_sort,
                            ),
                        ))
                    });

                let len_expr = repackaged
                    .as_ref()
                    .map(|(len, _)| len.clone())
                    .or_else(|| self.translate_operand_with_modified(&args[1], modified_locals));

                if let Some(len_expr) = len_expr
                    && let Some(dst_len_var) =
                        self.collections.len_state.get_len_var(dest_local).cloned()
                {
                    debug!(dest_local, %dst_len_var, "StringFromRawParts: setting len");
                    self.collection_len_set(
                        &dst_len_var,
                        len_expr,
                        &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                    );
                }

                if let Some((_, string_expr)) = repackaged
                    && let Some((_, dest_var)) = self.resolve_destination(dest_local)
                    && let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        string_expr,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_string_core::StringFromRawParts",
                    )
                {
                    extra_constraints.push(eq);
                }
                extra_dests.push(dest_local);
            }
            StubKind::StringFrom | StubKind::StringFromUtf8Lossy => {
                // dest = symbolic String. Try to constrain tracked len from input &str.
                // Part of #3582: Propagate input length to enable downstream len() proofs.
                let input_len: Option<Expr> = collection_local.and_then(|arg_local| {
                    // Path 1: subslice_len tracks the &str argument's known length.
                    if let Some(len) = self.ref_resolution.subslice_len.get(&arg_local) {
                        debug!(arg_local, "StringFrom: input len from subslice_len");
                        return Some(len.clone());
                    }
                    // Path 2: argument has a tracked collection length.
                    if let Some(len_var) =
                        self.collections.len_state.get_len_var(arg_local).cloned()
                    {
                        debug!(arg_local, "StringFrom: input len from collection len_state");
                        return Some(self.collection_current_len(&len_var));
                    }
                    // Path 3: argument has a Datatype state var with fld_len.
                    if let Some(idx) =
                        self.state_var_mgr.local_to_state_idx.get(&arg_local).copied()
                    {
                        if let Some((name, sort)) = self.state_var_mgr.state_vars.get(idx) {
                            let expr = Expr::var(&**name, sort.clone());
                            if let Some(dt_name) = sort.datatype_name() {
                                if sort
                                    .datatype_sort()
                                    .and_then(|dt| dt.constructors.first())
                                    .map_or(false, |ctor| {
                                        ctor.fields.iter().any(|f| f.name == "fld_len")
                                    })
                                {
                                    debug!(
                                        arg_local,
                                        %dt_name,
                                        "StringFrom: input len from Datatype fld_len"
                                    );
                                    return Some(expr.field_select(
                                        dt_name,
                                        "fld_len",
                                        crate::codegen_ay::types::ptr_sort(),
                                    ));
                                }
                            }
                        }
                    }
                    None
                });
                // Path 4: const &str literal — extract length from MIR allocation.
                // When args[0] is Operand::Constant (e.g., `String::from("Mark")`),
                // collection_local is None, so paths 1-3 are skipped. Read the
                // length word directly from the fat pointer allocation bytes.
                let input_len = input_len.or_else(|| {
                    let arg = args.first()?;
                    let len = Self::extract_str_len_from_const_operand(arg)?;
                    debug!(len, "StringFrom: const &str literal length");
                    Some(Expr::bitvec_const(len as u128, POINTER_WIDTH))
                });
                // Clone input_len before collection_len_set consumes it —
                // needed below for obj_size allocation constraint and the
                // flattened fld_len pin.
                let input_len_for_alloc = input_len.clone();
                let input_len_for_field = input_len.clone();
                if let Some(src_len) = input_len
                    && let Some(dst_len_var) =
                        self.collections.len_state.get_len_var(dest_local).cloned()
                {
                    debug!(dest_local, %dst_len_var, "StringFrom: propagating input length");
                    self.collection_len_set(
                        &dst_len_var,
                        src_len,
                        &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                    );
                }

                // Part of #3582 follow-up: for a *flattened* destination String,
                // also pin the datatype `fld_len` field (RustString layout index 1)
                // to the input length. `StringAsStr` (#4071) reads the flattened
                // `fld_len` as the authoritative &str length, so constraining only
                // the `len_state` var (above) is silently overridden by the
                // unconstrained `fld_len` field — the solver then picks len == 0 and
                // spuriously fails downstream `str::len()` proofs (e.g.
                // `String::from("Mark").as_str().len() > 0`).
                //
                // SOUND: only for `StubKind::StringFrom` (excludes
                // `StringFromUtf8Lossy`, whose lossy U+FFFD replacement can change
                // the byte length). For every `From<str-like>` (&str/&String/Box<str>/
                // Cow<str>) the output byte length equals the input byte length
                // exactly, so this is a precision gain, never a dropped check. For
                // `From<char>` and other non-str inputs `input_len` is `None`
                // (paths 1-4 all miss), so no constraint is emitted.
                if stub == StubKind::StringFrom
                    && let Some(len_for_field) = input_len_for_field
                    && self
                        .flatten
                        .flattened_local_field_count
                        .get(&dest_local)
                        .copied()
                        .unwrap_or(0)
                        >= 2
                {
                    debug!(dest_local, "StringFrom: pinning flattened fld_len to input length");
                    self.constrain_flattened_fields_for_call(
                        dest_local,
                        &[None, Some(len_for_field)],
                        &mut extra_constraints,
                    );
                }

                // Part of #3655: Allocate a heap object for the String's backing buffer.
                // Without this, fld_ptr is unconstrained and deallocation checks fail
                // because obj_size at the symbolic alloc_id is unknown. The solver can
                // pick an alloc_id that aliases a static object with a mismatched size,
                // producing a spurious Genuine CTREX.
                if let Some(obj_id) = self.heap_state.next_heap_alloc_id() {
                    let obj_id_expr = Expr::bitvec_const(obj_id as i128, 32);
                    let ptr =
                        Expr::bitvec_const(obj_id as i128, 32).concat(Expr::bitvec_const(0, 32));

                    // Constrain the destination's fld_ptr to the allocation pointer.
                    // For flattened RustString, resolve_destination returns fld_ptr (field 0).
                    if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                        if let Some(eq) = self.make_coerced_eq_constraint(
                            &dest_var,
                            ptr,
                            dest_var.sort(),
                            dest_local,
                            "codegen_call_string_core::StringFrom::alloc_ptr",
                        ) {
                            extra_constraints.push(eq);
                        }
                    }

                    // Set obj_size to the string length (concrete if known, symbolic otherwise).
                    let len_32 = input_len_for_alloc
                        .and_then(|len| self.coerce_to_heap_bv32(len))
                        .unwrap_or_else(|| {
                            // Part of #3447: string alloc size is unconstrained.
                            self.record_aggregate_gap("string_alloc_size_unconstrained");
                            declare_pending_var(
                                chc_fresh_name("__string_alloc_size"),
                                ay_bindings::Sort::bitvec(32),
                            )
                        });
                    self.record_known_heap_alloc_size_expr(obj_id, &len_32);
                    let obj_size_in = super::codegen_expr_heap::obj_size_in();
                    let obj_size_out = super::codegen_expr_heap::obj_size_out();
                    extra_constraints
                        .push(obj_size_out.eq(obj_size_in.store(obj_id_expr.clone(), len_32)));

                    // Set obj_valid for the allocation.
                    let obj_valid_in = super::codegen_expr_heap::obj_valid_in();
                    let obj_valid_out = super::codegen_expr_heap::obj_valid_out();
                    extra_constraints.push(
                        obj_valid_out.eq(obj_valid_in.store(obj_id_expr, Expr::bool_const(true))),
                    );

                    self.mark_heap_metadata_modified();
                    debug!(
                        obj_id,
                        dest_local, "StringFrom: allocated heap object for backing buffer"
                    );
                }

                extra_dests.push(dest_local);
            }
            StubKind::StringLen => {
                self.codegen_string_len(
                    dest_local,
                    collection_local,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StringPush => {
                self.codegen_string_push(
                    collection_local,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StringPushStr => {
                self.codegen_string_push_str(collection_local);
            }
            StubKind::StringClear => {
                self.codegen_string_clear(
                    collection_local,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StringTruncate => {
                self.codegen_string_truncate(collection_local);
            }
            StubKind::StringClone => {
                self.codegen_string_clone(
                    dest_local,
                    collection_local,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StringAsStr => {
                self.codegen_string_as_str(
                    dest_local,
                    collection_local,
                    args,
                    modified_locals,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StringIntoBoxedStr => {
                self.codegen_string_into_boxed_str(
                    dest_local,
                    collection_local,
                    modified_locals,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StrFromUtf8 => {
                self.codegen_str_from_utf8(
                    dest_local,
                    args,
                    modified_locals,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::IntParse => {
                self.codegen_int_parse(
                    dest_local,
                    args,
                    modified_locals,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StrBytesNth | StubKind::StrCharsNth => {
                // kani_str_bytes_nth / kani_str_chars_nth (#4161)
                // MIR-rewritten str.bytes/chars().nth(i) -> heap_select on backing array.
                // Part of #4161: uses shared try_build_str_nth_result_expr.
                let is_chars = matches!(stub, StubKind::StrCharsNth);
                let precise_reason = if is_chars {
                    "codegen_call_string_core::StrCharsNth"
                } else {
                    "codegen_call_string_core::StrBytesNth"
                };
                let const_fold_reason = if is_chars {
                    "codegen_call_string_core::StrCharsNth::const_fold"
                } else {
                    "codegen_call_string_core::StrBytesNth::const_fold"
                };
                let mut emitted = false;
                if let Some(backing) = self.resolve_string_backing(&args[0], modified_locals)
                    && let Some(index_expr) =
                        self.translate_operand_with_modified(&args[1], modified_locals)
                    && let Some(dest_sort) = self.str_nth_result_sort(destination)
                {
                    if let Some(result) = self
                        .try_build_str_nth_result_expr(&backing, index_expr, &dest_sort, is_chars)
                        && self.bind_str_nth_result(
                            dest_local,
                            result,
                            &mut extra_constraints,
                            precise_reason,
                        )
                    {
                        emitted = true;
                        extra_dests.push(dest_local);
                        debug!(dest_local, is_chars, "str_nth: precise heap_select result");
                    }
                }
                // Path 2: constant-fold when source &str and index are both concrete.
                if !emitted {
                    if let Some(dest_sort) = self.str_nth_result_sort(destination)
                        && let Some(result) = self.try_const_fold_str_nth(
                            &args[0],
                            &args[1],
                            modified_locals,
                            &dest_sort,
                            is_chars,
                        )
                        && self.bind_str_nth_result(
                            dest_local,
                            result,
                            &mut extra_constraints,
                            const_fold_reason,
                        )
                    {
                        emitted = true;
                        extra_dests.push(dest_local);
                        debug!(dest_local, is_chars, "str_nth: const-folded from MIR allocation");
                    }
                }
                if !emitted {
                    debug!(
                        dest_local,
                        is_chars, "str_nth: backing not resolved, symbolic over-approximation"
                    );
                    self.record_sound_fallback_reason(if is_chars {
                        "str_chars_nth_no_backing"
                    } else {
                        "str_bytes_nth_no_backing"
                    });
                }
                extra_dests.push(dest_local);
            }
            StubKind::SplitWhitespace => {
                self.codegen_split_whitespace(dest_local, args, modified_locals, &mut extra_dests);
            }
            StubKind::SplitWhitespaceNext => {
                self.codegen_split_whitespace_next(
                    dest_local,
                    args,
                    modified_locals,
                    &mut extra_constraints,
                    &mut extra_dests,
                );
            }
            StubKind::StringEq => {
                // Prefer a precise byte-array equality when both operands expose
                // backing bytes; fall back to a symbolic Bool otherwise.
                if let Some((_, dest_var)) = self.resolve_destination(dest_local) {
                    let result = self
                        .try_codegen_precise_string_eq(args, modified_locals)
                        .unwrap_or_else(|| {
                            self.record_sound_fallback_reason("string_eq_imprecise");
                            let sym_name = chc_fresh_name("str_eq");
                            declare_pending_var(sym_name, bool_sort())
                        });
                    if let Some(eq) = self.make_coerced_eq_constraint(
                        &dest_var,
                        result,
                        dest_var.sort(),
                        dest_local,
                        "codegen_call_string_core::StringEq",
                    ) {
                        extra_constraints.push(eq);
                    }
                    extra_dests.push(dest_local);
                }
            }
            _other => {
                // SOUND AUDIT (#3369): unexpected stub with &[] extra_dests — target
                // retains identity (under-approx). Reclassified from record_sound_fallback.
                warn!(?_other, "codegen_call_string_core: unexpected stub — update routing");
                self.record_fallback();
                let new_output_args = self.build_output_args(modified_locals, &[]);
                self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
                return;
            }
        }

        let new_output_args = self.build_output_args(modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            extra_constraints,
        );
    }
}
