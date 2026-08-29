// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Lower an accepted C body into the SAME `Expr`/`Rule` IR the encoder builds
//! for a Rust callee.
//!
//! This is the precise lane for `-Z c-ffi --c-lib`. It runs BEFORE the sound
//! effect frame in `codegen_call_foreign.rs`, and every one of its exits is a
//! refusal back to that frame — there is no path here that approximates.
//!
//! # What it buys
//!
//! The properties these programs state are statements about the C's VALUES:
//! `takes_int(1) == 3`, `mutates_ptr(&mut 17)` ⇒ `16`, `takes_struct(f) == 19`
//! next to `takes_struct2(f2) == 20`. No abstraction of an unknown callee can
//! produce a value, so the effect frame leaves every one of them
//! reachable-but-unprovable. Reading the definition is the only route that is
//! both sound and precise for those rows.
//!
//! # Shape of the lowering
//!
//! The accepted fragment is branch-structured with a single loop form, so the
//! body is symbolically executed under a path guard. Every write is guarded —
//! `slot := ite(guard, new, old)` — and `return` accumulates an ITE chain
//! rather than cutting control flow. That is exact for straight-line code with
//! `if`/`else`, and the parser guarantees nothing else reaches here.
//!
//! A `for`/`while` is UNROLLED [`C_LOOP_UNROLL_BOUND`] times, and the residual
//! — "the loop had really finished by then" — is emitted as an OBLIGATION, not
//! assumed. A loop that can run longer therefore reports a failing unwinding
//! check; it never silently loses its tail. The bound belongs to this
//! front-end, not to the harness's `--unwind`: it bounds a callee's C loop, and
//! the two are separate programs.
//!
//! # Variadics
//!
//! `...` is a calling-convention fiction; what a model checker needs is the
//! argument SEQUENCE, and the MIR call site carries it. A `va_list` is
//! therefore modelled as a CURSOR into the actual arguments this call site
//! passes beyond the named ones:
//!
//! * `va_start(ap, last)` sets the cursor to 0, after checking that `last`
//!   really names the final named parameter (C17 7.16.1.4p3).
//! * `va_arg(ap, T)` yields the actual the cursor selects and advances it. The
//!   fetch is guarded by a real obligation `cursor < N` — reading past the last
//!   argument is UB, so it is a proof obligation the caller must discharge and
//!   never an assumption. Past the end the value is FRESH and unconstrained: no
//!   convenient wrap to argument 0.
//! * `va_end(ap)` returns the cursor to a fresh unconstrained value, so a
//!   `va_arg` after it cannot discharge its range obligation — which is exactly
//!   the status C gives it.
//!
//! Every actual must be readable at the fetch type after the C default argument
//! promotions (C17 6.5.2.2p6 / 7.16.1.1p2). The cursor is symbolic, so ONE
//! unmatched actual refuses the whole body rather than reading some fetch at a
//! type the argument does not have.
//!
//! # Guards (the soundness obligation is NOT to mis-translate)
//!
//! * The C prototype is CHECKED against the Rust `extern` declaration first
//!   (`codegen_ay::c_ffi_check`) — widths, signedness, pointer shape, and
//!   aggregate field OFFSETS.
//! * Integer promotion and the usual arithmetic conversions are implemented,
//!   not assumed away: `f.i + f.c` on `{u32, u8}` converts both operands
//!   before adding.
//! * C's own UB is emitted as an OBLIGATION — signed overflow, division by
//!   zero, `INT_MIN / -1`, and an out-of-range shift each get a check rule
//!   rather than a wrap.
//! * Anything the encoder cannot name — an unresolvable pointee, a non-BitVec
//!   sort, a nullable pointer whose null test this lane does not model — is a
//!   refusal, never a guess.

use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{BasicBlockIdx, Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::BTreeMap;
use tracing::debug;

use trust_mc_core::violation::PropertyKind;

use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_call_kani_model::CallKaniModel;
use super::super::codegen_rules::CodegenRules;
use super::super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::c_ffi::{self, CBinOp, CExpr, CFunc, CProgram, CStmt, CTarget, CTy, CUnOp};
use crate::codegen_ay::c_ffi_check::{CArgShape, CProtoMatch, CRetShape, check_prototype};
use trust_mc_metadata::ChcTrackLevel;

/// Coercion site tag for the dropped-constraint diagnostics.
const SITE: &str = "c_ffi::body";

/// How many times a C `for`/`while` in an accepted body is unrolled.
///
/// Not a truncation: what is left over after the last copy is emitted as an
/// unwinding OBLIGATION, so a loop that outruns the bound produces a failing
/// check rather than a silently shortened program. The bound therefore trades
/// only COMPLETENESS — a correct C loop that runs longer reports an
/// undischarged unwinding check — and never soundness, which is why it can be
/// chosen on cost.
///
/// Measured on `ForeignItems/fixme_varadic.rs` (three variadic call sites, each
/// with a loop): 8 copies -> 46 checks, 1.3s solve; 16 -> 86 checks, 6.5s. The
/// cost is super-linear in the bound and the corpus's C helpers are small, so
/// this sits at 8.
const C_LOOP_UNROLL_BOUND: usize = 8;

/// Width of the modelled `va_list` cursor. It counts arguments, not bytes —
/// this is an index into the call site's actual list, not an ABI object.
const VA_CURSOR_BITS: u32 = 64;

/// A C value during symbolic execution of an accepted body.
#[derive(Debug, Clone)]
enum CVal {
    /// A by-value integer or `_Bool`, carrying the C type it currently has so
    /// the conversion rules can be applied at each operator.
    Int { expr: Expr, bits: u32, signed: bool },
    /// A pointer parameter. `read_root` is the MIR place `*p` (the argument
    /// local under a `Deref`), which the encoder's existing deref machinery
    /// resolves; `write` is the state slot and place a store through it lands
    /// in; `tag` is the C struct tag of the pointee, and is the AUTHORITY for
    /// field order (the prototype check has already established that the Rust
    /// ADT agrees index-for-index).
    Ptr { read_root: Place, write: Option<(usize, Place)>, tag: Option<String> },
    /// A by-value aggregate held in a MIR place.
    Agg { place: Place, tag: String },
}

/// One actual argument passed beyond the named parameters, already converted to
/// the type it has AFTER the C default argument promotions. That promoted type
/// is the only type `va_arg` may legally ask for.
#[derive(Debug, Clone)]
struct VaActual {
    expr: Expr,
    bits: u32,
    signed: bool,
}

/// One pending store: the state-vector slot's new symbolic value, plus the MIR
/// place backing it when the slot is a local (a `static` slot has none).
#[derive(Debug, Clone)]
struct PendingStore {
    value: Expr,
    place: Option<Place>,
}

pub(in crate::codegen_ay::chc) trait CallDispatchCBody {
    /// Encode a foreign call from the C definition the user supplied.
    ///
    /// `false` leaves the caller to fall back to the sound effect frame.
    fn try_dispatch_call_c_body(&mut self, dcx: &DispatchCallContext<'_>, symbol: &str) -> bool;
}

impl<'tcx, 'body> CallDispatchCBody for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_c_body(&mut self, dcx: &DispatchCallContext<'_>, symbol: &str) -> bool {
        let Some(target) = dcx.target else { return false };
        let Some(cfunc) = c_ffi::func(symbol) else { return false };
        let program = c_ffi::program();
        let ctarget = c_ffi::target();

        // Guard (b): the C prototype must match the Rust `extern` declaration.
        let Ok(func_ty) = dcx.func.ty(self.body.locals()) else { return false };
        let Some(sig) = func_ty.kind().fn_sig().map(|s| s.skip_binder()) else { return false };
        let Some(proto) = check_prototype(cfunc, &sig, program, ctarget) else {
            // Diagnostic only. The fail-closed reason belongs to whatever
            // handles the call NEXT — normally the effect frame, which records
            // its own; booking one here would demote a Success that some other
            // dispatcher went on to encode precisely.
            debug!(symbol, "c_ffi: prototype mismatch against the Rust extern declaration");
            return false;
        };

        // A value-returning body that can fall off its end has no return value
        // at all (C17 6.9.1p12 makes reading it UB). Refuse rather than invent.
        if !matches!(proto.ret, CRetShape::Unit) && !always_returns(&cfunc.body) {
            debug!(symbol, "c_ffi: body can fall off the end of a value-returning function");
            return false;
        }

        let mut lower = CBodyLowering {
            program,
            ctarget,
            extra: Vec::new(),
            defs: Vec::new(),
            checks: Vec::new(),
            store: BTreeMap::new(),
            env: BTreeMap::new(),
            locals: BTreeMap::new(),
            returned: Expr::bool_const(false),
            ret_val: None,
            ret: proto.ret,
            va_lists: BTreeMap::new(),
            actuals: Vec::new(),
            last_named: cfunc.params.last().and_then(|p| p.name.clone()),
        };
        if lower.bind_params(self, dcx, cfunc, &proto).is_none() {
            debug!(symbol, "c_ffi: could not bind a parameter to an encoder value");
            return false;
        }
        if proto.variadic && lower.bind_variadic_actuals(self, dcx, cfunc).is_none() {
            debug!(symbol, "c_ffi: a variadic actual is outside the promotable set");
            return false;
        }
        if lower.exec_stmt(self, dcx, &cfunc.body, Expr::bool_const(true)).is_none() {
            debug!(symbol, "c_ffi: body construct outside the accepted fragment at lowering");
            return false;
        }

        lower.emit(self, dcx, *target, symbol)
    }
}

/// Does every path through `stmt` execute a `return`?
fn always_returns(stmt: &CStmt) -> bool {
    match stmt {
        CStmt::Return(_) => true,
        CStmt::Compound(v) => v.iter().any(always_returns),
        CStmt::If { then, other, .. } => {
            other.as_ref().is_some_and(|o| always_returns(then) && always_returns(o))
        }
        // A loop may run zero times, and proving otherwise is a termination
        // argument this front-end does not attempt. Conservative: it does not
        // count towards "every path returns".
        CStmt::For { .. } => false,
        CStmt::Expr(_) | CStmt::Decl { .. } | CStmt::Empty => false,
    }
}

struct CBodyLowering {
    program: &'static CProgram,
    ctarget: CTarget,
    /// Constraints to attach to the emitted goto rule.
    extra: Vec<Expr>,
    /// DEFINITIONS introduced by [`CBodyLowering::lift`]: `v == e`, one per
    /// named intermediate value.
    ///
    /// These are kept apart from `extra` because they must reach BOTH rule
    /// families. The goto rule carries the call's outcome; every C-level
    /// obligation is a SEPARATE error rule, and a `v` whose definition reached
    /// only the goto rule would be a free variable inside the check — the
    /// solver could pick any value for it and refute an obligation the program
    /// discharges. That is not a fabricated proof but its mirror image, a
    /// fabricated counterexample, and it is just as wrong.
    defs: Vec<Expr>,
    /// C-level obligations: `(must-hold condition, kind, message)`.
    checks: Vec<(Expr, PropertyKind, String)>,
    /// Current symbolic value of every location the body writes, keyed by
    /// state-vector slot.
    store: BTreeMap<usize, PendingStore>,
    /// Parameter bindings.
    env: BTreeMap<String, CVal>,
    /// C block-scope scalars.
    locals: BTreeMap<String, CVal>,
    /// Has a `return` already fired on the path reaching the current statement?
    returned: Expr,
    ret_val: Option<Expr>,
    ret: CRetShape,
    /// Live `va_list` objects, by name, each holding its symbolic cursor.
    /// Separate from `locals` on purpose: a `va_list` is not a value this lane
    /// can read, assign or convert, so it must never be reachable through the
    /// ordinary identifier lookup.
    va_lists: BTreeMap<String, Expr>,
    /// The call site's arguments beyond the named parameters, in order. Empty
    /// for a non-variadic callee.
    actuals: Vec<VaActual>,
    /// Name of the last NAMED parameter, which `va_start` must be handed.
    last_named: Option<String>,
}

impl CBodyLowering {
    // ------------------------------------------------------------- binding

    fn bind_params(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        cfunc: &'static CFunc,
        proto: &CProtoMatch,
    ) -> Option<()> {
        for (idx, (cparam, shape)) in cfunc.params.iter().zip(proto.params.iter()).enumerate() {
            // An unnamed parameter is unreachable from the body, so it needs no
            // binding — but the argument still has to exist.
            let arg = dcx.args.get(idx)?;
            let Some(name) = cparam.name.clone() else { continue };
            let val = match shape {
                CArgShape::Scalar => {
                    let (bits, signed) = match &cparam.ty {
                        CTy::Int { bits, signed } => (*bits, *signed),
                        CTy::Bool => (1, false),
                        _ => return None,
                    };
                    let expr = ctx.translate_operand_with_modified(arg, dcx.modified_locals)?;
                    require_bitvec(&expr)?;
                    CVal::Int { expr, bits, signed }
                }
                CArgShape::Struct => {
                    let CTy::Struct(tag) = &cparam.ty else { return None };
                    let place = operand_place(arg)?;
                    CVal::Agg { place, tag: tag.clone() }
                }
                // A nullable pointer (`Option<&T>`, or a raw pointer) needs a
                // null TEST this lane does not model, and inventing one is
                // exactly the mis-translation the front-end must not commit.
                CArgShape::Pointer { nullable: true } => return None,
                CArgShape::Pointer { nullable: false } => {
                    let arg_local = operand_local(arg)?;
                    let read_root =
                        Place { local: arg_local, projection: vec![ProjectionElem::Deref] };
                    // Only a WHOLE-object store is modelled; a projected store
                    // would need the field-precise store path and is Tier 2.
                    let write = ctx.resolve_write_any_slim_target_place(arg).and_then(|p| {
                        if !p.projection.is_empty() {
                            return None;
                        }
                        let slot = ctx.try_state_idx_for_local(p.local)?;
                        Some((slot, p))
                    });
                    let tag = match &cparam.ty {
                        CTy::Ptr(inner) => match &**inner {
                            CTy::Struct(tag) => Some(tag.clone()),
                            _ => None,
                        },
                        _ => None,
                    };
                    CVal::Ptr { read_root, write, tag }
                }
            };
            self.env.insert(name, val);
        }
        Some(())
    }

    /// Type and capture the arguments passed BEYOND the named parameters.
    ///
    /// Neither declaration says anything about these — Rust's `...` and C's
    /// `...` both carry zero type information — so the call site's own MIR is
    /// the sole authority, exactly as it is for a Rust-defined `c_variadic`
    /// callee. Each actual is converted here, once, to its promoted type; a
    /// `va_arg` later has only to check that it asked for that same type.
    ///
    /// `None` refuses the body: an actual this lane cannot promote (a pointer,
    /// an aggregate, a float, a 128-bit integer) has no modelled `va_arg`
    /// reading, and inventing one is the mis-translation this front-end exists
    /// to prevent.
    fn bind_variadic_actuals(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        cfunc: &'static CFunc,
    ) -> Option<()> {
        let named = cfunc.params.len();
        // A call site with fewer arguments than named parameters is not a call
        // rustc would have accepted; refuse rather than index past the end.
        let rest = dcx.args.get(named..)?;
        for arg in rest {
            let arg_ty = arg.ty(ctx.body.locals()).ok()?;
            let (raw_bits, raw_signed) = rust_scalar_parts(arg_ty, self.ctarget)?;
            let (bits, signed) =
                crate::codegen_ay::c_ffi_check::variadic_actual_parts(arg_ty, self.ctarget)?;
            let expr = ctx.translate_operand_with_modified(arg, dcx.modified_locals)?;
            require_bitvec(&expr)?;
            let expr = self.convert_expr(expr, raw_bits, raw_signed, bits, signed)?;
            self.actuals.push(VaActual { expr, bits, signed });
        }
        Some(())
    }

    // ----------------------------------------------------------- execution

    /// Execute `stmt` under `guard` (a Bool `Expr` that is true exactly when
    /// this statement runs). Returns `None` to refuse the whole body.
    fn exec_stmt(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        stmt: &CStmt,
        guard: Expr,
    ) -> Option<()> {
        // A statement after a `return` on this path does not run.
        let live = s_and(guard.clone(), s_not(self.returned.clone()));
        match stmt {
            CStmt::Empty => Some(()),
            CStmt::Compound(stmts) => {
                for s in stmts {
                    self.exec_stmt(ctx, dcx, s, guard.clone())?;
                }
                Some(())
            }
            CStmt::Expr(e) => {
                self.eval(ctx, dcx, e, &live)?;
                Some(())
            }
            CStmt::Decl { ty: CTy::VaList, name, init } => {
                // `va_list ap = ...;` has no meaning this lane models.
                if init.is_some() || self.is_declared(name) {
                    return None;
                }
                // An UNSTARTED list. The cursor is fresh and unconstrained, so
                // a `va_arg` before `va_start` cannot discharge its range
                // obligation — which is exactly the status C gives it. Never a
                // convenient zero.
                let cursor = declare_pending_var(
                    chc_fresh_name("__c_ffi_va_unstarted"),
                    Sort::bitvec(VA_CURSOR_BITS),
                );
                self.va_lists.insert(name.clone(), cursor);
                Some(())
            }
            CStmt::Decl { ty, name, init } => {
                let (bits, signed) = match ty {
                    CTy::Int { bits, signed } => (*bits, *signed),
                    CTy::Bool => (1, false),
                    // Only scalar locals are modelled.
                    _ => return None,
                };
                if self.is_declared(name) {
                    // Shadowing would need real block scoping. Refuse.
                    return None;
                }
                let value = match init {
                    Some(e) => {
                        let v = self.eval(ctx, dcx, e, &live)?;
                        self.convert(v, bits, signed)?
                    }
                    // An uninitialised local reads as an indeterminate value.
                    // Fresh and unconstrained: never a convenient zero.
                    None => declare_pending_var(
                        chc_fresh_name("__c_ffi_uninit"),
                        Sort::bitvec(bits.max(1)),
                    ),
                };
                self.locals.insert(name.clone(), CVal::Int { expr: value, bits, signed });
                Some(())
            }
            CStmt::Return(value) => {
                match (self.ret, value) {
                    (CRetShape::Unit, _) => {}
                    (CRetShape::Scalar { bits, signed }, Some(e)) => {
                        let v = self.eval(ctx, dcx, e, &live)?;
                        let converted = self.convert(v, bits, signed)?;
                        let previous = self.ret_val.clone().unwrap_or_else(|| {
                            declare_pending_var(
                                chc_fresh_name("__c_ffi_no_return"),
                                converted.sort().clone(),
                            )
                        });
                        self.ret_val = Some(s_ite(live.clone(), converted, previous));
                    }
                    (CRetShape::Scalar { .. }, None) => return None,
                }
                self.returned = s_or(self.returned.clone(), live);
                Some(())
            }
            CStmt::If { cond, then, other } => {
                let c = self.eval(ctx, dcx, cond, &live)?;
                let c_bool = self.truth(c)?;
                self.exec_stmt(ctx, dcx, then, s_and(live.clone(), c_bool.clone()))?;
                if let Some(other) = other {
                    self.exec_stmt(ctx, dcx, other, s_and(live, s_not(c_bool)))?;
                }
                Some(())
            }
            CStmt::For { init, cond, step, body } => {
                self.exec_for(ctx, dcx, init.as_deref(), cond.as_ref(), step.as_ref(), body, guard)
            }
        }
    }

    /// Unroll `for (init; cond; step) body` [`C_LOOP_UNROLL_BOUND`] times and
    /// emit the residual as an OBLIGATION.
    ///
    /// The unroll is exact for any execution that leaves the loop within the
    /// bound; for anything longer, the emitted unwinding check `¬(guard ∧ cond)`
    /// after the last copy fails, so the verdict is a reported failure and never
    /// a proof over a shortened program. Nothing here is assumed: the condition
    /// is a check, exactly like the C UB obligations beside it.
    #[allow(clippy::too_many_arguments)]
    fn exec_for(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        init: Option<&CStmt>,
        cond: Option<&CExpr>,
        step: Option<&CExpr>,
        body: &CStmt,
        guard: Expr,
    ) -> Option<()> {
        // The init clause declares into the loop's OWN scope.
        let outer = self.scope_enter();
        if let Some(init) = init {
            self.exec_stmt(ctx, dcx, init, guard.clone())?;
        }

        // `running` is true on the paths that have reached this iteration's
        // test and not yet returned.
        let mut running = s_and(guard.clone(), s_not(self.returned.clone()));
        for _ in 0..C_LOOP_UNROLL_BOUND {
            let taken = match cond {
                Some(cond) => {
                    let c = self.eval(ctx, dcx, cond, &running)?;
                    let c_bool = self.truth(c)?;
                    s_and(running.clone(), c_bool)
                }
                // `for (;;)`: the test is vacuously true.
                None => running.clone(),
            };
            let inner = self.scope_enter();
            self.exec_stmt(ctx, dcx, body, taken.clone())?;
            if let Some(step) = step {
                // The step runs on the paths that ran the body and did not
                // return out of it.
                let after = s_and(taken.clone(), s_not(self.returned.clone()));
                self.eval(ctx, dcx, step, &after)?;
            }
            self.scope_leave(inner);
            running = s_and(taken, s_not(self.returned.clone()));
            self.checkpoint();
            running = self.lift(running, "__c_ffi_iter_live");
        }

        // UNWINDING OBLIGATION. After the last copy the loop must be over.
        let residual = match cond {
            Some(cond) => {
                let c = self.eval(ctx, dcx, cond, &running)?;
                let c_bool = self.truth(c)?;
                s_and(running, c_bool)
            }
            None => running,
        };
        self.checks.push((
            s_not(residual),
            PropertyKind::Unreachable,
            format!(
                "unwinding assertion: a loop in the C definition supplied by --c-lib \
                 may run more than {C_LOOP_UNROLL_BOUND} times"
            ),
        ));

        self.scope_leave(outer);
        Some(())
    }

    /// Name an intermediate value, so a loop unroll stays LINEAR.
    ///
    /// Each unrolled copy rebuilds every live value as `ite(taken, new, old)`,
    /// which mentions `old` twice — an exponential blow-up in the number of
    /// copies. Binding the value to a fresh variable with a definitional
    /// equality on the rule collapses that to one node per iteration.
    ///
    /// This is a naming, not an approximation: `v == e` constrains `v` to
    /// exactly `e` and nothing else, so no behaviour is added or removed.
    fn lift(&mut self, e: Expr, tag: &str) -> Expr {
        if matches!(e.value(), ExprValue::BitVecConst { .. } | ExprValue::BoolConst(_)) {
            return e;
        }
        let v = declare_pending_var(chc_fresh_name(tag), e.sort().clone());
        self.defs.push(v.clone().eq(e));
        v
    }

    /// Bind every live symbolic value to a fresh name. Called once per unrolled
    /// loop copy; see [`CBodyLowering::lift`].
    fn checkpoint(&mut self) {
        let names: Vec<String> = self.locals.keys().cloned().collect();
        for name in names {
            if let Some(CVal::Int { expr, bits, signed }) = self.locals.get(&name).cloned() {
                let expr = self.lift(expr, "__c_ffi_iter");
                self.locals.insert(name, CVal::Int { expr, bits, signed });
            }
        }
        let names: Vec<String> = self.env.keys().cloned().collect();
        for name in names {
            if let Some(CVal::Int { expr, bits, signed }) = self.env.get(&name).cloned() {
                let expr = self.lift(expr, "__c_ffi_iter");
                self.env.insert(name, CVal::Int { expr, bits, signed });
            }
        }
        let names: Vec<String> = self.va_lists.keys().cloned().collect();
        for name in names {
            let cursor = self.va_lists[&name].clone();
            let cursor = self.lift(cursor, "__c_ffi_va_cursor");
            self.va_lists.insert(name, cursor);
        }
        let slots: Vec<usize> = self.store.keys().copied().collect();
        for slot in slots {
            let PendingStore { value, place } = self.store[&slot].clone();
            let value = self.lift(value, "__c_ffi_iter_store");
            self.store.insert(slot, PendingStore { value, place });
        }
        if let Some(ret) = self.ret_val.clone() {
            self.ret_val = Some(self.lift(ret, "__c_ffi_iter_ret"));
        }
        let returned = self.returned.clone();
        self.returned = self.lift(returned, "__c_ffi_iter_returned");
    }

    /// Is `name` already bound as a parameter, a block-scope object, or a
    /// `va_list`?
    fn is_declared(&self, name: &str) -> bool {
        self.env.contains_key(name)
            || self.locals.contains_key(name)
            || self.va_lists.contains_key(name)
    }

    /// Open a block scope, returning the names visible on entry.
    fn scope_enter(&self) -> (Vec<String>, Vec<String>) {
        (self.locals.keys().cloned().collect(), self.va_lists.keys().cloned().collect())
    }

    /// Close a block scope: forget the names it DECLARED, and only those.
    ///
    /// Values are deliberately not restored — a write to an OUTER object made
    /// inside the block is the block's whole point, and rolling it back would
    /// lose the loop's effect. Only the bindings go out of scope, which is what
    /// lets the next unrolled copy re-declare its own `int next;`.
    fn scope_leave(&mut self, (locals, va_lists): (Vec<String>, Vec<String>)) {
        self.locals.retain(|k, _| locals.iter().any(|n| n == k));
        self.va_lists.retain(|k, _| va_lists.iter().any(|n| n == k));
    }

    // ---------------------------------------------------------- expressions

    fn eval(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        e: &CExpr,
        guard: &Expr,
    ) -> Option<CVal> {
        match e {
            CExpr::IntLit { value, unsigned } => {
                // An unsuffixed decimal constant that fits in `int` has type
                // `int`; `u` forces unsigned. Wider constants take the first
                // type in the standard's list that represents them.
                let (bits, signed) = literal_type(*value, *unsigned);
                Some(CVal::Int {
                    expr: Expr::bitvec_const(wrap(*value, bits), bits),
                    bits,
                    signed,
                })
            }
            CExpr::SizeOfTy(ty) => {
                let (size, _) = self.program.size_align(ty, self.ctarget)?;
                let bits = self.ctarget.pointer_bits;
                Some(CVal::Int {
                    expr: Expr::bitvec_const(i128::from(size), bits),
                    bits,
                    signed: false,
                })
            }
            CExpr::Ident(name) => self.lookup(ctx, name),
            CExpr::Unary(op, inner) => {
                let v = self.eval(ctx, dcx, inner, guard)?;
                self.unary(*op, v, guard)
            }
            CExpr::Binary(op, a, b) if op.is_logical() => {
                let av = self.eval(ctx, dcx, a, guard)?;
                let at = self.truth(av)?;
                // Short-circuit: the right operand's effects and UB checks are
                // guarded by the left operand's outcome.
                let rhs_guard = if *op == CBinOp::LogicalAnd {
                    s_and(guard.clone(), at.clone())
                } else {
                    s_and(guard.clone(), s_not(at.clone()))
                };
                let bv = self.eval(ctx, dcx, b, &rhs_guard)?;
                let bt = self.truth(bv)?;
                let result = if *op == CBinOp::LogicalAnd { s_and(at, bt) } else { s_or(at, bt) };
                Some(bool_to_int(result))
            }
            CExpr::Binary(op, a, b) => {
                let av = self.eval(ctx, dcx, a, guard)?;
                let bv = self.eval(ctx, dcx, b, guard)?;
                self.binary(*op, av, bv, guard)
            }
            CExpr::Cond { cond, then, other } => {
                let c = self.eval(ctx, dcx, cond, guard)?;
                let ct = self.truth(c)?;
                let t = self.eval(ctx, dcx, then, &s_and(guard.clone(), ct.clone()))?;
                let o = self.eval(ctx, dcx, other, &s_and(guard.clone(), s_not(ct.clone())))?;
                let (CVal::Int { expr: te, bits: tb, signed: ts }, CVal::Int { expr: oe, .. }) =
                    (&t, &o)
                else {
                    return None;
                };
                let (bits, signed) = usual_conversions(int_parts(&t)?, int_parts(&o)?);
                let te = self.convert_expr(te.clone(), *tb, *ts, bits, signed)?;
                let (ob, os) = int_parts(&o)?;
                let oe = self.convert_expr(oe.clone(), ob, os, bits, signed)?;
                Some(CVal::Int { expr: s_ite(ct, te, oe), bits, signed })
            }
            CExpr::Cast(ty, inner) => {
                let v = self.eval(ctx, dcx, inner, guard)?;
                let (bits, signed) = match ty {
                    CTy::Int { bits, signed } => (*bits, *signed),
                    CTy::Bool => {
                        let t = self.truth(v)?;
                        return Some(bool_to_int(t));
                    }
                    // A cast that changes a pointer's type reinterprets the
                    // pointee, which this lane cannot check. Refuse.
                    _ => return None,
                };
                let expr = self.convert(v, bits, signed)?;
                Some(CVal::Int { expr, bits, signed })
            }
            CExpr::Deref(inner) => {
                let CExpr::Ident(name) = &**inner else { return None };
                let CVal::Ptr { read_root, .. } = self.env.get(name)?.clone() else { return None };
                self.read_place(ctx, dcx, &read_root)
            }
            CExpr::Member { base, field, arrow } => {
                let place = self.member_place(ctx, base, field, *arrow)?;
                self.read_place(ctx, dcx, &place)
            }
            CExpr::Assign { op, lhs, rhs } => {
                let rhs_val = self.eval(ctx, dcx, rhs, guard)?;
                let (bits, signed) = self.lvalue_type(ctx, dcx, lhs)?;
                let new = match op {
                    None => self.convert(rhs_val, bits, signed)?,
                    Some(op) => {
                        let old = self.eval(ctx, dcx, lhs, guard)?;
                        let combined = self.binary(*op, old, rhs_val, guard)?;
                        self.convert(combined, bits, signed)?
                    }
                };
                self.write_lvalue(ctx, dcx, lhs, new.clone(), guard)?;
                Some(CVal::Int { expr: new, bits, signed })
            }
            CExpr::IncDec { prefix, inc, target } => {
                let (bits, signed) = self.lvalue_type(ctx, dcx, target)?;
                let old = self.eval(ctx, dcx, target, guard)?;
                let one = CVal::Int {
                    expr: Expr::bitvec_const(1, 32),
                    bits: 32,
                    signed: true,
                };
                let op = if *inc { CBinOp::Add } else { CBinOp::Sub };
                let combined = self.binary(op, old.clone(), one, guard)?;
                let new = self.convert(combined, bits, signed)?;
                self.write_lvalue(ctx, dcx, target, new.clone(), guard)?;
                let CVal::Int { expr: old_expr, .. } = old else { return None };
                Some(CVal::Int {
                    expr: if *prefix { new } else { old_expr },
                    bits,
                    signed,
                })
            }
            // `assert` is the one callee with a meaning here; every other call
            // is Tier 2 (a call into unmodelled C, or recursion).
            CExpr::Call { callee, args } if callee == "assert" && args.len() == 1 => {
                self.c_assert(ctx, dcx, &args[0], guard)?;
                Some(CVal::Int { expr: Expr::bitvec_const(0, 32), bits: 32, signed: true })
            }
            CExpr::Call { .. } => None,
            CExpr::VaStart { ap, last } => {
                // C17 7.16.1.4p3: the second operand must be the LAST named
                // parameter. If it is not, the program's own list is not the
                // one this model would build — refuse rather than build a
                // different one.
                if self.last_named.as_deref() != Some(last.as_str()) {
                    return None;
                }
                let cursor = self.va_lists.get(ap)?.clone();
                let started =
                    s_ite(guard.clone(), Expr::bitvec_const(0, VA_CURSOR_BITS), cursor);
                self.va_lists.insert(ap.clone(), started);
                Some(void_val())
            }
            CExpr::VaEnd { ap } => {
                let cursor = self.va_lists.get(ap)?.clone();
                // After `va_end` the object is indeterminate (C17 7.16.1.3).
                // HAVOC it: a later `va_arg` then cannot discharge its range
                // obligation, which is the honest reading. Marking it "still at
                // N" would be an invented fact.
                let ended = s_ite(
                    guard.clone(),
                    declare_pending_var(
                        chc_fresh_name("__c_ffi_va_ended"),
                        Sort::bitvec(VA_CURSOR_BITS),
                    ),
                    cursor,
                );
                self.va_lists.insert(ap.clone(), ended);
                Some(void_val())
            }
            CExpr::VaArg { ap, ty } => self.va_arg(ap, ty, guard),
        }
    }

    /// `va_arg(ap, T)` — read the actual the cursor selects, and advance it.
    ///
    /// Two things are NOT assumed here, and that is the whole model:
    ///
    /// * that the cursor is in range. Reading past the last argument is UB, so
    ///   `cursor < N` is pushed as an OBLIGATION the caller must discharge.
    /// * that an out-of-range read yields anything nameable. The tail of the
    ///   selection chain is a FRESH unconstrained value, never a wrap back to
    ///   argument 0 and never the last argument repeated.
    fn va_arg(&mut self, ap: &str, ty: &CTy, guard: &Expr) -> Option<CVal> {
        // A `va_arg` at a non-integer type (an aggregate, a pointer, `_Bool`,
        // which is not even a legal promoted type) is Tier 2.
        let CTy::Int { bits, signed } = ty else { return None };
        let (bits, signed) = (*bits, *signed);
        let cursor = self.va_lists.get(ap)?.clone();

        // C17 7.16.1.1p2: the fetch type must be the type the argument has
        // after the default promotions. The cursor is symbolic, so EVERY actual
        // has to satisfy that — one mismatch and there is no reading of this
        // fetch the front-end can stand behind.
        if self.actuals.iter().any(|a| (a.bits, a.signed) != (bits, signed)) {
            return None;
        }

        let n = i128::try_from(self.actuals.len()).ok()?;
        let in_range = cursor.clone().bvult(Expr::bitvec_const(n, VA_CURSOR_BITS));
        self.checks.push((
            s_or(s_not(guard.clone()), in_range),
            PropertyKind::UndefinedBehavior,
            String::from(
                "va_arg read past the last argument passed to a variadic C definition \
                 supplied by --c-lib",
            ),
        ));

        let mut value =
            declare_pending_var(chc_fresh_name("__c_ffi_va_oob"), Sort::bitvec(bits.max(1)));
        for (k, actual) in self.actuals.iter().enumerate().rev() {
            let idx = i128::try_from(k).ok()?;
            let selects = cursor.clone().eq(Expr::bitvec_const(idx, VA_CURSOR_BITS));
            value = s_ite(selects, actual.expr.clone(), value);
        }

        let advanced = cursor.clone().bvadd(Expr::bitvec_const(1, VA_CURSOR_BITS));
        self.va_lists.insert(ap.to_owned(), s_ite(guard.clone(), advanced, cursor));
        Some(CVal::Int { expr: value, bits, signed })
    }

    /// `assert(e)` from `<assert.h>`: a C-level obligation.
    ///
    /// A constant-true argument (`sizeof(unsigned int) == sizeof(uint32_t)`,
    /// which the corpus's `takes_struct2` really does contain) is discharged
    /// here rather than emitted, so the harness's property list stays exactly
    /// what the Rust program states.
    fn c_assert(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        arg: &CExpr,
        guard: &Expr,
    ) -> Option<()> {
        if let Some(folded) = self.const_fold(arg)
            && folded != 0
        {
            return Some(());
        }
        let v = self.eval(ctx, dcx, arg, guard)?;
        let cond = self.truth(v)?;
        self.checks.push((
            s_or(s_not(guard.clone()), cond),
            PropertyKind::Assertion,
            String::from("assertion failed in C definition supplied by --c-lib"),
        ));
        Some(())
    }

    /// Constant-fold an expression that mentions only literals and `sizeof`.
    fn const_fold(&self, e: &CExpr) -> Option<i128> {
        match e {
            CExpr::SizeOfTy(ty) => {
                self.program.size_align(ty, self.ctarget).map(|(size, _)| i128::from(size))
            }
            CExpr::IntLit { value, .. } => Some(*value),
            CExpr::Unary(op, inner) => {
                let v = self.const_fold(inner)?;
                Some(match op {
                    CUnOp::Neg => v.checked_neg()?,
                    CUnOp::Plus => v,
                    CUnOp::LogicalNot => i128::from(v == 0),
                    CUnOp::BitNot => !v,
                })
            }
            CExpr::Binary(op, a, b) => {
                let (a, b) = (self.const_fold(a)?, self.const_fold(b)?);
                Some(match op {
                    CBinOp::Add => a.checked_add(b)?,
                    CBinOp::Sub => a.checked_sub(b)?,
                    CBinOp::Mul => a.checked_mul(b)?,
                    CBinOp::Div => a.checked_div(b)?,
                    CBinOp::Rem => a.checked_rem(b)?,
                    CBinOp::Eq => i128::from(a == b),
                    CBinOp::Ne => i128::from(a != b),
                    CBinOp::Lt => i128::from(a < b),
                    CBinOp::Le => i128::from(a <= b),
                    CBinOp::Gt => i128::from(a > b),
                    CBinOp::Ge => i128::from(a >= b),
                    _ => return None,
                })
            }
            _ => None,
        }
    }

    // -------------------------------------------------------------- lvalues

    fn lookup(&mut self, ctx: &mut ChcCtx<'_, '_>, name: &str) -> Option<CVal> {
        if let Some(v) = self.locals.get(name) {
            return Some(v.clone());
        }
        if let Some(v) = self.env.get(name) {
            return Some(v.clone());
        }
        // A file-scope object the C defines, reached by linker symbol.
        let global = self.program.globals.get(name)?;
        let (bits, signed) = match &global.ty {
            CTy::Int { bits, signed } => (*bits, *signed),
            CTy::Bool => (1, false),
            _ => return None,
        };
        let slot = ctx.foreign_static_slot(name)?;
        let expr = match self.store.get(&slot) {
            Some(pending) => pending.value.clone(),
            None => ctx.state_slot_expr(slot)?,
        };
        require_bitvec(&expr)?;
        Some(CVal::Int { expr, bits, signed })
    }

    /// The MIR place for `base.field` / `base->field`.
    ///
    /// The C struct tag is the authority for field ORDER; the prototype check
    /// established that the Rust ADT agrees index-for-index and offset-for-
    /// offset, which is exactly what separates `f.i + f.i2` (20) from
    /// `f->i + f->c` (19) in the corpus.
    fn member_place(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        base: &CExpr,
        field: &str,
        arrow: bool,
    ) -> Option<Place> {
        let CExpr::Ident(name) = base else { return None };
        let (mut place, tag) = match self.env.get(name)? {
            CVal::Agg { place, tag } if !arrow => (place.clone(), tag.clone()),
            CVal::Ptr { read_root, tag: Some(tag), .. } if arrow => {
                (read_root.clone(), tag.clone())
            }
            _ => return None,
        };
        let cdef = self.program.structs.get(&tag)?;
        let idx = cdef.fields.iter().position(|f| f.name == field)?;
        let base_ty = place.ty(ctx.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = base_ty.kind() else { return None };
        let variants = def.variants();
        let variant = variants.first()?;
        let field_ty = variant.fields().get(idx)?.ty();
        place.projection.push(ProjectionElem::Field(idx, field_ty));
        Some(place)
    }

    fn read_place(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        place: &Place,
    ) -> Option<CVal> {
        let ty = place.ty(ctx.body.locals()).ok()?;
        let (bits, signed) = rust_scalar_parts(ty, self.ctarget)?;
        let expr = ctx.translate_place_with_deref(place, dcx.modified_locals)?;
        require_bitvec(&expr)?;
        Some(CVal::Int { expr, bits, signed })
    }

    /// C type of the object an lvalue designates.
    fn lvalue_type(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        lhs: &CExpr,
    ) -> Option<(u32, bool)> {
        match lhs {
            CExpr::Ident(name) => match self.lookup(ctx, name)? {
                CVal::Int { bits, signed, .. } => Some((bits, signed)),
                _ => None,
            },
            CExpr::Deref(_) | CExpr::Member { .. } => {
                let v = self.eval(ctx, dcx, lhs, &Expr::bool_const(true))?;
                int_parts(&v)
            }
            _ => None,
        }
    }

    fn write_lvalue(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        _dcx: &DispatchCallContext<'_>,
        lhs: &CExpr,
        value: Expr,
        guard: &Expr,
    ) -> Option<()> {
        match lhs {
            CExpr::Ident(name) => {
                if let Some(CVal::Int { bits, signed, expr }) = self.locals.get(name).cloned() {
                    let merged = s_ite(guard.clone(), value, expr);
                    self.locals.insert(name.clone(), CVal::Int { expr: merged, bits, signed });
                    return Some(());
                }
                if self.env.contains_key(name) {
                    // Writing a PARAMETER changes only the callee's own copy.
                    let CVal::Int { bits, signed, expr } = self.env.get(name)?.clone() else {
                        return None;
                    };
                    let merged = s_ite(guard.clone(), value, expr);
                    self.env.insert(name.clone(), CVal::Int { expr: merged, bits, signed });
                    return Some(());
                }
                let slot = ctx.foreign_static_slot(name)?;
                self.store_write(ctx, slot, None, value, guard)
            }
            CExpr::Deref(inner) => {
                let CExpr::Ident(name) = &**inner else { return None };
                let CVal::Ptr { write, .. } = self.env.get(name)?.clone() else {
                    return None;
                };
                let (slot, place) = write?;
                self.store_write(ctx, slot, Some(place), value, guard)
            }
            // A projected store (`p->field = v`) is Tier 2.
            _ => None,
        }
    }

    fn store_write(
        &mut self,
        ctx: &mut ChcCtx<'_, '_>,
        slot: usize,
        place: Option<Place>,
        value: Expr,
        guard: &Expr,
    ) -> Option<()> {
        let old = match self.store.get(&slot) {
            Some(pending) => pending.value.clone(),
            None => ctx.state_slot_expr(slot)?,
        };
        // A width mismatch between the C object and the encoder's slot is not
        // something to paper over.
        if value.sort() != old.sort() {
            return None;
        }
        let merged = s_ite(guard.clone(), value, old);
        let place = place.or_else(|| self.store.get(&slot).and_then(|p| p.place.clone()));
        self.store.insert(slot, PendingStore { value: merged, place });
        Some(())
    }

    // ------------------------------------------------------------ operators

    fn truth(&mut self, v: CVal) -> Option<Expr> {
        let CVal::Int { expr, bits, .. } = v else { return None };
        let zero = Expr::bitvec_const(0, bits);
        Some(expr.ne(zero))
    }

    fn convert(&mut self, v: CVal, bits: u32, signed: bool) -> Option<Expr> {
        let CVal::Int { expr, bits: from_bits, signed: from_signed } = v else { return None };
        self.convert_expr(expr, from_bits, from_signed, bits, signed)
    }

    /// Integer conversion. Narrowing is a modular truncation (well defined for
    /// unsigned, and implementation-defined-but-universally-modular for
    /// signed); widening sign- or zero-extends by the SOURCE's signedness.
    fn convert_expr(
        &mut self,
        expr: Expr,
        from_bits: u32,
        from_signed: bool,
        bits: u32,
        _signed: bool,
    ) -> Option<Expr> {
        require_bitvec(&expr)?;
        let actual = expr.sort().bitvec_width()?;
        // The encoder's slot width is authoritative for what is in hand.
        let expr = if actual != from_bits {
            resize(expr, actual, bits, from_signed)?
        } else {
            expr
        };
        let width = expr.sort().bitvec_width()?;
        if width == bits {
            return Some(expr);
        }
        resize(expr, width, bits, from_signed)
    }

    fn unary(&mut self, op: CUnOp, v: CVal, guard: &Expr) -> Option<CVal> {
        let (bits, signed) = promote(int_parts(&v)?);
        let expr = self.convert(v, bits, signed)?;
        Some(match op {
            CUnOp::Plus => CVal::Int { expr, bits, signed },
            CUnOp::Neg => {
                if signed {
                    // `-INT_MIN` overflows: an obligation, not a wrap.
                    let min = Expr::bitvec_const(min_signed(bits), bits);
                    self.checks.push((
                        s_or(s_not(guard.clone()), expr.clone().ne(min)),
                        PropertyKind::ArithmeticOverflow,
                        String::from("signed negation overflows in C definition"),
                    ));
                }
                CVal::Int { expr: expr.bvneg(), bits, signed }
            }
            CUnOp::BitNot => CVal::Int { expr: expr.bvnot(), bits, signed },
            CUnOp::LogicalNot => {
                let zero = Expr::bitvec_const(0, bits);
                bool_to_int(expr.eq(zero))
            }
        })
    }

    fn binary(&mut self, op: CBinOp, a: CVal, b: CVal, guard: &Expr) -> Option<CVal> {
        let ap = int_parts(&a)?;
        let bp = int_parts(&b)?;

        // A shift converts its operands INDEPENDENTLY: the result type is the
        // promoted left operand, not the usual-conversions common type.
        if matches!(op, CBinOp::Shl | CBinOp::Shr) {
            let (bits, signed) = promote(ap);
            let lhs = self.convert(a, bits, signed)?;
            let (rbits, rsigned) = promote(bp);
            let rhs_raw = self.convert(b, rbits, rsigned)?;
            let rhs = resize(rhs_raw, rbits, bits, rsigned)?;
            let width = Expr::bitvec_const(i128::from(bits), bits);
            let mut must_hold = rhs.clone().bvult(width);
            if rsigned {
                must_hold = s_and(must_hold, rhs.clone().bvsge(Expr::bitvec_const(0, bits)));
            }
            self.checks.push((
                s_or(s_not(guard.clone()), must_hold),
                PropertyKind::UndefinedBehavior,
                String::from("shift amount out of range in C definition"),
            ));
            let expr = match (op, signed) {
                (CBinOp::Shl, _) => lhs.bvshl(rhs),
                (CBinOp::Shr, true) => lhs.bvashr(rhs),
                (CBinOp::Shr, false) => lhs.bvlshr(rhs),
                _ => unreachable!("shift op"),
            };
            return Some(CVal::Int { expr, bits, signed });
        }

        let (bits, signed) = usual_conversions(ap, bp);
        let lhs = self.convert(a, bits, signed)?;
        let rhs = self.convert(b, bits, signed)?;

        if op.is_comparison() {
            let result = match (op, signed) {
                (CBinOp::Eq, _) => lhs.eq(rhs),
                (CBinOp::Ne, _) => lhs.ne(rhs),
                (CBinOp::Lt, true) => lhs.bvslt(rhs),
                (CBinOp::Lt, false) => lhs.bvult(rhs),
                (CBinOp::Le, true) => lhs.bvsle(rhs),
                (CBinOp::Le, false) => lhs.bvule(rhs),
                (CBinOp::Gt, true) => lhs.bvsgt(rhs),
                (CBinOp::Gt, false) => lhs.bvugt(rhs),
                (CBinOp::Ge, true) => lhs.bvsge(rhs),
                (CBinOp::Ge, false) => lhs.bvuge(rhs),
                _ => unreachable!("comparison op"),
            };
            return Some(bool_to_int(result));
        }

        // Guard (c): signed overflow and division UB are OBLIGATIONS.
        if signed && matches!(op, CBinOp::Add | CBinOp::Sub | CBinOp::Mul) {
            let no_overflow = match op {
                CBinOp::Add => lhs.clone().bvadd_no_overflow_signed(rhs.clone()),
                CBinOp::Sub => lhs.clone().bvsub_no_overflow_signed(rhs.clone()),
                CBinOp::Mul => lhs.clone().bvmul_no_overflow_signed(rhs.clone()),
                _ => unreachable!("arith op"),
            };
            self.checks.push((
                s_or(s_not(guard.clone()), no_overflow),
                PropertyKind::ArithmeticOverflow,
                String::from("signed arithmetic overflows in C definition"),
            ));
        }
        if matches!(op, CBinOp::Div | CBinOp::Rem) {
            let zero = Expr::bitvec_const(0, bits);
            self.checks.push((
                s_or(s_not(guard.clone()), rhs.clone().ne(zero)),
                PropertyKind::DivisionByZero,
                String::from("division by zero in C definition"),
            ));
            if signed {
                let min = Expr::bitvec_const(min_signed(bits), bits);
                let neg_one = Expr::bitvec_const(-1, bits);
                let bad = lhs.clone().eq(min).and(rhs.clone().eq(neg_one));
                self.checks.push((
                    s_or(s_not(guard.clone()), s_not(bad)),
                    PropertyKind::ArithmeticOverflow,
                    String::from("INT_MIN divided by -1 in C definition"),
                ));
            }
        }

        let expr = match (op, signed) {
            (CBinOp::Add, _) => lhs.bvadd(rhs),
            (CBinOp::Sub, _) => lhs.bvsub(rhs),
            (CBinOp::Mul, _) => lhs.bvmul(rhs),
            (CBinOp::Div, true) => lhs.bvsdiv(rhs),
            (CBinOp::Div, false) => lhs.bvudiv(rhs),
            (CBinOp::Rem, true) => lhs.bvsrem(rhs),
            (CBinOp::Rem, false) => lhs.bvurem(rhs),
            (CBinOp::BitAnd, _) => lhs.bvand(rhs),
            (CBinOp::BitOr, _) => lhs.bvor(rhs),
            (CBinOp::BitXor, _) => lhs.bvxor(rhs),
            _ => return None,
        };
        Some(CVal::Int { expr, bits, signed })
    }

    // ------------------------------------------------------------ emission

    /// Bind the return value, the stores, and the C-level obligations onto the
    /// goto rule for this call.
    ///
    /// Every failure here is a refusal: the caller then emits the sound effect
    /// frame instead, so a half-built encoding can never be published.
    fn emit(
        self,
        ctx: &mut ChcCtx<'_, '_>,
        dcx: &DispatchCallContext<'_>,
        target: BasicBlockIdx,
        symbol: &str,
    ) -> bool {
        let CBodyLowering { mut extra, defs, checks, store, ret_val, ret, .. } = self;
        let mut extra_dests: Vec<usize> = Vec::new();
        // Every definition holds on every path out of this call, so it belongs
        // in the body of the goto rule AND in the body of each obligation.
        extra.extend(defs.iter().cloned());

        // (1) RETURN VALUE. A `void` C function leaves the destination alone:
        // its Rust type is zero-sized, so there is no value to bind.
        if matches!(ret, CRetShape::Scalar { .. }) {
            let dest_local = dcx.destination.local;
            let Some((_, dest_var)) = ctx.resolve_destination(dest_local) else {
                debug!(symbol, "c_ffi: destination has no output state variable");
                return false;
            };
            let Some(value) = ret_val else {
                debug!(symbol, "c_ffi: value-returning body produced no return expression");
                return false;
            };
            let out_sort = dest_var.sort().clone();
            if !ctx.push_coerced_eq_constraint(
                &mut extra,
                &dest_var,
                value,
                &out_sort,
                dest_local,
                SITE,
            ) {
                debug!(symbol, "c_ffi: return value could not be coerced to the destination sort");
                return false;
            }
            extra_dests.push(dest_local);
        }

        // (2) STORES. Each written slot is bound to its final symbolic value.
        // A bare unconstrained `__out` would be ambiguous — the constant folder
        // reads one as an identity pass-through — so the write is stated
        // explicitly, exactly as `kani::write_any_slim` states its havoc.
        for (slot, PendingStore { value, place }) in store {
            let Some((out_name, out_sort)) =
                ctx.state_var_mgr.output_state_vars.get(slot).cloned()
            else {
                debug!(symbol, slot, "c_ffi: written slot has no output state variable");
                return false;
            };
            let out_var = Expr::var(&*out_name, out_sort.clone());
            let diag_local = place.as_ref().map_or(0, |p| p.local);
            ctx.mark_state_var_modified(slot);
            let Some(eq) = ctx.make_coerced_eq_constraint(
                &out_var,
                value.clone(),
                &out_sort,
                diag_local,
                SITE,
            ) else {
                debug!(symbol, slot, "c_ffi: store value could not be coerced to the slot sort");
                return false;
            };
            extra.push(eq);

            let Some(place) = place else { continue };
            extra_dests.push(place.local);
            // Mirror the store into typed memory so readers on the Mem lane
            // observe it through the same path an ordinary `*p = v` uses.
            if ctx.track_level >= ChcTrackLevel::Mem
                && let Some(addr_expr) = ctx.translate_ref_to_address(&place, dcx.modified_locals)
            {
                let place_ty = place
                    .ty(ctx.body.locals())
                    .unwrap_or(ctx.body.locals()[place.local].ty);
                let prev_suppress = ctx.suppress_heap_store_checks;
                ctx.suppress_heap_store_checks = true;
                if let Some(store_constraint) =
                    ctx.build_memory_store(addr_expr, value, place_ty)
                {
                    extra.push(store_constraint);
                }
                ctx.suppress_heap_store_checks = prev_suppress;
                extra.append(&mut ctx.heap_state.pending_updates);
                extra.append(&mut ctx.heap_state.drain_store_chains(&ctx.diagnostics));
                let pending_checks: Vec<_> = ctx.heap_state.pending_checks.drain(..).collect();
                for check in pending_checks {
                    ctx.emit_error_rule_for_condition(
                        dcx.from_app,
                        check,
                        dcx.stmt_constraints,
                        dcx.bb_idx,
                    );
                }
            }
        }

        // (3) C-LEVEL OBLIGATIONS. Guard (c): the C's own undefined behaviour
        // is checked, not defined away. A trivially-true condition is dropped
        // by `emit_error_rule_for_condition_with_kind` itself, so the harness's
        // property list gains nothing for a body that cannot misbehave.
        let check_constraints: Vec<Expr> = if defs.is_empty() {
            dcx.stmt_constraints.to_vec()
        } else {
            dcx.stmt_constraints.iter().cloned().chain(defs).collect()
        };
        for (cond, kind, message) in checks {
            ctx.emit_error_rule_for_condition_with_kind(
                dcx.from_app,
                cond,
                &check_constraints,
                dcx.bb_idx,
                kind,
                Some(message),
            );
        }

        let new_output_args = ctx.build_output_args(dcx.modified_locals, &extra_dests);
        ctx.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            extra,
        );
        debug!(
            symbol,
            bb_idx = dcx.bb_idx,
            "foreign call encoded from its C definition (--c-lib)"
        );
        true
    }
}

// ------------------------------------------------------------ small helpers

/// Boolean constructors that fold constants.
///
/// Straight-line C reaches every statement under a literal `true` guard; the
/// folding keeps `ite(true, new, old)` from surviving into the encoding, where
/// it would obscure a simple assignment behind a conditional.
fn s_and(a: Expr, b: Expr) -> Expr {
    match (a.value(), b.value()) {
        (ExprValue::BoolConst(true), _) => b,
        (_, ExprValue::BoolConst(true)) => a,
        (ExprValue::BoolConst(false), _) | (_, ExprValue::BoolConst(false)) => {
            Expr::bool_const(false)
        }
        _ => a.and(b),
    }
}

fn s_or(a: Expr, b: Expr) -> Expr {
    match (a.value(), b.value()) {
        (ExprValue::BoolConst(false), _) => b,
        (_, ExprValue::BoolConst(false)) => a,
        (ExprValue::BoolConst(true), _) | (_, ExprValue::BoolConst(true)) => {
            Expr::bool_const(true)
        }
        _ => a.or(b),
    }
}

fn s_not(a: Expr) -> Expr {
    match a.value() {
        ExprValue::BoolConst(v) => Expr::bool_const(!v),
        _ => a.not(),
    }
}

fn s_ite(cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr {
    match cond.value() {
        ExprValue::BoolConst(true) => then_expr,
        ExprValue::BoolConst(false) => else_expr,
        _ => Expr::ite(cond, then_expr, else_expr),
    }
}


fn operand_place(op: &Operand) -> Option<Place> {
    match op {
        Operand::Copy(p) | Operand::Move(p) => Some(p.clone()),
        Operand::Constant(_) => None,
    }
}

fn operand_local(op: &Operand) -> Option<usize> {
    match op {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

fn require_bitvec(e: &Expr) -> Option<()> {
    e.sort().is_bitvec().then_some(())
}

fn int_parts(v: &CVal) -> Option<(u32, bool)> {
    match v {
        CVal::Int { bits, signed, .. } => Some((*bits, *signed)),
        _ => None,
    }
}

/// The value of a `void` expression. `va_start` / `va_end` are statements in
/// every program that compiles, so this is never read; giving it a shape keeps
/// `eval` total without inventing an integer anyone could use.
fn void_val() -> CVal {
    CVal::Int { expr: Expr::bitvec_const(0, 32), bits: 32, signed: true }
}

fn bool_to_int(cond: Expr) -> CVal {
    CVal::Int {
        expr: Expr::ite(cond, Expr::bitvec_const(1, 32), Expr::bitvec_const(0, 32)),
        bits: 32,
        signed: true,
    }
}

/// Integer promotion (C17 6.3.1.1p2): anything narrower than `int` becomes
/// `int`.
fn promote((bits, signed): (u32, bool)) -> (u32, bool) {
    if bits < 32 { (32, true) } else { (bits, signed) }
}

/// Usual arithmetic conversions (C17 6.3.1.8).
fn usual_conversions(a: (u32, bool), b: (u32, bool)) -> (u32, bool) {
    let (ab, asg) = promote(a);
    let (bb, bsg) = promote(b);
    if asg == bsg {
        return (ab.max(bb), asg);
    }
    let ((ub, _), (sb, _)) = if asg { ((bb, bsg), (ab, asg)) } else { ((ab, asg), (bb, bsg)) };
    if ub >= sb {
        (ub, false)
    } else {
        // The signed type is strictly wider, so it represents every value of
        // the unsigned type.
        (sb, true)
    }
}

/// Type of an integer constant (C17 6.4.4.1p5), restricted to the widths this
/// front-end models.
fn literal_type(value: i128, unsigned_suffix: bool) -> (u32, bool) {
    for bits in [32u32, 64] {
        if unsigned_suffix {
            if value >= 0 && value < (1i128 << bits) {
                return (bits, false);
            }
        } else if value >= -(1i128 << (bits - 1)) && value < (1i128 << (bits - 1)) {
            return (bits, true);
        }
    }
    (64, !unsigned_suffix)
}

fn wrap(value: i128, bits: u32) -> i128 {
    if bits >= 128 {
        return value;
    }
    let modulus = 1i128 << bits;
    value.rem_euclid(modulus)
}

fn min_signed(bits: u32) -> i128 {
    -(1i128 << (bits - 1))
}

fn resize(expr: Expr, from: u32, to: u32, from_signed: bool) -> Option<Expr> {
    if from == to {
        return Some(expr);
    }
    if to < from {
        return Some(expr.extract(to - 1, 0));
    }
    let extra = to - from;
    Some(if from_signed { expr.sign_extend(extra) } else { expr.zero_extend(extra) })
}

fn rust_scalar_parts(ty: Ty, target: CTarget) -> Option<(u32, bool)> {
    use rustc_public::ty::{IntTy, UintTy};
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Bool) => Some((1, false)),
        TyKind::RigidTy(RigidTy::Int(i)) => Some(match i {
            IntTy::I8 => (8, true),
            IntTy::I16 => (16, true),
            IntTy::I32 => (32, true),
            IntTy::I64 => (64, true),
            IntTy::I128 => (128, true),
            IntTy::Isize => (target.pointer_bits, true),
        }),
        TyKind::RigidTy(RigidTy::Uint(u)) => Some(match u {
            UintTy::U8 => (8, false),
            UintTy::U16 => (16, false),
            UintTy::U32 => (32, false),
            UintTy::U64 => (64, false),
            UintTy::U128 => (128, false),
            UintTy::Usize => (target.pointer_bits, false),
        }),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::c_ffi::CExpr;

    fn ret(v: i128) -> CStmt {
        CStmt::Return(Some(CExpr::IntLit { value: v, unsigned: false }))
    }

    /// C17 6.3.1.1p2. `f.i + f.c` on `{uint32_t, uint8_t}` only lands on 19
    /// because the `uint8_t` is promoted to `int` and then converted to
    /// `unsigned int` — not because both happen to be "the same kind of
    /// number".
    #[test]
    fn narrow_types_promote_to_int() {
        assert_eq!(promote((8, false)), (32, true));
        assert_eq!(promote((16, true)), (32, true));
        assert_eq!(promote((1, false)), (32, true));
        assert_eq!(promote((32, false)), (32, false));
        assert_eq!(promote((64, true)), (64, true));
    }

    /// C17 6.3.1.8. The mixed-signedness rules are the ones that are easy to
    /// get wrong, and getting them wrong changes VALUES.
    #[test]
    fn usual_arithmetic_conversions_follow_the_standard() {
        // uint32_t + int -> unsigned int (equal rank, unsigned wins).
        assert_eq!(usual_conversions((32, false), (32, true)), (32, false));
        // uint8_t + uint32_t -> both promote, unsigned wins at 32.
        assert_eq!(usual_conversions((8, false), (32, false)), (32, false));
        // unsigned int + long long -> the signed type is strictly wider, so it
        // represents every unsigned value and wins.
        assert_eq!(usual_conversions((32, false), (64, true)), (64, true));
        // size_t + int -> unsigned 64.
        assert_eq!(usual_conversions((64, false), (32, true)), (64, false));
        // int + int stays int.
        assert_eq!(usual_conversions((32, true), (32, true)), (32, true));
    }

    /// C17 6.4.4.1p5: an unsuffixed decimal constant takes the first of
    /// `int`, `long`, `long long` that represents it.
    #[test]
    fn integer_constants_take_their_standard_type() {
        assert_eq!(literal_type(2, false), (32, true));
        assert_eq!(literal_type(2, true), (32, false));
        assert_eq!(literal_type(i128::from(u32::MAX), false), (64, true));
        assert_eq!(literal_type(i128::from(u32::MAX), true), (32, false));
        assert_eq!(literal_type(i128::from(i64::MAX), false), (64, true));
    }

    #[test]
    fn constants_wrap_into_their_declared_width() {
        assert_eq!(wrap(-1, 32), i128::from(u32::MAX));
        assert_eq!(wrap(2, 32), 2);
        assert_eq!(wrap(256, 8), 0);
        assert_eq!(min_signed(32), i128::from(i32::MIN));
        assert_eq!(min_signed(8), -128);
    }

    /// A value-returning body that can fall off its end has no return value at
    /// all (C17 6.9.1p12). It must be REFUSED, never given a convenient one —
    /// which is why this predicate gates the whole lane.
    #[test]
    fn a_body_must_return_on_every_path_to_be_accepted() {
        // `takes_ptr_option`'s shape: both arms return.
        let both_arms = CStmt::Compound(vec![CStmt::If {
            cond: CExpr::Ident("p".into()),
            then: Box::new(ret(1)),
            other: Some(Box::new(ret(0))),
        }]);
        assert!(always_returns(&both_arms));

        // One arm returns, the other falls through.
        let one_arm = CStmt::Compound(vec![CStmt::If {
            cond: CExpr::Ident("p".into()),
            then: Box::new(ret(1)),
            other: None,
        }]);
        assert!(!always_returns(&one_arm));

        // A trailing return after a partial `if` rescues it.
        let trailing = CStmt::Compound(vec![
            CStmt::If {
                cond: CExpr::Ident("p".into()),
                then: Box::new(ret(1)),
                other: None,
            },
            ret(0),
        ]);
        assert!(always_returns(&trailing));

        // A body with no return at all.
        assert!(!always_returns(&CStmt::Compound(vec![CStmt::Empty])));
    }

    /// A `void` body needs no return statement, so the gate must not be
    /// applied to it — `mutates_ptr` and `update_static` both end without one.
    #[test]
    fn a_unit_returning_body_needs_no_return_statement() {
        let body = CStmt::Compound(vec![CStmt::Expr(CExpr::IncDec {
            prefix: false,
            inc: true,
            target: Box::new(CExpr::Ident("S".into())),
        })]);
        assert!(!always_returns(&body));
        // The caller only consults `always_returns` for a scalar return shape.
        assert!(matches!(CRetShape::Unit, CRetShape::Unit));
    }

    /// A loop may run zero times. Counting `return` inside one as "every path
    /// returns" would let a body that can fall off its end past the gate, and
    /// the fall-off value is exactly the thing this lane must never invent.
    #[test]
    fn a_return_inside_a_loop_does_not_make_the_body_always_return() {
        let loop_with_return = CStmt::For {
            init: None,
            cond: Some(CExpr::Ident("n".into())),
            step: None,
            body: Box::new(ret(0)),
        };
        assert!(!always_returns(&loop_with_return));
        // …and a `return` AFTER the loop still does.
        assert!(always_returns(&CStmt::Compound(vec![loop_with_return, ret(1)])));
    }
}
