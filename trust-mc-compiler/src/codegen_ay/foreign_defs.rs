// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Which foreign (`extern "C"`) symbols have a DEFINITION available to this
//! verification run.
//!
//! Kani's contract for an `extern` declaration with no body is `assert(false)`:
//! calling a function nobody supplied is a verification failure. That is a
//! FAIL-CLOSED net over "we have no idea what this does", and it must stay
//! exactly where it is for symbols nobody supplied — `ForeignItems/
//! missing_fn_fail.rs` is the pinned test for it.
//!
//! When the user DOES supply the definition (`-Z c-ffi --c-lib foo.c`), the
//! call is no longer an unknown-callee error: it is a call to some concrete C
//! function whose prototype the `extern` block declares. The encoder can then
//! model it with a sound EFFECT FRAME (fresh return + havoc of every location
//! the callee could write) instead of an unconditional error edge. This module
//! answers only the gating question — *is a definition available from some
//! source* — and deliberately does NOT try to read the C semantics.
//!
//! The scan is LEXICAL and intentionally coarse, and its two error directions
//! are asymmetric by design:
//!   * a false "defined" routes a call to the sound effect frame (a strict
//!     over-approximation of ANY C function, so no bug can hide behind it);
//!   * a false "not defined" keeps the pre-existing fail-closed `error()`.
//! Neither direction can produce a false proof.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::HashSet;
use std::sync::OnceLock;

/// Symbol names for which a C definition was supplied on this run.
static C_LIB_DEFINED_SYMBOLS: OnceLock<HashSet<String>> = OnceLock::new();

/// C keywords that are followed by `(` … `) {` but are not function definitions.
const C_CONTROL_KEYWORDS: &[&str] =
    &["if", "for", "while", "switch", "do", "else", "return", "sizeof", "catch"];

/// Record the `--c-lib` files for this run and index the function definitions
/// they contain. Idempotent: only the first call populates the registry (the
/// argument list is process-global, identical for every harness).
pub(super) fn init_c_lib_symbols(paths: &[String]) {
    let _ = C_LIB_DEFINED_SYMBOLS.get_or_init(|| {
        let mut defined = HashSet::new();
        for path in paths {
            let Ok(src) = std::fs::read_to_string(path) else {
                // An unreadable `--c-lib` entry contributes no definitions, so
                // every symbol stays fail-closed. Nothing to do but skip it.
                continue;
            };
            collect_c_function_definitions(&src, &mut defined);
        }
        defined
    });
}

/// Did this run supply ANY C definitions at all?
///
/// Lets declaration-time passes skip work that only the foreign-call effect
/// frame consumes: with no `--c-lib` on the command line the frame can never
/// fire, so nothing reads what they would have collected.
pub(in crate::codegen_ay) fn any_c_definitions() -> bool {
    C_LIB_DEFINED_SYMBOLS.get().is_some_and(|set| !set.is_empty())
}

/// Does some `--c-lib` file define `symbol`?
///
/// `false` when `init_c_lib_symbols` was never called (no `--c-lib` on the
/// command line) — the fail-closed default.
pub(in crate::codegen_ay) fn c_lib_defines(symbol: &str) -> bool {
    C_LIB_DEFINED_SYMBOLS.get().is_some_and(|set| set.contains(symbol))
}

/// The LINKER symbol a foreign callee resolves to, honouring `#[link_name =
/// "..."]` (`ForeignItems/main.rs` declares `name_in_rust` for the C symbol
/// `name_in_c`).
///
/// `None` when `func_ty` is not a direct call to a foreign item — an indirect
/// call through a function pointer included, since the pointee is not known
/// from the operand's type alone.
pub(in crate::codegen_ay) fn foreign_link_symbol(tcx: TyCtxt<'_>, func_ty: Ty) -> Option<String> {
    let TyKind::RigidTy(RigidTy::FnDef(def, _)) = func_ty.kind() else {
        return None;
    };
    let def_id = rustc_public::rustc_internal::internal(tcx, def.def_id());
    if !tcx.is_foreign_item(def_id) {
        return None;
    }
    let attrs = tcx.codegen_fn_attrs(def_id);
    Some(attrs.symbol_name.unwrap_or_else(|| tcx.item_name(def_id)).to_string())
}

/// Does `ty` carry interior mutability (is it non-`Freeze`)? Fails toward
/// `true` — i.e. toward havoc — for a type with unresolved parameters.
pub(in crate::codegen_ay) fn ty_has_interior_mut(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    // Rule A's one parameter test (`shared::mono_ty`): deep, type and const
    // parameters. Lifetimes are erased before the `Freeze` query.
    if crate::codegen_ay::shared::mono_ty::has_unresolved_params(ty) {
        return true;
    }
    let internal_ty =
        tcx.erase_and_anonymize_regions(rustc_public::rustc_internal::internal(tcx, ty));
    !internal_ty.is_freeze(tcx, rustc_middle::ty::TypingEnv::fully_monomorphized())
}

/// Can a COPY of a value of `ty` go STALE — can the copy reach, through a
/// pointer it holds or an `UnsafeCell` it contains, state that another alias
/// may mutate while the copy lives?
///
/// This is the question a slice-view copy has to answer, and it is NOT
/// `Freeze`: `&Cell<u8>`, `Box<Cell<u8>>`, `Rc<Cell<u8>>` and `Arc<AtomicU8>`
/// are every one of them `Freeze` by type, yet the copy holds the same pointer
/// and the state behind it keeps changing. Deciding on `Freeze` let both lanes
/// copy such views: `let view: &[&Cell<u8>] = &refs[..]; view[1].set(7);
/// assert!(cells[1].get() == 2)` verified SUCCESSFUL in BMC and
/// `let view: &[Rc<Cell<u8>>] = &arr[..]; shared.set(7);
/// assert!(view[0].get() == 7)` FAILED with a Genuine counterexample in CHC
/// (negative/frozen_views_indirect.rs, main 31793ccc3 and bundle edec8fd8a).
///
/// It is also not "contains a pointer": `&str`, `String` and `Vec<u8>` all hold
/// pointers to plain data, and a copy of one of those is exactly as good as the
/// original, so those views stay exact.
///
/// Fails toward `true` — the caller then fails closed — for unresolved
/// parameters, for anything opaque (`dyn`, closures, coroutines) and for a type
/// nested deeper than [`COPY_STALENESS_DEPTH`] (a recursive type reaches it).
pub(in crate::codegen_ay) fn ty_copy_can_go_stale(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    ty_copy_can_go_stale_at(tcx, ty, 0)
}

/// Nesting budget for [`ty_copy_can_go_stale`].
const COPY_STALENESS_DEPTH: u32 = 12;

fn ty_copy_can_go_stale_at(tcx: TyCtxt<'_>, ty: Ty, depth: u32) -> bool {
    if depth > COPY_STALENESS_DEPTH {
        return true;
    }
    // An `UnsafeCell` reachable BY VALUE settles it without any recursion.
    if ty_has_interior_mut(tcx, ty) {
        return true;
    }
    let TyKind::RigidTy(rigid) = ty.kind() else {
        return true; // generic param / alias / bound: not certain
    };
    match rigid {
        RigidTy::Bool
        | RigidTy::Char
        | RigidTy::Int(_)
        | RigidTy::Uint(_)
        | RigidTy::Float(_)
        | RigidTy::Never
        | RigidTy::Str
        | RigidTy::Foreign(_)
        | RigidTy::FnDef(..)
        | RigidTy::FnPtr(_) => false,
        RigidTy::Array(elem, _) | RigidTy::Slice(elem) | RigidTy::Pat(elem, _) => {
            ty_copy_can_go_stale_at(tcx, elem, depth + 1)
        }
        RigidTy::Tuple(tys) => tys.into_iter().any(|t| ty_copy_can_go_stale_at(tcx, t, depth + 1)),
        // The copy holds the SAME pointer, so whatever the pointee can reach,
        // the copy can reach. `Box`, `Rc`, `Arc` and `NonNull` arrive here as
        // ADTs and reach their raw pointer field by the arm below.
        RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _) => {
            ty_copy_can_go_stale_at(tcx, pointee, depth + 1)
        }
        RigidTy::Adt(def, args) => def.variants().into_iter().any(|v| {
            v.fields().into_iter().any(|f| {
                crate::codegen_ay::shared::mono_ty::field_ty(&f, &args)
                    .is_none_or(|t| ty_copy_can_go_stale_at(tcx, t, depth + 1))
            })
        }),
        // Dynamic, Closure, Coroutine*, CoroutineWitness: opaque.
        _ => true,
    }
}

/// Can an opaque C callee legally write through an argument of this type?
///
/// `&mut T`, `*mut T` and `*const T` all say yes — a raw pointer carries no
/// no-write guarantee, and C routinely casts `const` away. A shared `&T` says
/// yes only when `T` is non-`Freeze`: writing through a shared reference to a
/// `Freeze` type is UB in the Rust abstract machine, and — exactly as Kani
/// does — the encoder trusts the `extern` declaration on that point rather
/// than havocking every by-reference input.
pub(in crate::codegen_ay) fn arg_is_writable_pointer(tcx: TyCtxt<'_>, ty: Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::RawPtr(_, _)) => true,
        TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Mut)) => true,
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => ty_has_interior_mut(tcx, pointee),
        _ => false,
    }
}

/// Strip C comments and string/char literals so a `{` inside them cannot be
/// mistaken for a function body.
fn strip_comments_and_literals(src: &str) -> String {
    let bytes = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'/' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'*' => {
                i += 2;
                while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(bytes.len());
                out.push(' ');
            }
            quote @ (b'"' | b'\'') => {
                i += 1;
                while i < bytes.len() && bytes[i] != quote {
                    // A backslash escapes the next byte, including the quote.
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
                i += 1;
                out.push(' ');
            }
            b => {
                out.push(b as char);
                i += 1;
            }
        }
    }
    out
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_' || b == b'$'
}

/// Collect the names of functions DEFINED (not merely declared) in `src`.
///
/// A definition is `ident ( … ) {`: an identifier, a balanced parameter list,
/// then an opening brace. A prototype ends in `;` and a call site is followed
/// by an operator, so both are skipped without needing a real C parser.
fn collect_c_function_definitions(src: &str, out: &mut HashSet<String>) {
    let text = strip_comments_and_literals(src);
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if !is_ident_byte(bytes[i]) || bytes[i].is_ascii_digit() {
            i += 1;
            continue;
        }
        // Only start an identifier at a real token boundary.
        if i > 0 && is_ident_byte(bytes[i - 1]) {
            i += 1;
            continue;
        }
        let start = i;
        while i < bytes.len() && is_ident_byte(bytes[i]) {
            i += 1;
        }
        let ident = &text[start..i];

        let mut j = i;
        while j < bytes.len() && bytes[j].is_ascii_whitespace() {
            j += 1;
        }
        if j >= bytes.len() || bytes[j] != b'(' {
            continue;
        }
        // Balance the parameter list.
        let mut depth = 0usize;
        while j < bytes.len() {
            match bytes[j] {
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        j += 1;
                        break;
                    }
                }
                _ => {}
            }
            j += 1;
        }
        if depth != 0 {
            continue;
        }
        while j < bytes.len() && bytes[j].is_ascii_whitespace() {
            j += 1;
        }
        if j < bytes.len() && bytes[j] == b'{' && !C_CONTROL_KEYWORDS.contains(&ident) {
            out.insert(ident.to_owned());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn defs(src: &str) -> HashSet<String> {
        let mut out = HashSet::new();
        collect_c_function_definitions(src, &mut out);
        out
    }

    #[test]
    fn definition_is_found_prototype_is_not() {
        let set = defs(
            "uint32_t takes_int(uint32_t i) { return i + 2; }\nuint32_t only_declared(int);\n",
        );
        assert!(set.contains("takes_int"));
        assert!(!set.contains("only_declared"));
    }

    #[test]
    fn brace_on_next_line_is_a_definition() {
        let set = defs("struct Unit update_static()\n{\n    S++;\n}\n");
        assert!(set.contains("update_static"));
    }

    #[test]
    fn call_sites_and_control_flow_are_not_definitions() {
        let set = defs(
            "int f(int n) {\n    if (n) { g(n); }\n    for (int i = 0; i < n; ++i) { h(i); }\n    return 0;\n}\n",
        );
        assert!(set.contains("f"));
        assert!(!set.contains("g"));
        assert!(!set.contains("h"));
        assert!(!set.contains("if"));
        assert!(!set.contains("for"));
    }

    #[test]
    fn commented_out_and_quoted_definitions_are_ignored() {
        let set = defs(
            "// int commented(void) { return 0; }\n/* int blocked(void) { return 0; } */\nconst char *s = \"int quoted(void) { }\";\n",
        );
        assert!(set.is_empty(), "unexpected definitions: {set:?}");
    }

    #[test]
    fn variadic_definition_is_found() {
        let set = defs("size_t my_add(size_t num, ...)\n{\n    return 0;\n}\n");
        assert!(set.contains("my_add"));
    }

    #[test]
    fn unknown_symbol_stays_undefined_when_no_c_lib_was_given() {
        // The registry defaults to fail-closed for every symbol.
        assert!(!c_lib_defines("__definitely_not_a_symbol_in_any_c_lib"));
    }
}
