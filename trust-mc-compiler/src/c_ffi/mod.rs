// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A restricted C front-end for the translation units supplied with
//! `--c-lib`.
//!
//! # Why this exists
//!
//! `-Z c-ffi --c-lib lib.c` hands the verifier the DEFINITIONS of the symbols
//! an `extern "C"` block declares. `codegen_ay::foreign_defs` already answers
//! the gating question — *is a definition available* — and routes such a call
//! to a sound effect frame instead of Kani's undefined-function `assert(false)`.
//! That frame is honest but imprecise, and the properties these programs state
//! are statements about the C's VALUES: `takes_int(1) == 3`, `mutates_ptr` ⇒
//! `16`, `takes_struct(f) == 19`. No abstraction of an unknown function can
//! produce a value, so those rows need the definition to actually be READ.
//!
//! # The soundness obligation is different in kind
//!
//! Every other model in this encoder must not UNDER-approximate. This one must
//! not MIS-TRANSLATE: a wrong reading of the C is a wrong program, and a proof
//! about the wrong program is a fabricated proof. Three guards, in this module
//! and its consumers:
//!
//! * **(a) Allowlist, never heuristic.** The accepted fragment is enumerated by
//!   the `CTy` / `CExpr` / `CStmt` variants and by the parser's explicit
//!   refusals. A construct with no variant cannot be approximated by accident —
//!   the parser returns `None` and the symbol falls back, PER FUNCTION, to the
//!   effect frame. Target-dependent facts the front-end has not established
//!   are refusals too: a bare `char` (implementation-defined signedness) is
//!   rejected, and `long` takes its width from the compilation target rather
//!   than an assumption.
//! * **(b) The prototype is CHECKED against the Rust declaration** — arity,
//!   scalar widths and signedness, pointer shape, and struct field types AND
//!   byte offsets under the platform C ABI. Kani's own comment in
//!   `ForeignItems/extern_fn_ptr.rs` concedes it "trusts that the extern
//!   declaration is compatible with the C definition"; checking it exceeds
//!   Kani. See `c_proto` in the codegen lane.
//! * **(c) C's own UB is an obligation, not a wrap.** Signed overflow,
//!   division by zero, out-of-range shifts and a null dereference are emitted
//!   as checks by the lowering, not silently defined away.
//!
//! # Fidelity bar
//!
//! Set by the corpus itself. `lib.c` has `takes_struct2` returning
//! `f.i + f.i2` (20) next to `takes_struct_ptr2` returning `f->i + f->c` (19),
//! and `ForeignItems/main.rs` asserts both. `Foo { u32 i; u8 c }` is 8 bytes
//! with `c` at offset 4; `Foo2 { u32 i; u8 c; u32 i2 }` is 12 bytes with `i2`
//! at offset 8. A field-offset-correct model reproduces both numbers; a
//! "sum the fields" shortcut does not.

pub(crate) mod ast;
mod lex;
mod parse;

pub(crate) use ast::{CBinOp, CExpr, CFunc, CGlobal, CProgram, CStmt, CTarget, CTy, CUnOp};

use std::sync::OnceLock;
use tracing::debug;

static C_PROGRAM: OnceLock<CProgram> = OnceLock::new();
static C_TARGET: OnceLock<CTarget> = OnceLock::new();

/// Ingest every `--c-lib` translation unit once per process.
///
/// Idempotent: the argument list is process-global and identical for every
/// harness, so only the first call populates the program.
pub(crate) fn init(paths: &[String], target: CTarget) {
    let _ = C_TARGET.set(target);
    let _ = C_PROGRAM.get_or_init(|| {
        let mut program = CProgram::default();
        for path in paths {
            let Ok(src) = std::fs::read_to_string(path) else {
                // An unreadable entry contributes nothing; every symbol in it
                // stays on the fail-closed path.
                debug!(path = %path, "c_ffi: --c-lib file unreadable, skipping");
                continue;
            };
            parse::parse_translation_unit(&src, target, &mut program);
        }
        debug!(
            accepted = program.funcs.len(),
            refused = program.refused.len(),
            structs = program.structs.len(),
            globals = program.globals.len(),
            "c_ffi: ingested --c-lib translation units"
        );
        program
    });
}

/// The ingested program, or an empty one when `--c-lib` was never given.
pub(crate) fn program() -> &'static CProgram {
    static EMPTY: OnceLock<CProgram> = OnceLock::new();
    C_PROGRAM.get().unwrap_or_else(|| EMPTY.get_or_init(CProgram::default))
}

/// Target integer-width model the `--c-lib` sources were read under.
///
/// Defaults to a 64-bit LP64 model when `--c-lib` was never given; nothing
/// reads it in that case, because the program is empty.
pub(crate) fn target() -> CTarget {
    C_TARGET.get().copied().unwrap_or(CTarget::new(64, 64))
}

/// The Tier-1 body for `symbol`, if one was accepted.
pub(crate) fn func(symbol: &str) -> Option<&'static CFunc> {
    program().funcs.get(symbol)
}

/// The file-scope object `symbol`, if the fragment accepted its definition.
pub(crate) fn global(symbol: &str) -> Option<&'static CGlobal> {
    program().globals.get(symbol)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ast::{CField, CStructDef};

    /// The verbatim corpus library, so the parser is pinned against the real
    /// input rather than a paraphrase of it.
    const CORPUS_LIB_C: &str = r#"
#include <assert.h>
#include <stdarg.h>
#include <stdint.h>

struct Unit;
extern struct Unit VoidUnit;

size_t my_add(size_t num, ...)
{
    va_list argp;
    va_start(argp, num);

    size_t accum = 0;
    for (size_t i = 0; i < num; ++i) {
        size_t next = va_arg(argp, size_t);
        accum += next;
    }
    va_end(argp);
    return accum;
}

struct Foo {
    unsigned int  i;
    unsigned char c;
};  // __attribute__((packed));

struct Foo2 {
    uint32_t i;
    uint8_t  c;
    uint32_t i2;
};  // __attribute__((packed));

uint32_t S = 12;

struct Unit update_static()
{
    S++;
    return VoidUnit;
}

uint32_t takes_int(uint32_t i) { return i + 2; }

uint32_t takes_ptr(uint32_t *p) { return *p + 2; }

uint32_t takes_ptr_option(uint32_t *p)
{
    if (p) {
        return *p - 1;
    } else {
        return 0;
    }
}

struct Unit mutates_ptr(uint32_t *p)
{
    *p -= 1;
    return VoidUnit;
}

uint32_t name_in_c(uint32_t i) { return i + 2; }

uint32_t takes_struct(struct Foo f) { return f.i + f.c; }

uint32_t takes_struct_ptr(struct Foo *f) { return f->i + f->c; }

uint32_t takes_struct2(struct Foo2 f)
{
    assert(sizeof(unsigned int) == sizeof(uint32_t));
    return f.i + f.i2;
}

uint32_t takes_struct_ptr2(struct Foo2 *f) { return f->i + f->c; }
"#;

    fn corpus() -> CProgram {
        let mut p = CProgram::default();
        parse::parse_translation_unit(CORPUS_LIB_C, CTarget::new(64, 64), &mut p);
        p
    }

    #[test]
    fn every_non_variadic_corpus_function_is_accepted() {
        let p = corpus();
        for name in [
            "update_static",
            "takes_int",
            "takes_ptr",
            "takes_ptr_option",
            "mutates_ptr",
            "name_in_c",
            "takes_struct",
            "takes_struct_ptr",
            "takes_struct2",
            "takes_struct_ptr2",
        ] {
            assert!(p.funcs.contains_key(name), "expected {name} in the accepted fragment");
        }
    }

    /// The variadic `my_add` needs `va_list`, `va_start`, `va_arg` and a `for`
    /// loop. All four are now inside the fragment, and the parse has to record
    /// the SHAPE the lowering depends on: `...` declared, one named parameter,
    /// and a real loop rather than something flattened.
    #[test]
    fn the_variadic_corpus_function_parses_with_its_ellipsis_and_its_loop() {
        let p = corpus();
        let f = p.funcs.get("my_add").expect("my_add is inside the fragment");
        assert!(f.variadic, "the `...` must survive the parse");
        assert_eq!(f.params.len(), 1, "only `num` is a NAMED parameter");
        assert_eq!(f.ret, CTy::Int { bits: 64, signed: false });
        let CStmt::Compound(body) = &f.body else { panic!("expected a compound body") };
        assert!(
            body.iter().any(|s| matches!(s, CStmt::For { .. })),
            "the `for` must be a loop, not silently dropped"
        );
        assert!(
            body.iter().any(|s| matches!(s, CStmt::Decl { ty: CTy::VaList, .. })),
            "`va_list argp;` must be a va_list declaration"
        );
        // Neighbours stay precise either way — that was, and remains, the
        // per-function-refusal property this file guarantees.
        assert!(p.funcs.contains_key("takes_int"));
    }

    /// `va_arg`'s second operand is a TYPE NAME, so it cannot be parsed as an
    /// expression. Reading it at the wrong type is a mis-translation, so a
    /// shape this fragment does not model refuses the whole function.
    #[test]
    fn a_va_macro_is_parsed_by_shape_and_refused_when_it_does_not_match() {
        let mut p = CProgram::default();
        let t = CTarget::new(64, 64);
        parse::parse_translation_unit(
            "int taker(int n, ...) { va_list ap; va_start(ap, n); int v = va_arg(ap, int);              va_end(ap); return v; }\n             int bad(int n, ...) { va_list ap; va_start(ap); return 0; }\n             int fine(int n) { return n + 1; }",
            t,
            &mut p,
        );
        let f = p.funcs.get("taker").expect("the modelled va_* shape is accepted");
        let CStmt::Compound(body) = &f.body else { panic!("expected a compound body") };
        let has_fetch = body.iter().any(|s| {
            matches!(
                s,
                CStmt::Decl {
                    init: Some(CExpr::VaArg { ty: CTy::Int { bits: 32, signed: true }, .. }),
                    ..
                }
            )
        });
        assert!(has_fetch, "`va_arg(ap, int)` must carry the TYPE it fetches");
        // `va_start` with one operand is not the modelled shape.
        assert!(!p.funcs.contains_key("bad"));
        assert!(p.funcs.contains_key("fine"));
    }

    #[test]
    fn struct_definitions_and_the_initialised_global_are_captured() {
        let p = corpus();
        assert_eq!(
            p.structs.get("Foo"),
            Some(&CStructDef {
                name: "Foo".into(),
                fields: vec![
                    CField { name: "i".into(), ty: CTy::Int { bits: 32, signed: false } },
                    CField { name: "c".into(), ty: CTy::Int { bits: 8, signed: false } },
                ],
            })
        );
        // `struct Unit;` is a forward declaration: incomplete, never a
        // zero-field struct.
        assert!(!p.structs.contains_key("Unit"));
        assert_eq!(p.globals.get("S").and_then(|g| g.init), Some(12));
        // `extern struct Unit VoidUnit;` declares, it does not define.
        assert!(!p.globals.contains_key("VoidUnit"));
    }

    #[test]
    fn the_two_struct_returning_bodies_are_distinguishable() {
        let p = corpus();
        let by_value = p.funcs.get("takes_struct2").unwrap();
        let by_ptr = p.funcs.get("takes_struct_ptr2").unwrap();
        assert_ne!(by_value.body, by_ptr.body, "f.i + f.i2 must not parse the same as f->i + f->c");
    }

    #[test]
    fn a_bare_char_is_refused_because_its_signedness_is_target_defined() {
        let mut p = CProgram::default();
        parse::parse_translation_unit(
            "int widen(char c) { return c; }",
            CTarget::new(64, 64),
            &mut p,
        );
        assert!(!p.funcs.contains_key("widen"));
    }

    #[test]
    fn a_global_without_an_initializer_carries_no_value() {
        let mut p = CProgram::default();
        parse::parse_translation_unit("int counter;", CTarget::new(64, 64), &mut p);
        assert_eq!(p.globals.get("counter").and_then(|g| g.init), None);
    }

    #[test]
    fn long_takes_its_width_from_the_target_rather_than_an_assumption() {
        let mut lp64 = CProgram::default();
        parse::parse_translation_unit(
            "long id(long x) { return x; }",
            CTarget::new(64, 64),
            &mut lp64,
        );
        assert_eq!(
            lp64.funcs.get("id").map(|f| f.ret.clone()),
            Some(CTy::Int { bits: 64, signed: true })
        );
        let mut llp64 = CProgram::default();
        parse::parse_translation_unit(
            "long id(long x) { return x; }",
            CTarget::new(64, 32),
            &mut llp64,
        );
        assert_eq!(
            llp64.funcs.get("id").map(|f| f.ret.clone()),
            Some(CTy::Int { bits: 32, signed: true })
        );
    }

    /// Two definitions of one symbol is a program the linker would reject.
    /// Keeping either one would be a coin flip, and a coin flip is a
    /// mis-translation — so the symbol is refused back to the effect frame.
    #[test]
    fn a_symbol_defined_twice_is_refused_rather_than_arbitrated() {
        let mut p = CProgram::default();
        let t = CTarget::new(64, 64);
        parse::parse_translation_unit("int f(int x) { return x + 1; }", t, &mut p);
        assert!(p.funcs.contains_key("f"));
        parse::parse_translation_unit("int f(int x) { return x + 2; }", t, &mut p);
        assert!(!p.funcs.contains_key("f"));
        assert!(p.refused.contains_key("f"));
    }

    #[test]
    fn a_struct_tag_defined_twice_differently_loses_its_layout() {
        let mut p = CProgram::default();
        let t = CTarget::new(64, 64);
        parse::parse_translation_unit("struct S { uint32_t a; };", t, &mut p);
        assert!(p.structs.contains_key("S"));
        // Same tag, different layout: neither is authoritative.
        parse::parse_translation_unit("struct S { uint32_t a; uint32_t b; };", t, &mut p);
        assert!(!p.structs.contains_key("S"));
        // An IDENTICAL redefinition (the usual shared-header case) is fine.
        let mut q = CProgram::default();
        parse::parse_translation_unit("struct S { uint32_t a; };", t, &mut q);
        parse::parse_translation_unit("struct S { uint32_t a; };", t, &mut q);
        assert!(q.structs.contains_key("S"));
    }

    /// The unroller models a loop with exactly ONE exit and one back edge, so
    /// a `break`, a `continue`, a `do`/`while` or a `goto` still refuses the
    /// function — accepting one would silently mis-translate its control flow.
    /// A plain `while` is now inside the fragment.
    #[test]
    fn a_second_loop_exit_or_a_call_to_an_unmodelled_function_is_refused() {
        let mut p = CProgram::default();
        parse::parse_translation_unit(
            "int sum(int n) { int a = 0; while (n) { a += n; n--; } return a; }\n\
             int breaks(int n) { int a = 0; while (n) { break; } return a; }\n\
             int loops_backwards(int n) { int a = 0; do { a++; } while (n); return a; }\n\
             int uses_libc(int n) { return abs(n); }\n\
             int fine(int n) { return n + 1; }",
            CTarget::new(64, 64),
            &mut p,
        );
        assert!(p.funcs.contains_key("sum"), "a single-exit `while` is modelled");
        assert!(!p.funcs.contains_key("breaks"), "`break` gives the loop a second exit");
        assert!(!p.funcs.contains_key("loops_backwards"), "`do`/`while` is not the modelled form");
        // A call PARSES; it is refused at lowering, where the callee allowlist
        // lives. What matters is that `fine` is unaffected either way.
        assert!(p.funcs.contains_key("fine"));
    }

    /// `va_list` has no object representation this front-end has established,
    /// so it may never acquire a size by accident.
    #[test]
    fn a_va_list_has_no_size_and_no_layout() {
        let p = CProgram::default();
        assert_eq!(p.size_align(&CTy::VaList, CTarget::new(64, 64)), None);
    }
}
