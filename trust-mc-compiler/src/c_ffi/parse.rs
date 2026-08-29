// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Recursive-descent parser for the restricted C fragment.
//!
//! Two properties matter more than coverage:
//!
//! * **Per-declaration refusal.** The unit is split into top-level
//!   declarations FIRST, so one unparsable function (`my_add`, with `va_list`
//!   and a loop) refuses only itself. Its neighbours in the same file still
//!   get precise semantics, and it still gets the sound effect frame.
//! * **No silent approximation.** Every construct outside the fragment returns
//!   `None`. There is no "close enough" branch anywhere in this file.

use super::ast::*;
use super::lex::{Tok, tokenize};

/// Storage-class and qualifier keywords that carry no type information.
const IGNORED_SPECIFIERS: &[&str] =
    &["const", "volatile", "restrict", "__restrict", "register", "inline", "__inline", "auto"];

/// Type-specifier keywords the fragment understands, used to recognise the
/// start of a declaration or a cast.
const TYPE_KEYWORDS: &[&str] = &[
    "void",
    "_Bool",
    "bool",
    "signed",
    "unsigned",
    "short",
    "int",
    "long",
    "char",
    "struct",
    "int8_t",
    "int16_t",
    "int32_t",
    "int64_t",
    "uint8_t",
    "uint16_t",
    "uint32_t",
    "uint64_t",
    "size_t",
    "ssize_t",
    "ptrdiff_t",
    "intptr_t",
    "uintptr_t",
    "intmax_t",
    "uintmax_t",
    "va_list",
];

pub(crate) struct Parser<'a> {
    toks: &'a [Tok],
    pos: usize,
    target: CTarget,
}

/// Parse one `--c-lib` translation unit into `out`.
///
/// A tokenizer refusal drops the whole file (every symbol keeps the effect
/// frame); a parser refusal drops only the offending declaration.
pub(crate) fn parse_translation_unit(src: &str, target: CTarget, out: &mut CProgram) {
    let Some(toks) = tokenize(src) else {
        out.refused.insert(String::from("<translation-unit>"), "tokenizer refused".into());
        return;
    };
    for unit in split_top_level(&toks) {
        let mut p = Parser { toks: unit, pos: 0, target };
        match p.parse_declaration(out) {
            Some(()) => {}
            None => {
                if let Some(name) = guess_declared_name(unit) {
                    out.refused
                        .entry(name)
                        .or_insert_with(|| "outside the accepted C fragment".into());
                }
            }
        }
    }
}

/// Split a token stream into top-level declarations.
///
/// A declaration ends at a `;` seen at brace depth 0, or at the `}` that
/// returns brace depth to 0. Parenthesis depth is tracked so a `;` inside a
/// `for(;;)` header never splits a body.
fn split_top_level(toks: &[Tok]) -> Vec<&[Tok]> {
    let mut units = Vec::new();
    let mut start = 0usize;
    let mut brace = 0i32;
    let mut paren = 0i32;
    for (i, t) in toks.iter().enumerate() {
        match t {
            Tok::Punct("{") => brace += 1,
            Tok::Punct("}") => {
                brace -= 1;
                if brace <= 0 {
                    brace = 0;
                    units.push(&toks[start..=i]);
                    start = i + 1;
                }
            }
            Tok::Punct("(") => paren += 1,
            Tok::Punct(")") => paren -= 1,
            Tok::Punct(";") if brace == 0 && paren == 0 => {
                units.push(&toks[start..=i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < toks.len() {
        units.push(&toks[start..]);
    }
    units.into_iter().filter(|u| u.iter().any(|t| !t.is_punct(";"))).collect()
}

/// Best-effort name for a refused declaration: the identifier directly before
/// the first `(` or `=` or `;`. Diagnostic only.
fn guess_declared_name(toks: &[Tok]) -> Option<String> {
    let idx = toks
        .iter()
        .position(|t| t.is_punct("(") || t.is_punct("=") || t.is_punct(";"))
        .unwrap_or(toks.len());
    toks[..idx].iter().rev().find_map(|t| t.ident()).map(str::to_owned)
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn peek_at(&self, n: usize) -> Option<&Tok> {
        self.toks.get(self.pos + n)
    }
    fn bump(&mut self) -> Option<&Tok> {
        let t = self.toks.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn eat_punct(&mut self, p: &str) -> bool {
        if self.peek().is_some_and(|t| t.is_punct(p)) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn expect_punct(&mut self, p: &str) -> Option<()> {
        if self.eat_punct(p) { Some(()) } else { None }
    }
    fn eat_ident(&mut self, name: &str) -> bool {
        if self.peek().and_then(Tok::ident) == Some(name) {
            self.pos += 1;
            true
        } else {
            false
        }
    }
    fn at_end(&self) -> bool {
        self.pos >= self.toks.len()
    }

    fn at_type_start(&self) -> bool {
        self.peek()
            .and_then(Tok::ident)
            .is_some_and(|s| TYPE_KEYWORDS.contains(&s) || IGNORED_SPECIFIERS.contains(&s))
    }

    // ---------------------------------------------------------------- types

    /// Parse a declaration specifier sequence into a base type.
    ///
    /// Returns `None` for anything outside the fragment — `union`, `enum`,
    /// `typedef`, floating types, `_Complex`, an unknown typedef name, or a
    /// bare `char` (whose signedness is TARGET-DEFINED, so accepting it would
    /// make the translation depend on a fact the front-end has not
    /// established).
    fn parse_base_ty(&mut self) -> Option<CTy> {
        let mut signed: Option<bool> = None;
        let mut longs = 0u32;
        let mut shorts = 0u32;
        let mut core: Option<String> = None;
        let mut saw_any = false;

        loop {
            let Some(word) = self.peek().and_then(Tok::ident).map(str::to_owned) else { break };
            let word = word.as_str();
            if IGNORED_SPECIFIERS.contains(&word) {
                self.pos += 1;
                continue;
            }
            match word {
                "static" | "extern" => {
                    self.pos += 1;
                    saw_any = true;
                }
                "signed" => {
                    if signed.is_some() {
                        return None;
                    }
                    signed = Some(true);
                    self.pos += 1;
                    saw_any = true;
                }
                "unsigned" => {
                    if signed.is_some() {
                        return None;
                    }
                    signed = Some(false);
                    self.pos += 1;
                    saw_any = true;
                }
                "long" => {
                    longs += 1;
                    self.pos += 1;
                    saw_any = true;
                }
                "short" => {
                    shorts += 1;
                    self.pos += 1;
                    saw_any = true;
                }
                "struct" => {
                    if core.is_some() || signed.is_some() || longs > 0 || shorts > 0 {
                        return None;
                    }
                    self.pos += 1;
                    let tag = self.bump()?.ident()?.to_owned();
                    // An inline `struct T { ... }` body inside a declaration is
                    // outside the fragment: only a top-level definition is
                    // accepted, so the layout check has one authority.
                    if self.peek().is_some_and(|t| t.is_punct("{")) {
                        return None;
                    }
                    return Some(CTy::Struct(tag));
                }
                w if TYPE_KEYWORDS.contains(&w) => {
                    if core.is_some() {
                        return None;
                    }
                    core = Some(w.to_owned());
                    self.pos += 1;
                    saw_any = true;
                }
                _ => break,
            }
        }
        if !saw_any {
            return None;
        }
        if shorts > 1 || longs > 2 {
            return None;
        }

        let ptr = self.target.pointer_bits;
        let long_bits = self.target.long_bits;
        let ty = match core.as_deref() {
            Some("void") => {
                if signed.is_some() || longs > 0 || shorts > 0 {
                    return None;
                }
                CTy::Void
            }
            Some("_Bool") | Some("bool") => {
                if signed.is_some() || longs > 0 || shorts > 0 {
                    return None;
                }
                CTy::Bool
            }
            // Signedness of a bare `char` is implementation-defined. Refuse.
            Some("char") => match signed {
                Some(s) => CTy::Int { bits: 8, signed: s },
                None => return None,
            },
            Some("int") | None => {
                let bits = if shorts > 0 {
                    16
                } else if longs == 1 {
                    long_bits
                } else if longs == 2 {
                    64
                } else {
                    32
                };
                CTy::Int { bits, signed: signed.unwrap_or(true) }
            }
            // `va_list` takes no signedness and no length modifier, and it
            // is not an integer: it never reaches the width table below.
            Some("va_list") => {
                if signed.is_some() || longs > 0 || shorts > 0 {
                    return None;
                }
                CTy::VaList
            }
            Some(name) => {
                if longs > 0 || shorts > 0 {
                    return None;
                }
                let (bits, sgn) = match name {
                    "int8_t" => (8, true),
                    "int16_t" => (16, true),
                    "int32_t" => (32, true),
                    "int64_t" => (64, true),
                    "uint8_t" => (8, false),
                    "uint16_t" => (16, false),
                    "uint32_t" => (32, false),
                    "uint64_t" => (64, false),
                    "size_t" | "uintptr_t" => (ptr, false),
                    "ssize_t" | "ptrdiff_t" | "intptr_t" => (ptr, true),
                    "intmax_t" => (64, true),
                    "uintmax_t" => (64, false),
                    _ => return None,
                };
                if let Some(explicit) = signed
                    && explicit != sgn
                {
                    return None;
                }
                CTy::Int { bits, signed: sgn }
            }
        };
        Some(ty)
    }

    /// Apply pointer declarator stars to `base`.
    fn parse_pointer(&mut self, mut base: CTy) -> CTy {
        while self.eat_punct("*") {
            while self.peek().and_then(Tok::ident).is_some_and(|w| IGNORED_SPECIFIERS.contains(&w))
            {
                self.pos += 1;
            }
            base = CTy::Ptr(Box::new(base));
        }
        base
    }

    /// A type name in a cast or `sizeof`: specifiers plus pointer stars, no
    /// declarator identifier.
    fn parse_type_name(&mut self) -> Option<CTy> {
        let base = self.parse_base_ty()?;
        Some(self.parse_pointer(base))
    }

    // --------------------------------------------------------- declarations

    fn parse_declaration(&mut self, out: &mut CProgram) -> Option<()> {
        if self.at_end() {
            return Some(());
        }
        // `struct Tag { ... } ;`
        if self.peek().and_then(Tok::ident) == Some("struct")
            && self.peek_at(2).is_some_and(|t| t.is_punct("{"))
        {
            return self.parse_struct_definition(out);
        }
        // A bare `struct Tag ;` forward declaration leaves the type incomplete.
        if self.peek().and_then(Tok::ident) == Some("struct")
            && self.peek_at(2).is_some_and(|t| t.is_punct(";"))
        {
            return Some(());
        }

        let is_extern = self.toks.iter().any(|t| t.ident() == Some("extern"));
        let base = self.parse_base_ty()?;
        let ty = self.parse_pointer(base);
        let name = self.bump()?.ident()?.to_owned();

        if self.eat_punct("(") {
            let (params, variadic) = self.parse_params()?;
            self.expect_punct(")")?;
            if self.eat_punct(";") {
                // A prototype defines nothing.
                return Some(());
            }
            let body = self.parse_compound()?;
            if !self.at_end() {
                return None;
            }
            // A SECOND definition of the same symbol is a program the linker
            // would reject; whichever one this front-end kept would be a
            // coin flip, and a coin flip is a mis-translation. Refuse the
            // symbol entirely — it falls back to the sound effect frame.
            if out.funcs.contains_key(&name) {
                out.funcs.remove(&name);
                out.refused.insert(name, "defined more than once across --c-lib files".into());
                return Some(());
            }
            out.funcs.insert(name.clone(), CFunc { name, ret: ty, params, variadic, body });
            return Some(());
        }

        // File-scope object.
        let init = if self.eat_punct("=") {
            let expr = self.parse_expr()?;
            Some(const_fold(&expr)?)
        } else {
            None
        };
        self.expect_punct(";")?;
        if !self.at_end() {
            return None;
        }
        if !is_extern {
            // Same rule as for functions: two definitions, no authority.
            if let Some(previous) = out.globals.get(&name)
                && (previous.ty != ty || previous.init != init)
            {
                out.globals.remove(&name);
                out.refused.insert(name, "defined more than once across --c-lib files".into());
                return Some(());
            }
            out.globals.insert(name.clone(), CGlobal { name, ty, init });
        }
        Some(())
    }

    fn parse_struct_definition(&mut self, out: &mut CProgram) -> Option<()> {
        self.eat_ident("struct").then_some(())?;
        let tag = self.bump()?.ident()?.to_owned();
        self.expect_punct("{")?;
        let mut fields = Vec::new();
        while !self.eat_punct("}") {
            let base = self.parse_base_ty()?;
            loop {
                let fty = self.parse_pointer(base.clone());
                let fname = self.bump()?.ident()?.to_owned();
                // Arrays and bitfields are outside the fragment.
                if self.peek().is_some_and(|t| t.is_punct("[") || t.is_punct(":")) {
                    return None;
                }
                fields.push(CField { name: fname, ty: fty });
                if !self.eat_punct(",") {
                    break;
                }
            }
            self.expect_punct(";")?;
        }
        self.eat_punct(";");
        if !self.at_end() {
            return None;
        }
        // A tag with two DIFFERENT definitions has no layout this front-end
        // may pick between, so the tag is dropped and every prototype
        // mentioning it then fails the layout check.
        if let Some(previous) = out.structs.get(&tag)
            && previous.fields != fields
        {
            out.structs.remove(&tag);
            out.refused.insert(tag, "struct defined more than once across --c-lib files".into());
            return Some(());
        }
        out.structs.insert(tag.clone(), CStructDef { name: tag, fields });
        Some(())
    }

    fn parse_params(&mut self) -> Option<(Vec<CParam>, bool)> {
        let mut params = Vec::new();
        let mut variadic = false;
        if self.peek().is_some_and(|t| t.is_punct(")")) {
            // In a DEFINITION an empty list specifies no parameters (C17
            // 6.7.6.3p14). Prototypes are discarded before they reach the
            // registry, so the unspecified-arguments reading never applies.
            return Some((params, false));
        }
        if self.peek().and_then(Tok::ident) == Some("void")
            && self.peek_at(1).is_some_and(|t| t.is_punct(")"))
        {
            self.pos += 1;
            return Some((params, false));
        }
        loop {
            if self.eat_punct("...") {
                variadic = true;
                break;
            }
            let base = self.parse_base_ty()?;
            let ty = self.parse_pointer(base);
            let name = match self.peek() {
                Some(Tok::Ident(n)) => {
                    let n = n.clone();
                    self.pos += 1;
                    Some(n)
                }
                _ => None,
            };
            if self.peek().is_some_and(|t| t.is_punct("[")) {
                return None;
            }
            params.push(CParam { name, ty });
            if !self.eat_punct(",") {
                break;
            }
        }
        Some((params, variadic))
    }

    // ----------------------------------------------------------- statements

    fn parse_compound(&mut self) -> Option<CStmt> {
        self.expect_punct("{")?;
        let mut stmts = Vec::new();
        while !self.eat_punct("}") {
            if self.at_end() {
                return None;
            }
            stmts.push(self.parse_stmt()?);
        }
        Some(CStmt::Compound(stmts))
    }

    fn parse_stmt(&mut self) -> Option<CStmt> {
        if self.eat_punct(";") {
            return Some(CStmt::Empty);
        }
        if self.peek().is_some_and(|t| t.is_punct("{")) {
            return self.parse_compound();
        }
        match self.peek().and_then(Tok::ident) {
            Some("return") => {
                self.pos += 1;
                if self.eat_punct(";") {
                    return Some(CStmt::Return(None));
                }
                let e = self.parse_expr()?;
                self.expect_punct(";")?;
                Some(CStmt::Return(Some(e)))
            }
            Some("if") => {
                self.pos += 1;
                self.expect_punct("(")?;
                let cond = self.parse_expr()?;
                self.expect_punct(")")?;
                let then = Box::new(self.parse_stmt()?);
                let other =
                    if self.eat_ident("else") { Some(Box::new(self.parse_stmt()?)) } else { None };
                Some(CStmt::If { cond, then, other })
            }
            Some("for") => {
                self.pos += 1;
                self.expect_punct("(")?;
                // The init clause is a declaration or an expression statement;
                // both are already `parse_stmt` shapes, and both consume the
                // first `;`.
                let init =
                    if self.eat_punct(";") { None } else { Some(Box::new(self.parse_stmt()?)) };
                let cond = if self.peek().is_some_and(|t| t.is_punct(";")) {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                self.expect_punct(";")?;
                let step = if self.peek().is_some_and(|t| t.is_punct(")")) {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                self.expect_punct(")")?;
                let body = Box::new(self.parse_stmt()?);
                Some(CStmt::For { init, cond, step, body })
            }
            Some("while") => {
                self.pos += 1;
                self.expect_punct("(")?;
                let cond = self.parse_expr()?;
                self.expect_punct(")")?;
                let body = Box::new(self.parse_stmt()?);
                Some(CStmt::For { init: None, cond: Some(cond), step: None, body })
            }
            // `do`/`switch`/`goto` and the jumps that would give a loop body a
            // second exit stay Tier 2: the unroller models exactly one back
            // edge and one exit, and a `break` inside it would be a silent
            // mis-translation.
            Some("do" | "switch" | "goto" | "break" | "continue" | "case" | "default") => None,
            _ => {
                if self.at_type_start() {
                    let base = self.parse_base_ty()?;
                    let ty = self.parse_pointer(base);
                    let name = self.bump()?.ident()?.to_owned();
                    if self.peek().is_some_and(|t| t.is_punct("[")) {
                        return None;
                    }
                    let init = if self.eat_punct("=") { Some(self.parse_expr()?) } else { None };
                    self.expect_punct(";")?;
                    return Some(CStmt::Decl { ty, name, init });
                }
                let e = self.parse_expr()?;
                self.expect_punct(";")?;
                Some(CStmt::Expr(e))
            }
        }
    }

    // ---------------------------------------------------------- expressions

    pub(crate) fn parse_expr(&mut self) -> Option<CExpr> {
        self.parse_assign()
    }

    fn parse_assign(&mut self) -> Option<CExpr> {
        let lhs = self.parse_conditional()?;
        let op = match self.peek() {
            Some(Tok::Punct("=")) => None,
            Some(Tok::Punct("+=")) => Some(CBinOp::Add),
            Some(Tok::Punct("-=")) => Some(CBinOp::Sub),
            Some(Tok::Punct("*=")) => Some(CBinOp::Mul),
            Some(Tok::Punct("/=")) => Some(CBinOp::Div),
            Some(Tok::Punct("%=")) => Some(CBinOp::Rem),
            Some(Tok::Punct("<<=")) => Some(CBinOp::Shl),
            Some(Tok::Punct(">>=")) => Some(CBinOp::Shr),
            Some(Tok::Punct("&=")) => Some(CBinOp::BitAnd),
            Some(Tok::Punct("|=")) => Some(CBinOp::BitOr),
            Some(Tok::Punct("^=")) => Some(CBinOp::BitXor),
            _ => return Some(lhs),
        };
        self.pos += 1;
        let rhs = self.parse_assign()?;
        Some(CExpr::Assign { op, lhs: Box::new(lhs), rhs: Box::new(rhs) })
    }

    fn parse_conditional(&mut self) -> Option<CExpr> {
        let cond = self.parse_binary(0)?;
        if !self.eat_punct("?") {
            return Some(cond);
        }
        let then = self.parse_expr()?;
        self.expect_punct(":")?;
        let other = self.parse_conditional()?;
        Some(CExpr::Cond { cond: Box::new(cond), then: Box::new(then), other: Box::new(other) })
    }

    fn parse_binary(&mut self, min_prec: u8) -> Option<CExpr> {
        let mut lhs = self.parse_unary()?;
        loop {
            let Some((op, prec)) = self.peek().and_then(binary_op) else { break };
            if prec < min_prec {
                break;
            }
            self.pos += 1;
            let rhs = self.parse_binary(prec + 1)?;
            lhs = CExpr::Binary(op, Box::new(lhs), Box::new(rhs));
        }
        Some(lhs)
    }

    fn parse_unary(&mut self) -> Option<CExpr> {
        if self.eat_punct("-") {
            return Some(CExpr::Unary(CUnOp::Neg, Box::new(self.parse_unary()?)));
        }
        if self.eat_punct("+") {
            return Some(CExpr::Unary(CUnOp::Plus, Box::new(self.parse_unary()?)));
        }
        if self.eat_punct("!") {
            return Some(CExpr::Unary(CUnOp::LogicalNot, Box::new(self.parse_unary()?)));
        }
        if self.eat_punct("~") {
            return Some(CExpr::Unary(CUnOp::BitNot, Box::new(self.parse_unary()?)));
        }
        if self.eat_punct("*") {
            return Some(CExpr::Deref(Box::new(self.parse_unary()?)));
        }
        if self.eat_punct("++") {
            let t = self.parse_unary()?;
            return Some(CExpr::IncDec { prefix: true, inc: true, target: Box::new(t) });
        }
        if self.eat_punct("--") {
            let t = self.parse_unary()?;
            return Some(CExpr::IncDec { prefix: true, inc: false, target: Box::new(t) });
        }
        if self.peek().and_then(Tok::ident) == Some("sizeof") {
            self.pos += 1;
            // Only `sizeof(type-name)` is accepted; `sizeof expr` needs a full
            // type checker over the expression grammar.
            self.expect_punct("(")?;
            let ty = self.parse_type_name()?;
            self.expect_punct(")")?;
            return Some(CExpr::SizeOfTy(ty));
        }
        // Cast: `(` type-name `)` unary.
        if self.peek().is_some_and(|t| t.is_punct("("))
            && self
                .peek_at(1)
                .and_then(Tok::ident)
                .is_some_and(|w| TYPE_KEYWORDS.contains(&w) || IGNORED_SPECIFIERS.contains(&w))
        {
            let save = self.pos;
            self.pos += 1;
            if let Some(ty) = self.parse_type_name()
                && self.eat_punct(")")
            {
                let inner = self.parse_unary()?;
                return Some(CExpr::Cast(ty, Box::new(inner)));
            }
            self.pos = save;
        }
        self.parse_postfix()
    }

    fn parse_postfix(&mut self) -> Option<CExpr> {
        let mut e = self.parse_primary()?;
        loop {
            if self.eat_punct(".") {
                let f = self.bump()?.ident()?.to_owned();
                e = CExpr::Member { base: Box::new(e), field: f, arrow: false };
            } else if self.eat_punct("->") {
                let f = self.bump()?.ident()?.to_owned();
                e = CExpr::Member { base: Box::new(e), field: f, arrow: true };
            } else if self.eat_punct("++") {
                e = CExpr::IncDec { prefix: false, inc: true, target: Box::new(e) };
            } else if self.eat_punct("--") {
                e = CExpr::IncDec { prefix: false, inc: false, target: Box::new(e) };
            } else if self.peek().is_some_and(|t| t.is_punct("(")) {
                let CExpr::Ident(callee) = e else { return None };
                if let Some(va) = self.parse_va_macro(&callee)? {
                    e = va;
                    continue;
                }
                self.pos += 1;
                let mut args = Vec::new();
                if !self.eat_punct(")") {
                    loop {
                        args.push(self.parse_assign()?);
                        if self.eat_punct(")") {
                            break;
                        }
                        self.expect_punct(",")?;
                    }
                }
                e = CExpr::Call { callee, args };
            } else if self.peek().is_some_and(|t| t.is_punct("[")) {
                // Array subscript is Tier 2.
                return None;
            } else {
                break;
            }
        }
        Some(e)
    }

    /// `va_start(ap, last)`, `va_arg(ap, type-name)`, `va_end(ap)`.
    ///
    /// `Some(None)` means "not one of these", so the caller parses an ordinary
    /// call. `None` REFUSES the declaration: a `va_*` macro whose shape is not
    /// the one modelled must never fall through to the generic `Call` path,
    /// where the lowering would meet an unknown callee and `va_arg`'s type
    /// operand would already have been mis-parsed as an expression.
    fn parse_va_macro(&mut self, callee: &str) -> Option<Option<CExpr>> {
        if !matches!(callee, "va_start" | "va_arg" | "va_end") {
            return Some(None);
        }
        self.expect_punct("(")?;
        let ap = self.bump()?.ident()?.to_owned();
        let built = match callee {
            "va_end" => CExpr::VaEnd { ap },
            "va_start" => {
                self.expect_punct(",")?;
                let last = self.bump()?.ident()?.to_owned();
                CExpr::VaStart { ap, last }
            }
            // The second operand of `va_arg` is a TYPE NAME. A type outside
            // this fragment refuses the whole declaration rather than reading
            // the fetch at some other type.
            _ => {
                self.expect_punct(",")?;
                let ty = self.parse_type_name()?;
                CExpr::VaArg { ap, ty }
            }
        };
        self.expect_punct(")")?;
        Some(Some(built))
    }

    fn parse_primary(&mut self) -> Option<CExpr> {
        match self.bump()? {
            Tok::Num { value, unsigned_suffix } => {
                Some(CExpr::IntLit { value: *value, unsigned: *unsigned_suffix })
            }
            Tok::Char(v) => Some(CExpr::IntLit { value: *v, unsigned: false }),
            Tok::Ident(name) => {
                if matches!(
                    name.as_str(),
                    "return" | "if" | "else" | "for" | "while" | "do" | "switch" | "sizeof"
                ) {
                    return None;
                }
                Some(CExpr::Ident(name.clone()))
            }
            Tok::Punct("(") => {
                let e = self.parse_expr()?;
                self.expect_punct(")")?;
                Some(e)
            }
            _ => None,
        }
    }
}

fn binary_op(t: &Tok) -> Option<(CBinOp, u8)> {
    let Tok::Punct(p) = t else { return None };
    Some(match *p {
        "||" => (CBinOp::LogicalOr, 0),
        "&&" => (CBinOp::LogicalAnd, 1),
        "|" => (CBinOp::BitOr, 2),
        "^" => (CBinOp::BitXor, 3),
        "&" => (CBinOp::BitAnd, 4),
        "==" => (CBinOp::Eq, 5),
        "!=" => (CBinOp::Ne, 5),
        "<" => (CBinOp::Lt, 6),
        "<=" => (CBinOp::Le, 6),
        ">" => (CBinOp::Gt, 6),
        ">=" => (CBinOp::Ge, 6),
        "<<" => (CBinOp::Shl, 7),
        ">>" => (CBinOp::Shr, 7),
        "+" => (CBinOp::Add, 8),
        "-" => (CBinOp::Sub, 8),
        "*" => (CBinOp::Mul, 9),
        "/" => (CBinOp::Div, 9),
        "%" => (CBinOp::Rem, 9),
        _ => return None,
    })
}

/// Fold a file-scope initializer to a constant.
///
/// Only literal integer arithmetic is folded. Anything that reads an object,
/// takes an address, or calls a function yields `None` — and a global with no
/// folded initializer is left with NO initial value, i.e. nondet, never zero.
pub(crate) fn const_fold(e: &CExpr) -> Option<i128> {
    Some(match e {
        CExpr::IntLit { value, .. } => *value,
        CExpr::Unary(op, inner) => {
            let v = const_fold(inner)?;
            match op {
                CUnOp::Neg => v.checked_neg()?,
                CUnOp::Plus => v,
                CUnOp::LogicalNot => i128::from(v == 0),
                CUnOp::BitNot => !v,
            }
        }
        CExpr::Binary(op, a, b) => {
            let (a, b) = (const_fold(a)?, const_fold(b)?);
            match op {
                CBinOp::Add => a.checked_add(b)?,
                CBinOp::Sub => a.checked_sub(b)?,
                CBinOp::Mul => a.checked_mul(b)?,
                CBinOp::Div => a.checked_div(b)?,
                CBinOp::Rem => a.checked_rem(b)?,
                CBinOp::Shl => a.checked_shl(u32::try_from(b).ok()?)?,
                CBinOp::Shr => a.checked_shr(u32::try_from(b).ok()?)?,
                CBinOp::BitAnd => a & b,
                CBinOp::BitOr => a | b,
                CBinOp::BitXor => a ^ b,
                CBinOp::Eq => i128::from(a == b),
                CBinOp::Ne => i128::from(a != b),
                CBinOp::Lt => i128::from(a < b),
                CBinOp::Le => i128::from(a <= b),
                CBinOp::Gt => i128::from(a > b),
                CBinOp::Ge => i128::from(a >= b),
                CBinOp::LogicalAnd => i128::from(a != 0 && b != 0),
                CBinOp::LogicalOr => i128::from(a != 0 || b != 0),
            }
        }
        CExpr::Cond { cond, then, other } => {
            if const_fold(cond)? != 0 {
                const_fold(then)?
            } else {
                const_fold(other)?
            }
        }
        _ => return None,
    })
}
