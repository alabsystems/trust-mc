// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The restricted C fragment's abstract syntax, plus the C ABI layout rules
//! needed to CHECK a C aggregate against the Rust `#[repr(C)]` type the
//! `extern` block declares.
//!
//! Everything here is an ALLOWLIST. A construct with no variant in these enums
//! has no representation at all, so it cannot be approximated by accident: the
//! parser refuses the enclosing declaration and the call keeps the sound
//! effect frame.

use std::collections::BTreeMap;

/// Integer widths that vary by target. Resolved once from the compilation
/// target rather than assumed, because a wrong `long` is a MIS-TRANSLATION and
/// the front-end's whole soundness obligation is to never commit one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CTarget {
    pub pointer_bits: u32,
    pub long_bits: u32,
}

impl CTarget {
    pub(crate) fn new(pointer_bits: u32, long_bits: u32) -> Self {
        Self { pointer_bits, long_bits }
    }
}

/// A type in the accepted fragment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CTy {
    Void,
    Bool,
    Int {
        bits: u32,
        signed: bool,
    },
    Struct(String),
    Ptr(Box<CTy>),
    /// `va_list`. It has NO modelled object representation — its ABI is
    /// target-defined and this front-end has established nothing about it. It
    /// is admissible in exactly one position, a block-scope declaration whose
    /// only uses are `va_start` / `va_arg` / `va_end`; everywhere else
    /// (parameter, return, struct field, pointee, `sizeof`) it is refused,
    /// because a size or a layout for it would be an invention.
    VaList,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CUnOp {
    Neg,
    Plus,
    LogicalNot,
    BitNot,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    LogicalAnd,
    LogicalOr,
}

impl CBinOp {
    pub(crate) fn is_comparison(self) -> bool {
        matches!(self, CBinOp::Eq | CBinOp::Ne | CBinOp::Lt | CBinOp::Le | CBinOp::Gt | CBinOp::Ge)
    }
    pub(crate) fn is_logical(self) -> bool {
        matches!(self, CBinOp::LogicalAnd | CBinOp::LogicalOr)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CExpr {
    /// `unsigned` records a `u`/`U` suffix.
    IntLit {
        value: i128,
        unsigned: bool,
    },
    Ident(String),
    Unary(CUnOp, Box<CExpr>),
    Binary(CBinOp, Box<CExpr>, Box<CExpr>),
    /// `lhs = rhs`, or `lhs op= rhs` when the op is present.
    Assign {
        op: Option<CBinOp>,
        lhs: Box<CExpr>,
        rhs: Box<CExpr>,
    },
    IncDec {
        prefix: bool,
        inc: bool,
        target: Box<CExpr>,
    },
    /// `base.field` (`arrow == false`) or `base->field` (`arrow == true`).
    Member {
        base: Box<CExpr>,
        field: String,
        arrow: bool,
    },
    Deref(Box<CExpr>),
    Cast(CTy, Box<CExpr>),
    SizeOfTy(CTy),
    Cond {
        cond: Box<CExpr>,
        then: Box<CExpr>,
        other: Box<CExpr>,
    },
    /// A call. Only `assert` survives lowering; every other callee is refused
    /// there, so parsing one here costs nothing and keeps the refusal message
    /// specific.
    Call {
        callee: String,
        args: Vec<CExpr>,
    },
    /// `va_start(ap, last)`. `last` must NAME the final named parameter
    /// (C17 7.16.1.4p3); the lowering checks that and refuses otherwise.
    VaStart {
        ap: String,
        last: String,
    },
    /// `va_arg(ap, T)`. The second operand is a TYPE NAME, not an expression,
    /// so it cannot be spelled with `Call`.
    VaArg {
        ap: String,
        ty: CTy,
    },
    /// `va_end(ap)`.
    VaEnd {
        ap: String,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CStmt {
    Compound(Vec<CStmt>),
    Expr(CExpr),
    Return(Option<CExpr>),
    If {
        cond: CExpr,
        then: Box<CStmt>,
        other: Option<Box<CStmt>>,
    },
    Decl {
        ty: CTy,
        name: String,
        init: Option<CExpr>,
    },
    /// `for (init; cond; step) body`, and `while (cond) body` as the form with
    /// no `init` and no `step`. An absent `cond` is `for(;;)` — a loop this
    /// front-end unrolls like any other and whose unwinding OBLIGATION then
    /// cannot be discharged, which is the honest outcome rather than a hidden
    /// truncation. `break`, `continue` and `goto` stay refused, so the body has
    /// exactly one exit and one back edge.
    For {
        init: Option<Box<CStmt>>,
        cond: Option<CExpr>,
        step: Option<CExpr>,
        body: Box<CStmt>,
    },
    Empty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CParam {
    pub name: Option<String>,
    pub ty: CTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CFunc {
    pub name: String,
    pub ret: CTy,
    pub params: Vec<CParam>,
    pub variadic: bool,
    pub body: CStmt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CField {
    pub name: String,
    pub ty: CTy,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CStructDef {
    pub name: String,
    pub fields: Vec<CField>,
}

/// A file-scope object with an initializer this front-end could evaluate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CGlobal {
    pub name: String,
    pub ty: CTy,
    /// `None` for a tentative definition or an `extern` declaration — no
    /// initial value is known, so nothing may be pinned.
    pub init: Option<i128>,
}

/// Everything the front-end managed to accept across all `--c-lib` files.
#[derive(Debug, Default)]
pub(crate) struct CProgram {
    pub funcs: BTreeMap<String, CFunc>,
    pub structs: BTreeMap<String, CStructDef>,
    pub globals: BTreeMap<String, CGlobal>,
    /// Symbols a `--c-lib` file defines but this fragment refused, with the
    /// reason. Diagnostic only: the call still gets the sound effect frame.
    pub refused: BTreeMap<String, String>,
}

impl CProgram {
    /// Byte size and alignment of `ty` under the platform C ABI.
    ///
    /// `None` for an incomplete struct — it has no size, and guessing one is
    /// exactly the class of error guard (b) exists to prevent.
    pub(crate) fn size_align(&self, ty: &CTy, target: CTarget) -> Option<(u64, u64)> {
        match ty {
            CTy::Void => None,
            // No established object representation: `sizeof(va_list)` is a
            // number this front-end has not been given, and inventing one
            // would silently mis-lay-out anything containing it.
            CTy::VaList => None,
            CTy::Bool => Some((1, 1)),
            CTy::Int { bits, .. } => {
                let bytes = u64::from(bits / 8);
                Some((bytes, bytes))
            }
            CTy::Ptr(_) => {
                let bytes = u64::from(target.pointer_bits / 8);
                Some((bytes, bytes))
            }
            CTy::Struct(tag) => {
                let def = self.structs.get(tag)?;
                let mut offset = 0u64;
                let mut max_align = 1u64;
                for f in &def.fields {
                    let (fsize, falign) = self.size_align(&f.ty, target)?;
                    max_align = max_align.max(falign);
                    offset = offset.next_multiple_of(falign);
                    offset += fsize;
                }
                Some((offset.next_multiple_of(max_align), max_align))
            }
        }
    }

    /// Byte offsets of every field of `tag`, in declaration order.
    pub(crate) fn field_offsets(&self, tag: &str, target: CTarget) -> Option<Vec<u64>> {
        let def = self.structs.get(tag)?;
        let mut offsets = Vec::with_capacity(def.fields.len());
        let mut offset = 0u64;
        for f in &def.fields {
            let (fsize, falign) = self.size_align(&f.ty, target)?;
            offset = offset.next_multiple_of(falign);
            offsets.push(offset);
            offset += fsize;
        }
        Some(offsets)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn program() -> CProgram {
        let mut p = CProgram::default();
        p.structs.insert(
            "Foo".into(),
            CStructDef {
                name: "Foo".into(),
                fields: vec![
                    CField { name: "i".into(), ty: CTy::Int { bits: 32, signed: false } },
                    CField { name: "c".into(), ty: CTy::Int { bits: 8, signed: false } },
                ],
            },
        );
        p.structs.insert(
            "Foo2".into(),
            CStructDef {
                name: "Foo2".into(),
                fields: vec![
                    CField { name: "i".into(), ty: CTy::Int { bits: 32, signed: false } },
                    CField { name: "c".into(), ty: CTy::Int { bits: 8, signed: false } },
                    CField { name: "i2".into(), ty: CTy::Int { bits: 32, signed: false } },
                ],
            },
        );
        p
    }

    /// The corpus's own fidelity bar: `Foo` is 8 bytes with `c` at 4, and
    /// `Foo2` is 12 bytes with `i2` at 8. A layout that gets these wrong
    /// cannot tell `takes_struct2` (20) from `takes_struct_ptr2` (19).
    #[test]
    fn c_abi_layout_matches_the_corpus_structs() {
        let p = program();
        let t = CTarget::new(64, 64);
        assert_eq!(p.size_align(&CTy::Struct("Foo".into()), t), Some((8, 4)));
        assert_eq!(p.field_offsets("Foo", t).unwrap(), vec![0, 4]);
        assert_eq!(p.size_align(&CTy::Struct("Foo2".into()), t), Some((12, 4)));
        assert_eq!(p.field_offsets("Foo2", t).unwrap(), vec![0, 4, 8]);
    }

    #[test]
    fn an_incomplete_struct_has_no_size() {
        let p = program();
        assert_eq!(p.size_align(&CTy::Struct("Unit".into()), CTarget::new(64, 64)), None);
    }
}
