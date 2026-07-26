// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! MIR analysis passes that extracts information about the MIR model given as input to codegen.
//!
//! # Performance Impact
//!
//! This module will perform all the analyses requested. Callers are responsible for selecting
//! when the cost of these analyses are worth it.

use rustc_public::mir::mono::MonoItem;
use rustc_public::mir::{
    MirVisitor, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, visit::Location,
};
use std::collections::HashMap;
use std::fmt::Display;
use tracing::info;

/// This function will collect and print some information about the given set of mono items.
///
/// This function will print information like:
///  - Number of items per type (Function / Constant / Shims)
///  - Number of instructions per type.
///  - Total number of MIR instructions.
pub(crate) fn print_stats(items: &[MonoItem]) {
    let item_types = items.iter().collect::<Counter>();
    let visitor = items
        .iter()
        .filter_map(|mono| if let MonoItem::Fn(instance) = mono { Some(instance) } else { None })
        .fold(StatsVisitor::default(), |mut visitor, body| {
            visitor.visit_body(&body.body().expect("function should have body"));
            visitor
        });
    info!("====== Reachability Analysis Result =======");
    info!("Total # items: {}", item_types.total());
    info!("Total # statements: {}", visitor.stmts.total());
    info!("Total # expressions: {}", visitor.exprs.total());
    info!("\nReachable Items:\n{item_types}");
    info!("Statements:\n{}", visitor.stmts);
    info!("Expressions:\n{}", visitor.exprs);
    info!("-------------------------------------------")
}

#[derive(Default)]
/// MIR Visitor that collects information about the body of an item.
struct StatsVisitor {
    /// The types of each statement / terminator visited.
    stmts: Counter,
    /// The kind of each expressions found.
    exprs: Counter,
}

impl MirVisitor for StatsVisitor {
    fn visit_statement(&mut self, statement: &Statement, location: Location) {
        self.stmts.add(statement);
        // Also visit the type of expression.
        self.super_statement(statement, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator, _location: Location) {
        self.stmts.add(terminator);
        // Stop here since we don't care today about the information inside the terminator.
        // self.super_terminator(terminator, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue, _location: Location) {
        self.exprs.add(rvalue);
        // Stop here since we don't care today about the information inside the rvalue.
        // self.super_rvalue(rvalue, location);
    }
}

#[derive(Default)]
struct Counter {
    data: HashMap<Key, usize>,
}

impl Counter {
    fn add<T: Into<Key>>(&mut self, item: T) {
        *self.data.entry(item.into()).or_default() += 1;
    }

    fn total(&self) -> usize {
        self.data.iter().fold(0, |acc, item| acc + item.1)
    }
}

impl Display for Counter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (name, freq) in &self.data {
            writeln!(f, "  - {}: {freq}", name.0)?;
        }
        std::fmt::Result::Ok(())
    }
}

impl<T: Into<Key>> FromIterator<T> for Counter {
    // Required method
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut counter = Counter::default();
        for item in iter {
            counter.add(item.into())
        }
        counter
    }
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct Key(pub &'static str);

impl From<&MonoItem> for Key {
    fn from(value: &rustc_public::mir::mono::MonoItem) -> Self {
        match value {
            MonoItem::Fn(_) => Key("function"),
            MonoItem::GlobalAsm(_) => Key("global assembly"),
            MonoItem::Static(_) => Key("static item"),
        }
    }
}

impl From<&Statement> for Key {
    fn from(value: &Statement) -> Self {
        match value.kind {
            StatementKind::Assign(..) => Key("Assign"),
            StatementKind::Intrinsic(_) => Key("Intrinsic"),
            StatementKind::SetDiscriminant { .. } => Key("SetDiscriminant"),
            // For now, we don't care about the ones below.
            StatementKind::AscribeUserType { .. }
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::FakeRead(..)
            | StatementKind::Nop
            | StatementKind::PlaceMention(_)
            | StatementKind::Retag(_, _)
            | StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_) => Key("Ignored"),
        }
    }
}

impl From<&Terminator> for Key {
    fn from(value: &Terminator) -> Self {
        match value.kind {
            TerminatorKind::Abort => Key("Abort"),
            TerminatorKind::Assert { .. } => Key("Assert"),
            TerminatorKind::Call { .. } => Key("Call"),
            TerminatorKind::Drop { .. } => Key("Drop"),
            TerminatorKind::Goto { .. } => Key("Goto"),
            TerminatorKind::InlineAsm { .. } => Key("InlineAsm"),
            TerminatorKind::Resume => Key("Resume"),
            TerminatorKind::Return => Key("Return"),
            TerminatorKind::SwitchInt { .. } => Key("SwitchInt"),
            TerminatorKind::Unreachable => Key("Unreachable"),
        }
    }
}

impl From<&Rvalue> for Key {
    fn from(value: &Rvalue) -> Self {
        match value {
            Rvalue::Use(_) => Key("Use"),
            Rvalue::Repeat(_, _) => Key("Repeat"),
            Rvalue::Ref(_, _, _) => Key("Ref"),
            Rvalue::ThreadLocalRef(_) => Key("ThreadLocalRef"),
            Rvalue::AddressOf(_, _) => Key("AddressOf"),
            Rvalue::Len(_) => Key("Len"),
            Rvalue::Cast(_, _, _) => Key("Cast"),
            Rvalue::BinaryOp(..) => Key("BinaryOp"),
            Rvalue::CheckedBinaryOp(..) => Key("CheckedBinaryOp"),
            Rvalue::NullaryOp(_) => Key("NullaryOp"),
            Rvalue::UnaryOp(_, _) => Key("UnaryOp"),
            Rvalue::Discriminant(_) => Key("Discriminant"),
            Rvalue::Aggregate(_, _) => Key("Aggregate"),
            Rvalue::ShallowInitBox(_, _) => Key("ShallowInitBox"),
            Rvalue::CopyForDeref(_) => Key("CopyForDeref"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rustc_public_bridge::IndexedVal;
    use rustc_public::mir::{
        Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind, UnwindAction,
    };
    use rustc_public::ty::Span;

    fn dummy_span() -> Span {
        Span::to_val(0)
    }

    // === Counter tests ===

    #[test]
    fn test_counter_default_is_empty() {
        let counter = Counter::default();
        assert_eq!(counter.total(), 0);
    }

    #[test]
    fn test_counter_add_single_key() {
        let mut counter = Counter::default();
        counter.add(Key("test"));
        assert_eq!(counter.total(), 1);
    }

    #[test]
    fn test_counter_add_same_key_increments() {
        let mut counter = Counter::default();
        counter.add(Key("item"));
        counter.add(Key("item"));
        counter.add(Key("item"));
        assert_eq!(counter.total(), 3);
        assert_eq!(*counter.data.get(&Key("item")).expect("key should exist"), 3);
    }

    #[test]
    fn test_counter_add_distinct_keys() {
        let mut counter = Counter::default();
        counter.add(Key("alpha"));
        counter.add(Key("beta"));
        counter.add(Key("gamma"));
        assert_eq!(counter.total(), 3);
        assert_eq!(*counter.data.get(&Key("alpha")).expect("key should exist"), 1);
        assert_eq!(*counter.data.get(&Key("beta")).expect("key should exist"), 1);
        assert_eq!(*counter.data.get(&Key("gamma")).expect("key should exist"), 1);
    }

    #[test]
    fn test_counter_from_iterator() {
        let keys = vec![Key("a"), Key("b"), Key("a"), Key("c"), Key("a")];
        let counter: Counter = keys.into_iter().collect();
        assert_eq!(counter.total(), 5);
        assert_eq!(*counter.data.get(&Key("a")).expect("key should exist"), 3);
        assert_eq!(*counter.data.get(&Key("b")).expect("key should exist"), 1);
        assert_eq!(*counter.data.get(&Key("c")).expect("key should exist"), 1);
    }

    #[test]
    fn test_counter_display_format() {
        let mut counter = Counter::default();
        counter.add(Key("Assign"));
        counter.add(Key("Assign"));
        let output = format!("{}", counter);
        assert!(output.contains("Assign"));
        assert!(output.contains("2"));
    }

    // === Key conversion tests ===

    #[test]
    fn test_key_from_statement_assign() {
        let stmt = Statement {
            kind: StatementKind::Assign(
                Place { local: 0, projection: vec![] },
                Rvalue::Use(Operand::Copy(Place { local: 1, projection: vec![] })),
            ),
            span: dummy_span(),
        };
        let key: Key = (&stmt).into();
        assert_eq!(key, Key("Assign"));
    }

    #[test]
    fn test_key_from_statement_storage_live() {
        let stmt = Statement { kind: StatementKind::StorageLive(5), span: dummy_span() };
        let key: Key = (&stmt).into();
        assert_eq!(key, Key("Ignored"));
    }

    #[test]
    fn test_key_from_statement_storage_dead() {
        let stmt = Statement { kind: StatementKind::StorageDead(3), span: dummy_span() };
        let key: Key = (&stmt).into();
        assert_eq!(key, Key("Ignored"));
    }

    #[test]
    fn test_key_from_statement_nop() {
        let stmt = Statement { kind: StatementKind::Nop, span: dummy_span() };
        let key: Key = (&stmt).into();
        assert_eq!(key, Key("Ignored"));
    }

    #[test]
    fn test_key_from_terminator_goto() {
        let term = Terminator { kind: TerminatorKind::Goto { target: 1 }, span: dummy_span() };
        let key: Key = (&term).into();
        assert_eq!(key, Key("Goto"));
    }

    #[test]
    fn test_key_from_terminator_return() {
        let term = Terminator { kind: TerminatorKind::Return, span: dummy_span() };
        let key: Key = (&term).into();
        assert_eq!(key, Key("Return"));
    }

    #[test]
    fn test_key_from_terminator_unreachable() {
        let term = Terminator { kind: TerminatorKind::Unreachable, span: dummy_span() };
        let key: Key = (&term).into();
        assert_eq!(key, Key("Unreachable"));
    }

    #[test]
    fn test_key_from_terminator_resume() {
        let term = Terminator { kind: TerminatorKind::Resume, span: dummy_span() };
        let key: Key = (&term).into();
        assert_eq!(key, Key("Resume"));
    }

    #[test]
    fn test_key_from_terminator_abort() {
        let term = Terminator { kind: TerminatorKind::Abort, span: dummy_span() };
        let key: Key = (&term).into();
        assert_eq!(key, Key("Abort"));
    }

    #[test]
    fn test_key_from_terminator_drop() {
        let term = Terminator {
            kind: TerminatorKind::Drop {
                place: Place { local: 0, projection: vec![] },
                target: 1,
                unwind: UnwindAction::Continue,
            },
            span: dummy_span(),
        };
        let key: Key = (&term).into();
        assert_eq!(key, Key("Drop"));
    }

    #[test]
    fn test_key_from_rvalue_use() {
        let rvalue = Rvalue::Use(Operand::Copy(Place { local: 0, projection: vec![] }));
        let key: Key = (&rvalue).into();
        assert_eq!(key, Key("Use"));
    }

    #[test]
    fn test_key_from_rvalue_discriminant() {
        let rvalue = Rvalue::Discriminant(Place { local: 2, projection: vec![] });
        let key: Key = (&rvalue).into();
        assert_eq!(key, Key("Discriminant"));
    }

    #[test]
    fn test_key_from_rvalue_len() {
        let rvalue = Rvalue::Len(Place { local: 3, projection: vec![] });
        let key: Key = (&rvalue).into();
        assert_eq!(key, Key("Len"));
    }

    #[test]
    fn test_key_from_rvalue_copy_for_deref() {
        let rvalue = Rvalue::CopyForDeref(Place { local: 0, projection: vec![] });
        let key: Key = (&rvalue).into();
        assert_eq!(key, Key("CopyForDeref"));
    }

    // === StatsVisitor integration with Counter ===

    #[test]
    fn test_counter_mixed_statement_types() {
        let stmts = [
            Statement {
                kind: StatementKind::Assign(
                    Place { local: 0, projection: vec![] },
                    Rvalue::Use(Operand::Copy(Place { local: 1, projection: vec![] })),
                ),
                span: dummy_span(),
            },
            Statement { kind: StatementKind::StorageLive(1), span: dummy_span() },
            Statement { kind: StatementKind::StorageDead(1), span: dummy_span() },
            Statement {
                kind: StatementKind::Assign(
                    Place { local: 2, projection: vec![] },
                    Rvalue::Use(Operand::Copy(Place { local: 3, projection: vec![] })),
                ),
                span: dummy_span(),
            },
            Statement { kind: StatementKind::Nop, span: dummy_span() },
        ];
        let counter: Counter = stmts.iter().collect();
        assert_eq!(counter.total(), 5);
        assert_eq!(*counter.data.get(&Key("Assign")).expect("key should exist"), 2);
        assert_eq!(*counter.data.get(&Key("Ignored")).expect("key should exist"), 3);
    }

    #[test]
    fn test_counter_multiple_terminator_types() {
        let terminators = [
            Terminator { kind: TerminatorKind::Return, span: dummy_span() },
            Terminator { kind: TerminatorKind::Goto { target: 0 }, span: dummy_span() },
            Terminator { kind: TerminatorKind::Goto { target: 1 }, span: dummy_span() },
            Terminator { kind: TerminatorKind::Unreachable, span: dummy_span() },
        ];
        let counter: Counter = terminators.iter().collect();
        assert_eq!(counter.total(), 4);
        assert_eq!(*counter.data.get(&Key("Return")).expect("key should exist"), 1);
        assert_eq!(*counter.data.get(&Key("Goto")).expect("key should exist"), 2);
        assert_eq!(*counter.data.get(&Key("Unreachable")).expect("key should exist"), 1);
    }
}
