// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Invocation-local immutable facts and prepaid MIR traversal work.

use rustc_public::mir::visit::{Location, MirVisitor, PlaceContext};
use rustc_public::mir::{Operand, Place, Rvalue, Statement, Terminator, TerminatorKind};
use rustc_public::ty::Ty;
use std::collections::HashMap;

pub(super) const DEFAULT_WORK: usize = 65_536;
#[derive(Clone, Copy)]
pub(super) struct TypeFacts {
    pub(super) carrier: bool,
    pub(super) plain_native_owner: bool,
}
#[derive(Clone, Copy)]
pub(super) struct CallFacts {
    pub(super) header: bool,
    pub(super) drop: bool,
    pub(super) initializes: bool,
}

pub(super) struct RegionWork {
    pub(super) remaining: usize,
    pub(super) exhausted: bool,
    pub(super) types: HashMap<Ty, TypeFacts>,
    pub(super) calls: HashMap<usize, CallFacts>,
    pub(super) custom_global_allocator: Option<bool>,
}
impl RegionWork {
    pub(super) fn new(limit: usize) -> Self {
        Self {
            remaining: limit,
            exhausted: false,
            types: HashMap::new(),
            calls: HashMap::new(),
            custom_global_allocator: None,
        }
    }
    pub(super) fn charge(&mut self, count: usize) -> Result<(), ()> {
        match self.remaining.checked_sub(count) {
            Some(left) => {
                self.remaining = left;
                Ok(())
            }
            None => {
                self.remaining = 0;
                self.exhausted = true;
                Err(())
            }
        }
    }
    pub(super) fn place(&mut self, place: &Place) -> Result<(), ()> {
        // Prepay hashing/typing/cloning or a scan of this projection path.
        self.charge(place.projection.len().checked_mul(3).and_then(|n| n.checked_add(1)).ok_or(())?)
    }
    pub(super) fn operand(&mut self, operand: &Operand) -> Result<(), ()> {
        self.charge(1)?;
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.place(place)?;
        }
        Ok(())
    }
}

pub(super) struct Places<'a> {
    pub(super) values: Vec<Place>,
    work: &'a mut RegionWork,
    failed: bool,
}
impl<'a> Places<'a> {
    pub(super) fn new(work: &'a mut RegionWork) -> Self {
        Self { values: Vec::new(), work, failed: false }
    }
    fn charge(&mut self, count: usize) -> bool {
        if self.failed {
            return false;
        }
        if self.work.charge(count).is_err() {
            self.failed = true;
            return false;
        }
        true
    }
    pub(super) fn finish(self) -> Result<Vec<Place>, ()> {
        if self.failed { Err(()) } else { Ok(self.values) }
    }
}
impl MirVisitor for Places<'_> {
    fn visit_place(&mut self, place: &Place, _: PlaceContext, _: Location) {
        if self.failed {
            return;
        }
        if self.work.place(place).is_err() {
            self.failed = true;
            return;
        }
        self.values.push(place.clone());
    }
    fn visit_operand(&mut self, operand: &Operand, location: Location) {
        if self.charge(1) {
            self.super_operand(operand, location);
        }
    }
    fn visit_rvalue(&mut self, rvalue: &Rvalue, location: Location) {
        // super_rvalue's only variable-length loop is the aggregate operand
        // list. Prepay its complete outer loop before entering the visitor:
        // even if an inner projection exhausts work, the remaining callbacks
        // are bounded prepaid no-ops, never an uncharged oversized tail.
        let outer = match rvalue {
            Rvalue::Aggregate(_, ops) => ops.len(),
            _ => 0,
        };
        if outer.checked_add(1).is_some_and(|count| self.charge(count)) {
            self.super_rvalue(rvalue, location);
        } else {
            self.failed = true;
        }
    }
    fn visit_statement(&mut self, statement: &Statement, location: Location) {
        if self.charge(1) {
            self.super_statement(statement, location);
        }
    }
    fn visit_terminator(&mut self, term: &Terminator, location: Location) {
        let outer = match &term.kind {
            TerminatorKind::Call { args, .. } => args.len(),
            TerminatorKind::InlineAsm { operands, .. } => operands.len(),
            _ => 0,
        };
        if outer.checked_add(1).is_some_and(|count| self.charge(count)) {
            self.super_terminator(term, location);
        } else {
            self.failed = true;
        }
    }
    // Ty is an immutable handle, not a reason to recurse through a type graph.
    // Its authority/carrier classification is memoized separately by RegionWork.
    fn visit_ty(&mut self, _: &Ty, _: Location) {}
}
