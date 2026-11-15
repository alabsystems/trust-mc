// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Initialized scalar/array source evidence at the STORE event. This walk
//! proves validity only; it never reconstructs a value from source MIR.
//! The actual value comes from the encoder's event-time expression/memory.

use super::{ChcCtx, native_init_custody::scalar};
use rustc_public::mir::{AggregateKind, Body, Operand, Rvalue, StatementKind, TerminatorKind};

struct Values<'a> {
    body: &'a Body,
    budget: usize,
    path: Vec<(usize, usize, usize)>,
}
impl Values<'_> {
    fn spend(&mut self) -> Option<()> {
        self.budget = self.budget.checked_sub(1)?;
        Some(())
    }
    fn rvalue(&mut self, rhs: &Rvalue, bb: usize, before: usize) -> bool {
        if self.spend().is_none() || self.path.len() >= 64 {
            return false;
        }
        let operands = match rhs {
            Rvalue::Use(op, ..) | Rvalue::Repeat(op, _) | Rvalue::UnaryOp(_, op) => vec![op],
            Rvalue::Aggregate(AggregateKind::Array(_), ops) => ops.iter().collect(),
            Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => vec![a, b],
            _ => return false,
        };
        operands.into_iter().all(|op| self.operand(op, bb, before))
    }
    fn operand(&mut self, op: &Operand, bb: usize, before: usize) -> bool {
        let body = self.body;
        match op {
            Operand::Constant(_) => op.ty(body.locals()).is_ok_and(scalar),
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                self.local(place.local, bb, before)
            }
            _ => false,
        }
    }
    fn local(&mut self, local: usize, bb: usize, before: usize) -> bool {
        let body = self.body;
        let point = (local, bb, before);
        if self.path.len() >= 64 || self.path.contains(&point) || self.spend().is_none() {
            return false;
        }
        self.path.push(point);
        let result=(||{
            // Any address escape could have changed validity without a typed
            // MIR definition. Decline even an otherwise harmless shared borrow.
            for block in &body.blocks {for statement in &block.statements {
                self.spend()?;
                if matches!(&statement.kind,StatementKind::Assign(_,Rvalue::Ref(_,_,p)|Rvalue::AddressOf(_,p)|Rvalue::Reborrow(_,_,p)) if p.local==local){return None;}
            }}
            let block=body.blocks.get(bb)?;
            if before>block.statements.len(){return None;}
            for index in (0..before).rev(){
                self.spend()?;
                match &block.statements[index].kind{
                    StatementKind::Assign(lhs,rhs) if lhs.local==local=>return Some(lhs.projection.is_empty()&&self.rvalue(rhs,bb,index)),
                    StatementKind::StorageLive(l)|StatementKind::StorageDead(l) if *l==local=>return None,
                    StatementKind::SetDiscriminant{place,..} if place.local==local=>return None,
                    _=>{},
                }
            }
            if bb==0{return None;}
            let mut predecessors=Vec::new();
            for (site,block) in body.blocks.iter().enumerate(){
                self.spend()?;
                if block.terminator.successors().contains(&bb){predecessors.push(site);}
            }
            if predecessors.is_empty(){return None;}
            for site in predecessors{
                let block=&body.blocks[site];
                // Call-produced values need their own validity contract. In
                // particular an unchecked MaybeUninit::assume_init is not one.
                if matches!(&block.terminator.kind,TerminatorKind::Call{destination,..} if destination.local==local){return None;}
                if !self.local(local,site,block.statements.len()){return None;}
            }
            Some(true)
        })().unwrap_or(false);
        self.path.pop();
        result
    }
}
impl ChcCtx<'_, '_> {
    pub(super) fn native_init_operand_is_defined_at(
        &self,
        op: &Operand,
        bb: usize,
        before: usize,
    ) -> bool {
        Values { body: self.body, budget: 16_384, path: Vec::new() }.operand(op, bb, before)
    }
    pub(super) fn native_init_rhs_is_defined_at(
        &self,
        rhs: &Rvalue,
        bb: usize,
        before: usize,
    ) -> bool {
        Values { body: self.body, budget: 16_384, path: Vec::new() }.rvalue(rhs, bb, before)
    }
}
