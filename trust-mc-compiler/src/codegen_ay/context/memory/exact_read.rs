// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Byte-memory reads decided at codegen time.
//!
//! Byte memory is one store chain, and a read of it is `select(chain, addr)`:
//! the solver has to decide every store index against `addr`. Codegen can
//! decide many of them itself. Two constants, or one base plus two constant
//! offsets, are equal or not. A registered stack object shares no byte with an
//! allocated heap region, nor, below the pairwise cap, with another registered
//! stack object; both facts are asserted when the object is registered
//! (`AYCtx::register_stack_object`) or a region allocated (`AYCtx::heap_alloc`).
//! A store the read provably misses is stepped over, and a store at the read
//! address is the byte. SSA names are followed to the terms they were asserted
//! equal to.
//!
//! A folded term equals the original in every model of those assertions, so it
//! can replace the original anywhere in the same query. On the raw-read guard's
//! two select chains ay answered `unknown (incomplete)`, and on the swap and
//! copy shapes it ran out of memory; the folded checks are small bitvector
//! formulas.

use std::collections::HashMap;

use ay_bindings::{Expr, ExprValue};

use crate::codegen_ay::context::AYCtx;
use crate::codegen_ay::context::heap::{HEAP_STRIDE, MAX_PAIRWISE_STACK_OBJECTS};
use crate::codegen_ay::types::POINTER_WIDTH;

/// Store nodes one read steps over before it keeps the rest of the chain.
const MAX_STORE_WALK: usize = 1024;
/// Term nodes one fold visits; past it, terms are returned as they are.
const MAX_VISITS: usize = 50_000;
/// Nesting depth one fold descends into a term.
const MAX_DEPTH: usize = 64;
/// Nesting depth one address resolution descends into a term.
const ADDR_DEPTH: usize = 32;
/// Implied terms an assumption contributes to a fold.
const MAX_ASSUMED: usize = 256;
/// Nodes visited when recovering common facts at control-flow joins.
const MAX_ASSUMPTION_VISITS: usize = 1024;

/// What codegen has asserted about addresses and the values stored at them.
pub(in crate::codegen_ay) struct ByteMemoryFacts<'a> {
    /// SSA name to the term it was asserted equal to.
    defs: &'a HashMap<String, Expr>,
    /// Registered stack objects `(address, size)`, in registration order.
    stack_objects: &'a [(Expr, u64)],
    /// Heap regions `1..next_alloc_id` are allocated.
    next_alloc_id: u64,
}

impl AYCtx<'_, '_> {
    /// The facts a fold may use; `defs` are the codegen's SSA definitions.
    pub(in crate::codegen_ay) fn byte_memory_facts<'s>(
        &'s self,
        defs: &'s HashMap<String, Expr>,
    ) -> ByteMemoryFacts<'s> {
        ByteMemoryFacts {
            defs,
            stack_objects: &self.heap_state.stack_objects,
            next_alloc_id: self.heap_state.next_alloc_id,
        }
    }
}

impl ByteMemoryFacts<'_> {
    /// `e` with every byte-memory read these facts decide folded away.
    #[must_use]
    pub(in crate::codegen_ay) fn fold(&self, e: &Expr) -> Expr {
        self.fold_assuming(e, None)
    }

    /// `fold` for a term used only where `assumption` holds. A conditional
    /// whose condition is implied by the assumption takes its first branch,
    /// and one whose negation is implied takes its second. Keep conjunction
    /// facts and facts common to all arms of a disjunction. An asserted
    /// `ite(path, value, init)` can then resolve beyond another join.
    /// The result equals `e` in every model of the facts where the assumption
    /// holds.
    #[must_use]
    pub(in crate::codegen_ay) fn fold_assuming(&self, e: &Expr, assumption: Option<&Expr>) -> Expr {
        let mut implied = Vec::new();
        if let Some(assumption) = assumption {
            let mut remaining = MAX_ASSUMPTION_VISITS;
            implied_terms(assumption, &mut implied, MAX_DEPTH, &mut remaining);
        }
        let assumed = implied
            .iter()
            .map(|fact| {
                let (condition, positive) = boolean_polarity(fact);
                (condition.clone(), positive)
            })
            .collect();
        let mut folder = Folder { facts: self, visits: 0, assumed };
        if e.sort().is_bool()
            && let Some(value) = folder.decided(e)
        {
            return Expr::bool_const(value);
        }
        folder.term(e, MAX_DEPTH)
    }
}

/// Collect terms forced true by `e`. At a disjunction, an implied term
/// must appear in every arm's facts. Exhausting a bound drops facts only.
fn implied_terms(e: &Expr, out: &mut Vec<Expr>, depth: usize, remaining: &mut usize) {
    if out.len() >= MAX_ASSUMED || depth == 0 || *remaining == 0 {
        return;
    }
    *remaining -= 1;
    let depth = depth - 1;
    out.push(e.clone());
    match e.value() {
        ExprValue::And(children) => {
            for child in children {
                implied_terms(child, out, depth, remaining);
                if out.len() >= MAX_ASSUMED || *remaining == 0 {
                    break;
                }
            }
        }
        ExprValue::Or(children) => {
            let mut children = children.iter();
            let Some(first) = children.next() else {
                return;
            };
            let mut common = Vec::new();
            implied_terms(first, &mut common, depth, remaining);
            let mut arm = Vec::new();
            for child in children {
                if common.is_empty() {
                    return;
                }
                arm.clear();
                implied_terms(child, &mut arm, depth, remaining);
                common.retain(|term| arm.contains(term));
            }
            out.extend(common.into_iter().take(MAX_ASSUMED - out.len()));
        }
        _ => {}
    }
}

/// Separate a condition from its leading negations. A bounded partial peel
/// still preserves the exact parity of every operator it removes.
fn boolean_polarity(mut condition: &Expr) -> (&Expr, bool) {
    let mut positive = true;
    for _ in 0..MAX_DEPTH {
        let ExprValue::Not(inner) = condition.value() else {
            break;
        };
        condition = inner;
        positive = !positive;
    }
    (condition, positive)
}

/// An address as `base + offset`, wrapping at the pointer width; no base for a
/// constant.
struct Addr {
    base: Option<Expr>,
    offset: u64,
}

enum Relation {
    Same,
    Distinct,
    Unknown,
}

enum ChainRead {
    /// The store at the read address wrote this byte.
    Byte(Expr),
    /// Every store above this rest of the chain misses the read address.
    Rest(Expr),
    /// The first store could not be decided.
    Unchanged,
}

struct Folder<'f, 'a> {
    facts: &'f ByteMemoryFacts<'a>,
    visits: usize,
    /// Conditions and their truth values wherever the folded term is used.
    assumed: Vec<(Expr, bool)>,
}

impl Folder<'_, '_> {
    fn spend(&mut self) -> bool {
        if self.visits >= MAX_VISITS {
            return false;
        }
        self.visits += 1;
        true
    }

    /// The truth value of `cond`, when it is a constant or the assumption
    /// decides it.
    fn decided(&self, cond: &Expr) -> Option<bool> {
        let (condition, positive) = boolean_polarity(cond);
        if let Some(value) = bool_value(condition) {
            return Some(value == positive);
        }
        self.assumed
            .iter()
            .find_map(|(known, value)| (known == condition).then_some(*value == positive))
    }

    fn term(&mut self, e: &Expr, depth: usize) -> Expr {
        if depth == 0 || !self.spend() {
            return e.clone();
        }
        let depth = depth - 1;
        let folded = match e.value() {
            ExprValue::Select { array, index } => match self.read(array, index) {
                ChainRead::Byte(byte) => return self.term(&byte, depth),
                ChainRead::Rest(rest) => return rest.select(index.clone()),
                ChainRead::Unchanged => return e.clone(),
            },
            ExprValue::BvExtract { expr, high, low } => {
                extract(self.term(expr, depth), *high, *low)
            }
            ExprValue::BvConcat(high, low) => {
                let high = self.term(high, depth);
                let low = self.term(low, depth);
                concat(high, low)
            }
            ExprValue::BvZeroExtend { expr, extra_bits } => {
                zero_extend(self.term(expr, depth), *extra_bits)
            }
            ExprValue::Ite { cond, then_expr, else_expr } => {
                let cond = if self.decided(cond).is_some() {
                    cond.clone()
                } else {
                    self.term(cond, depth)
                };
                match self.decided(&cond) {
                    Some(true) => return self.term(then_expr, depth),
                    Some(false) => return self.term(else_expr, depth),
                    None => {
                        let then_expr = self.term(then_expr, depth);
                        let else_expr = self.term(else_expr, depth);
                        ite(cond, then_expr, else_expr)
                    }
                }
            }
            ExprValue::And(children) => return self.junction(e, children, depth, true),
            ExprValue::Or(children) => return self.junction(e, children, depth, false),
            ExprValue::BvAdd(left, right)
            | ExprValue::BvSub(left, right)
            | ExprValue::BvMul(left, right)
            | ExprValue::BvAnd(left, right) => {
                let left = self.term(left, depth);
                let right = self.term(right, depth);
                arithmetic(e, left, right)
            }
            ExprValue::Not(inner) => match self.decided(inner) {
                Some(value) => Expr::bool_const(!value),
                None => not(self.term(inner, depth)),
            },
            ExprValue::Eq(left, right) => {
                let left = self.term(left, depth);
                let right = self.term(right, depth);
                equal(left, right)
            }
            ExprValue::Var { .. } => return self.constant(e, depth).unwrap_or_else(|| e.clone()),
            _ => return e.clone(),
        };
        // A rebuilt node with the original children keeps the original's sharing.
        if folded == *e { e.clone() } else { folded }
    }

    /// A conjunction (`all`) or disjunction with decided children dropped or
    /// deciding the whole; the original node when nothing changed.
    fn junction(&mut self, e: &Expr, children: &[Expr], depth: usize, all: bool) -> Expr {
        if let Some(value) = self.decided(e) {
            return Expr::bool_const(value);
        }
        let mut kept = Vec::with_capacity(children.len());
        let mut changed = false;
        for child in children {
            let folded = self.term(child, depth);
            match self.decided(&folded) {
                Some(value) if value != all => return Expr::bool_const(value),
                Some(_) => changed = true,
                None => {
                    changed |= folded != *child;
                    kept.push(folded);
                }
            }
        }
        if !changed {
            return e.clone();
        }
        match kept.len() {
            0 => Expr::bool_const(all),
            1 => kept.swap_remove(0),
            _ if all => Expr::and_many(kept),
            _ => Expr::or_many(kept),
        }
    }

    /// The constant `e` was asserted equal to, following SSA definitions and
    /// folding the term they end in.
    fn constant(&mut self, e: &Expr, depth: usize) -> Option<Expr> {
        let facts = self.facts;
        let mut current = e.clone();
        let mut depth = depth;
        loop {
            let next = match current.value() {
                ExprValue::BitVecConst { .. } | ExprValue::BoolConst(_) => return Some(current),
                ExprValue::Var { name } => facts
                    .defs
                    .get(name.as_str())
                    .filter(|def| def.sort() == current.sort())
                    .cloned(),
                _ => {
                    let folded = self.term(&current, depth);
                    return is_constant(&folded).then_some(folded);
                }
            };
            let next = next?;
            if depth == 0 || !self.spend() {
                return None;
            }
            depth -= 1;
            current = next;
        }
    }

    /// `e` as `base + offset`. Only pointer-width terms are addresses: an
    /// offset of another width would wrap somewhere else.
    fn addr(&mut self, e: &Expr, depth: usize) -> Addr {
        let opaque = Addr { base: Some(e.clone()), offset: 0 };
        if e.sort().bitvec_width() != Some(POINTER_WIDTH) || depth == 0 || !self.spend() {
            return opaque;
        }
        let depth = depth - 1;
        match e.value() {
            ExprValue::BitVecConst { value, .. } => {
                u64::try_from(value).map_or(opaque, |offset| Addr { base: None, offset })
            }
            ExprValue::BvAdd(left, right) => {
                let left = self.addr(left, depth);
                let right = self.addr(right, depth);
                let offset = left.offset.wrapping_add(right.offset);
                match (left.base, right.base) {
                    (None, None) => Addr { base: None, offset },
                    (Some(base), None) | (None, Some(base)) => Addr { base: Some(base), offset },
                    (Some(_), Some(_)) => opaque,
                }
            }
            ExprValue::Var { name } => {
                let facts = self.facts;
                match facts.defs.get(name.as_str()) {
                    Some(def) if def.sort() == e.sort() => self.addr(def, depth),
                    _ => opaque,
                }
            }
            ExprValue::Select { .. }
            | ExprValue::BvConcat(..)
            | ExprValue::BvExtract { .. }
            | ExprValue::BvZeroExtend { .. }
            | ExprValue::Ite { .. } => {
                let folded = self.term(e, depth);
                match folded.value() {
                    ExprValue::BitVecConst { .. }
                    | ExprValue::Var { .. }
                    | ExprValue::BvAdd(..) => self.addr(&folded, depth),
                    _ => opaque,
                }
            }
            _ => opaque,
        }
    }

    fn read(&mut self, array: &Expr, index: &Expr) -> ChainRead {
        if index.sort().bitvec_width() != Some(POINTER_WIDTH) {
            return ChainRead::Unchanged;
        }
        let target = self.addr(index, ADDR_DEPTH);
        let mut chain = array.clone();
        let mut moved = false;
        for _ in 0..MAX_STORE_WALK {
            let (inner, at, value) = match chain.value() {
                ExprValue::Store { array, index, value } => {
                    (array.clone(), index.clone(), value.clone())
                }
                ExprValue::ConstArray { value, .. } => return ChainRead::Byte(value.clone()),
                _ => break,
            };
            if !self.spend() {
                break;
            }
            let written = self.addr(&at, ADDR_DEPTH);
            match self.relation(&target, &written) {
                Relation::Same => return ChainRead::Byte(value),
                Relation::Distinct => {
                    chain = inner;
                    moved = true;
                }
                Relation::Unknown => break,
            }
        }
        if moved { ChainRead::Rest(chain) } else { ChainRead::Unchanged }
    }

    fn relation(&self, read: &Addr, write: &Addr) -> Relation {
        if read.base == write.base {
            return if read.offset == write.offset { Relation::Same } else { Relation::Distinct };
        }
        match (&read.base, &write.base) {
            (None, Some(object)) => self.apart_from_heap(object, write.offset, read.offset),
            (Some(object), None) => self.apart_from_heap(object, read.offset, write.offset),
            (Some(left), Some(right)) => self.apart_objects(left, read.offset, right, write.offset),
            (None, None) => Relation::Unknown,
        }
    }

    /// Byte `object + offset` of a registered stack object against a constant
    /// address in an allocated heap region. The object lies within one region
    /// (`AYCtx::heap_constrain_within_region`) and outside every allocated one.
    fn apart_from_heap(&self, object: &Expr, offset: u64, heap_addr: u64) -> Relation {
        let region = heap_addr / HEAP_STRIDE;
        let allocated = region >= 1 && region < self.facts.next_alloc_id;
        if allocated && self.stack_object(object, offset).is_some() {
            Relation::Distinct
        } else {
            Relation::Unknown
        }
    }

    /// Bytes of two different registered stack objects, the later registered
    /// below the pairwise cap, never coincide.
    fn apart_objects(
        &self,
        left: &Expr,
        left_offset: u64,
        right: &Expr,
        right_offset: u64,
    ) -> Relation {
        match (self.stack_object(left, left_offset), self.stack_object(right, right_offset)) {
            (Some(i), Some(j)) if i != j && i.max(j) < MAX_PAIRWISE_STACK_OBJECTS => {
                Relation::Distinct
            }
            _ => Relation::Unknown,
        }
    }

    /// Position of the registered stack object at `base` that holds byte `offset`.
    fn stack_object(&self, base: &Expr, offset: u64) -> Option<usize> {
        self.facts.stack_objects.iter().position(|(addr, size)| addr == base && offset < *size)
    }
}

fn is_constant(e: &Expr) -> bool {
    matches!(e.value(), ExprValue::BitVecConst { .. } | ExprValue::BoolConst(_))
}

fn bool_value(e: &Expr) -> Option<bool> {
    match e.value() {
        ExprValue::BoolConst(value) => Some(*value),
        _ => None,
    }
}

/// Value and width of a bitvector constant of at most 128 bits.
fn bits(e: &Expr) -> Option<(u128, u32)> {
    match e.value() {
        ExprValue::BitVecConst { value, width } if *width <= 128 => {
            u128::try_from(value).ok().map(|value| (value, *width))
        }
        _ => None,
    }
}

/// A bitvector arithmetic operation over folded operands.
fn arithmetic(e: &Expr, left: Expr, right: Expr) -> Expr {
    let width = e.sort().bitvec_width().unwrap_or(0);
    if let (Some((l, _)), Some((r, _))) = (bits(&left), bits(&right))
        && width <= 128
    {
        let value = match e.value() {
            ExprValue::BvAdd(..) => l.wrapping_add(r),
            ExprValue::BvSub(..) => l.wrapping_sub(r),
            ExprValue::BvMul(..) => l.wrapping_mul(r),
            _ => l & r,
        };
        return Expr::bitvec_const(low_bits(value, width), width);
    }
    let zero = |side: &Expr| bits(side).is_some_and(|(value, _)| value == 0);
    match e.value() {
        ExprValue::BvAnd(..) if zero(&left) || zero(&right) => Expr::bitvec_const(0u128, width),
        ExprValue::BvAdd(..) => left.bvadd(right),
        ExprValue::BvSub(..) => left.bvsub(right),
        ExprValue::BvMul(..) => left.bvmul(right),
        _ => left.bvand(right),
    }
}

fn low_bits(value: u128, width: u32) -> u128 {
    if width >= 128 { value } else { value & ((1u128 << width) - 1) }
}

fn ite(cond: Expr, then_expr: Expr, else_expr: Expr) -> Expr {
    if then_expr == else_expr {
        return then_expr;
    }
    match bool_value(&cond) {
        Some(true) => then_expr,
        Some(false) => else_expr,
        None => Expr::ite(cond, then_expr, else_expr),
    }
}

fn not(e: Expr) -> Expr {
    match e.value() {
        ExprValue::BoolConst(value) => Expr::bool_const(!*value),
        ExprValue::Not(inner) => inner.clone(),
        _ => e.not(),
    }
}

fn equal(left: Expr, right: Expr) -> Expr {
    if left == right {
        return Expr::bool_const(true);
    }
    if let (Some(l), Some(r)) = (bits(&left), bits(&right)) {
        return Expr::bool_const(l == r);
    }
    if let (Some(l), Some(r)) = (bool_value(&left), bool_value(&right)) {
        return Expr::bool_const(l == r);
    }
    for (choice, other) in [(&left, &right), (&right, &left)] {
        if let (ExprValue::Ite { cond, then_expr, else_expr }, Some((k, _))) =
            (choice.value(), bits(other))
            && let (Some((t, _)), Some((f, _))) = (bits(then_expr), bits(else_expr))
        {
            return match (t == k, f == k) {
                (true, true) => Expr::bool_const(true),
                (false, false) => Expr::bool_const(false),
                (true, false) => cond.clone(),
                (false, true) => not(cond.clone()),
            };
        }
    }
    left.eq(right)
}

fn extract(inner: Expr, high: u32, low: u32) -> Expr {
    let Some(width) = inner.sort().bitvec_width() else {
        return inner.extract(high, low);
    };
    if low == 0 && high + 1 == width {
        return inner;
    }
    let out = high - low + 1;
    if let Some((value, _)) = bits(&inner) {
        return Expr::bitvec_const(low_bits(value >> low, out), out);
    }
    match inner.value() {
        ExprValue::BvConcat(upper, lower) => {
            if let Some(lower_width) = lower.sort().bitvec_width() {
                if high < lower_width {
                    return extract(lower.clone(), high, low);
                }
                if low >= lower_width {
                    return extract(upper.clone(), high - lower_width, low - lower_width);
                }
            }
        }
        ExprValue::BvExtract { expr, low: base, .. } => {
            return extract(expr.clone(), high + base, low + base);
        }
        ExprValue::BvZeroExtend { expr, .. } => {
            if let Some(expr_width) = expr.sort().bitvec_width() {
                if high < expr_width {
                    return extract(expr.clone(), high, low);
                }
                if low >= expr_width {
                    return Expr::bitvec_const(0u128, out);
                }
            }
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            let then_expr = extract(then_expr.clone(), high, low);
            let else_expr = extract(else_expr.clone(), high, low);
            return ite(cond.clone(), then_expr, else_expr);
        }
        _ => {}
    }
    inner.extract(high, low)
}

fn concat(high: Expr, low: Expr) -> Expr {
    if let (Some((h, high_width)), Some((l, low_width))) = (bits(&high), bits(&low))
        && high_width + low_width <= 128
    {
        return Expr::bitvec_const((h << low_width) | l, high_width + low_width);
    }
    if let (
        ExprValue::BvExtract { expr: upper, high: top, low: split },
        ExprValue::BvExtract { expr: lower, high: below, low: bottom },
    ) = (high.value(), low.value())
        && upper == lower
        && *split == below + 1
    {
        return extract(upper.clone(), *top, *bottom);
    }
    if let (
        ExprValue::Ite { cond: high_cond, then_expr: high_then, else_expr: high_else },
        ExprValue::Ite { cond: low_cond, then_expr: low_then, else_expr: low_else },
    ) = (high.value(), low.value())
        && high_cond == low_cond
    {
        let then_expr = concat(high_then.clone(), low_then.clone());
        let else_expr = concat(high_else.clone(), low_else.clone());
        return ite(high_cond.clone(), then_expr, else_expr);
    }
    high.concat(low)
}

fn zero_extend(inner: Expr, extra_bits: u32) -> Expr {
    if extra_bits == 0 {
        return inner;
    }
    if let Some((value, width)) = bits(&inner)
        && width + extra_bits <= 128
    {
        return Expr::bitvec_const(value, width + extra_bits);
    }
    inner.zero_extend(extra_bits)
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ay_bindings::{Expr, Sort};

    use super::ByteMemoryFacts;
    use crate::codegen_ay::context::heap::MAX_PAIRWISE_STACK_OBJECTS;
    use crate::codegen_ay::types::POINTER_WIDTH;

    fn ptr(value: u128) -> Expr {
        Expr::bitvec_const(value, POINTER_WIDTH)
    }

    fn byte(value: u128) -> Expr {
        Expr::bitvec_const(value, 8)
    }

    fn var(name: &str, width: u32) -> Expr {
        Expr::var(name, Sort::bitvec(width))
    }

    fn memory() -> Expr {
        Expr::var("memory", Sort::memory())
    }

    fn offset(base: &Expr, k: u128) -> Expr {
        base.clone().bvadd(ptr(k))
    }

    /// As `store_memory_bytes`: byte `i` of `value` at `addr + i`, little-endian.
    fn store_bytes(memory: Expr, addr: &Expr, value: &Expr) -> Expr {
        let width = value.sort().bitvec_width().expect("bitvector value");
        (0..width / 8).fold(memory, |memory, i| {
            memory.store(offset(addr, u128::from(i)), value.clone().extract(8 * i + 7, 8 * i))
        })
    }

    /// As `load_memory_bytes`: byte 0 at `addr`, byte `i` at `addr + i`.
    fn load_bytes(memory: &Expr, addr: &Expr, num_bytes: u32) -> Expr {
        (1..num_bytes).fold(memory.clone().select(addr.clone()), |low, i| {
            memory.clone().select(offset(addr, u128::from(i))).concat(low)
        })
    }

    fn facts<'a>(
        defs: &'a HashMap<String, Expr>,
        stack_objects: &'a [(Expr, u64)],
        next_alloc_id: u64,
    ) -> ByteMemoryFacts<'a> {
        ByteMemoryFacts { defs, stack_objects, next_alloc_id }
    }

    #[test]
    fn distinct_constant_stores_are_stepped_over() {
        let defs = HashMap::new();
        let chain =
            store_bytes(store_bytes(memory(), &ptr(0x100000), &byte(1)), &ptr(0x200000), &byte(2));
        let read = load_bytes(&chain, &ptr(0x100000), 1);
        assert_eq!(facts(&defs, &[], 3).fold(&read), byte(1));
    }

    #[test]
    fn a_store_at_an_unknown_address_keeps_the_read() {
        let defs = HashMap::new();
        let below = store_bytes(memory(), &ptr(0x100000), &byte(1));
        let chain = store_bytes(below, &var("q", 64), &byte(9));
        let read = load_bytes(&chain, &ptr(0x100000), 1);
        assert_eq!(facts(&defs, &[], 3).fold(&read), read);
    }

    #[test]
    fn a_registered_stack_object_misses_allocated_heap_regions_only() {
        let defs = HashMap::new();
        let slot = var("local_7_addr", 64);
        let objects = [(slot.clone(), 8)];
        let chain =
            store_bytes(store_bytes(memory(), &ptr(0x100000), &byte(1)), &slot, &var("v", 64));
        let read = load_bytes(&chain, &ptr(0x100000), 1);
        assert_eq!(facts(&defs, &objects, 2).fold(&read), byte(1));
        // Region 1 is not allocated yet, so no placement fact covers it.
        assert_eq!(facts(&defs, &objects, 1).fold(&read), read);
        // An unregistered slot is not known to miss anything.
        assert_eq!(facts(&defs, &[], 2).fold(&read), read);
    }

    #[test]
    fn a_byte_past_the_registered_size_is_not_stepped_over() {
        let defs = HashMap::new();
        let slot = var("local_7_addr", 64);
        let objects = [(slot.clone(), 8)];
        let chain = memory().store(ptr(0x100000), byte(1)).store(offset(&slot, 8), byte(5));
        let read = chain.select(ptr(0x100000));
        assert_eq!(facts(&defs, &objects, 2).fold(&read), read);
    }

    #[test]
    fn offsets_from_one_base_decide() {
        let defs = HashMap::new();
        let base = var("p", 64);
        let chain = memory().store(offset(&base, 0), byte(3)).store(offset(&base, 1), byte(4));
        assert_eq!(facts(&defs, &[], 1).fold(&chain.clone().select(base.clone())), byte(3));
        assert_eq!(facts(&defs, &[], 1).fold(&chain.select(offset(&base, 1))), byte(4));
    }

    #[test]
    fn ssa_definitions_resolve_addresses() {
        let mut defs = HashMap::new();
        defs.insert("p_1".to_string(), var("p_0", 64));
        defs.insert("p_0".to_string(), ptr(0x200000));
        let chain =
            store_bytes(store_bytes(memory(), &ptr(0x200000), &byte(7)), &ptr(0x100000), &byte(8));
        let read = load_bytes(&chain, &var("p_1", 64), 1);
        assert_eq!(facts(&defs, &[], 3).fold(&read), byte(7));
    }

    #[test]
    fn a_multi_byte_value_reassembles() {
        let defs = HashMap::new();
        let value = var("v", 32);
        let chain = store_bytes(memory(), &ptr(0x100000), &value);
        let read = load_bytes(&chain, &ptr(0x100000), 4);
        assert_eq!(facts(&defs, &[], 2).fold(&read), value);
    }

    #[test]
    fn a_path_guarded_store_folds_to_both_values() {
        let defs = HashMap::new();
        let c = Expr::var("c", Sort::bool());
        let addr = ptr(0x100000);
        let initial = store_bytes(memory(), &addr, &var("v", 16));
        let previous = load_bytes(&initial, &addr, 2);
        let nine = Expr::bitvec_const(9u128, 16);
        let guarded = store_bytes(initial, &addr, &Expr::ite(c.clone(), nine.clone(), previous));
        let read = load_bytes(&guarded, &addr, 2);
        assert_eq!(facts(&defs, &[], 2).fold(&read), Expr::ite(c, nine, var("v", 16)));
    }

    #[test]
    fn a_boolean_byte_compare_folds_to_the_boolean() {
        let defs = HashMap::new();
        let b = Expr::var("b", Sort::bool());
        let addr = ptr(0x100000);
        let chain = memory().store(addr.clone(), Expr::ite(b.clone(), byte(1), byte(0)));
        let read = chain.select(addr).eq(byte(0)).not();
        assert_eq!(facts(&defs, &[], 2).fold(&read), b);
    }

    #[test]
    fn a_pointer_loaded_from_memory_resolves_to_its_target() {
        // `let d = *outer; *d = 9;` then a read of `*inner`: the store through
        // the loaded pointer is a store to `inner`, and the read must see it.
        let mut defs = HashMap::new();
        defs.insert("inner_0".to_string(), ptr(0x100000));
        let inner = var("inner_0", 64);
        let outer = ptr(0x200000);
        let initial = store_bytes(store_bytes(memory(), &inner, &byte(1)), &outer, &inner);
        let d = load_bytes(&initial, &outer, 8);
        let chain = store_bytes(initial, &d, &byte(9));
        let read = load_bytes(&chain, &ptr(0x100000), 1);
        assert_eq!(facts(&defs, &[], 3).fold(&read), byte(9));
    }

    #[test]
    fn stack_objects_past_the_pairwise_cap_are_not_known_apart() {
        let defs = HashMap::new();
        let objects: Vec<(Expr, u64)> = (0..=MAX_PAIRWISE_STACK_OBJECTS)
            .map(|i| (var(&format!("local_{i}_addr"), 64), 1))
            .collect();
        let first = objects[0].0.clone();
        let second = objects[1].0.clone();
        let last = objects[MAX_PAIRWISE_STACK_OBJECTS].0.clone();
        let below_cap = memory().store(first.clone(), byte(1)).store(second, byte(2));
        assert_eq!(facts(&defs, &objects, 1).fold(&below_cap.select(first.clone())), byte(1));
        let past_cap = memory().store(first.clone(), byte(1)).store(last, byte(2));
        let read = past_cap.select(first);
        assert_eq!(facts(&defs, &objects, 1).fold(&read), read);
    }

    #[test]
    fn a_value_defined_on_the_checked_path_resolves_under_that_path() {
        // `p_1 = ite(path, #x100000, init)`: the join definition of a pointer
        // assigned on this path. Only a check posed on the path may use it.
        let mut defs = HashMap::new();
        let path = Expr::var("path", Sort::bool());
        let init = var("p_init", 64);
        defs.insert("p_1".to_string(), Expr::ite(path.clone(), ptr(0x100000), init));
        let chain =
            store_bytes(store_bytes(memory(), &ptr(0x100000), &byte(5)), &ptr(0x200000), &byte(6));
        let read = load_bytes(&chain, &var("p_1", 64), 1);
        let facts = facts(&defs, &[], 3);
        assert_eq!(facts.fold(&read), read);
        assert_eq!(facts.fold_assuming(&read, Some(&path)), byte(5));
        let elsewhere = path.clone().not();
        assert_ne!(facts.fold_assuming(&read, Some(&elsewhere)), byte(5));
    }

    #[test]
    fn conjuncts_of_the_assumption_decide_conditions() {
        let defs = HashMap::new();
        let a = Expr::var("a", Sort::bool());
        let b = Expr::var("b", Sort::bool());
        let both = a.clone().and(b.clone());
        let facts = facts(&defs, &[], 1);
        let on_b = Expr::ite(b.clone(), byte(1), byte(2));
        let off_a = Expr::ite(a.clone().not(), byte(1), byte(2));
        assert_eq!(facts.fold_assuming(&on_b, Some(&both)), byte(1));
        assert_eq!(facts.fold_assuming(&off_a, Some(&both)), byte(2));
        assert_eq!(facts.fold(&on_b), on_b);
    }

    #[test]
    fn a_join_keeps_only_facts_implied_by_every_arm() {
        let defs = HashMap::new();
        let selected = Expr::var("selected", Sort::bool());
        let previous_join = Expr::var("previous_join", Sort::bool());
        let aligned = Expr::var("aligned", Sort::bool());
        let condition = previous_join
            .clone()
            .and(selected.clone())
            .or(previous_join.clone().and(selected.clone().not()))
            .and(aligned);
        let facts = facts(&defs, &[], 1);

        let initialized = Expr::ite(previous_join, byte(1), byte(2));
        let branch_value = Expr::ite(selected, byte(3), byte(4));
        assert_eq!(facts.fold_assuming(&initialized, Some(&condition)), byte(1));
        assert_eq!(facts.fold_assuming(&branch_value, Some(&condition)), branch_value);
    }

    #[test]
    fn nested_negations_select_the_feasible_pointer_arm() {
        let defs = HashMap::new();
        let selected = Expr::var("selected", Sort::bool());
        let condition = selected.clone().not().not();
        let opposite = selected.clone().not().not().not();
        let on_path = Expr::bool_const(true).and(opposite);
        let facts = facts(&defs, &[], 1);
        assert_eq!(facts.fold_assuming(&condition, Some(&on_path)), Expr::bool_const(false));
        assert_eq!(facts.fold_assuming(&selected, Some(&on_path)), Expr::bool_const(false));
        let joined = Expr::ite(condition, ptr(1), ptr(2));
        let displacement = joined.bvmul(ptr(8));
        assert_eq!(facts.fold_assuming(&displacement, Some(&on_path)), ptr(16));
    }

    #[test]
    fn alignment_and_non_null_checks_on_a_constant_pointer_fold_to_true() {
        // `ptr & (align - 1) == 0` with align 1, and `!(ptr == 0 && size != 0)`.
        let mut defs = HashMap::new();
        defs.insert("ptr_0".to_string(), ptr(0x100000));
        let pointer = var("ptr_0", 64);
        let mask = ptr(1).bvsub(ptr(1));
        let aligned = pointer.clone().bvand(mask).eq(ptr(0));
        let null_and_sized = pointer.eq(ptr(0)).and(ptr(2).eq(ptr(0)).not());
        let path = aligned.and(null_and_sized.not());
        assert_eq!(facts(&defs, &[], 2).fold(&path), Expr::bool_const(true));
        let unknown = Expr::var("c", Sort::bool());
        let partly = unknown.clone().and(Expr::bool_const(true));
        assert_eq!(facts(&defs, &[], 2).fold(&partly), unknown);
    }

    #[test]
    fn indices_of_other_widths_are_left_to_the_solver() {
        let defs = HashMap::new();
        let i = var("i", 32);
        let array = Expr::var("a", Sort::array(Sort::bitvec(32), Sort::bitvec(8)));
        // Equal modulo 2^32, different as 64-bit offsets.
        let written = i.clone().bvadd(Expr::bitvec_const(0xffff_ffffu128, 32));
        let chain = array.store(written, byte(1));
        let read = chain.select(i.bvsub(Expr::bitvec_const(1u128, 32)));
        assert_eq!(facts(&defs, &[], 1).fold(&read), read);
    }
}
