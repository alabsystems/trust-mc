// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Reconcile early coverage encounters with exact, later callsite models.
//!
//! A path is never authority. Every encounter of a callee must be a direct
//! call in the one root body, carried through the compiler's inliner with its
//! complete block unchanged, and modeled in every encoding attempt. Unknown
//! uses, partial inventories, changed bodies and aborted scopes retain all events.

use super::diagnostics::{add_unstubbed_semantic_events, record_unstubbed_coverage};
use crate::kani_middle::reachability::AbstractionCallsite;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlock, Body, MirVisitor, Operand, TerminatorKind, visit::Location};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::rc::Rc;

#[derive(Clone, PartialEq, Eq)]
struct BodyIdentity {
    blocks: Vec<BasicBlock>,
    types: Vec<Ty>,
}
impl BodyIdentity {
    fn of(body: &Body) -> Self {
        Self { blocks: body.blocks.clone(), types: body.locals().iter().map(|d| d.ty).collect() }
    }
    fn matches(&self, body: &Body) -> bool {
        self.blocks == body.blocks
            && self.types.iter().copied().eq(body.locals().iter().map(|d| d.ty))
    }
}
struct ObservedRoot {
    address: usize,
    snapshot: Rc<BodyIdentity>,
}
struct Site {
    caller: Instance,
    block: usize,
    body: Rc<BodyIdentity>,
}
struct Encounter {
    callee: Instance,
    site: Option<Site>,
    identity_established: bool,
}
struct ActiveEncoding {
    body_address: usize,
    observed: HashSet<usize>,
}
#[derive(Default)]
struct Ledger {
    root: Option<Instance>,
    encounters: Vec<Encounter>,
    encoded_body: Option<BodyIdentity>,
    preserved: HashMap<usize, Instance>,
    active: Option<ActiveEncoding>,
    confirmed: Option<HashSet<usize>>,
    invalid: bool,
    opaque_uses: HashSet<Instance>,
    inventory: HashSet<(Instance, usize, Instance)>,
    collecting: bool,
    inventory_complete: bool,
    root_observed: bool,
    observed_root: Option<ObservedRoot>,
}
thread_local! {
    static SCOPES: RefCell<Vec<(u64, Ledger)>> = const { RefCell::new(Vec::new()) };
    static NEXT_SCOPE_ID: Cell<u64> = const { Cell::new(1) };
}
fn with_current<R>(f: impl FnOnce(&mut Ledger) -> R) -> Option<R> {
    SCOPES.with(|scopes| scopes.borrow_mut().last_mut().map(|(_, ledger)| f(ledger)))
}
fn with_owned<R>(owner: u64, f: impl FnOnce(&mut Ledger) -> R) -> Option<R> {
    SCOPES.with(|scopes| {
        scopes.borrow_mut().iter_mut().find(|(id, _)| *id == owner).map(|(_, ledger)| f(ledger))
    })
}

/// Each guard owns exactly one ledger, even if guards are dropped out of order.
/// Dropping without `finish` (including unwind/timeout) appends every event.
pub(super) struct AccountingScope {
    id: u64,
    // IDs address this thread's ledger stack; a guard must never migrate.
    _thread: PhantomData<Rc<()>>,
}
impl AccountingScope {
    pub(super) fn begin(root: Option<Instance>) -> Self {
        let id = NEXT_SCOPE_ID.with(|next| {
            let id = next.get();
            next.set(id.checked_add(1).expect("accounting scope identity exhausted"));
            id
        });
        SCOPES.with(|scopes| scopes.borrow_mut().push((id, Ledger { root, ..Ledger::default() })));
        Self { id, _thread: PhantomData }
    }
    pub(super) fn finish(mut self) {
        self.close(true);
    }
    fn close(&mut self, completed: bool) {
        if self.id == 0 {
            return;
        }
        let ledger = SCOPES.with(|scopes| {
            let mut scopes = scopes.borrow_mut();
            scopes.iter().position(|(id, _)| *id == self.id).map(|index| scopes.remove(index).1)
        });
        if let Some(ledger) = ledger {
            add_unstubbed_semantic_events(ledger.unresolved(completed));
        }
        self.id = 0;
    }
}
impl Drop for AccountingScope {
    fn drop(&mut self) {
        self.close(false);
    }
}
impl Ledger {
    fn unresolved(&self, completed: bool) -> usize {
        let matched = |event: &Encounter| {
            completed
                && self.inventory_complete
                && self.root_observed
                && !self.collecting
                && !self.invalid
                && self.active.is_none()
                && event.identity_established
                && !self.opaque_uses.contains(&event.callee)
                && event.site.as_ref().is_some_and(|site| {
                    Some(site.caller) == self.root
                        && self.preserved.get(&site.block) == Some(&event.callee)
                        && self.confirmed.as_ref().is_some_and(|s| s.contains(&site.block))
                })
        };
        let mut unresolved: HashSet<Instance> = self
            .encounters
            .iter()
            .filter(|event| !matched(event))
            .map(|event| event.callee)
            .collect();
        let events: HashSet<_> = self
            .encounters
            .iter()
            .filter_map(|event| {
                event.site.as_ref().map(|site| (site.caller, site.block, event.callee))
            })
            .collect();
        for site @ (_, _, callee) in &self.inventory {
            if !events.contains(site) {
                unresolved.insert(*callee);
            }
        }
        self.encounters.iter().filter(|event| unresolved.contains(&event.callee)).count()
    }
}

/// A successful return from the complete reachability walk is explicit evidence.
/// Every subsequent recollection must also complete and observe the root body.
pub(super) fn begin_inventory() {
    with_current(|ledger| {
        ledger.invalid |= ledger.collecting;
        ledger.collecting = true;
        ledger.inventory_complete = false;
        ledger.root_observed = false;
        ledger.observed_root = None;
    });
}
pub(super) fn finish_inventory() {
    with_current(|ledger| {
        ledger.inventory_complete = ledger.collecting && ledger.root_observed;
        ledger.collecting = false;
    });
}

/// Independently inventory every typed use, including zero-sized FnDef values.
/// Indirect calls and unresolved definitions close this lane. The pointer index
/// identifies actual operands in this immutable borrowed body; it never guesses
/// a callsite from names, spans or structural similarity.
pub(super) fn record_reachable_body(caller: Instance, body: &Body) {
    struct Uses<'a> {
        body: &'a Body,
        caller: Instance,
        operands: HashMap<usize, usize>,
        direct: HashSet<(Instance, usize, Instance)>,
        opaque: HashSet<Instance>,
        indirect: bool,
    }
    impl MirVisitor for Uses<'_> {
        fn visit_operand(&mut self, operand: &Operand, location: Location) {
            if let Ok(ty) = operand.ty(self.body.locals()) {
                if let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() {
                    match Instance::resolve(def, &args) {
                        Ok(callee) => {
                            if let Some(bb) =
                                self.operands.get(&(operand as *const Operand as usize))
                            {
                                self.direct.insert((self.caller, *bb, callee));
                            } else {
                                self.opaque.insert(callee);
                            }
                        }
                        Err(_) => self.indirect = true,
                    }
                    return;
                }
            }
            self.super_operand(operand, location);
        }
        fn visit_ty(&mut self, ty: &Ty, _location: Location) {
            if let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() {
                match Instance::resolve(def, &args) {
                    Ok(callee) => {
                        self.opaque.insert(callee);
                    }
                    Err(_) => self.indirect = true,
                }
            }
            self.super_ty(ty);
        }
        fn visit_terminator(&mut self, term: &rustc_public::mir::Terminator, location: Location) {
            if let TerminatorKind::Call { func, .. } = &term.kind {
                if !matches!(
                    func.ty(self.body.locals()).map(|t| t.kind()),
                    Ok(TyKind::RigidTy(RigidTy::FnDef(..)))
                ) {
                    self.indirect = true;
                }
            }
            self.super_terminator(term, location);
        }
    }
    with_current(|ledger| {
        if ledger.root.is_none() {
            return;
        }
        ledger.invalid |= !ledger.collecting;
        let operands = body
            .blocks
            .iter()
            .enumerate()
            .filter_map(|(bb, block)| {
                if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                    Some((func as *const Operand as usize, bb))
                } else {
                    None
                }
            })
            .collect();
        let mut uses = Uses {
            body,
            caller,
            operands,
            direct: HashSet::new(),
            opaque: HashSet::new(),
            indirect: false,
        };
        uses.visit_body(body);
        ledger.inventory.extend(uses.direct);
        ledger.opaque_uses.extend(uses.opaque);
        ledger.invalid |= uses.indirect;
        if ledger.root == Some(caller) {
            ledger.root_observed = true;
            // At most one full copy per root visit/revision, never per call.
            ledger.observed_root = Some(ObservedRoot {
                address: body as *const Body as usize,
                snapshot: Rc::new(BodyIdentity::of(body)),
            });
        }
    });
}

pub(super) fn record_pending(
    path: &str,
    callee: Instance,
    site: Option<AbstractionCallsite<'_>>,
    identity_established: bool,
) {
    record_unstubbed_coverage(path);
    if with_current(|ledger| {
        let site = site.and_then(|site| {
            let observed = ledger.observed_root.as_ref()?;
            (ledger.collecting
                && Some(site.caller) == ledger.root
                && observed.address == site.body as *const Body as usize)
                .then(|| Site {
                    caller: site.caller,
                    block: site.block,
                    body: Rc::clone(&observed.snapshot),
                })
        });
        ledger.encounters.push(Encounter { callee, site, identity_established });
    })
    .is_none()
    {
        add_unstubbed_semantic_events(1);
    }
}

pub(super) struct InlineCustody {
    owner: u64,
    root: Instance,
    input: Rc<BodyIdentity>,
}
pub(super) fn before_root_inline(root: Instance, body: &Body) -> Option<InlineCustody> {
    SCOPES.with(|scopes| {
        let scopes = scopes.borrow();
        let (owner, ledger) = scopes.last()?;
        if ledger.root != Some(root)
            || !ledger.inventory_complete
            || !ledger.root_observed
            || ledger.collecting
            || ledger.invalid
        {
            return None;
        }
        let observed = ledger.observed_root.as_ref()?;
        if !observed.snapshot.matches(body) {
            return None;
        }
        let mut checked = HashSet::new();
        let root_sites: Vec<_> = ledger
            .encounters
            .iter()
            .filter_map(|e| e.site.as_ref())
            .filter(|s| s.caller == root)
            .collect();
        if root_sites.is_empty()
            || root_sites.iter().any(|site| {
                checked.insert(Rc::as_ptr(&site.body) as usize) && !site.body.matches(body)
            })
        {
            return None;
        }
        Some(InlineCustody { owner: *owner, root, input: Rc::clone(&observed.snapshot) })
    })
}

/// Only the actual inliner return can establish custody. Original locals keep
/// their types/indices; each original call block must remain entirely identical.
pub(super) fn after_root_inline(custody: Option<InlineCustody>, body: &Body) {
    let Some(custody) = custody else {
        return;
    };
    with_owned(custody.owner, |ledger| {
        if ledger.root != Some(custody.root) {
            return;
        }
        let types: Vec<_> = body.locals().iter().map(|d| d.ty).collect();
        if !types.starts_with(&custody.input.types) {
            return;
        }
        let mut compared_snapshots = HashMap::new();
        for event in &ledger.encounters {
            let Some(site) = &event.site else {
                continue;
            };
            let same_input =
                *compared_snapshots.entry(Rc::as_ptr(&site.body) as usize).or_insert_with(|| {
                    Rc::ptr_eq(&site.body, &custody.input) || *site.body == *custody.input
                });
            if site.caller == custody.root
                && same_input
                && body.blocks.get(site.block) == custody.input.blocks.get(site.block)
            {
                if let Some(prior) = ledger.preserved.insert(site.block, event.callee) {
                    ledger.invalid |= prior != event.callee;
                }
            }
        }
        ledger.encoded_body = Some(BodyIdentity::of(body));
    });
}

/// Each attempt owns its ledger; nesting cannot write or invalidate a sibling.
pub(super) struct EncodingAttempt<'a> {
    owner: Option<u64>,
    _body: &'a Body,
    _thread: PhantomData<Rc<()>>,
}
impl<'a> EncodingAttempt<'a> {
    pub(super) fn begin(root: Option<Instance>, body: &'a Body) -> Self {
        let owner = SCOPES.with(|scopes| {
            let mut scopes = scopes.borrow_mut();
            let (owner, ledger) = scopes.last_mut()?;
            if root.is_none() || ledger.root != root {
                return None;
            }
            if ledger.active.is_some()
                || !ledger.encoded_body.as_ref().is_some_and(|b| b.matches(body))
            {
                ledger.invalid = true;
                return None;
            }
            ledger.active = Some(ActiveEncoding {
                body_address: body as *const Body as usize,
                observed: HashSet::new(),
            });
            Some(*owner)
        });
        Self { owner, _body: body, _thread: PhantomData }
    }
    pub(super) fn finish(mut self) {
        if let Some(owner) = self.owner.take() {
            with_owned(owner, |ledger| {
                let Some(active) = ledger.active.take() else {
                    ledger.invalid = true;
                    return;
                };
                match &mut ledger.confirmed {
                    Some(confirmed) => confirmed.retain(|site| active.observed.contains(site)),
                    None => ledger.confirmed = Some(active.observed),
                }
            });
        }
    }
}
impl Drop for EncodingAttempt<'_> {
    fn drop(&mut self) {
        if let Some(owner) = self.owner.take() {
            with_owned(owner, |ledger| {
                ledger.invalid = true;
                ledger.active = None;
            });
        }
    }
}

/// Evidence can only be constructed by the guarded exact-address handler after
/// emitting its rule. Full-body equality was checked at the attempt boundary;
/// this receipt must borrow that same immutable body and preserve the callee.
pub(super) fn record_exact_address(
    evidence: super::chc::call::codegen_call_static_atomic_address::ExactAtomicAddressModel<'_>,
) {
    record_exact_call(evidence.into_parts());
}

/// The BMC singleton producer issues this only after its canonical, live-storage
/// model binds the result of the actual call. Helper calls keep their encounters:
/// the existing root/inliner custody rule cannot authenticate their relocation.
pub(super) fn record_exact_shared_scalar_slice(
    evidence: super::statement::ExactSharedScalarSliceModel<'_>,
) {
    record_exact_call(evidence.into_parts());
}

fn record_exact_call((root, body, block, callee): (Option<Instance>, &Body, usize, Instance)) {
    with_current(|ledger| {
        if ledger.root != root || root.is_none() || ledger.preserved.get(&block) != Some(&callee) {
            return;
        }
        let Some(active) = &mut ledger.active else {
            return;
        };
        if active.body_address == body as *const Body as usize {
            active.observed.insert(block);
        }
    });
}

#[cfg(test)]
pub(super) fn unresolved_for_test() -> usize {
    with_current(|ledger| ledger.unresolved(true)).expect("active accounting scope")
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
#[path = "unstubbed_accounting_tests.rs"]
mod tests;
