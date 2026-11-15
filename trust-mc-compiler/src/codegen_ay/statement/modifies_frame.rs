// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! FC-06 (BMC): modifies frame-condition enforcement for contract CHECK mode.
//!
//! The contracts transform instruments the modifies-wrapper closure with
//! `modifies_frame_enter(_wrapper_arg)` / `modifies_frame_exit()` marker
//! calls (`kani_middle::transform::contracts_frame`). After MIR inlining the
//! markers delimit the dynamic extent of the checked function inside the
//! harness body. The CHC backend enforces the full declared footprint
//! (`chc::modifies_frame`). BMC classifies every store it encodes inside the
//! extent by the storage NAME the register model gives it.
//!
//! Every store inside a frame gets exactly one of four outcomes — none of
//! them is "no check":
//! - ACCUSED (failing assigns check): an empty declared footprint (`()`
//!   wrapper tuple, no `#[kani::modifies]` clause) and one of the two shapes
//!   the register model can attribute with certainty — a raw-pointer deref
//!   store (including `static mut` writes), or a whole `*r = v` store through
//!   `&mut` whose tracked pointee existed before the frame.
//! - CERTIFIED (passing assigns check): a non-empty footprint whose resolved
//!   pointee names cover the store's storage name (equal, or a field /
//!   variant / element path under it) — the obligation Kani reports as
//!   'Check that *x is assignable: SUCCESS'.
//! - FRAME-LOCAL (no obligation): the storage is a plain function local that
//!   did not exist when the frame was entered.
//! - FAIL-CLOSED (`unsupported_with_fallback`, which demotes the proof):
//!   everything else. That includes a store to pre-existing storage that a
//!   non-empty footprint does not cover — a same-object field outside the
//!   frame (`p.b` against `modifies(&p.a)`) and a different object (`*q`)
//!   alike — because base-name aliasing is precise enough to CERTIFY but not
//!   to ACCUSE; a store whose pointer has no tracked pointee (e.g. a raw
//!   pointer to a static); a store through a synthetic alias name minted
//!   inside the extent (`X_deref`) that does not resolve to a frame-local; and
//!   the opaque stores (`copy_nonoverlapping`, untracked `mem::swap`).
//!
//! Until 2026-09-11 a store outside a non-empty footprint was fail-OPEN (no
//! check at all): `modifies-frame-offset-drop_repro.rs::check_evil` (writes
//! `p.b` under `modifies(&p.a)`) and `..._control.rs::check_caught` (writes
//! `*q`) verified SUCCESSFUL with `PROOF_QUALIFIERS:clean` — false proofs.
//! Stores reached only through a store handler without a hook
//! (`(*r).f = v`, box/array/datatype-field deref writes, call destinations,
//! `SetDiscriminant`) were unchecked in EVERY frame; the classification now
//! runs before store dispatch, so the handler choice no longer matters.
//!
//! Known limits, documented on purpose:
//! - Raw-pointer stores into allocations created INSIDE the extent in a
//!   no-modifies checked function are accused (pre-existing behaviour; DFCC
//!   freshness belongs with address-level footprint enforcement).
//! - Stores performed inside stub / model handlers for non-inlined calls are
//!   attributed only for `mem::swap` (by name) and the container model
//!   families (Vec, HashMap/BTreeMap, HashSet/BTreeSet, String, BigInt),
//!   whose stores through a `&mut` argument are frame-local or fail closed
//!   (`bmc_modifies_check_stub_mut_args`). Other stub families are not
//!   attributed here.
//!   Every other call is attributed through its pointer arguments in
//!   `statement::modifies_frame_calls`.

use rustc_public::mir::{Mutability, Operand, Place, ProjectionElem};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::BTreeSet;
use std::sync::Arc;
use tracing::debug;

use super::{BmcModifiesFrame, Expr, IntoOption, MergedAlternative, StatementCodegen};

/// Bound on `X_deref -> ref_pointees[X]` alias walks; a malformed table
/// terminates rather than spins.
const MAX_ALIAS_CHAIN: usize = 8;

/// Name segments that address a PART of the storage named by the prefix.
const STRUCTURAL_MARKERS: [&str; 3] = ["_field_", "_variant_", "_idx_by_"];

/// Unsupported-construct key for a store the frame cannot certify.
const UNCERTIFIED_STORE: &str = "bmc_modifies_frame_uncertified_store";

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum PointerKind {
    Ref,
    Raw,
    /// `Box` or anything else: no tracked pointee to name.
    Other,
}

/// What the register model can say about the storage a deref store writes.
struct DerefStoreTarget {
    kind: PointerKind,
    /// `Deref` is the first projection (`*p` / `(*p).f`).
    deref_first: bool,
    /// `Deref` is the ONLY projection (`*p = v`).
    whole: bool,
    /// Tracked pointee of the pointer local (`ref_pointees`), if any.
    pointee: Option<Arc<str>>,
    /// Field indices projected after the deref, up to the first non-field
    /// projection. Stopping early names an ENCLOSING storage, which can only
    /// make coverage harder to show and pre-existence easier — never unsound.
    field_path: Vec<usize>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Freshness {
    /// A plain function local created inside the extent.
    Fresh,
    /// Existed (itself or an enclosing storage) when the frame was entered.
    Preexisting,
    /// Cannot be shown fresh (unresolved or synthetic alias name).
    Unknown,
}

/// `name` followed by every enclosing storage name obtained by cutting at a
/// structural marker, innermost first: `a_field_1_field_2`, `a_field_1`, `a`.
fn structural_prefixes(name: &str) -> Vec<&str> {
    let mut out = vec![name];
    let mut current = name;
    while let Some(pos) = STRUCTURAL_MARKERS.iter().filter_map(|m| current.rfind(m)).max() {
        if pos == 0 {
            break;
        }
        current = &current[..pos];
        out.push(current);
    }
    out
}

fn name_preexisting(preexisting: &BTreeSet<Arc<str>>, name: &str) -> bool {
    structural_prefixes(name).into_iter().any(|prefix| preexisting.contains(prefix))
}

/// `name` is an allowed storage or a structural part of one.
fn footprint_covers(allowed: &BTreeSet<Arc<str>>, name: &str) -> bool {
    allowed.iter().any(|a| {
        let a = a.as_ref();
        name == a
            || (name.len() > a.len()
                && name.starts_with(a)
                && STRUCTURAL_MARKERS.iter().any(|m| name[a.len()..].starts_with(m)))
    })
}

/// A plain function-local storage name — not a synthetic alias.
fn is_plain_local_name(name: &str) -> bool {
    name.contains("::local_") && !name.contains("_deref") && !name.contains("arg_pointee")
}

fn classify_freshness(preexisting: &BTreeSet<Arc<str>>, names: &[Arc<str>]) -> Freshness {
    if names.iter().any(|n| name_preexisting(preexisting, n)) {
        return Freshness::Preexisting;
    }
    match names.last() {
        Some(last) if is_plain_local_name(last) => Freshness::Fresh,
        _ => Freshness::Unknown,
    }
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle the `modifies_frame_enter(_wrapper_arg)` marker: push a frame.
    ///
    /// The declared footprint is the tuple type of `_wrapper_arg`: an empty
    /// tuple means no `#[kani::modifies]` clause. A non-empty tuple is
    /// resolved to pointee names; an unresolved footprint certifies nothing,
    /// so every pre-existing store inside it fails closed.
    pub(super) fn bmc_modifies_frame_enter(&mut self, args: &[Operand]) {
        let field_count = args
            .first()
            .and_then(|arg| arg.ty(self.body.locals()).into_option())
            .and_then(|ty| match ty.kind() {
                TyKind::RigidTy(RigidTy::Tuple(fields)) => Some(fields.len()),
                _ => None,
            });
        let enforce_empty = field_count == Some(0);
        let allowed = match field_count {
            Some(n) if n > 0 => self.resolve_footprint_pointees(args, n),
            _ => None,
        };
        let preexisting = self.current_env.keys().cloned().collect();
        debug!(enforce_empty, ?allowed, "FC-06(bmc): modifies frame entered");
        self.modifies_frames.push(BmcModifiesFrame { enforce_empty, preexisting, allowed });
    }

    /// Resolve the wrapper tuple's pointer fields to pointee storage names.
    ///
    /// Returns `None` unless EVERY field has a `ref_pointees` entry: a
    /// partial footprint could certify stores the unresolved remainder was
    /// meant to constrain.
    fn resolve_footprint_pointees(
        &mut self,
        args: &[Operand],
        field_count: usize,
    ) -> Option<BTreeSet<Arc<str>>> {
        let (Operand::Copy(place) | Operand::Move(place)) = args.first()? else {
            return None;
        };
        let base = self.ssa_base_name(place);
        let mut set = BTreeSet::new();
        for i in 0..field_count {
            let key = crate::codegen_ay::names::indexed_field_name(&base, i);
            let pointee = Arc::clone(self.ref_pointees.get(key.as_str())?);
            set.extend(self.bmc_modifies_alias_chain(&pointee));
        }
        Some(set)
    }

    /// `name`, then the storage each `X_deref` alias denotes
    /// (`ref_pointees[X]`), following the chain.
    ///
    /// Only the `_deref` stem is followed. Looking a STORAGE name up in
    /// `ref_pointees` directly would jump from a pointer slot to what that
    /// slot points at — a different storage — and could certify a store the
    /// footprint does not cover.
    pub(super) fn bmc_modifies_alias_chain(&self, name: &str) -> Vec<Arc<str>> {
        let mut current: Arc<str> = Arc::from(name);
        let mut chain = vec![Arc::clone(&current)];
        for _ in 0..MAX_ALIAS_CHAIN {
            let next = match current.as_ref().strip_suffix("_deref") {
                Some(stem) => self.ref_pointees.get(stem).cloned(),
                None => None,
            };
            let Some(next) = next else {
                break;
            };
            if chain.contains(&next) {
                break;
            }
            chain.push(Arc::clone(&next));
            current = next;
        }
        chain
    }

    fn bmc_modifies_deref_store_target(&self, lhs: &Place) -> DerefStoreTarget {
        let ptr_place = Place { local: lhs.local, projection: vec![] };
        let kind = match ptr_place.ty(self.body.locals()).into_option().map(|ty| ty.kind()) {
            Some(TyKind::RigidTy(RigidTy::Ref(..))) => PointerKind::Ref,
            Some(TyKind::RigidTy(RigidTy::RawPtr(..))) => PointerKind::Raw,
            _ => PointerKind::Other,
        };
        let deref_first = matches!(lhs.projection.first(), Some(ProjectionElem::Deref));
        let whole = deref_first && lhs.projection.len() == 1;
        let pointee = if deref_first && kind != PointerKind::Other {
            let ref_base =
                crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), lhs.local);
            self.ref_pointees.get(ref_base.as_str()).cloned()
        } else {
            None
        };
        let mut field_path = Vec::new();
        if deref_first {
            for proj in lhs.projection.iter().skip(1) {
                match proj {
                    ProjectionElem::Field(idx, _) => field_path.push(*idx),
                    _ => break,
                }
            }
        }
        DerefStoreTarget { kind, deref_first, whole, pointee, field_path }
    }

    /// Storage names the store may be written under: the tracked pointee and
    /// every alias it resolves to, each extended by the store's field path.
    fn bmc_modifies_store_names(&self, target: &DerefStoreTarget) -> Vec<Arc<str>> {
        let Some(pointee) = target.pointee.as_deref() else {
            return Vec::new();
        };
        self.bmc_modifies_alias_chain(pointee)
            .into_iter()
            .map(|storage| {
                if target.field_path.is_empty() {
                    return storage;
                }
                let mut name = storage.to_string();
                for idx in &target.field_path {
                    name = crate::codegen_ay::names::indexed_field_name(&name, *idx);
                }
                Arc::from(name)
            })
            .collect()
    }

    /// Classify a store to `lhs` against the innermost modifies frame.
    ///
    /// Called BEFORE store dispatch for every assignment, call destination
    /// and discriminant write, so the outcome does not depend on which store
    /// handler later encodes the write. No-op outside frames and for stores
    /// that do not go through a deref (the checked function's own locals).
    pub(super) fn bmc_modifies_check_deref_store(&mut self, lhs: &Place) {
        if self.modifies_frames.is_empty()
            || !lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
        {
            return;
        }
        let target = self.bmc_modifies_deref_store_target(lhs);
        // A pointer merged at a join names a different pointee on each incoming
        // path, and `ref_pointees` keeps only one of them. Certifying by that one
        // name passed `*p = 1` through `if c { b } else { a }` against
        // `modifies(a)` (negative/modifies_frame_residual.rs::
        // merge_last_in_footprint_must_fail). Classify every path instead.
        if target.deref_first && target.kind != PointerKind::Other {
            let ref_base =
                crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), lhs.local);
            if let Some(alternatives) =
                self.ref_pointees.merged_alternatives(ref_base.as_str()).map(<[_]>::to_vec)
            {
                self.bmc_modifies_check_merged_store(lhs, &target, &alternatives);
                return;
            }
        }
        let names = self.bmc_modifies_store_names(&target);
        let Some(frame) = self.modifies_frames.last() else {
            return;
        };
        let enforce_empty = frame.enforce_empty;
        let freshness = classify_freshness(&frame.preexisting, &names);
        let covered = !enforce_empty
            && frame
                .allowed
                .as_ref()
                .is_some_and(|allowed| names.iter().any(|n| footprint_covers(allowed, n)));
        let pointee_preexisting =
            target.pointee.as_ref().is_some_and(|p| frame.preexisting.contains(p.as_ref()));
        let accuse = enforce_empty
            && ((target.kind == PointerKind::Raw && target.deref_first)
                || (target.kind == PointerKind::Ref && target.whole && pointee_preexisting));

        if accuse {
            debug!(ptr_local = lhs.local, "FC-06(bmc): store outside empty modifies footprint");
            self.record_violation_guarded_with_message(
                Expr::bool_const(true),
                "assigns_check",
                Some(format!("Check that *var_{} is assignable", lhs.local)),
            );
            return;
        }
        if covered {
            let shown = names.first().map_or("", |n| n.as_ref()).to_owned();
            debug!(storage = %shown, "FC-06(bmc): store certified inside modifies footprint");
            self.record_violation_guarded_with_message(
                Expr::bool_const(false),
                "assigns_check",
                Some(format!("Check that *{shown} is assignable")),
            );
            return;
        }
        if freshness == Freshness::Fresh {
            return; // Frame-local storage: always assignable, no obligation.
        }
        let storage = names.first().cloned();
        self.bmc_modifies_fail_closed(&format!("{lhs:?}"), storage.as_deref());
    }

    /// Classify a store through a pointer merged at a join, one incoming path at
    /// a time. A path whose pointee is covered (or frame-local) is certified; a
    /// path whose pointee is outside the footprint, or unknown, is accused under
    /// that path's edge predicate. The accusation rests on storage names, which
    /// can certify but cannot prove two names distinct, so the store also fails
    /// closed: the counterexample is never certified Genuine and a proof stays
    /// demoted.
    fn bmc_modifies_check_merged_store(
        &mut self,
        lhs: &Place,
        target: &DerefStoreTarget,
        alternatives: &[MergedAlternative],
    ) {
        let mut violation: Option<Expr> = None;
        let mut first_uncovered: Option<Arc<str>> = None;
        for alternative in alternatives {
            let uncovered = match alternative.pointee.as_ref() {
                None => true,
                Some(pointee) => {
                    let per_path = DerefStoreTarget {
                        kind: target.kind,
                        deref_first: target.deref_first,
                        whole: target.whole,
                        pointee: Some(Arc::clone(pointee)),
                        field_path: target.field_path.clone(),
                    };
                    let names = self.bmc_modifies_store_names(&per_path);
                    let Some(frame) = self.modifies_frames.last() else {
                        return;
                    };
                    let covered = !frame.enforce_empty
                        && frame.allowed.as_ref().is_some_and(|allowed| {
                            names.iter().any(|n| footprint_covers(allowed, n))
                        });
                    let fresh = classify_freshness(&frame.preexisting, &names) == Freshness::Fresh;
                    if !(covered || fresh) && first_uncovered.is_none() {
                        first_uncovered = names.first().cloned();
                    }
                    !(covered || fresh)
                }
            };
            if !uncovered {
                continue;
            }
            let on_path =
                alternative.edge_predicate.clone().unwrap_or_else(|| Expr::bool_const(true));
            violation = Some(match violation {
                None => on_path,
                Some(previous) => previous.or(on_path),
            });
        }
        let message = Some(format!("Check that *var_{} is assignable", lhs.local));
        match violation {
            Some(violation) => {
                debug!(ptr_local = lhs.local, "FC-06(bmc): merged-pointer store accused per path");
                self.record_violation_guarded_with_message(violation, "assigns_check", message);
                self.bmc_modifies_fail_closed(&format!("{lhs:?}"), first_uncovered.as_deref());
            }
            None => {
                debug!(
                    ptr_local = lhs.local,
                    "FC-06(bmc): merged-pointer store certified on every path"
                );
                self.record_violation_guarded_with_message(
                    Expr::bool_const(false),
                    "assigns_check",
                    message,
                );
            }
        }
    }

    /// Classify a swap's deref-store by its tracked pointee NAME. An
    /// untracked pointee cannot be attributed and fails closed.
    pub(super) fn bmc_modifies_certify_swap_store(&mut self, pointee_base: Option<&str>) {
        if self.modifies_frames.is_empty() {
            return;
        }
        let Some(base) = pointee_base else {
            self.bmc_modifies_fail_closed("mem::swap", None);
            return;
        };
        let names = self.bmc_modifies_alias_chain(base);
        let Some(frame) = self.modifies_frames.last() else {
            return;
        };
        let freshness = classify_freshness(&frame.preexisting, &names);
        let covered = !frame.enforce_empty
            && frame
                .allowed
                .as_ref()
                .is_some_and(|allowed| names.iter().any(|n| footprint_covers(allowed, n)));
        if covered {
            debug!(pointee = base, "FC-06(bmc): swap store certified inside modifies footprint");
            self.record_violation_guarded_with_message(
                Expr::bool_const(false),
                "assigns_check",
                Some(format!("Check that *{base} is assignable")),
            );
            return;
        }
        if freshness == Freshness::Fresh {
            return;
        }
        self.bmc_modifies_fail_closed("mem::swap", Some(base));
    }

    /// Classify the stores a container model stub makes through its `&mut`
    /// arguments (`Vec::push(&mut v, x)`, `HashMap::insert`, `String::push_str`).
    ///
    /// The stub encodes such a write as an env-level update of the
    /// container's storage, which the deref-store hook never sees; before
    /// this hook `Vec::push` on a pre-existing vector outside a non-empty
    /// footprint verified SUCCESSFUL with `PROOF_QUALIFIERS:clean`
    /// (`negative/modifies_frame_residual.rs::vec_push_outside_must_fail`).
    ///
    /// A store to a plain local created inside the extent is frame-local (no
    /// obligation). Anything else FAILS CLOSED, including an argument with no
    /// tracked pointee. It is never CERTIFIED: the model folds the heap
    /// buffer into the container value, while a footprint naming the
    /// container (`modifies(v)`) does not cover a write into a buffer that
    /// existed before the call, so a name match cannot discharge the
    /// obligation. A `&mut` argument the handler only reads also fails
    /// closed; that costs precision, never soundness.
    pub(in crate::codegen_ay::statement) fn bmc_modifies_check_stub_mut_args(
        &mut self,
        args: &[Operand],
        callee_path: &str,
    ) {
        if self.modifies_frames.is_empty() {
            return;
        }
        for arg in args {
            let (Operand::Copy(place) | Operand::Move(place)) = arg else {
                continue;
            };
            let mutable_ref = matches!(
                arg.ty(self.body.locals()).into_option().map(|ty| ty.kind()),
                Some(TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut)))
            );
            if !mutable_ref {
                continue;
            }
            let ref_base = self.ssa_base_name(place);
            let names = match self.ref_pointees.get(ref_base.as_str()).cloned() {
                Some(pointee) => self.bmc_modifies_alias_chain(&pointee),
                None => Vec::new(),
            };
            let Some(frame) = self.modifies_frames.last() else {
                return;
            };
            if classify_freshness(&frame.preexisting, &names) == Freshness::Fresh {
                continue;
            }
            let storage = names.first().cloned();
            self.bmc_modifies_fail_closed(callee_path, storage.as_deref());
        }
    }

    /// A store the register model encodes without a nameable target
    /// (`copy_nonoverlapping`) fails closed inside any frame.
    pub(super) fn bmc_modifies_opaque_store(&mut self, what: &'static str) {
        if self.modifies_frames.is_empty() {
            return;
        }
        self.bmc_modifies_fail_closed(what, None);
    }

    /// Demote: a store inside a modifies frame that BMC can neither accuse
    /// nor certify nor show frame-local.
    /// Whether the innermost frame's footprint covers `names`, and whether they
    /// name storage created inside the frame.
    pub(super) fn bmc_modifies_coverage(&self, names: &[Arc<str>]) -> (bool, bool) {
        let Some(frame) = self.modifies_frames.last() else {
            return (false, false);
        };
        let covered = !frame.enforce_empty
            && frame
                .allowed
                .as_ref()
                .is_some_and(|allowed| names.iter().any(|n| footprint_covers(allowed, n)));
        let fresh = classify_freshness(&frame.preexisting, names) == Freshness::Fresh;
        (covered, fresh)
    }

    pub(super) fn bmc_modifies_fail_closed(&mut self, store: &str, storage: Option<&str>) {
        let site = match self.current_source_location() {
            Some(loc) => format!("{loc}: {store}"),
            None => store.to_owned(),
        };
        let detail = match storage {
            Some(storage) => {
                format!("{site} writes {storage}, not provably inside the modifies footprint")
            }
            None => format!("{site}: store target not attributable to the modifies footprint"),
        };
        debug!(%detail, "FC-06(bmc): uncertified store inside modifies frame (fail-closed)");
        self.ctx.unsupported_with_fallback(UNCERTIFIED_STORE, detail);
    }

    /// Handle the `modifies_frame_exit()` marker: pop the innermost frame.
    pub(super) fn bmc_modifies_frame_exit(&mut self) {
        debug!("FC-06(bmc): modifies frame exited");
        self.modifies_frames.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn set(names: &[&str]) -> BTreeSet<Arc<str>> {
        names.iter().map(|n| Arc::from(*n)).collect()
    }

    #[test]
    fn structural_prefixes_walk_out_to_the_root() {
        assert_eq!(
            structural_prefixes("h::local_2_field_1_variant_0_field_3"),
            vec![
                "h::local_2_field_1_variant_0_field_3",
                "h::local_2_field_1_variant_0",
                "h::local_2_field_1",
                "h::local_2",
            ]
        );
        assert_eq!(structural_prefixes("h::local_4"), vec!["h::local_4"]);
    }

    #[test]
    fn same_object_sibling_field_is_not_covered() {
        // modifies(&p.a) must not cover p.b (the offset-drop dual).
        let allowed = set(&["h::local_2_field_0"]);
        assert!(footprint_covers(&allowed, "h::local_2_field_0"));
        assert!(footprint_covers(&allowed, "h::local_2_field_0_field_1"));
        assert!(!footprint_covers(&allowed, "h::local_2_field_1"));
        assert!(!footprint_covers(&allowed, "h::local_2"));
        assert!(!footprint_covers(&set(&["h::local_2_field_1"]), "h::local_2_field_10"));
    }

    #[test]
    fn a_field_of_a_preexisting_object_is_preexisting() {
        let pre = set(&["h::local_2"]);
        let names = [Arc::<str>::from("h::local_2_field_1")];
        assert_eq!(classify_freshness(&pre, &names), Freshness::Preexisting);
    }

    #[test]
    fn synthetic_alias_is_never_fresh() {
        let pre = set(&[]);
        assert_eq!(
            classify_freshness(&pre, &[Arc::from("h::local_209_deref")]),
            Freshness::Unknown
        );
        assert_eq!(classify_freshness(&pre, &[Arc::from("f::arg_pointee_1")]), Freshness::Unknown);
        assert_eq!(classify_freshness(&pre, &[]), Freshness::Unknown);
        assert_eq!(classify_freshness(&pre, &[Arc::from("h::local_150")]), Freshness::Fresh);
    }
}
