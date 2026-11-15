// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Strong-count ghost state for `Rc`/`Arc` allocations (`__rc_strong_bb<N>`).
//!
//! `Rc::clone`/`Arc::clone` is modeled as pointer identity
//! (`codegen_call_dispatch_dyn_rc.rs`) and a handle's drop as the drop of the
//! allocation (`transition_drop/arc_drop.rs`), with no count. So every handle's
//! drop freed the shared allocation: a harness that cloned an `Rc<Cell<u8>>`
//! and let both handles go out of scope got a Genuine double free, and one that
//! dropped the clone and then read through the other handle a Genuine
//! use-after-free, both of which Kani verifies. A pointee the no-drop test
//! accepts took the other branch, which skips the dealloc of EVERY handle of a
//! cloned allocation: nothing is ever freed there.
//!
//! When the pre-scan below can account for every handle of a body, each
//! `Rc::new`/`Arc::new` call site whose allocation is cloned gets a bv64 state
//! variable holding that allocation's strong count. The call sets it to 1, a
//! clone adds 1, and a drop subtracts 1. The drop frees the allocation (and
//! runs the pointee's drop) only on the path where the count reaches 0; on the
//! other path it changes nothing else. A body the pre-scan cannot account for
//! keeps the old encoding.
//!
//! The pre-scan accepts a body when:
//! * every local whose type mentions `Rc`/`Arc`/`Weak` is a whole handle
//!   (`Rc<T>`/`Arc<T>` with a `T` that mentions none of them) or a shared
//!   reference to one, and neither an argument local nor the return local
//!   mentions them. "Mentions" looks through the FIELDS of every ADT, with its
//!   generic arguments substituted, not only through its generic arguments: a
//!   non-generic `struct SD { r: Rc<D> }` or `enum ED { A(Rc<D>), B }` mentions
//!   them, so a local of that type (a `Vec<SD>` too) refuses the body;
//! * a handle local is assigned once: by `new` (its site), by a clone of a
//!   reference to a handle, or by a move (or unsizing cast) of a handle;
//! * a reference-to-handle local is assigned once, as `&h` of a handle local
//!   or a copy of another such reference;
//! * no other statement reads a handle or a reference to one as a whole
//!   (`SD { r: move h }`, `h as usize`, `(r, 1)`): a handle leaves the
//!   locals the scan tracks only through the calls below;
//! * `new`, a clone, or a read-only method (`deref`, `as_ptr`,
//!   `strong_count`, `weak_count`, `ptr_eq`, `inner`) is core's own, named by
//!   its def path (`std::rc::Rc::<T>::new`, `<std::rc::Rc<T> as
//!   std::clone::Clone>::clone`), never by a name a user impl can share;
//! * any other call is handed nothing and returns nothing whose type mentions
//!   them, and its path names no other `Rc`/`Arc`/`Weak` function
//!   (`increment_strong_count` takes a raw pointer), so no callee can clone
//!   or drop a handle behind the host's back;
//! * any other terminator reads no handle and no reference to one as a whole;
//! * a drop of a place whose type mentions them drops a whole handle local;
//! * no cloned site's `new` is on a cycle of the CFG (it runs at most once, so
//!   its count is one allocation's count).
//!
//! Every handle local then names the call site whose allocation it holds, and
//! a clone or drop of it updates exactly that site's count. A handle that
//! reached anything else would take its clone or drop out of the count: the
//! allocation would then be freed too late or never
//! (tools/soundness-duals/rc_shared_handle_dual.rs, the `bug_vec_*` rows).

use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use std::collections::{BTreeSet, HashMap, HashSet};

use ay_bindings::{Expr, Sort};
use rustc_public::mir::mono::Instance;
use rustc_public::mir::visit::{
    Location, MirVisitor, PlaceContext, statement_location, terminator_location,
};
use rustc_public::mir::{
    BorrowKind, CastKind, Mutability, Operand, Place, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};
use tracing::debug;

use super::ChcCtx;

const RC_STRONG_WIDTH: u32 = 64;

/// The counted `Rc`/`Arc` allocation sites of the body being encoded.
#[derive(Default)]
pub(in crate::codegen_ay::chc) struct RcStrongCounters {
    /// A handle local -> the `new` call site (its block) whose allocation it
    /// holds. Only locals of counted sites.
    site_by_local: HashMap<usize, usize>,
    /// A counted `new` call site -> the state-var index of its count.
    state_idx_by_site: HashMap<usize, usize>,
}

/// A counted allocation's strong count at one transition.
pub(in crate::codegen_ay::chc) struct RcStrongCount {
    /// The count before the transition.
    pub(in crate::codegen_ay::chc) current: Expr,
    /// The count after it.
    pub(in crate::codegen_ay::chc) next: Expr,
    state_idx: usize,
}

fn rc_strong_names(site: usize) -> (String, String) {
    (format!("__rc_strong_bb{site}"), format!("__rc_strong_bb{site}__out"))
}

fn rc_strong_sort() -> Sort {
    Sort::bitvec(RC_STRONG_WIDTH)
}

/// A strong-count constant.
pub(in crate::codegen_ay::chc) fn rc_strong_const(value: u64) -> Expr {
    Expr::bitvec_const(value, RC_STRONG_WIDTH)
}

/// `Some(true)` for `Rc`/`Arc`, `Some(false)` for the other handle types of the
/// same families (`Weak`, `UniqueRc`, `UniqueArc`), `None` otherwise. The
/// allocation's own types (`RcInner`, `ArcInner`) are not handles: the inlined
/// `Deref` reads through them.
fn rc_family_adt(ty: Ty) -> Option<bool> {
    use rustc_public::CrateDef;
    let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else {
        return None;
    };
    let path = def.name();
    if !(path.contains("rc::") || path.contains("sync::")) {
        return None;
    }
    match def.trimmed_name().as_str() {
        "Rc" | "Arc" => Some(true),
        "Weak" | "UniqueRc" | "UniqueArc" => Some(false),
        _ => None,
    }
}

/// Past this depth a type answers "mentions" (the scan refuses the body).
const MENTIONS_DEPTH_CAP: usize = 32;

fn generic_args_mention_rc_family(
    args: &GenericArgs,
    depth: usize,
    visited: &mut HashSet<Ty>,
) -> bool {
    args.0.iter().any(|arg| match arg {
        GenericArgKind::Type(ty) => ty_mentions_rc_family_rec(*ty, depth + 1, visited),
        _ => false,
    })
}

/// Whether `ty` holds or points at an `Rc`/`Arc`/`Weak` anywhere: through the
/// fields of every variant of an ADT (with its generic arguments substituted)
/// as well as through its generic arguments, and through the generic
/// arguments of a closure or coroutine (its captures). An unresolved type
/// (a parameter, an alias, a bound variable) or one past the depth cap
/// answers yes. A trait object or a fn pointer answers no: a handle reaches
/// one only through a local or a call the scan already refuses.
fn ty_mentions_rc_family(ty: Ty) -> bool {
    ty_mentions_rc_family_rec(ty, 0, &mut HashSet::new())
}

/// Reachability of an `Rc`/`Arc`/`Weak` in the type graph from `ty`. A type
/// already visited answers no: its fields are (or were) explored where it was
/// first reached, and a cycle adds no type of its own.
fn ty_mentions_rc_family_rec(ty: Ty, depth: usize, visited: &mut HashSet<Ty>) -> bool {
    if depth > MENTIONS_DEPTH_CAP {
        return true;
    }
    if rc_family_adt(ty).is_some() {
        return true;
    }
    if !visited.insert(ty) {
        return false;
    }
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            generic_args_mention_rc_family(&args, depth, visited)
                || def.variants_iter().any(|variant| {
                    variant.fields().iter().any(|field| {
                        // A field whose type does not instantiate may hold a
                        // handle (fail closed).
                        mono_ty::field_ty(field, &args)
                            .is_none_or(|t| ty_mentions_rc_family_rec(t, depth + 1, visited))
                    })
                })
        }
        TyKind::RigidTy(RigidTy::Closure(_, args))
        | TyKind::RigidTy(RigidTy::Coroutine(_, args))
        | TyKind::RigidTy(RigidTy::CoroutineClosure(_, args)) => {
            generic_args_mention_rc_family(&args, depth, visited)
        }
        TyKind::RigidTy(RigidTy::Ref(_, inner, _))
        | TyKind::RigidTy(RigidTy::RawPtr(inner, _))
        | TyKind::RigidTy(RigidTy::Array(inner, _))
        | TyKind::RigidTy(RigidTy::Slice(inner)) => {
            ty_mentions_rc_family_rec(inner, depth + 1, visited)
        }
        TyKind::RigidTy(RigidTy::Tuple(tys)) => {
            tys.iter().any(|t| ty_mentions_rc_family_rec(*t, depth + 1, visited))
        }
        TyKind::Param(_) | TyKind::Alias(..) | TyKind::Bound(..) => true,
        _ => false,
    }
}

/// A whole `Rc<T>`/`Arc<T>` whose `T` mentions no handle.
fn is_counted_handle_ty(ty: Ty) -> bool {
    rc_family_adt(ty) == Some(true)
        && matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(_, args))
            if !generic_args_mention_rc_family(&args, 0, &mut HashSet::new()))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LocalKind {
    Handle,
    HandleRef,
    Plain,
}

#[derive(Clone, Copy)]
enum HandleSource {
    New(usize),
    Clone(usize),
    Move(usize),
}

/// The def-path prefixes of core's `Rc`/`Arc` inherent methods
/// (`std::rc::Rc::<T>::new`).
const RC_INHERENT_PREFIXES: [&str; 4] =
    ["std::rc::Rc::<", "alloc::rc::Rc::<", "std::sync::Arc::<", "alloc::sync::Arc::<"];
/// The def-path prefixes of a trait method of core's `Rc`/`Arc`
/// (`<std::rc::Rc<T> as std::clone::Clone>::clone`).
const RC_TRAIT_IMPL_PREFIXES: [&str; 4] =
    ["<std::rc::Rc<", "<alloc::rc::Rc<", "<std::sync::Arc<", "<alloc::sync::Arc<"];

/// The method name of a call to an inherent method of core's `Rc`/`Arc`.
fn core_rc_inherent_method(path: &str) -> Option<&str> {
    let rest = RC_INHERENT_PREFIXES.iter().find_map(|prefix| path.strip_prefix(prefix))?;
    rest.rsplit_once(">::").map(|(_, method)| method)
}

/// The (trait path, method name) of a call to a trait method implemented for
/// core's `Rc`/`Arc`.
fn core_rc_trait_method(path: &str) -> Option<(&str, &str)> {
    let rest = RC_TRAIT_IMPL_PREFIXES.iter().find_map(|prefix| path.strip_prefix(prefix))?;
    let (head, method) = rest.rsplit_once(">::")?;
    let (_, trait_path) = head.rsplit_once("> as ")?;
    Some((trait_path, method))
}

/// Core's `Rc::new`/`Arc::new`, by def path.
fn is_core_rc_new(path: &str) -> bool {
    core_rc_inherent_method(path) == Some("new")
}

/// Core's `<Rc<T> as Clone>::clone`/`<Arc<T> as Clone>::clone`, by def path.
fn is_core_rc_clone(path: &str) -> bool {
    matches!(
        core_rc_trait_method(path),
        Some(("std::clone::Clone" | "core::clone::Clone", "clone"))
    )
}

/// Core's read-only `Rc`/`Arc` methods, by def path: handed a `&Rc`, they
/// neither clone nor drop it.
fn is_read_only_rc_method(path: &str) -> bool {
    matches!(
        core_rc_inherent_method(path),
        Some("as_ptr" | "strong_count" | "weak_count" | "ptr_eq" | "inner")
    ) || matches!(
        core_rc_trait_method(path),
        Some(("std::ops::Deref" | "core::ops::Deref", "deref"))
    )
}

/// Whether `path` names a function of the `Rc`/`Arc`/`Weak` families (or is
/// generic over one of their handle types), or one the call dispatch would
/// route as `Rc::new`/`Rc::clone` by its name. A family name counts only as a
/// whole path segment: `NonNull::<std::rc::RcInner<T>>::as_ref`, which
/// `Rc::inner` leaves as a call, reads the allocation and touches no count.
fn path_mentions_rc_family(path: &str) -> bool {
    ["rc::Rc", "sync::Arc", "rc::Weak", "sync::Weak", "rc::UniqueRc", "sync::UniqueArc"]
        .iter()
        .any(|family| path_has_segment(path, family))
        || ChcCtx::is_rc_arc_new_path(path)
        || ChcCtx::is_rc_arc_clone_path(path)
}

/// Whether `segment` occurs in `path` not followed by an identifier character
/// (`rc::Rc<`, `rc::Rc::`, never `rc::RcInner`).
fn path_has_segment(path: &str, segment: &str) -> bool {
    path.match_indices(segment).any(|(at, _)| {
        path[at + segment.len()..]
            .chars()
            .next()
            .is_none_or(|next| !(next.is_alphanumeric() || next == '_'))
    })
}

/// The locals a statement's rvalue or a terminator reads or borrows WHOLE
/// (a place with no projection).
#[derive(Default)]
struct WholeLocalUses(Vec<usize>);

impl MirVisitor for WholeLocalUses {
    fn visit_place(&mut self, place: &Place, _ptx: PlaceContext, _location: Location) {
        if place.projection.is_empty() {
            self.0.push(place.local);
        }
    }
}

fn bare_local(place: &Place) -> Option<usize> {
    place.projection.is_empty().then_some(place.local)
}

fn operand_bare_local(operand: &Operand) -> Option<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => bare_local(place),
        _ => None,
    }
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Declare one strong-count state variable per counted allocation site
    /// (module doc). Declares nothing for a body the pre-scan refuses or that
    /// clones no handle, so ordinary harnesses keep their relation arity.
    pub(in crate::codegen_ay::chc) fn collect_rc_strong_count_state_vars(&mut self) {
        let Some((site_by_local, sites)) = self.plan_rc_strong_counters() else {
            return;
        };
        let mut counters = RcStrongCounters::default();
        for site in sites {
            let (in_name, out_name) = rc_strong_names(site);
            self.push_state_var_pair(&in_name, &out_name, rc_strong_sort());
            let Some(idx) = self.state_var_index_by_name(&in_name) else {
                continue;
            };
            counters.state_idx_by_site.insert(site, idx);
        }
        counters.site_by_local = site_by_local
            .into_iter()
            .filter(|(_, site)| counters.state_idx_by_site.contains_key(site))
            .collect();
        debug!(
            fn_name = %self.fn_name,
            sites = ?counters.state_idx_by_site.keys().collect::<Vec<_>>(),
            handles = counters.site_by_local.len(),
            "CHC: Rc/Arc strong-count state declared"
        );
        self.rc_strong_counters = counters;
    }

    fn rc_strong_count_at(&self, state_idx: usize) -> Option<RcStrongCount> {
        let (in_name, in_sort) = self.state_var_mgr.state_vars.get(state_idx)?;
        let (out_name, out_sort) = self.state_var_mgr.output_state_vars.get(state_idx)?;
        Some(RcStrongCount {
            current: Expr::var(&**in_name, in_sort.clone()),
            next: Expr::var(&**out_name, out_sort.clone()),
            state_idx,
        })
    }

    /// The count of the allocation the `new` call in block `site` makes.
    pub(in crate::codegen_ay::chc) fn rc_strong_count_for_new_site(
        &self,
        site: usize,
    ) -> Option<RcStrongCount> {
        self.rc_strong_count_at(*self.rc_strong_counters.state_idx_by_site.get(&site)?)
    }

    /// The count of the allocation the handle local `local` holds.
    pub(in crate::codegen_ay::chc) fn rc_strong_count_for_local(
        &self,
        local: usize,
    ) -> Option<RcStrongCount> {
        let site = self.rc_strong_counters.site_by_local.get(&local)?;
        self.rc_strong_count_for_new_site(*site)
    }

    /// Mark the count written by the transition being emitted, and return the
    /// constraint `next == value`.
    pub(in crate::codegen_ay::chc) fn write_rc_strong_count(
        &mut self,
        count: &RcStrongCount,
        value: Expr,
    ) -> Expr {
        self.mark_state_var_modified(count.state_idx);
        count.next.clone().eq(value)
    }

    fn call_path(&self, func: &Operand) -> Option<String> {
        let func_ty = func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(def, args)) = func_ty.kind() else {
            return None;
        };
        Instance::resolve(def, &args).ok().map(|instance| instance.name())
    }

    /// The pre-scan of the module doc. Returns every handle local's site and
    /// the sites whose allocation some handle clones, or `None` to keep the old
    /// encoding.
    fn plan_rc_strong_counters(&self) -> Option<(HashMap<usize, usize>, BTreeSet<usize>)> {
        if self.int_lift {
            return None;
        }
        let locals = self.body.locals();
        let arg_count = self.body.arg_locals().len();
        let mut kinds = Vec::with_capacity(locals.len());
        let mut any_handle = false;
        for (local, decl) in locals.iter().enumerate() {
            let ty = self.resolve_body_ty(decl.ty);
            let kind = if is_counted_handle_ty(ty) {
                LocalKind::Handle
            } else if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, Mutability::Not))
                if is_counted_handle_ty(self.resolve_body_ty(inner)))
            {
                LocalKind::HandleRef
            } else if ty_mentions_rc_family(ty) {
                return None;
            } else {
                LocalKind::Plain
            };
            if kind != LocalKind::Plain && (0..=arg_count).contains(&local) {
                return None;
            }
            any_handle |= kind == LocalKind::Handle;
            kinds.push(kind);
        }
        if !any_handle {
            return None;
        }
        let kind_of = |local: usize| kinds.get(local).copied().unwrap_or(LocalKind::Plain);

        let mut handle_sources: HashMap<usize, HandleSource> = HashMap::new();
        let mut ref_sources: HashMap<usize, (bool, usize)> = HashMap::new();
        let mut clones = 0usize;
        let mut assign_handle =
            |local: usize, source: HandleSource| handle_sources.insert(local, source).is_none();

        for (bb, block) in self.body.blocks.iter().enumerate() {
            for (stmt_idx, stmt) in block.statements.iter().enumerate() {
                let StatementKind::Assign(lhs, rvalue) = &stmt.kind else {
                    continue;
                };
                match kind_of(lhs.local) {
                    LocalKind::Handle => {
                        let dest = bare_local(lhs)?;
                        let src = match rvalue {
                            Rvalue::Use(operand, ..) => operand_bare_local(operand),
                            Rvalue::Cast(CastKind::PointerCoercion(_), operand, _) => {
                                operand_bare_local(operand)
                            }
                            _ => None,
                        }
                        .filter(|src| kind_of(*src) == LocalKind::Handle)?;
                        if !assign_handle(dest, HandleSource::Move(src)) {
                            return None;
                        }
                    }
                    LocalKind::HandleRef => {
                        let dest = bare_local(lhs)?;
                        let source = match rvalue {
                            Rvalue::Ref(_, BorrowKind::Shared, place) => bare_local(place)
                                .filter(|src| kind_of(*src) == LocalKind::Handle)
                                .map(|src| (true, src)),
                            Rvalue::Use(operand, ..) => operand_bare_local(operand)
                                .filter(|src| kind_of(*src) == LocalKind::HandleRef)
                                .map(|src| (false, src)),
                            _ => None,
                        }?;
                        if ref_sources.insert(dest, source).is_some() {
                            return None;
                        }
                    }
                    LocalKind::Plain => {
                        // A handle or a reference to one leaves the tracked
                        // locals: into an aggregate, a cast, a tuple.
                        let mut uses = WholeLocalUses::default();
                        uses.visit_rvalue(rvalue, statement_location(self.body, &bb, stmt_idx));
                        if uses.0.iter().any(|local| kind_of(*local) != LocalKind::Plain) {
                            return None;
                        }
                    }
                }
            }
            match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    let path = self.call_path(func).unwrap_or_default();
                    if is_core_rc_new(&path) {
                        let dest = bare_local(destination)
                            .filter(|dest| kind_of(*dest) == LocalKind::Handle)?;
                        if args.iter().any(|arg| {
                            arg.ty(locals)
                                .is_ok_and(|ty| ty_mentions_rc_family(self.resolve_body_ty(ty)))
                        }) || !assign_handle(dest, HandleSource::New(bb))
                        {
                            return None;
                        }
                    } else if is_core_rc_clone(&path) {
                        let dest = bare_local(destination)
                            .filter(|dest| kind_of(*dest) == LocalKind::Handle)?;
                        let [arg] = args.as_slice() else { return None };
                        let src = operand_bare_local(arg)
                            .filter(|src| kind_of(*src) == LocalKind::HandleRef)?;
                        if !assign_handle(dest, HandleSource::Clone(src)) {
                            return None;
                        }
                        clones += 1;
                    } else if is_read_only_rc_method(&path) {
                        if kind_of(destination.local) != LocalKind::Plain
                            || args.iter().any(|arg| match operand_bare_local(arg) {
                                Some(local) => kind_of(local) == LocalKind::Handle,
                                None => arg.ty(locals).is_ok_and(|ty| {
                                    ty_mentions_rc_family(self.resolve_body_ty(ty))
                                }),
                            })
                        {
                            return None;
                        }
                    } else if path_mentions_rc_family(&path)
                        || kind_of(destination.local) != LocalKind::Plain
                        || args.iter().any(|arg| {
                            operand_bare_local(arg)
                                .is_some_and(|local| kind_of(local) != LocalKind::Plain)
                                || arg.ty(locals).is_err()
                                || arg
                                    .ty(locals)
                                    .is_ok_and(|ty| ty_mentions_rc_family(self.resolve_body_ty(ty)))
                        })
                    {
                        return None;
                    }
                }
                TerminatorKind::Drop { place, .. } => {
                    let place_ty = place.ty(locals).ok().map(|ty| self.resolve_body_ty(ty));
                    if place_ty.is_none_or(ty_mentions_rc_family)
                        && bare_local(place).is_none_or(|local| kind_of(local) != LocalKind::Handle)
                    {
                        return None;
                    }
                }
                _ => {
                    let mut uses = WholeLocalUses::default();
                    uses.visit_terminator(&block.terminator, terminator_location(self.body, &bb));
                    if uses.0.iter().any(|local| kind_of(*local) != LocalKind::Plain) {
                        return None;
                    }
                }
            }
        }
        if clones == 0 {
            return None;
        }

        let resolve_ref = |mut local: usize| {
            for _ in 0..=ref_sources.len() {
                match ref_sources.get(&local)? {
                    (true, handle) => return Some(*handle),
                    (false, next) => local = *next,
                }
            }
            None
        };
        let mut site_by_local: HashMap<usize, usize> = HashMap::new();
        loop {
            let mut changed = false;
            for (&local, &source) in &handle_sources {
                if site_by_local.contains_key(&local) {
                    continue;
                }
                let site = match source {
                    HandleSource::New(site) => Some(site),
                    HandleSource::Move(src) => site_by_local.get(&src).copied(),
                    HandleSource::Clone(reference) => {
                        resolve_ref(reference).and_then(|h| site_by_local.get(&h).copied())
                    }
                };
                if let Some(site) = site {
                    site_by_local.insert(local, site);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        if site_by_local.len() != handle_sources.len() {
            return None;
        }
        // Every dropped handle must name its site.
        for block in &self.body.blocks {
            if let TerminatorKind::Drop { place, .. } = &block.terminator.kind
                && let Some(local) = bare_local(place)
                && kind_of(local) == LocalKind::Handle
                && !site_by_local.contains_key(&local)
            {
                return None;
            }
        }
        let cloned_sites: BTreeSet<usize> = handle_sources
            .iter()
            .filter(|(_, source)| matches!(source, HandleSource::Clone(_)))
            .filter_map(|(local, _)| site_by_local.get(local).copied())
            .collect();
        // One count per site holds one allocation's count only if the site runs
        // at most once: a `new` inside a loop would reset the count of an
        // allocation a handle from an earlier iteration still holds, and a drop
        // of that handle would then take the count past 0 (a bv64 wrap), so the
        // later allocation would never be freed.
        if cloned_sites.iter().any(|site| self.block_on_cycle(*site)) {
            return None;
        }
        Some((site_by_local, cloned_sites))
    }

    /// Whether block `bb` can run more than once: it is reachable from one of
    /// its own successors.
    fn block_on_cycle(&self, bb: usize) -> bool {
        let blocks = &self.body.blocks;
        let mut seen = vec![false; blocks.len()];
        let mut stack: Vec<usize> =
            blocks.get(bb).map(|block| block.terminator.successors()).unwrap_or_default();
        while let Some(next) = stack.pop() {
            if next == bb {
                return true;
            }
            if next >= blocks.len() || std::mem::replace(&mut seen[next], true) {
                continue;
            }
            stack.extend(blocks[next].terminator.successors());
        }
        false
    }
}
