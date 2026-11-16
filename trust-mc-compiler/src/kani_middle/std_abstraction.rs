// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The standard-library code the reachability boundary abstracts, by identity.
//!
//! Reachability does not collect the bodies of the std collections, `String`,
//! `Cow`, the slice and atomic modules, `std::fs` and a few others: codegen
//! emits stubs or CHC handlers for them instead (`Boundary::abstracts` in
//! `reachability.rs`; the inline gate in `codegen_function.rs`). Stubs
//! intercept at codegen time, so the boundary must stop the collector before
//! it fetches the internal bodies (designs/archive/2026-02-01-reachability-
//! intercept-fix.md).
//!
//! The set was a list of path spellings matched against printed text:
//! `def_path_str` at reachability, `Instance::name` at the inline gate. A
//! spelling matched a path that started with it, or, for a qualified path
//! (`<Ty as Trait>::item`), one that contained it anywhere. The text depends on
//! how rustc renders a path (separators, generic arguments, elided defaults,
//! impl segments, a crate-name prefix), so a change to the rendering changed
//! the set, and a keyword scan could only guess that it had happened.
//!
//! The set is the same now, decided from definitions:
//!
//! * Every anchor is a definition, resolved for each codegen unit (by
//!   reachability and again by codegen's inline gate): a module, a
//!   struct or a trait by its real definition path in the sysroot crate that
//!   defines it, a type by diagnostic or lang item, and `hashbrown` as the
//!   crate std's `HashMap` keeps its table in. Its former spellings are kept as
//!   the printed paths it was matched under.
//! * A spelling named the anchor as rustc PRINTS it, and that depends on the
//!   session: `std::vec::Vec` when std re-exports it, `alloc::vec::Vec`
//!   through `extern crate alloc` in a `no_std` crate, and
//!   `probe::alloc::vec::Vec` there under `Instance::name`, which prints the
//!   local crate's name. So each anchor's printed path is derived per session
//!   and per printer from the queries the printer uses (`visible_parent_map`,
//!   `extern_crate`, `module_children`), as segments. An anchor counts where
//!   that path IS one of its spellings, or, inside a qualified path, ENDS with
//!   one. `VecDeque` prints `alloc::collections::VecDeque` in a `no_std` crate,
//!   which no spelling named, so it is collected there as it always was.
//! * An item's path is walked as `print_def_path` builds it (visible paths,
//!   impl segments, trait-qualified items, generic arguments without
//!   defaults, function signatures, foreign closures, trait objects), and each
//!   definition it names is checked for membership: in the leading segments
//!   of a plain path, or anywhere in a qualified one.
//! * `fetch_update` keeps its body wherever `::fetch_update` appeared in the
//!   text: a segment starting with that name, after another segment,
//!   including in generic arguments (`Vec::<fn() {m::fetch_update}>::push`).
//!
//! Fail closed: an anchor whose crate is loaded but which does not resolve is
//! matched by its former spellings against the printed text (the old rule);
//! an anchor printed under the crate of one of its spellings but as none of
//! them (a re-export moved) is abstracted wherever it is named; a `HashMap`
//! table in a crate not named `hashbrown` is abstracted whole. Each is
//! reported once per process, and every function it abstracts is recorded as
//! an unstubbed abstraction in the harness's unsoundness metadata
//! (`Abstraction::FailClosed`). An anchor whose crate is not loaded names
//! nothing that can be reached and is not a failure.
//! `std_abstraction_every_anchor_prints_as_a_former_spelling` fails on a
//! toolchain where one fails closed.
//!
//! What the text matched and definitions cannot (each abstracted, and is now
//! collected): a spelling inside a longer segment (`std::alloc::Global` in
//! `std::alloc::GlobalAlloc`, so every `GlobalAlloc` impl;
//! `alloc::collections::btree` in `alloc::collections::btree_map::Iter`, so
//! the `btree_map` and `btree_set` iterators of a `no_std` crate), `hashbrown`
//! anywhere in a qualified path (a user module or type of that name, a local
//! closure's file name), and a projection's trait. Two spellings could never
//! match a printed path and are gone: `alloc::collections::btree_map::BTreeMap`
//! and `alloc::collections::btree_set::BTreeSet` (`alloc::collections`
//! re-exports both types itself, and a visible path is the shortest).

use std::collections::HashSet;
use std::sync::{Mutex, OnceLock};

#[cfg(all(trust_toolchain, version("1.101")))]
use rustc_crate_store::{ExternCrate, ExternCrateSource};
use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CRATE_DEF_INDEX, CrateNum, DefId, LOCAL_CRATE};
use rustc_hir::definitions::DefPathData;
use rustc_middle::ty::print::{
    characteristic_def_id_of_type, with_no_trimmed_paths, with_resolve_crate_name,
};
use rustc_middle::ty::{
    self, ExistentialPredicate, GenericArg, Instance, TraitRef, Ty, TyCtxt, TypeSuperVisitable,
    TypeVisitable, TypeVisitor,
};
#[cfg(not(all(trust_toolchain, version("1.101"))))]
use rustc_session::cstore::{ExternCrate, ExternCrateSource};
use rustc_span::Symbol;
use rustc_span::symbol::kw;

use crate::rustc_compat::{LangItem, skip_normalization};

mod wrapper_identity;
pub(crate) use wrapper_identity::{
    NativeWrapperKind, is_compiler_library_definition, native_wrapper_kind,
};

/// The sysroot crate an anchor is defined in.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SysrootCrate {
    Core,
    Alloc,
    Std,
}

impl SysrootCrate {
    fn name(self) -> &'static str {
        match self {
            SysrootCrate::Core => "core",
            SysrootCrate::Alloc => "alloc",
            SysrootCrate::Std => "std",
        }
    }

    /// A lang item only this crate defines. A name does not identify the
    /// crate: Kani's sysroot loads a `std` of its own beside the real one.
    fn marker(self) -> LangItem {
        match self {
            SysrootCrate::Core => LangItem::Sized,
            SysrootCrate::Alloc => LangItem::OwnedBox,
            SysrootCrate::Std => LangItem::Start,
        }
    }
}

/// How an anchor is found.
#[derive(Clone, Copy, Debug)]
enum Find {
    /// A module, by its real definition path in the crate.
    Module(SysrootCrate, &'static [&'static str]),
    /// A struct, by its real definition path in the crate.
    Struct(SysrootCrate, &'static [&'static str]),
    /// A trait, by its real definition path in the crate.
    Trait(SysrootCrate, &'static [&'static str]),
    /// A type, by its diagnostic item.
    DiagnosticType(SysrootCrate, &'static str),
    /// A type, by its lang item.
    LangType(SysrootCrate, LangItem),
    /// The crate std's `HashMap` keeps its table in, and every crate printed
    /// by the name its spelling gives.
    HashMapBackend,
}

/// One anchor of the abstraction set.
#[derive(Clone, Copy, Debug)]
struct Anchor {
    find: Find,
    /// The printed paths its former spellings named it by (`a::b::C`; the
    /// spelling was `a::b::C::`).
    printed: &'static [&'static str],
}

/// The abstraction set: every former spelling, each with the definition it
/// named.
const ANCHORS: &[Anchor] = &[
    // Collections, modeled as SMT arrays (Part of #1659). Their iterator
    // types live in the modules, not on the type path (Part of #3057).
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Std, "HashMap"),
        printed: &["std::collections::HashMap"],
    },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Std, "HashSet"),
        printed: &["std::collections::HashSet"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Std, &["collections", "hash_map"]),
        printed: &["std::collections::hash_map"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Std, &["collections", "hash_set"]),
        printed: &["std::collections::hash_set"],
    },
    // HashMap and HashSet delegate to hashbrown, whose raw tables and buckets
    // have no CHC stubs.
    Anchor { find: Find::HashMapBackend, printed: &["hashbrown"] },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Alloc, "BTreeSet"),
        printed: &["std::collections::BTreeSet"],
    },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Alloc, "BTreeMap"),
        printed: &["std::collections::BTreeMap"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Alloc, &["collections", "btree_map"]),
        printed: &["std::collections::btree_map"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Alloc, &["collections", "btree_set"]),
        printed: &["std::collections::btree_set"],
    },
    // The internal BTree modules (node, search, navigate, ...).
    Anchor {
        find: Find::Module(SysrootCrate::Alloc, &["collections", "btree"]),
        printed: &["alloc::collections::btree"],
    },
    // Vec and String, modeled as SMT sequences or arrays. Without the
    // `into_iter` items rustc inlines `IntoIter::next` into raw pointer
    // operations (#2876 RC2); std re-exports both types (#2967).
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Alloc, "Vec"),
        printed: &["alloc::vec::Vec", "std::vec::Vec"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Alloc, &["vec", "into_iter"]),
        printed: &["alloc::vec::into_iter"],
    },
    Anchor {
        find: Find::Struct(SysrootCrate::Alloc, &["vec", "into_iter", "IntoIter"]),
        printed: &["std::vec::IntoIter"],
    },
    Anchor {
        find: Find::LangType(SysrootCrate::Alloc, LangItem::String),
        printed: &["alloc::string::String", "std::string::String"],
    },
    // `Cow<str>` collapses to `String` (#1691).
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Alloc, "Cow"),
        printed: &["std::borrow::Cow", "alloc::borrow::Cow"],
    },
    // `from_utf8_lossy`'s `Utf8Chunks` iterator needs no model.
    Anchor {
        find: Find::Module(SysrootCrate::Core, &["str", "lossy"]),
        printed: &["core::str::lossy"],
    },
    Anchor {
        find: Find::Struct(SysrootCrate::Core, &["str", "lossy", "Utf8Chunk"]),
        printed: &["core::str::Utf8Chunk", "alloc::str::Utf8Chunk", "std::str::Utf8Chunk"],
    },
    Anchor {
        find: Find::Struct(SysrootCrate::Core, &["str", "lossy", "Utf8Chunks"]),
        printed: &["core::str::Utf8Chunks", "alloc::str::Utf8Chunks", "std::str::Utf8Chunks"],
    },
    // Allocation internals, already stubbed: RawVec's bodies explode codegen
    // (#1691); the global allocator's inherent methods (its trait impls print
    // as `<Global as Allocator>`).
    Anchor { find: Find::Module(SysrootCrate::Alloc, &["raw_vec"]), printed: &["alloc::raw_vec"] },
    Anchor {
        find: Find::LangType(SysrootCrate::Alloc, LangItem::GlobalAlloc),
        printed: &["std::alloc::Global"],
    },
    // Slices: `into_vec` (the `vec![..]` expansion, #2967), the slice methods
    // and iterators the Vec stubs dispatch on (#3012). std re-exports
    // `alloc::slice`, which re-exports `core::slice`'s items.
    Anchor {
        find: Find::Module(SysrootCrate::Alloc, &["slice"]),
        printed: &["alloc::slice", "std::slice"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Core, &["slice"]),
        printed: &["core::slice", "std::slice"],
    },
    // VecDeque and LinkedList: pointer-heavy bodies the solver cannot reason
    // about (Part of #2984).
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Alloc, "VecDeque"),
        printed: &["std::collections::VecDeque"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Alloc, &["collections", "vec_deque"]),
        printed: &["std::collections::vec_deque", "alloc::collections::vec_deque"],
    },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Alloc, "LinkedList"),
        printed: &["std::collections::LinkedList"],
    },
    Anchor {
        find: Find::Module(SysrootCrate::Alloc, &["collections", "linked_list"]),
        printed: &["std::collections::linked_list", "alloc::collections::linked_list"],
    },
    // `spec_next` is the CHC-stubbed entry of range iteration (#3002). The
    // trait is private, so it prints through `core::iter`, which std
    // re-exports.
    Anchor {
        find: Find::Trait(SysrootCrate::Core, &["iter", "range", "RangeIteratorImpl"]),
        printed: &["core::iter::range::RangeIteratorImpl", "std::iter::range::RangeIteratorImpl"],
    },
    // The stable atomic wrappers inflate CHC clause counts; their calls are
    // dispatched to stable atomic stubs (Part of #3452).
    Anchor {
        find: Find::Module(SysrootCrate::Core, &["sync", "atomic"]),
        printed: &["core::sync::atomic", "std::sync::atomic"],
    },
    // Mutex and RwLock are transparent in single-threaded verification
    // (Part of #4067).
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Std, "Mutex"),
        printed: &["std::sync::Mutex"],
    },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Std, "RwLock"),
        printed: &["std::sync::RwLock"],
    },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Std, "MutexGuard"),
        printed: &["std::sync::MutexGuard"],
    },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Std, "RwLockReadGuard"),
        printed: &["std::sync::RwLockReadGuard"],
    },
    Anchor {
        find: Find::DiagnosticType(SysrootCrate::Std, "RwLockWriteGuard"),
        printed: &["std::sync::RwLockWriteGuard"],
    },
    // Filesystem operations: OS side effects with no verification semantics
    // (Part of #4134).
    Anchor { find: Find::Module(SysrootCrate::Std, &["fs"]), printed: &["std::fs"] },
];

/// A function of an abstracted module that keeps its body: `fetch_update`
/// runs its closure, which no stub can evaluate, so it is inlined and its
/// inner calls reach their own stubs (Part of #3516). A segment starting with
/// this name exempts the whole path, as `::fetch_update` in the text did.
const EXEMPT_FUNCTION: &str = "fetch_update";

/// Failures already reported, so each is reported once per process.
static WARNED_FAILURES: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();

/// The printer whose text the former spellings were matched against. The
/// two print a local path differently, and with it every path that reaches a
/// crate through a local `extern crate` item.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Printing {
    /// `TyCtxt::def_path_str`: reachability decides per definition. The
    /// local crate prints as nothing, so `extern crate alloc` gives `alloc::..`.
    Definition,
    /// `Instance::name` (`with_resolve_crate_name`): the inline gate decides
    /// per instance. The local crate prints its name: `probe::alloc::..`.
    Instance,
}

impl Printing {
    const ALL: [Printing; 2] = [Printing::Definition, Printing::Instance];

    fn index(self) -> usize {
        match self {
            Printing::Definition => 0,
            Printing::Instance => 1,
        }
    }
}

/// Whether a body is behind the boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Abstraction {
    /// Collected (or inlined) like any other body.
    Collected,
    /// Abstracted: an anchor of the set names it.
    Abstracted,
    /// Abstracted only by an anchor that failed closed on this sysroot, so
    /// that what models it is not established either.
    FailClosed,
}

impl Abstraction {
    pub(crate) fn is_abstracted(self) -> bool {
        self != Abstraction::Collected
    }
}

/// The abstraction set of one session, resolved to definitions.
#[derive(Debug, Default)]
pub(crate) struct StdAbstraction {
    /// Per printing: anchors printed as one of their spellings, which a path
    /// starting with them matched.
    heads: [FxHashSet<DefId>; 2],
    /// Per printing: anchors whose printed path ends with one of their
    /// spellings, which a qualified path naming them contained.
    named: [FxHashSet<DefId>; 2],
    /// Anchors that failed closed.
    failed_closed: FxHashSet<DefId>,
    /// Former spellings of anchors that did not resolve, matched against the
    /// printed text instead (fail closed).
    unresolved_spellings: Vec<&'static str>,
    /// What failed closed.
    failures: Vec<String>,
}

impl StdAbstraction {
    /// Resolve every anchor against the crates this session loaded.
    pub(crate) fn resolve(tcx: TyCtxt<'_>) -> Self {
        Self::resolve_anchors(tcx, ANCHORS)
    }

    fn resolve_anchors(tcx: TyCtxt<'_>, anchors: &[Anchor]) -> Self {
        let mut set = StdAbstraction::default();
        for anchor in anchors {
            match resolve_anchor(tcx, anchor.find) {
                Resolution::Defs(defs) => {
                    for def in defs {
                        set.add(tcx, anchor, def);
                    }
                }
                Resolution::FailClosed(defs, what) => {
                    for def in defs {
                        set.add_failed_closed(def);
                    }
                    set.failures.push(format!("{what}; every item of it is abstracted"));
                }
                Resolution::CrateAbsent => {}
                Resolution::Missing(what) => {
                    set.unresolved_spellings.extend(anchor.printed.iter().copied());
                    set.failures.push(format!(
                        "{what} does not resolve; its items are abstracted by the former \
                         spellings `{}`",
                        anchor.printed.join("`, `")
                    ));
                }
            }
        }
        if !set.failures.is_empty() {
            let warned = WARNED_FAILURES.get_or_init(|| Mutex::new(HashSet::new()));
            let mut warned = warned.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
            for failure in &set.failures {
                if warned.insert(failure.clone()) {
                    tcx.dcx().warn(format!(
                        "the reachability boundary fails closed on this sysroot: {failure}"
                    ));
                }
            }
        }
        set
    }

    /// Record where `def` (an anchor) is matched, from how this session
    /// prints it.
    fn add(&mut self, tcx: TyCtxt<'_>, anchor: &Anchor, def: DefId) {
        for printing in Printing::ALL {
            let printed = PrintedPath::of(tcx, def, printing);
            let index = printing.index();
            if anchor.printed.iter().any(|spelling| printed.is(spelling)) {
                self.heads[index].insert(def);
            }
            if anchor.printed.iter().any(|spelling| printed.ends_with(spelling)) {
                self.named[index].insert(def);
            } else if printed.starts_in_a_crate_of(anchor.printed) {
                // Printed under the crate one of its spellings names, as none
                // of them: the re-export a spelling named has moved.
                self.add_failed_closed(def);
                self.failures.push(format!(
                    "`{}` prints as `{printed}`, which none of `{}` names",
                    tcx.def_path_str(def),
                    anchor.printed.join("`, `")
                ));
                return;
            }
        }
    }

    fn add_failed_closed(&mut self, def: DefId) {
        for printing in Printing::ALL {
            self.heads[printing.index()].insert(def);
            self.named[printing.index()].insert(def);
        }
        self.failed_closed.insert(def);
    }

    /// What failed closed in this session (empty on a sysroot every anchor
    /// fits).
    #[cfg(test)]
    pub(crate) fn failures(&self) -> &[String] {
        &self.failures
    }

    /// [`Self::resolve`] with the anchors whose first spelling is in `missing`
    /// treated as unresolved, and those in `respelled` given other spellings.
    #[cfg(test)]
    pub(crate) fn resolve_altered(
        tcx: TyCtxt<'_>,
        missing: &[&str],
        respelled: &[(&str, &'static [&'static str])],
    ) -> Self {
        let anchors: Vec<Anchor> = ANCHORS
            .iter()
            .map(|anchor| {
                let first = anchor.printed[0];
                let mut anchor = *anchor;
                if missing.contains(&first) {
                    anchor.find = Find::Module(SysrootCrate::Core, &["no_such_module"]);
                }
                if let Some((_, printed)) = respelled.iter().find(|(name, _)| *name == first) {
                    anchor.printed = printed;
                }
                anchor
            })
            .collect();
        Self::resolve_anchors(tcx, &anchors)
    }

    /// Is the body of `def_id` behind the boundary? Reachability decides per
    /// definition, as `def_path_str` printed it.
    pub(crate) fn decide_definition(&self, tcx: TyCtxt<'_>, def_id: DefId) -> Abstraction {
        self.decide(tcx, def_id, &[], Printing::Definition)
    }

    /// Is the body of `instance` behind the boundary? The inline gate decides
    /// per instance, with its generic arguments, as `Instance::name` printed it.
    pub(crate) fn decide_instance<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        instance: Instance<'tcx>,
    ) -> Abstraction {
        self.decide(tcx, instance.def_id(), instance.args, Printing::Instance)
    }

    /// [`Self::decide_instance`] for a `rustc_public` instance.
    pub(crate) fn abstracts_public_instance(
        &self,
        tcx: TyCtxt<'_>,
        instance: rustc_public::mir::mono::Instance,
    ) -> bool {
        self.decide_instance(tcx, rustc_public::rustc_internal::internal(tcx, instance))
            .is_abstracted()
    }

    fn decide<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        args: &'tcx [GenericArg<'tcx>],
        printing: Printing,
    ) -> Abstraction {
        let mut walk = PathWalk::new(tcx, self, printing);
        walk.def(def_id, args);
        if walk.exempt {
            return Abstraction::Collected;
        }
        let hit = if walk.qualified { walk.named } else { walk.head };
        match hit {
            Hit::Anchor => Abstraction::Abstracted,
            Hit::FailedClosed => Abstraction::FailClosed,
            Hit::None if self.matches_unresolved_spelling(tcx, def_id, args, printing) => {
                Abstraction::FailClosed
            }
            Hit::None => Abstraction::Collected,
        }
    }

    /// Fail-closed match for anchors that did not resolve: the former rule
    /// over the printed text, for their spellings only.
    fn matches_unresolved_spelling<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        args: &'tcx [GenericArg<'tcx>],
        printing: Printing,
    ) -> bool {
        if self.unresolved_spellings.is_empty() {
            return false;
        }
        let path = match printing {
            Printing::Definition => with_no_trimmed_paths!(tcx.def_path_str(def_id)),
            Printing::Instance => with_resolve_crate_name!(with_no_trimmed_paths!(
                tcx.def_path_str_with_args(def_id, args)
            )),
        };
        matches_spelling(&path, &self.unresolved_spellings)
    }
}

/// The former rule over a printed path: it starts with a spelling, or, when
/// qualified, contains one. A doubled leading `std::` (Kani's std re-exports
/// std's own items) collapses first (#4231).
pub(crate) fn matches_spelling(path: &str, spellings: &[&str]) -> bool {
    let mut path = path;
    while path.starts_with("std::std::") {
        path = &path["std::".len()..];
    }
    let qualified = path.starts_with('<');
    spellings.iter().any(|spelling| {
        path.strip_prefix(spelling).is_some_and(|rest| rest.starts_with("::"))
            || (qualified && path.contains(spelling))
    })
}

/// One piece of a printed path.
#[derive(Clone, Copy, Debug)]
enum Atom {
    /// A crate's name (`print_crate_name`); the local crate prints as nothing
    /// under `def_path_str`.
    Crate(CrateNum),
    /// A segment naming a definition, preceded by `::` unless the path is
    /// still empty. Anonymous segments (`{closure#0}`) carry no name.
    Segment(DefId, Option<Symbol>),
}

/// An anchor's printed path, as segments.
struct PrintedPath {
    segments: Vec<Symbol>,
    /// It starts with the local crate's name (`Instance::name` through a
    /// local `extern crate`), which no spelling starts with.
    local_first: bool,
}

impl PrintedPath {
    /// How `printing` prints `def`, a definition outside any impl.
    fn of(tcx: TyCtxt<'_>, def: DefId, printing: Printing) -> Self {
        let mut segments = Vec::new();
        let mut local_first = false;
        for atom in plain_atoms(tcx, def) {
            match atom {
                Atom::Crate(LOCAL_CRATE) => {
                    if printing == Printing::Instance {
                        local_first = segments.is_empty();
                        segments.push(tcx.crate_name(LOCAL_CRATE));
                    }
                }
                Atom::Crate(krate) => segments.push(tcx.crate_name(krate)),
                Atom::Segment(_, name) => segments.extend(name),
            }
        }
        // The text was matched after collapsing a doubled leading `std::`.
        while segments.len() > 1 && segments[0].as_str() == "std" && segments[1].as_str() == "std" {
            segments.remove(0);
        }
        PrintedPath { segments, local_first }
    }

    fn is(&self, spelling: &str) -> bool {
        self.segments.iter().map(Symbol::as_str).eq(spelling.split("::"))
    }

    fn ends_with(&self, spelling: &str) -> bool {
        let wanted: Vec<&str> = spelling.split("::").collect();
        self.segments.len() >= wanted.len()
            && self.segments[self.segments.len() - wanted.len()..]
                .iter()
                .map(Symbol::as_str)
                .eq(wanted.iter().copied())
    }

    /// It starts with a crate one of `spellings` starts with.
    fn starts_in_a_crate_of(&self, spellings: &[&str]) -> bool {
        !self.local_first
            && self.segments.first().is_some_and(|first| {
                spellings.iter().any(|spelling| spelling.split("::").next() == Some(first.as_str()))
            })
    }
}

impl std::fmt::Display for PrintedPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let segments: Vec<&str> = self.segments.iter().map(Symbol::as_str).collect();
        f.write_str(&segments.join("::"))
    }
}

/// `print_def_path(def, &[])` for a definition outside any impl: its visible
/// path, or its definition path, whose parent prints the same way.
fn plain_atoms(tcx: TyCtxt<'_>, def: DefId) -> Vec<Atom> {
    if let Some(atoms) = visible_atoms(tcx, def, &mut Vec::new()) {
        return atoms;
    }
    let key = tcx.def_key(def);
    match key.parent {
        None => vec![Atom::Crate(def.krate)],
        Some(parent) => {
            let mut atoms = plain_atoms(tcx, DefId { index: parent, ..def });
            atoms.push(Atom::Segment(def, key.disambiguated_data.data.get_opt_name()));
            atoms
        }
    }
}

/// The visible path rustc prints for `def` (`try_print_visible_def_path`):
/// `None` where it falls back to the definition path.
fn visible_atoms(tcx: TyCtxt<'_>, def: DefId, callers: &mut Vec<DefId>) -> Option<Vec<Atom>> {
    if let Some(krate) = def.as_crate_root() {
        if krate == LOCAL_CRATE {
            return Some(vec![Atom::Crate(LOCAL_CRATE)]);
        }
        match tcx.extern_crate(krate) {
            Some(&ExternCrate { src, dependency_of, span, .. }) => match (src, dependency_of) {
                (ExternCrateSource::Extern(item), LOCAL_CRATE) => {
                    // The `extern crate` std and core get injected with has
                    // no span and prints the crate's name; one the source
                    // wrote prints the item's path, without visible paths.
                    return Some(if span.is_dummy() {
                        vec![Atom::Crate(krate)]
                    } else {
                        definition_atoms(tcx, item)
                    });
                }
                (ExternCrateSource::Path, LOCAL_CRATE) => return Some(vec![Atom::Crate(krate)]),
                _ => {}
            },
            None => return Some(vec![Atom::Crate(krate)]),
        }
    }
    if def.is_local() {
        return None;
    }
    let visible_parent = *tcx.visible_parent_map(()).get(&def)?;
    // (A `#[doc(hidden)]` visible parent bails only under
    // `with_no_visible_paths_if_doc_hidden`, which neither printer sets.)
    let mut key = tcx.def_key(def);
    if let DefPathData::Ctor = key.disambiguated_data.data {
        let parent = key.parent.expect("a constructor has a parent");
        key = tcx.def_key(DefId { index: parent, ..def });
    }
    let name = match key.disambiguated_data.data {
        // Re-exported under the visible parent: the name it is re-exported by.
        DefPathData::TypeNs(_) if Some(visible_parent) != tcx.opt_parent(def) => Some(
            tcx.module_children(visible_parent)
                .iter()
                .filter(|child| child.res.opt_def_id() == Some(def))
                .find(|child| child.vis.is_public() && child.ident.name != kw::Underscore)?
                .ident
                .name,
        ),
        // A re-exported crate.
        DefPathData::CrateRoot => Some(tcx.crate_name(def.krate)),
        data => data.get_opt_name(),
    };
    if callers.contains(&visible_parent) {
        return None;
    }
    callers.push(visible_parent);
    let mut atoms = visible_atoms(tcx, visible_parent, callers)?;
    callers.pop();
    atoms.push(Atom::Segment(def, name));
    Some(atoms)
}

/// The definition path of `def`, printed with no visible paths.
fn definition_atoms(tcx: TyCtxt<'_>, def: DefId) -> Vec<Atom> {
    let key = tcx.def_key(def);
    match key.parent {
        None => vec![Atom::Crate(def.krate)],
        Some(parent) => {
            let mut atoms = definition_atoms(tcx, DefId { index: parent, ..def });
            atoms.push(Atom::Segment(def, key.disambiguated_data.data.get_opt_name()));
            atoms
        }
    }
}

/// Which anchor a path named where it counts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Hit {
    None,
    /// Only anchors that failed closed.
    FailedClosed,
    Anchor,
}

/// Walks the path `print_def_path(def, args)` prints, in printing order,
/// and records what the former spellings would have seen in its text.
struct PathWalk<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    set: &'a StdAbstraction,
    printing: Printing,
    /// Still printing the leading segments: no generic arguments, impl
    /// segment or qualified segment yet.
    in_head: bool,
    /// Anything printed yet.
    started: bool,
    /// The path starts with `<` (a qualified path).
    qualified: bool,
    /// Nothing printed in the current path yet (`empty_path`), so the next
    /// segment is not preceded by `::`.
    empty_path: bool,
    /// An anchor in the leading segments.
    head: Hit,
    /// An anchor anywhere.
    named: Hit,
    /// A segment after another segment starts with `fetch_update`.
    exempt: bool,
}

impl<'a, 'tcx> PathWalk<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, set: &'a StdAbstraction, printing: Printing) -> Self {
        PathWalk {
            tcx,
            set,
            printing,
            in_head: true,
            started: false,
            qualified: false,
            empty_path: true,
            head: Hit::None,
            named: Hit::None,
            exempt: false,
        }
    }

    fn atom(&mut self, atom: Atom) {
        self.started = true;
        let def = match atom {
            Atom::Crate(krate) => {
                self.empty_path = krate == LOCAL_CRATE && self.printing == Printing::Definition;
                krate.as_def_id()
            }
            Atom::Segment(def, name) => {
                if !self.empty_path
                    && name.is_some_and(|name| name.as_str().starts_with(EXEMPT_FUNCTION))
                {
                    self.exempt = true;
                }
                self.empty_path = false;
                def
            }
        };
        let index = self.printing.index();
        let hit =
            if self.set.failed_closed.contains(&def) { Hit::FailedClosed } else { Hit::Anchor };
        if self.in_head && self.set.heads[index].contains(&def) {
            self.head = self.head.max(hit);
        }
        if self.set.named[index].contains(&def) {
            self.named = self.named.max(hit);
        }
    }

    /// `print_def_path(def, args)`.
    fn def(&mut self, def: DefId, args: &'tcx [GenericArg<'tcx>]) {
        let tcx = self.tcx;
        if args.is_empty()
            && let Some(atoms) = visible_atoms(tcx, def, &mut Vec::new())
        {
            for atom in atoms {
                self.atom(atom);
            }
            return;
        }
        let key = tcx.def_key(def);
        match key.disambiguated_data.data {
            DefPathData::CrateRoot => self.atom(Atom::Crate(def.krate)),
            DefPathData::Impl => self.impl_path(def, args),
            data => {
                let parent = DefId { index: key.parent.expect("a non-root definition"), ..def };
                let mut parent_args = args;
                let mut trait_qualify_parent = false;
                if !args.is_empty() {
                    let generics = tcx.generics_of(def);
                    parent_args = &args[..generics.parent_count.min(args.len())];
                    match data {
                        // A coroutine desugared from a closure prints its kind.
                        DefPathData::Closure => {
                            if let Some(rustc_hir::CoroutineKind::Desugared(
                                _,
                                rustc_hir::CoroutineSource::Closure,
                            )) = tcx.coroutine_kind(def)
                                && args.len() > parent_args.len()
                            {
                                self.def(def, parent_args);
                                self.generic_args(&args[parent_args.len()..][..1]);
                                return;
                            }
                        }
                        // Captures, coroutine state and anonymous constants'
                        // generics are not printed.
                        DefPathData::SyntheticCoroutineBody | DefPathData::AnonConst => {}
                        _ => {
                            if !generics.is_own_empty() && args.len() >= generics.count() {
                                self.def(def, parent_args);
                                self.generic_args(generics.own_args_no_defaults(tcx, args));
                                return;
                            }
                        }
                    }
                    trait_qualify_parent = generics.has_self
                        && generics.parent == Some(parent)
                        && parent_args.len() == generics.parent_count
                        && tcx.generics_of(parent).parent_count == 0;
                }
                if trait_qualify_parent {
                    let trait_ref = TraitRef::new(tcx, parent, parent_args.iter().copied());
                    self.qualified(trait_ref.self_ty(), Some(trait_ref));
                } else {
                    self.def(parent, parent_args);
                }
                self.atom(Atom::Segment(def, data.get_opt_name()));
            }
        }
    }

    /// `print_impl_path`: `module::<impl Trait for Ty>` for an impl apart
    /// from its self type and its trait, `<Ty as Trait>` (or `Ty`) beside one.
    fn impl_path(&mut self, impl_def: DefId, args: &'tcx [GenericArg<'tcx>]) {
        let header = ImplHeader::of(self.tcx, impl_def, args);
        if header.is_co_located(self.tcx, impl_def) {
            self.qualified(header.self_ty, header.trait_ref);
        } else {
            self.def(self.tcx.parent(impl_def), &[]);
            self.in_head = false;
            if let Some(trait_ref) = header.trait_ref {
                self.def(trait_ref.def_id, trait_ref.args);
            }
            header.self_ty.visit_with(self);
            self.empty_path = false;
        }
    }

    /// `print_path_with_qualified`: `Ty` for an inherent impl of a nominal or
    /// primitive type, `<Ty>` or `<Ty as Trait>` otherwise.
    fn qualified(&mut self, self_ty: Ty<'tcx>, trait_ref: Option<TraitRef<'tcx>>) {
        if trait_ref.is_none()
            && matches!(
                self_ty.kind(),
                ty::Adt(..)
                    | ty::Foreign(_)
                    | ty::Bool
                    | ty::Char
                    | ty::Str
                    | ty::Int(_)
                    | ty::Uint(_)
                    | ty::Float(_)
            )
        {
            self.started = true;
            self_ty.visit_with(self);
            return;
        }
        if !self.started {
            self.qualified = true;
        }
        self.started = true;
        self.in_head = false;
        self_ty.visit_with(self);
        if let Some(trait_ref) = trait_ref {
            // `print_only_trait_path`.
            self.def(trait_ref.def_id, trait_ref.args);
        }
        self.empty_path = false;
    }

    /// `print_path_with_generic_args`: the printed arguments, if any.
    fn generic_args(&mut self, args: &[GenericArg<'tcx>]) {
        // Lifetimes name nothing; const arguments print values.
        if args.iter().all(|arg| arg.as_region().is_some()) {
            return;
        }
        self.in_head = false;
        for arg in args {
            if let Some(ty) = arg.as_type() {
                ty.visit_with(self);
            }
        }
        self.empty_path = false;
    }
}

/// The paths a type prints: an ADT's or a foreign type's, a function item's
/// signature and path, a foreign closure's or coroutine's path (a local one
/// prints as its span), a trait object's traits and arguments.
impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for PathWalk<'_, 'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        match *ty.kind() {
            ty::Adt(adt, args) => self.def(adt.did(), args),
            ty::Foreign(def) => self.def(def, &[]),
            ty::FnDef(def, args) => {
                // This visitor only records definition paths. Visiting the
                // raw argument structure preserves names under a modern
                // function-item binder; it neither resolves an executable
                // instance nor erases a binder in verification.
                #[cfg(all(trust_toolchain, version("1.101")))]
                let args = args.skip_binder();
                let sig = skip_normalization(self.tcx.fn_sig(def).instantiate(self.tcx, args));
                sig.skip_binder().inputs_and_output.visit_with(self);
                self.def(def, args);
            }
            ty::Closure(def, args) | ty::CoroutineClosure(def, args) | ty::Coroutine(def, args) => {
                if !def.is_local() {
                    self.def(def, args);
                }
            }
            ty::CoroutineWitness(..) => {}
            ty::Dynamic(predicates, ..) => {
                for predicate in predicates.iter() {
                    match predicate.skip_binder() {
                        ExistentialPredicate::Trait(trait_ref) => {
                            self.def(trait_ref.def_id, &[]);
                            trait_ref.args.visit_with(self);
                        }
                        ExistentialPredicate::Projection(projection) => {
                            projection.args.visit_with(self);
                            projection.term.visit_with(self);
                        }
                        ExistentialPredicate::AutoTrait(def) => self.def(def, &[]),
                    }
                }
            }
            _ => ty.super_visit_with(self),
        }
    }
}

/// An impl's self type and trait reference, instantiated as its items'
/// paths print them: with the arguments when they cover the impl's generics,
/// with the impl's own parameters otherwise.
struct ImplHeader<'tcx> {
    self_ty: Ty<'tcx>,
    trait_ref: Option<TraitRef<'tcx>>,
}

impl<'tcx> ImplHeader<'tcx> {
    fn of(tcx: TyCtxt<'tcx>, impl_def: DefId, args: &'tcx [GenericArg<'tcx>]) -> Self {
        let self_ty = tcx.type_of(impl_def);
        let trait_ref = crate::rustc_compat::impl_opt_trait_ref(tcx, impl_def);
        if tcx.generics_of(impl_def).count() <= args.len() {
            ImplHeader {
                self_ty: skip_normalization(self_ty.instantiate(tcx, args)),
                trait_ref: trait_ref.map(|tr| skip_normalization(tr.instantiate(tcx, args))),
            }
        } else {
            ImplHeader {
                self_ty: skip_normalization(self_ty.instantiate_identity()),
                trait_ref: trait_ref.map(|tr| skip_normalization(tr.instantiate_identity())),
            }
        }
    }

    /// Whether the impl lives beside its self type or its trait, so that its
    /// items print as `<Ty as Trait>::item` (or `Ty::item`) rather than
    /// `module::<impl ..>::item` (rustc's `default_print_impl_path`).
    fn is_co_located(&self, tcx: TyCtxt<'tcx>, impl_def: DefId) -> bool {
        let module = tcx.parent(impl_def);
        characteristic_def_id_of_type(self.self_ty).is_some_and(|ty| tcx.parent(ty) == module)
            || self.trait_ref.is_some_and(|tr| tcx.parent(tr.def_id) == module)
    }
}

/// The outcome of resolving one anchor.
enum Resolution {
    Defs(Vec<DefId>),
    /// Found, but not as the anchor expects: abstracted whole (what failed).
    FailClosed(Vec<DefId>, String),
    /// The crate that would define it is not part of this session.
    CrateAbsent,
    /// Its crate is loaded and it is not there: what was looked for.
    Missing(String),
}

fn resolve_anchor(tcx: TyCtxt<'_>, find: Find) -> Resolution {
    match find {
        Find::HashMapBackend => resolve_hash_map_backend(tcx),
        Find::Module(krate, path) | Find::Struct(krate, path) | Find::Trait(krate, path) => {
            let (want, what): (&[DefKind], &str) = match find {
                Find::Module(..) => (&[DefKind::Mod], "module"),
                Find::Struct(..) => (&[DefKind::Struct], "struct"),
                _ => (&[DefKind::Trait], "trait"),
            };
            let krate_num = match anchor_crate(tcx, krate) {
                Ok(krate_num) => krate_num,
                Err(resolution) => return resolution,
            };
            match resolve_definition_path(tcx, krate_num, path, want) {
                Some(def) => Resolution::Defs(vec![def]),
                None => {
                    Resolution::Missing(format!("{what} `{}::{}`", krate.name(), path.join("::")))
                }
            }
        }
        Find::DiagnosticType(krate, name) => {
            let krate_num = match anchor_crate(tcx, krate) {
                Ok(krate_num) => krate_num,
                Err(resolution) => return resolution,
            };
            match tcx.get_diagnostic_item(Symbol::intern(name)) {
                Some(def) if def.krate == krate_num && is_type_definition(tcx, def) => {
                    Resolution::Defs(vec![def])
                }
                _ => Resolution::Missing(format!(
                    "type `{name}` (diagnostic item of `{}`)",
                    krate.name()
                )),
            }
        }
        Find::LangType(krate, item) => {
            let krate_num = match anchor_crate(tcx, krate) {
                Ok(krate_num) => krate_num,
                Err(resolution) => return resolution,
            };
            match tcx.lang_items().get(item) {
                Some(def) if def.krate == krate_num && is_type_definition(tcx, def) => {
                    Resolution::Defs(vec![def])
                }
                _ => Resolution::Missing(format!(
                    "type `{}` (lang item of `{}`)",
                    item.name(),
                    krate.name()
                )),
            }
        }
    }
}

/// Every crate named `hashbrown` (the spelling named whatever printed so),
/// checked against the crate std's `HashMap` keeps its table in: a table in a
/// crate of another name is abstracted whole (fail closed), and a `HashMap`
/// whose table crate cannot be found fails closed by the spelling.
fn resolve_hash_map_backend(tcx: TyCtxt<'_>) -> Resolution {
    let named: Vec<DefId> = tcx
        .crates(())
        .iter()
        .filter(|krate| tcx.crate_name(**krate).as_str() == "hashbrown")
        .map(|krate| krate.as_def_id())
        .collect();
    let std = match anchor_crate(tcx, SysrootCrate::Std) {
        Ok(std) => std,
        Err(Resolution::CrateAbsent) if named.is_empty() => return Resolution::CrateAbsent,
        Err(Resolution::CrateAbsent) => return Resolution::Defs(named),
        Err(failure) => return failure,
    };
    let backend = tcx
        .get_diagnostic_item(Symbol::intern("HashMap"))
        .filter(|def| def.krate == std && matches!(tcx.def_kind(*def), DefKind::Struct))
        .and_then(|hash_map| {
            tcx.adt_def(hash_map).all_fields().find_map(|field| {
                match skip_normalization(tcx.type_of(field.did).instantiate_identity()).kind() {
                    ty::Adt(table, _) if table.did().krate != std => Some(table.did().krate),
                    _ => None,
                }
            })
        });
    match backend {
        Some(backend) if named.contains(&backend.as_def_id()) => Resolution::Defs(named),
        Some(backend) => Resolution::FailClosed(
            named.into_iter().chain([backend.as_def_id()]).collect(),
            format!(
                "std's `HashMap` keeps its table in crate `{}`, not `hashbrown`",
                tcx.crate_name(backend)
            ),
        ),
        None => Resolution::Missing("the crate std's `HashMap` keeps its table in".to_string()),
    }
}

fn is_type_definition(tcx: TyCtxt<'_>, def: DefId) -> bool {
    matches!(tcx.def_kind(def), DefKind::Struct | DefKind::Enum | DefKind::Union)
}

/// Where a sysroot crate is in this session.
enum SysrootLookup {
    Found(CrateNum),
    /// No crate of its name is loaded.
    Absent,
    /// A crate of its name is loaded, but none defines its marker lang item.
    Unidentified,
}

/// The sysroot crate `krate`, identified by its marker lang item.
fn sysroot_crate(tcx: TyCtxt<'_>, krate: SysrootCrate) -> SysrootLookup {
    if let Some(def) = tcx.lang_items().get(krate.marker())
        && tcx.crate_name(def.krate).as_str() == krate.name()
    {
        return SysrootLookup::Found(def.krate);
    }
    if tcx.crates(()).iter().any(|candidate| tcx.crate_name(*candidate).as_str() == krate.name()) {
        SysrootLookup::Unidentified
    } else {
        SysrootLookup::Absent
    }
}

/// A core definition supplied by this session's compiler libraries.
///
/// The marker identifies the crate by definition, rather than a printable
/// name. Artifact residency is the same additional origin check used by
/// Trust's `trust-mir-extract::crate_is_sysroot_resident`: an external crate
/// defining its own lang items must not acquire standard-library semantics.
pub(crate) fn is_sysroot_core_definition(tcx: TyCtxt<'_>, def: DefId) -> bool {
    is_sysroot_definition(tcx, def, SysrootCrate::Core)
}

/// An Alloc definition supplied by this session's compiler libraries.
pub(crate) fn is_sysroot_alloc_definition(tcx: TyCtxt<'_>, def: DefId) -> bool {
    is_sysroot_definition(tcx, def, SysrootCrate::Alloc)
}

fn is_sysroot_definition(tcx: TyCtxt<'_>, def: DefId, krate: SysrootCrate) -> bool {
    if def.is_local() {
        return false;
    }
    let SysrootLookup::Found(core) = sysroot_crate(tcx, krate) else {
        return false;
    };
    if def.krate != core {
        return false;
    }
    let source = tcx.used_crate_source(core);
    let library_dir: &std::path::Path = &tcx.sess.target_tlib_path.dir;
    let mut saw_artifact = false;
    for path in source.paths() {
        saw_artifact = true;
        if path.parent() != Some(library_dir) {
            return false;
        }
    }
    saw_artifact
}

/// Authenticate the real definition hierarchy, independently of visible
/// re-exports such as std::slice::Iter for core::slice::iter::Iter.
pub(crate) fn is_sysroot_core_definition_at(tcx: TyCtxt<'_>, def: DefId, path: &[&str]) -> bool {
    is_sysroot_definition_at(tcx, def, SysrootCrate::Core, path)
}

/// Authenticate an Alloc definition independently of visible re-exports.
pub(crate) fn is_sysroot_alloc_definition_at(tcx: TyCtxt<'_>, def: DefId, path: &[&str]) -> bool {
    is_sysroot_definition_at(tcx, def, SysrootCrate::Alloc, path)
}

fn is_sysroot_definition_at(
    tcx: TyCtxt<'_>,
    def: DefId,
    krate: SysrootCrate,
    path: &[&str],
) -> bool {
    if !is_sysroot_definition(tcx, def, krate) {
        return false;
    }
    let mut current = def;
    for expected in path.iter().rev() {
        let key = tcx.def_key(current);
        if key.disambiguated_data.data.get_opt_name().is_none_or(|name| name.as_str() != *expected)
        {
            return false;
        }
        let Some(parent) = key.parent else { return false };
        current = DefId { index: parent, ..current };
    }
    tcx.def_key(current).parent.is_none()
}

/// Native size-hint semantics of the authenticated receiver, not its layout.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum IteratorSizeHintKind {
    Exact,
    Chars,
    Transparent(&'static str),
    Take,
}

pub(crate) fn iterator_size_hint_kind(
    tcx: TyCtxt<'_>,
    mut ty: rustc_public::ty::Ty,
) -> Option<IteratorSizeHintKind> {
    use rustc_public::ty::{RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() {
        ty = inner;
    }
    let TyKind::RigidTy(RigidTy::Adt(adt, _)) = ty.kind() else { return None };
    let def = rustc_internal::internal(tcx, adt.def_id());
    let core_at = |path: &[&str]| is_sysroot_core_definition_at(tcx, def, path);
    if core_at(&["slice", "iter", "Iter"])
        || core_at(&["slice", "iter", "IterMut"])
        || core_at(&["array", "iter", "IntoIter"])
        || is_sysroot_definition_at(
            tcx,
            def,
            SysrootCrate::Alloc,
            &["vec", "into_iter", "IntoIter"],
        )
    {
        Some(IteratorSizeHintKind::Exact)
    } else if core_at(&["str", "iter", "Chars"]) {
        Some(IteratorSizeHintKind::Chars)
    } else if core_at(&["iter", "adapters", "take", "Take"]) {
        Some(IteratorSizeHintKind::Take)
    } else if ["map", "copied", "cloned", "rev"].into_iter().any(|module| {
        let name = match module {
            "map" => "Map",
            "copied" => "Copied",
            "cloned" => "Cloned",
            _ => "Rev",
        };
        core_at(&["iter", "adapters", module, name])
    }) {
        Some(IteratorSizeHintKind::Transparent(
            if core_at(&["iter", "adapters", "copied", "Copied"])
                || core_at(&["iter", "adapters", "cloned", "Cloned"])
            {
                "fld_it"
            } else {
                "fld_iter"
            },
        ))
    } else {
        None
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeIteratorQuery {
    SizeHint,
    Len,
}

/// Preserve only a native Iterator method whose supported receiver model can
/// replay its bounds. A custom implementation or a unit stub keeps its body.
pub(crate) fn is_native_iterator_size_hint(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> bool {
    native_iterator_query(tcx, instance) == Some(NativeIteratorQuery::SizeHint)
}

/// Authenticate native query methods independently of their printed names.
/// Len is admitted only if the expression model also proves exact item
/// cardinality; recognizing the trait here alone does not establish that.
pub(crate) fn native_iterator_query(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> Option<NativeIteratorQuery> {
    use rustc_public::ty::{RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if crate::kani_middle::transform::unit_has_stubs()
        || matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
    {
        return None;
    }
    let def = rustc_internal::internal(tcx, instance.def.def_id());
    if !is_sysroot_core_definition(tcx, def)
        && !is_sysroot_definition(tcx, def, SysrootCrate::Alloc)
    {
        return None;
    }
    let item = tcx.opt_associated_item(def)?;
    let method = item.trait_item_def_id().unwrap_or(def);
    let owner = tcx.trait_of_assoc(method)?;
    let query = match tcx.item_name(method).as_str() {
        "size_hint"
            if is_sysroot_core_definition_at(
                tcx,
                owner,
                &["iter", "traits", "iterator", "Iterator"],
            ) =>
        {
            NativeIteratorQuery::SizeHint
        }
        "len"
            if is_sysroot_core_definition_at(
                tcx,
                owner,
                &["iter", "traits", "exact_size", "ExactSizeIterator"],
            ) =>
        {
            NativeIteratorQuery::Len
        }
        _ => return None,
    };
    let signature = instance.ty().kind().fn_sig()?;
    let signature = signature.skip_binder();
    let [receiver] = signature.inputs() else { return None };
    let TyKind::RigidTy(RigidTy::Ref(_, _, _)) = receiver.kind() else { return None };
    native_size_hint_receiver_supported(tcx, *receiver, 0).then_some(query)
}

fn native_size_hint_receiver_supported(
    tcx: TyCtxt<'_>,
    mut ty: rustc_public::ty::Ty,
    depth: usize,
) -> bool {
    use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
    if depth > 8 {
        return false;
    }
    while let TyKind::RigidTy(RigidTy::Ref(_, inner, _)) = ty.kind() {
        ty = inner;
    }
    match iterator_size_hint_kind(tcx, ty) {
        Some(IteratorSizeHintKind::Transparent(_)) => {
            let TyKind::RigidTy(RigidTy::Adt(_, args)) = ty.kind() else { return false };
            args.0
                .iter()
                .find_map(|arg| match arg {
                    GenericArgKind::Type(inner) => Some(*inner),
                    _ => None,
                })
                .is_some_and(|inner| native_size_hint_receiver_supported(tcx, inner, depth + 1))
        }
        // Take(0) is exact even when its inner iterator is unsupported.
        Some(_) => true,
        None => false,
    }
}

/// The real core str::chars constructor, shared by preprocessing and CHC.
/// A unit stub changes its transitive program and must retain the body.
pub(crate) fn is_core_str_chars(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> bool {
    use rustc_public::{CrateDef, rustc_internal};
    if crate::kani_middle::transform::unit_has_stubs() {
        return false;
    }
    let def = rustc_internal::internal(tcx, instance.def.def_id());
    is_sysroot_core_definition(tcx, def)
        && tcx.get_diagnostic_item(Symbol::intern("str_chars")) == Some(def)
}

/// The actual core Chars::next implementation, not an arbitrary Iterator.
pub(crate) fn is_core_chars_next(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> bool {
    use rustc_public::ty::{RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if crate::kani_middle::transform::unit_has_stubs() {
        return false;
    }
    let def = rustc_internal::internal(tcx, instance.def.def_id());
    if !is_sysroot_core_definition(tcx, def) {
        return false;
    }
    let Some(item) = tcx.opt_associated_item(def) else { return false };
    let method = item.trait_item_def_id().unwrap_or(def);
    let Some(owner) = tcx.trait_of_assoc(method) else { return false };
    if tcx.item_name(method).as_str() != "next"
        || !is_sysroot_core_definition_at(tcx, owner, &["iter", "traits", "iterator", "Iterator"])
    {
        return false;
    }
    let Some(signature) = instance.ty().kind().fn_sig() else { return false };
    let signature = signature.skip_binder();
    let [receiver] = signature.inputs() else { return false };
    let TyKind::RigidTy(RigidTy::Ref(_, chars, rustc_public::mir::Mutability::Mut)) =
        receiver.kind()
    else {
        return false;
    };
    let TyKind::RigidTy(RigidTy::Adt(adt, _)) = chars.kind() else { return false };
    is_sysroot_core_definition_at(
        tcx,
        rustc_internal::internal(tcx, adt.def_id()),
        &["str", "iter", "Chars"],
    )
}

/// Preserve the typed sequence boundaries whose exact CHC models need the
/// original iterator values. Printed instance names are not an identity test.
pub(crate) fn preserve_core_iterator_boundary(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> bool {
    use rustc_public::ty::{FloatTy, GenericArgKind, RigidTy, TyKind};
    use rustc_public::{CrateDef, rustc_internal};
    if is_core_str_chars(tcx, instance)
        || is_core_chars_next(tcx, instance)
        || is_native_iterator_size_hint(tcx, instance)
    {
        return true;
    }
    if crate::kani_middle::transform::unit_has_stubs()
        || matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
    {
        return false;
    }
    let def = rustc_internal::internal(tcx, instance.def.def_id());
    if !is_sysroot_core_definition(tcx, def) {
        return false;
    }
    let Some(item) = tcx.opt_associated_item(def) else { return false };
    let method = item.trait_item_def_id().unwrap_or(def);
    let Some(owner) = tcx.trait_of_assoc(method) else { return false };
    if def != method
        || tcx.item_name(method).as_str() != "eq"
        || !is_sysroot_core_definition_at(tcx, owner, &["iter", "traits", "iterator", "Iterator"])
    {
        return false;
    }
    let Some(signature) = instance.ty().kind().fn_sig() else { return false };
    let signature = signature.skip_binder();
    let [lhs, rhs] = signature.inputs() else { return false };
    if lhs != rhs {
        return false;
    }
    let TyKind::RigidTy(RigidTy::Adt(adt, args)) = lhs.kind() else { return false };
    let adt = rustc_internal::internal(tcx, adt.def_id());
    if is_sysroot_core_definition_at(tcx, adt, &["str", "iter", "Chars"]) {
        return true;
    }
    if !is_sysroot_core_definition_at(tcx, adt, &["slice", "iter", "Iter"])
        && !is_sysroot_core_definition_at(tcx, adt, &["slice", "iter", "IterMut"])
    {
        return false;
    }
    args.0.iter().find_map(|arg| match arg {
        GenericArgKind::Type(elem) => Some(matches!(elem.kind(),
            TyKind::RigidTy(RigidTy::Bool | RigidTy::Char | RigidTy::Int(_) | RigidTy::Uint(_)
                | RigidTy::Float(FloatTy::F32 | FloatTy::F64))
        ) || matches!(elem.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty())),
        _ => None,
    }).unwrap_or(false)
}

/// The crate an anchor lives in, or why it is not looked for: absent (nothing
/// of it can be reached) or unidentified (fail closed).
fn anchor_crate(tcx: TyCtxt<'_>, krate: SysrootCrate) -> Result<CrateNum, Resolution> {
    match sysroot_crate(tcx, krate) {
        SysrootLookup::Found(krate_num) => Ok(krate_num),
        SysrootLookup::Absent => Err(Resolution::CrateAbsent),
        SysrootLookup::Unidentified => Err(Resolution::Missing(format!(
            "crate `{}` (loaded, but none of that name defines its `{}` lang item)",
            krate.name(),
            krate.marker().name()
        ))),
    }
}

/// Follow `path` from the root of `krate` through the items each module
/// defines (not its re-exports), ending at a definition of a kind in `want`.
fn resolve_definition_path(
    tcx: TyCtxt<'_>,
    krate: CrateNum,
    path: &[&str],
    want: &[DefKind],
) -> Option<DefId> {
    let mut current = DefId { krate, index: CRATE_DEF_INDEX };
    for (position, segment) in path.iter().enumerate() {
        let last = position + 1 == path.len();
        current = tcx.module_children(current).iter().find_map(|child| {
            if !child.reexport_chain.is_empty() || child.ident.as_str() != *segment {
                return None;
            }
            let def = child.res.opt_def_id()?;
            let kind = tcx.def_kind(def);
            let fits = if last { want.contains(&kind) } else { kind == DefKind::Mod };
            (fits && tcx.opt_parent(def) == Some(current)).then_some(def)
        })?;
    }
    Some(current)
}

/// Resolved core array comparison identity shared by preprocessing and CHC.
/// Printed paths select the known trait only after real sysroot ownership.
pub(crate) fn authenticated_spec_array_comparison_is_ne(
    tcx: TyCtxt<'_>,
    def: rustc_public::DefId,
) -> Option<bool> {
    let def = rustc_public::rustc_internal::internal(tcx, def);
    if !is_sysroot_core_definition(tcx, def) {
        return None;
    }
    let item = tcx.opt_associated_item(def)?;
    let method = item.trait_item_def_id().unwrap_or(def);
    let owner = tcx.trait_of_assoc(method)?;
    if !is_sysroot_core_definition(tcx, owner) {
        return None;
    }
    if !matches!(
        tcx.def_path_str(owner).as_str(),
        "core::array::equality::SpecArrayEq" | "std::array::equality::SpecArrayEq"
    ) {
        return None;
    }
    match tcx.item_name(method).as_str() {
        "spec_eq" => Some(false),
        "spec_ne" => Some(true),
        _ => None,
    }
}

/// The actual default implementation provides element comparison semantics;
/// neither a trait declaration nor a bytewise specialization establishes it.
pub(crate) fn is_default_spec_array_comparison(
    tcx: TyCtxt<'_>,
    instance: &rustc_public::mir::mono::Instance,
) -> bool {
    use rustc_public::CrateDef;
    if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
        || authenticated_spec_array_comparison_is_ne(tcx, instance.def.def_id()).is_none()
        || crate::kani_middle::transform::instance_has_unit_stub(instance)
    {
        return false;
    }
    let def = rustc_public::rustc_internal::internal(tcx, instance.def.def_id());
    let Some(item) = tcx.opt_associated_item(def) else { return false };
    let defaultness = item.defaultness(tcx);
    item.trait_item_def_id().is_some() && defaultness.is_default() && defaultness.has_value()
}
