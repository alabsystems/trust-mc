// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Compiler-library identities of the wrappers the CHC value models admit.
//! Recognition is independent of layout, allocator, stub and byte-view permission.
//! In particular, a logical payload model does not authenticate physical bytes.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::ty::AdtDef;
use rustc_span::Symbol;

use super::{SysrootCrate, is_sysroot_definition, is_sysroot_definition_at};
use crate::rustc_compat::LangItem;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NativeWrapperKind {
    UnsafeCell,
    Cell,
    RefCell,
    ManuallyDrop,
    MaybeUninit,
    NonZero,
    NonNull,
    Box,
    Rc,
    Arc,
    RcWeak,
    ArcWeak,
    Cow,
    RcInner,
    ArcInner,
    DynMetadata,
    Mutex,
    RwLock,
    MutexGuard,
    RwLockReadGuard,
    RwLockWriteGuard,
    PoisonError,
    Ref,
    RefMut,
    OnceBox,
    AtomicPtr,
    PlatformSync,
    PhantomData,
    Unique,
}

fn compiler_library_crate(tcx: TyCtxt<'_>, def: DefId) -> Option<SysrootCrate> {
    if def.is_local() {
        return None;
    }
    [SysrootCrate::Core, SysrootCrate::Alloc, SysrootCrate::Std]
        .into_iter()
        .find(|krate| is_sysroot_definition(tcx, def, *krate))
}

/// Origin guard for ordinary compiler-library infrastructure fallbacks.
/// A user module printing `alloc::raw_vec` has no allocator-model authority.
pub(crate) fn is_compiler_library_definition(tcx: TyCtxt<'_>, def: DefId) -> bool {
    compiler_library_crate(tcx, def).is_some()
}

/// Match actual definitions, so imports and re-exports preserve their identity
/// while a same-named local or dependency type retains its own ADT.
pub(crate) fn native_wrapper_kind(tcx: TyCtxt<'_>, adt: AdtDef) -> Option<NativeWrapperKind> {
    use NativeWrapperKind as Kind;
    use SysrootCrate::{Alloc, Core, Std};

    let def = rustc_public::rustc_internal::internal(tcx, adt.def_id());
    let origin = compiler_library_crate(tcx, def)?;

    for (krate, item, kind) in [
        (Core, LangItem::UnsafeCell, Kind::UnsafeCell),
        (Core, LangItem::ManuallyDrop, Kind::ManuallyDrop),
        (Core, LangItem::MaybeUninit, Kind::MaybeUninit),
        #[cfg(all(trust_toolchain, version("1.101")))]
        (Core, LangItem::NonNull, Kind::NonNull),
        (Core, LangItem::DynMetadata, Kind::DynMetadata),
        (Core, LangItem::PhantomData, Kind::PhantomData),
        (Alloc, LangItem::OwnedBox, Kind::Box),
    ] {
        if origin == krate && tcx.lang_items().get(item) == Some(def) {
            return Some(kind);
        }
    }
    for (krate, item, kind) in [
        (Core, "Cell", Kind::Cell),
        (Core, "RefCell", Kind::RefCell),
        (Core, "RefCellRef", Kind::Ref),
        (Core, "RefCellRefMut", Kind::RefMut),
        (Core, "NonZero", Kind::NonZero),
        #[cfg(not(all(trust_toolchain, version("1.101"))))]
        (Core, "NonNull", Kind::NonNull),
        (Alloc, "Rc", Kind::Rc),
        (Alloc, "Arc", Kind::Arc),
        (Alloc, "RcWeak", Kind::RcWeak),
        (Alloc, "ArcWeak", Kind::ArcWeak),
        (Alloc, "Cow", Kind::Cow),
        (Std, "Mutex", Kind::Mutex),
        (Std, "RwLock", Kind::RwLock),
        (Std, "MutexGuard", Kind::MutexGuard),
        (Std, "RwLockReadGuard", Kind::RwLockReadGuard),
        (Std, "RwLockWriteGuard", Kind::RwLockWriteGuard),
        (Std, "NonPoisonMutex", Kind::Mutex),
        (Std, "NonPoisonRwLock", Kind::RwLock),
        (Std, "NonPoisonMutexGuard", Kind::MutexGuard),
        (Std, "NonPoisonRwLockReadGuard", Kind::RwLockReadGuard),
        (Std, "NonPoisonRwLockWriteGuard", Kind::RwLockWriteGuard),
    ] {
        if origin == krate && tcx.get_diagnostic_item(Symbol::intern(item)) == Some(def) {
            return Some(kind);
        }
    }

    // These private definitions have no diagnostic item. Use their real
    // definition hierarchy inside the already authenticated library crate.
    let paths: &[(SysrootCrate, &[&str], Kind)] = &[
        (Alloc, &["rcs", "rc", "RcInner"], Kind::RcInner),
        (Alloc, &["rcs", "arc", "ArcInner"], Kind::ArcInner),
        (Std, &["sync", "poison", "PoisonError"], Kind::PoisonError),
        (Std, &["sys", "sync", "once_box", "OnceBox"], Kind::OnceBox),
        // AtomicPtr is a direct type on the frozen oracle. The held Trust
        // library aliases Atomic<*mut T>; that definition must keep its own sort.
        (Core, &["sync", "atomic", "AtomicPtr"], Kind::AtomicPtr),
    ];
    for &(krate, path, kind) in paths {
        if origin == krate && is_sysroot_definition_at(tcx, def, krate, path) {
            return Some(kind);
        }
    }
    // The only stock lane is the frozen oracle. Its real private definitions
    // predate the held Trust library; an absent Unique never acquires authority.
    #[cfg(not(trust_toolchain))]
    for (krate, path, kind) in [
        (Core, &["ptr", "unique", "Unique"][..], Kind::Unique),
        (Alloc, &["rc", "RcInner"][..], Kind::RcInner),
        (Alloc, &["sync", "ArcInner"][..], Kind::ArcInner),
    ] {
        if origin == krate && is_sysroot_definition_at(tcx, def, krate, path) {
            return Some(kind);
        }
    }

    if origin == Std {
        if is_sysroot_definition_at(tcx, def, Std, &["sync", "poison", "Flag"]) {
            return Some(Kind::PlatformSync);
        }
        let mut ancestor = tcx.opt_parent(def);
        while let Some(parent) = ancestor {
            if is_sysroot_definition_at(tcx, parent, Std, &["sys", "sync", "mutex"])
                || is_sysroot_definition_at(tcx, parent, Std, &["sys", "pal", "unix", "sync"])
            {
                return Some(Kind::PlatformSync);
            }
            ancestor = tcx.opt_parent(parent);
        }
    }
    None
}
