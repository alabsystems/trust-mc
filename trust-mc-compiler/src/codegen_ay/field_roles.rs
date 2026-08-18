// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! The per-datatype **field-role table** — `docs/addr-vs-value-conversion-queue.md`
//! §4 item 7.
//!
//! # The fact a datatype declaration used to throw away
//!
//! A CHC datatype is declared from a MIR type. At that moment the encoder knows,
//! for every field, whether it holds an ADDRESS: the field's Rust type is a
//! `&T`, a `*mut T`, a `Box`/`NonNull`/`Unique`/`Rc`/`Arc`/`Weak`, or it is not
//! ([`mir_ty_denotes_address`]). One line later that fact is gone — all that
//! survives into [`ay_bindings::Sort`] is a name and a sort, and `bv64` is
//! equally a `usize`, an index, a capacity or an address.
//!
//! Every consumer downstream then has to *re-derive* what the declaration knew,
//! and the only material left to derive it from is the shape. That is where the
//! guesses come from, and the guesses have a measured history: `DtSolver`'s
//! `fld_scope_len` read as a base address (#4099); `IndexRange`'s `fld_start`,
//! `VecIntoIter`'s `fld_pos` and `Layout`'s `fld_size` all being "the first
//! pointer-width field of a small datatype".
//!
//! The encoder already had **one** field role, spelled as a name: a field
//! literally called `fld_ptr`, which the pointer-wrapper sorts (`Vec`, `String`,
//! `Slice_*`, `Dyn_*`, `RawVec`) declare by hand. That convention is sound —
//! the declaration asserts the role — but it only reaches sorts the encoder
//! writes literally. Datatypes built **from MIR** (structs, enum variants,
//! tuples, closure captures) name their fields after the MIR field, so their
//! address fields are called `fld_inner`, `fld_0`, `cap_2`, `Some_field_0`, and
//! the role is unrecoverable from the sort.
//!
//! This table is the missing half: the same assertion, for the fields whose
//! names are not free to carry it. It is written **where the datatype is
//! declared**, from the field's MIR type, and read by
//! `chc::dyn_coercion::extract_pointer_expr` — which no longer has any lane that
//! guesses.
//!
//! # Keyed by SORT NAME, because that is what an SMT datatype's identity is
//!
//! The table is keyed by `(datatype sort name, field name)`. That is not a
//! weaker key than the ADT it came from: two datatypes that share a sort name
//! ARE the same sort to the solver, so a sort-name collision is already a defect
//! of its own. What this table adds is that such a collision now *announces
//! itself*: recording two different roles for one `(sort, field)` POISONS the
//! entry, and a poisoned entry answers [`None`] forever after — the fail-closed
//! direction. The collision is not hypothetical — `Option<*mut u8>` and
//! `Option<usize>` genuinely produce the same `Option_bv64` sort name — which is
//! why the rule is "poison", not "first writer wins". (That particular arm
//! records nothing today: `extract_pointer_expr` reads the first constructor,
//! which for an Option-like enum is the empty one, so the payload role has no
//! reader. It is annotated in place in `codegen_types_adt_sort.rs`.)
//!
//! # Why a process-global table rather than a field on the context
//!
//! The reader is a free function on an [`ay_bindings::Expr`] — it has a sort and
//! nothing else, which is precisely the problem. Threading a context through
//! ~25 call sites would say the same thing with more ceremony: the table is
//! monotone (insert-only, poison-only), so it has no phase in which a reader can
//! observe a half-written state that a `&mut ChcCtx` would have prevented.
//! Ordering is not a hazard either — an expression of a datatype sort cannot
//! exist before the sort was translated, and the sort is translated by the code
//! that records the roles.
//!
//! # What is NOT in here, and what that costs
//!
//! Only declarations that HAVE a MIR type to read record a role. Sorts the
//! encoder synthesizes without one — stub datatypes, coroutine state machines,
//! reconstructed-by-name sorts — record nothing, and an unrecorded field is
//! [`None`]: not an address, not a value, *unknown*. Consumers must take their
//! demotion lane. That is the honest answer, and it is the one this table exists
//! to make sayable: a demotion is sound, a fabricated address is not.

use std::collections::HashMap;
use std::sync::{LazyLock, RwLock};

use rustc_public::ty::Ty;

use crate::codegen_ay::provenance::mir_ty_denotes_address;

/// What a datatype field holds, as **asserted by the declaration**.
///
/// This is the same distinction [`crate::codegen_ay::provenance::Loc`] and
/// [`crate::codegen_ay::provenance::Val`] draw for expressions, recorded one
/// level up — for a *slot* rather than for a term. A field declared
/// [`FieldRole::Addr`] holds an address in every value of the datatype, because
/// the MIR type of that field says so.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FieldRole {
    /// The field holds an ADDRESS: its MIR type is a reference, a raw pointer,
    /// or a pointer wrapper `translate_adt_ty` flattens to `ptr_sort()`.
    Addr,
    /// The field holds a VALUE. Recorded explicitly rather than by omission:
    /// "declared not-an-address" is what detects a sort-name collision against
    /// an `Addr` recorded by some other instantiation, and omission cannot.
    Value,
}

/// `sort name -> field name -> role`, where a `None` role is a POISONED entry:
/// two declarations disagreed, so nothing may be concluded about that field.
type RoleTable = HashMap<String, HashMap<String, Option<FieldRole>>>;

static DECLARED_FIELD_ROLES: LazyLock<RwLock<RoleTable>> =
    LazyLock::new(|| RwLock::new(HashMap::new()));

/// Record the role of `field_name` in the datatype `dt_name`.
///
/// Idempotent for an agreeing re-declaration (the same datatype is translated
/// many times); a *disagreeing* one poisons the entry, permanently.
pub(crate) fn declare_field_role(dt_name: &str, field_name: &str, role: FieldRole) {
    let Ok(mut table) = DECLARED_FIELD_ROLES.write() else {
        // A poisoned lock means a panic unwound mid-write. Declining to record
        // is the fail-closed direction: readers see `None`.
        return;
    };
    let fields = table.entry(dt_name.to_owned()).or_default();
    match fields.get(field_name) {
        None => {
            fields.insert(field_name.to_owned(), Some(role));
        }
        Some(Some(existing)) if *existing == role => {}
        Some(_) => {
            // Disagreement, or already poisoned. Either way the pair `(sort,
            // field)` no longer identifies one role.
            fields.insert(field_name.to_owned(), None);
        }
    }
}

/// Record the role of a field from the MIR type the declaration was built from.
///
/// The whole point of the table: the caller is the code that *has* the type, so
/// the classification happens once, where the fact is known, instead of at every
/// consumer that later needs it.
///
/// Pass a type already resolved through `ty_with_args` / `resolve_body_ty`; an
/// unresolved `Param` classifies as [`FieldRole::Value`], which is the safe
/// direction (an unknown field is never treated as an address) at the cost of
/// poisoning the entry if a resolved instantiation later declares `Addr`.
pub(crate) fn declare_field_role_from_mir_ty(dt_name: &str, field_name: &str, field_ty: Ty) {
    let role = if mir_ty_denotes_address(field_ty) { FieldRole::Addr } else { FieldRole::Value };
    declare_field_role(dt_name, field_name, role);
}

/// The declared role of `field_name` in `dt_name`, or [`None`] when the
/// declaration did not record one (no MIR type was available) or when two
/// declarations disagreed.
///
/// `None` means **unknown**, never "value": a consumer that needs an address
/// must take its demotion lane rather than fall back to a shape test.
pub(crate) fn declared_field_role(dt_name: &str, field_name: &str) -> Option<FieldRole> {
    let table = DECLARED_FIELD_ROLES.read().ok()?;
    *table.get(dt_name)?.get(field_name)?
}

#[cfg(test)]
mod tests {
    use super::{FieldRole, declare_field_role, declared_field_role};

    // Each test uses its own datatype names: the table is process-global and
    // monotone, and the suite runs in parallel.

    #[test]
    fn unrecorded_field_is_unknown() {
        assert_eq!(declared_field_role("Roles_Unrecorded", "fld_0"), None);
    }

    #[test]
    fn declared_role_is_read_back() {
        declare_field_role("Roles_ReadBack", "fld_0", FieldRole::Addr);
        declare_field_role("Roles_ReadBack", "fld_1", FieldRole::Value);
        assert_eq!(declared_field_role("Roles_ReadBack", "fld_0"), Some(FieldRole::Addr));
        assert_eq!(declared_field_role("Roles_ReadBack", "fld_1"), Some(FieldRole::Value));
        assert_eq!(declared_field_role("Roles_ReadBack", "fld_2"), None);
    }

    #[test]
    fn agreeing_redeclaration_is_idempotent() {
        for _ in 0..3 {
            declare_field_role("Roles_Idempotent", "fld_0", FieldRole::Addr);
        }
        assert_eq!(declared_field_role("Roles_Idempotent", "fld_0"), Some(FieldRole::Addr));
    }

    /// The `Option_bv64` case: two instantiations share a sort name and
    /// disagree, so neither may be trusted. Poisoning is permanent — a later
    /// agreeing re-declaration must not resurrect the entry.
    #[test]
    fn disagreeing_declarations_poison_the_entry() {
        declare_field_role("Roles_Collision", "value", FieldRole::Addr);
        declare_field_role("Roles_Collision", "value", FieldRole::Value);
        assert_eq!(declared_field_role("Roles_Collision", "value"), None);

        declare_field_role("Roles_Collision", "value", FieldRole::Addr);
        assert_eq!(
            declared_field_role("Roles_Collision", "value"),
            None,
            "poisoning must be permanent: the sort name no longer identifies one role"
        );
    }

    #[test]
    fn roles_are_scoped_to_their_datatype() {
        declare_field_role("Roles_ScopeA", "fld_0", FieldRole::Addr);
        declare_field_role("Roles_ScopeB", "fld_0", FieldRole::Value);
        assert_eq!(declared_field_role("Roles_ScopeA", "fld_0"), Some(FieldRole::Addr));
        assert_eq!(declared_field_role("Roles_ScopeB", "fld_0"), Some(FieldRole::Value));
    }
}
