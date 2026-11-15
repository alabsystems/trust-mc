// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! trust-ir's tensor region (wire v67-v70, PKG-U13a-e), which no trust-mc
//! lowering models.
//!
//! The region is nine constructs: the type `Ty::Tensor(elem, rank)` (v67),
//! the six instructions `Inst::TensorContract` (v67), `TensorMap`,
//! `TensorReduce`, `TensorView` (v68), `TensorGather` and `TensorScatter`
//! (v69), the constant `Constant::TensorBlob` (v70) and the module's
//! content-addressed weight table `Module.blobs` (v70). A tensor has no memory
//! layout and no machine lowering, and its values (an extent per axis and a
//! row-major element sequence) have no carrier in either SMT model here: the
//! BMC and CHC lowerings map every value to a bit-vector, Boolean or
//! uninterpreted sort, and none of those denotes a tensor of unknown extents.
//! Read through a placeholder sort, a contraction, map, reduction, view,
//! gather or scatter would be an unconstrained value with no out-of-bounds or
//! extent-agreement obligation, so a property that rests on one could be
//! proved or refuted wrongly.
//!
//! trust-mc therefore refuses the region by name, at every entry, the way it
//! refuses addressable `Ty::Storage` and a typed signature ABI:
//!
//! - the native-bundle boundary refuses the whole bundle before validation
//!   hashes the module
//!   ([`crate::NativeTrustMcBundleError::TensorRegionNotModeled`]);
//! - the shared module input of the diagnostic BMC and CHC lanes refuses the
//!   whole module before any function, array or SSA symbol is translated;
//! - each exhaustive trust-ir match in the translators has its own arm for the
//!   six instructions, the tensor type and the blob constant, which fails
//!   closed by name if a caller ever bypasses those boundaries
//!   ([`crate::TrustIrChcUnsupportedReason::TensorRegion`], the BMC lane's
//!   unsupported-semantics violation, `checked_ty_to_sort`'s
//!   `UnsupportedSort::Tensor`, `const_to_expr`'s `None`);
//! - the driver's proof-authority input gate refuses the region before any
//!   instruction reaches its admitting arm.
//!
//! Every stored occurrence is read, used or not: an unused tensor row in the
//! type table, a signature, an aggregate field, a global and a blob row no
//! constant names all still put the module outside what trust-mc models, and
//! skipping one would turn an unsupported module into an empty-success batch.

use std::collections::BTreeSet;
use std::ops::ControlFlow;

use trust_ir::constant::Constant;
use trust_ir::pred::{Pred, Universe};
use trust_ir::{Inst, Module, Ty};

/// One construct of trust-ir's tensor region, named as trust-ir spells it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TensorConstruct {
    /// `Ty::Tensor(elem, rank)` (wire v67), anywhere a type is stored.
    TensorType,
    /// `Inst::TensorContract` (wire v67).
    TensorContract,
    /// `Inst::TensorMap` (wire v68).
    TensorMap,
    /// `Inst::TensorReduce` (wire v68).
    TensorReduce,
    /// `Inst::TensorView` (wire v68).
    TensorView,
    /// `Inst::TensorGather` (wire v69).
    TensorGather,
    /// `Inst::TensorScatter` (wire v69).
    TensorScatter,
    /// `Constant::TensorBlob` (wire v70), at any depth of a stored constant:
    /// an `Inst::Const` value, an `Inst::Switch` case value, a global
    /// initializer, a `Universe::Members` or a `Pred::FiniteSet` member.
    TensorBlobConstant,
    /// A non-empty `Module.blobs` weight table (wire v70).
    BlobTable,
}

impl TensorConstruct {
    /// trust-ir's own spelling of the construct.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::TensorType => "Ty::Tensor",
            Self::TensorContract => "Inst::TensorContract",
            Self::TensorMap => "Inst::TensorMap",
            Self::TensorReduce => "Inst::TensorReduce",
            Self::TensorView => "Inst::TensorView",
            Self::TensorGather => "Inst::TensorGather",
            Self::TensorScatter => "Inst::TensorScatter",
            Self::TensorBlobConstant => "Constant::TensorBlob",
            Self::BlobTable => "Module.blobs",
        }
    }

    /// The tensor instruction `inst` is, or `None` for every other
    /// instruction. Only the instruction itself is named here: the types it
    /// spells are [`inst_spells_tensor_type`]'s, a blob constant
    /// [`inst_carries_tensor_blob`]'s.
    #[must_use]
    pub fn of_inst(inst: &Inst) -> Option<Self> {
        match inst {
            Inst::TensorContract { .. } => Some(Self::TensorContract),
            Inst::TensorMap { .. } => Some(Self::TensorMap),
            Inst::TensorReduce { .. } => Some(Self::TensorReduce),
            Inst::TensorView { .. } => Some(Self::TensorView),
            Inst::TensorGather { .. } => Some(Self::TensorGather),
            Inst::TensorScatter { .. } => Some(Self::TensorScatter),
            _ => None,
        }
    }
}

/// Whether `ty` is, or holds as an inline child, a `Ty::Tensor`. Table
/// references are not followed.
pub(crate) fn ty_holds_tensor(ty: &Ty) -> bool {
    let mut tensor = false;
    ty.visit_types(|child| tensor |= matches!(child, Ty::Tensor(..)));
    tensor
}

/// The tensor-region construct a `Const { ty, value }` builds, or `None`: a
/// `Constant::TensorBlob` at any depth of `value`, else a `Ty::Tensor` in `ty`.
pub(crate) fn const_tensor_construct(ty: &Ty, value: &Constant) -> Option<TensorConstruct> {
    if constant_carries_tensor_blob(value) {
        Some(TensorConstruct::TensorBlobConstant)
    } else if ty_holds_tensor(ty) {
        Some(TensorConstruct::TensorType)
    } else {
        None
    }
}

/// Whether `inst` spells a `Ty::Tensor` among its types (inline children and a
/// `TensorMap` body's node types included). Table references are not followed.
#[must_use]
pub fn inst_spells_tensor_type(inst: &Inst) -> bool {
    let mut tensor = false;
    inst.visit_types(|ty| tensor |= matches!(ty, Ty::Tensor(..)));
    tensor
}

impl std::fmt::Display for TensorConstruct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

/// Whether `inst` stores a `Constant::TensorBlob` at any depth of a constant
/// it carries: an `Inst::Const` value or an `Inst::Switch` case value, the two
/// instruction fields trust-ir stores a `Constant` in. A case constant carries
/// no type, and trust-ir checks a case's shape only at an integer or `char`
/// selector, so a blob case at a `bool` selector validates; it is read here.
#[must_use]
pub fn inst_carries_tensor_blob(inst: &Inst) -> bool {
    match inst {
        Inst::Const { value, .. } => constant_carries_tensor_blob(value),
        Inst::Switch { cases, .. } => {
            cases.iter().any(|case| constant_carries_tensor_blob(&case.value))
        }
        _ => false,
    }
}

/// Whether `value` is, or holds at any depth, a `Constant::TensorBlob`.
#[must_use]
pub fn constant_carries_tensor_blob(value: &Constant) -> bool {
    value
        .try_visit_constants(|constant| {
            if matches!(constant, Constant::TensorBlob { .. }) {
                ControlFlow::Break(())
            } else {
                ControlFlow::Continue(())
            }
        })
        .is_break()
}

/// Every tensor-region construct `module` stores, in [`TensorConstruct`]
/// order, or an empty set when it stores none.
///
/// Linear in the module: every stored type (tables, signatures, aggregate
/// fields, captures, globals, drop-glue keys, block parameters and instruction
/// types, through `Module::visit_types`), every instruction, every stored
/// constant (an `Inst::Const` value, an `Inst::Switch` case value, a global
/// initializer, a `Universe::Members` or `Pred::FiniteSet` member) and the blob
/// table.
#[must_use]
pub fn tensor_region_constructs(module: &Module) -> BTreeSet<TensorConstruct> {
    let mut found = BTreeSet::new();
    if !module.blobs.is_empty() {
        found.insert(TensorConstruct::BlobTable);
    }
    module.visit_types(|ty| {
        if matches!(ty, Ty::Tensor(..)) {
            found.insert(TensorConstruct::TensorType);
        }
    });
    let table_blob = module
        .globals
        .iter()
        .filter_map(|global| global.initializer.as_ref())
        .chain(module.universes.iter().flat_map(|universe| match universe {
            Universe::Members(members) => members.as_slice(),
            Universe::IntRange { .. } => &[],
        }))
        .chain(module.predicates.iter().flat_map(|predicate| match predicate {
            Pred::FiniteSet(members) => members.as_slice(),
            Pred::Interval { .. }
            | Pred::InUniverse(..)
            | Pred::NonZero
            | Pred::NonNull
            | Pred::Conj(_)
            | Pred::Disj(_)
            | Pred::Top
            | Pred::Bottom => &[],
        }))
        .any(constant_carries_tensor_blob);
    if table_blob {
        found.insert(TensorConstruct::TensorBlobConstant);
    }
    for node in
        module.functions.iter().flat_map(|function| &function.blocks).flat_map(|block| &block.body)
    {
        if let Some(construct) = TensorConstruct::of_inst(&node.inst) {
            found.insert(construct);
        }
        if inst_carries_tensor_blob(&node.inst) {
            found.insert(TensorConstruct::TensorBlobConstant);
        }
    }
    found
}

/// The names of `constructs`, comma-separated, in [`TensorConstruct`] order.
#[must_use]
pub fn tensor_construct_names(constructs: &BTreeSet<TensorConstruct>) -> String {
    constructs.iter().map(|construct| construct.name()).collect::<Vec<_>>().join(", ")
}

/// The refusal text for a module that stores `constructs` (non-empty).
pub(crate) fn tensor_region_refusal_message(constructs: &BTreeSet<TensorConstruct>) -> String {
    format!(
        "the trust-ir tensor region ({}) has no SMT value model in trust_mc",
        tensor_construct_names(constructs)
    )
}
