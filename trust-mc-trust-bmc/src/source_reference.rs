// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Live source claims, separate from public IR annotations and pointer bits.

use std::collections::BTreeMap;

use thiserror::Error;
use trust_ir::{
    BlockId, FuncId, Inst, Module, NativeVerificationBundle, ProofAnnotation,
    SourceGenerationAuthority, Ty, ValueId,
};

/// The source entry parameter refers to an initialized logical scalar/product.
/// In a callee summary this is a REQUIREMENT on the actual, never an assumption.
#[derive(Debug, PartialEq)]
pub struct SourceReferenceParameterFact {
    pub function: FuncId,
    pub parameter_index: u32,
    pub value: ValueId,
    pub pointee: Ty,
}

/// One exact nonvolatile source reference load is eligible for a typed pointee
/// proof. The consumer must still establish initialization in this invocation;
/// this record does not make an entry premise permanent across memory writes.
#[derive(Debug, PartialEq)]
pub struct SourceReferenceLoadFact {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction_index: u32,
    pub result: ValueId,
    pub pointer: ValueId,
    pub pointee: Ty,
}

/// Exact erasure of an independently certified initialized reference VALUE.
/// Initially issued only for the source compiler's promoted empty-closure
/// shared-borrow certificate. This conveys no address, pointee, memory or
/// ValidBorrow permission; the opaque pointer bits remain unconstrained.
#[derive(Debug, PartialEq)]
pub struct SourceReferenceValueFact {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction_index: u32,
    pub result: ValueId,
}

/// Exact erasure of an independently certified INITIALIZED fresh value: one
/// marked `Undef` site that the source compiler certifies stands, in every
/// execution reaching it, for a valid value of its source type whose every
/// logical lane is initialized. Issued only from the audited live source seam
/// for sites whose source meaning establishes that (for example the result of
/// a call that returned normally whose source return type is `bool` or an
/// integer: such a type's validity requires initialized bits). It conveys NO
/// value: the SMT term stays exactly as unconstrained as before, so it supplies
/// no range, equality, address, pointee, memory or `ValidBorrow` fact, and it
/// never discharges an assertion by itself. A bare `FreshSymbolicHavoc` marker,
/// generic havoc or public/replayed data establishes nothing. Pointer values
/// are excluded: their only value record is [`SourceReferenceValueFact`].
#[derive(Debug, PartialEq)]
pub struct SourceInitializedValueFact {
    pub function: FuncId,
    pub block: BlockId,
    pub instruction_index: u32,
    pub result: ValueId,
}

/// Exact erasure of an independently certified INITIALIZED by-value entry
/// parameter: `params[parameter_index] == (value, ty)` of `function`'s entry
/// block, a non-pointer parameter the source compiler certifies is, in every
/// execution that enters the function, a valid value of a source type whose
/// validity initializes every logical lane of `ty` (for example a fieldless
/// enum: its only lane is the discriminant, which every valid value holds).
/// Read ONLY for a ROOT translation of `function` (a callee's parameter still
/// takes its definedness from the caller's actual argument). It conveys NO
/// value: the lanes stay exactly as unconstrained as before. Pointers are
/// excluded: their record is [`SourceReferenceParameterFact`].
#[derive(Debug, PartialEq)]
pub struct SourceInitializedParameterFact {
    pub function: FuncId,
    pub parameter_index: u32,
    pub value: ValueId,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SourceReferenceFactsError {
    #[error("source reference facts require the current exact live bundle authority")]
    AuthorityMismatch,
    #[error("invalid source reference parameter fact: {0}")]
    Parameter(&'static str),
    #[error("invalid source reference-load fact: {0}")]
    Load(&'static str),
    #[error("invalid source reference-value fact: {0}")]
    ReferenceValue(&'static str),
    #[error("invalid source initialized-value fact: {0}")]
    InitializedValue(&'static str),
    #[error("invalid source initialized-parameter fact: {0}")]
    InitializedParameter(&'static str),
}

/// Non-cloneable, non-serializable claims borrowed from ONE live source seam.
/// Neither a saved diagnostic record nor `ValidBorrow` can construct this context.
pub struct SourceReferenceFacts<'a> {
    bundle: &'a NativeVerificationBundle,
    authority: &'a SourceGenerationAuthority,
    parameters: BTreeMap<(FuncId, ValueId), SourceReferenceParameterFact>,
    loads: BTreeMap<(FuncId, ValueId), SourceReferenceLoadFact>,
    values: BTreeMap<(FuncId, ValueId), SourceReferenceValueFact>,
    initialized: BTreeMap<(FuncId, ValueId), SourceInitializedValueFact>,
    initialized_parameters: BTreeMap<(FuncId, ValueId), SourceInitializedParameterFact>,
}

impl<'a> SourceReferenceFacts<'a> {
    /// Bind explicit source claims to this exact live bundle AND authority.
    ///
    /// # Semantic TCB contract
    /// Call only at the audited live source-lowering seam. The producer must prove
    /// genuine reference provenance and initialized INTEGER/BOOL pointees before
    /// type erasure. A finite Struct/Tuple product additionally requires an opaque
    /// current-session, body-bound original-source-type certificate for its full
    /// logical field tree, excluding unions, MaybeUninit/UnsafeCell and erased
    /// wrappers. Reconcile every final SSA site and withdraw claims when final
    /// caller/reach analysis withholds that provenance. Public aggregate metadata,
    /// optimization attributes and `ValidBorrow` alone establish no such property.
    /// Structural checks below bind
    /// sites and types; they do NOT prove the source truth of the supplied claims.
    /// Both borrows last for the context's lifetime; cloning/replaying a bundle,
    /// substituting authority, or changing content cannot carry this context.
    pub fn from_live_source_lowering(
        bundle: &'a NativeVerificationBundle,
        authority: &'a SourceGenerationAuthority,
        parameters: Vec<SourceReferenceParameterFact>,
        loads: Vec<SourceReferenceLoadFact>,
    ) -> Result<Self, SourceReferenceFactsError> {
        Self::from_live_source_lowering_with_values(
            bundle,
            authority,
            parameters,
            loads,
            Vec::new(),
        )
    }

    /// The existing reference context plus separately certified reference-value
    /// erasures. The same semantic-TCB source contract applies: each value record
    /// must come from the compiler's sealed, body/occurrence-bound certificate of
    /// a promoted empty-closure shared borrow, reconciled to the final SSA node.
    /// A bare marker, generic havoc, FnDef or arbitrary pointer is not evidence.
    /// This only selects the independently audited initialized-value
    /// over-approximation; it imports no pointer-bit constraint, memory fact or
    /// counterexample-grounding authority. Public/replayed bundles remain denied.
    pub fn from_live_source_lowering_with_values(
        bundle: &'a NativeVerificationBundle,
        authority: &'a SourceGenerationAuthority,
        parameters: Vec<SourceReferenceParameterFact>,
        loads: Vec<SourceReferenceLoadFact>,
        values: Vec<SourceReferenceValueFact>,
    ) -> Result<Self, SourceReferenceFactsError> {
        Self::from_live_source_lowering_with_initialized_values(
            bundle,
            authority,
            parameters,
            loads,
            values,
            Vec::new(),
            Vec::new(),
        )
    }

    /// The reference context plus separately certified INITIALIZED fresh values
    /// ([`SourceInitializedValueFact`]) and INITIALIZED by-value root parameters
    /// ([`SourceInitializedParameterFact`]). The same semantic-TCB source
    /// contract applies: each record must come from the compiler's own
    /// certificate, made while the source type and the site's source meaning
    /// were visible, that the marked `Undef` (or the entry parameter) stands for
    /// an initialized value of a supported type (`bool`, an integer, `Unit`, or a
    /// bounded Struct/Tuple of them; a value record also a `Sequence` of
    /// `bool`/integers), reconciled to the final SSA node. This only selects the
    /// initialized reading of that one value; the value itself stays
    /// unconstrained. Public/replayed bundles remain denied.
    pub fn from_live_source_lowering_with_initialized_values(
        bundle: &'a NativeVerificationBundle,
        authority: &'a SourceGenerationAuthority,
        parameters: Vec<SourceReferenceParameterFact>,
        loads: Vec<SourceReferenceLoadFact>,
        values: Vec<SourceReferenceValueFact>,
        initialized: Vec<SourceInitializedValueFact>,
        initialized_parameters: Vec<SourceInitializedParameterFact>,
    ) -> Result<Self, SourceReferenceFactsError> {
        if !authority.authorizes_bundle(bundle) {
            return Err(SourceReferenceFactsError::AuthorityMismatch);
        }
        let functions: BTreeMap<_, _> =
            bundle.module.functions.iter().map(|function| (function.id, function)).collect();
        let blocks: BTreeMap<_, _> = bundle
            .module
            .functions
            .iter()
            .flat_map(|function| {
                function.blocks.iter().map(move |block| ((function.id, block.id), block))
            })
            .collect();
        let mut result = Self {
            bundle,
            authority,
            parameters: BTreeMap::new(),
            loads: BTreeMap::new(),
            values: BTreeMap::new(),
            initialized: BTreeMap::new(),
            initialized_parameters: BTreeMap::new(),
        };
        for fact in parameters {
            let function = functions
                .get(&fact.function)
                .ok_or(SourceReferenceFactsError::Parameter("missing function"))?;
            let entry = blocks
                .get(&(fact.function, function.entry))
                .ok_or(SourceReferenceFactsError::Parameter("missing entry"))?;
            let Some((value, Ty::Ptr)) = entry.params.get(fact.parameter_index as usize) else {
                return Err(SourceReferenceFactsError::Parameter(
                    "not a thin-pointer entry parameter",
                ));
            };
            if *value != fact.value || !supported_pointee(&bundle.module, &fact.pointee) {
                return Err(SourceReferenceFactsError::Parameter("value/type mismatch"));
            }
            if result.parameters.insert((fact.function, fact.value), fact).is_some() {
                return Err(SourceReferenceFactsError::Parameter("duplicate parameter"));
            }
        }
        for fact in loads {
            let node = blocks
                .get(&(fact.function, fact.block))
                .and_then(|block| block.body.get(fact.instruction_index as usize))
                .ok_or(SourceReferenceFactsError::Load("missing instruction"))?;
            if !matches!(&node.inst, Inst::Load { ty, ptr, volatile: false, align: None }
                if *ptr == fact.pointer && *ty == fact.pointee
                    && supported_pointee(&bundle.module, ty))
                || node.results.as_slice() != [fact.result]
                || !node.proofs.contains(&ProofAnnotation::ValidBorrow)
            {
                return Err(SourceReferenceFactsError::Load(
                    "site/result/pointer/type/access mismatch",
                ));
            }
            if result.loads.insert((fact.function, fact.result), fact).is_some() {
                return Err(SourceReferenceFactsError::Load("duplicate result"));
            }
        }
        for fact in result.loads.values() {
            if result
                .parameters
                .get(&(fact.function, fact.pointer))
                .is_some_and(|parameter| parameter.pointee != fact.pointee)
            {
                return Err(SourceReferenceFactsError::Load("entry pointee/type mismatch"));
            }
        }
        for fact in values {
            let node = blocks
                .get(&(fact.function, fact.block))
                .and_then(|block| block.body.get(fact.instruction_index as usize))
                .ok_or(SourceReferenceFactsError::ReferenceValue("missing instruction"))?;
            if !matches!(&node.inst, Inst::Undef { ty: Ty::Ptr })
                || node.results.as_slice() != [fact.result]
                || !node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc)
            {
                return Err(SourceReferenceFactsError::ReferenceValue(
                    "not the exact marked single-result opaque pointer site",
                ));
            }
            let key = (fact.function, fact.result);
            if result.parameters.contains_key(&key)
                || result.loads.contains_key(&key)
                || result.values.insert(key, fact).is_some()
            {
                return Err(SourceReferenceFactsError::ReferenceValue(
                    "duplicate/conflicting value",
                ));
            }
        }
        for fact in initialized {
            let node = blocks
                .get(&(fact.function, fact.block))
                .and_then(|block| block.body.get(fact.instruction_index as usize))
                .ok_or(SourceReferenceFactsError::InitializedValue("missing instruction"))?;
            if !matches!(&node.inst, Inst::Undef { ty }
                    if initialized_value_type(&bundle.module, ty))
                || node.results.as_slice() != [fact.result]
                || !node.proofs.contains(&ProofAnnotation::FreshSymbolicHavoc)
            {
                return Err(SourceReferenceFactsError::InitializedValue(
                    "not the exact marked single-result supported-type fresh value site",
                ));
            }
            let key = (fact.function, fact.result);
            if result.parameters.contains_key(&key)
                || result.loads.contains_key(&key)
                || result.values.contains_key(&key)
                || result.initialized.insert(key, fact).is_some()
            {
                return Err(SourceReferenceFactsError::InitializedValue(
                    "duplicate/conflicting value",
                ));
            }
        }
        for fact in initialized_parameters {
            let function = functions
                .get(&fact.function)
                .ok_or(SourceReferenceFactsError::InitializedParameter("missing function"))?;
            let entry = blocks
                .get(&(fact.function, function.entry))
                .ok_or(SourceReferenceFactsError::InitializedParameter("missing entry"))?;
            let Some((value, ty)) = entry.params.get(fact.parameter_index as usize) else {
                return Err(SourceReferenceFactsError::InitializedParameter(
                    "not an entry parameter",
                ));
            };
            if *value != fact.value || !supported_pointee(&bundle.module, ty) {
                return Err(SourceReferenceFactsError::InitializedParameter(
                    "value/type mismatch",
                ));
            }
            let key = (fact.function, fact.value);
            if result.parameters.contains_key(&key)
                || result.loads.contains_key(&key)
                || result.values.contains_key(&key)
                || result.initialized.contains_key(&key)
                || result.initialized_parameters.insert(key, fact).is_some()
            {
                return Err(SourceReferenceFactsError::InitializedParameter(
                    "duplicate/conflicting parameter",
                ));
            }
        }
        Ok(result)
    }

    /// Diagnostic inventory only; this count grants no source or proof authority.
    pub fn initialized_value_count(&self) -> usize {
        self.initialized.len()
    }

    /// Diagnostic inventory only; this count grants no source or proof authority.
    pub fn initialized_parameter_count(&self) -> usize {
        self.initialized_parameters.len()
    }

    /// Diagnostic inventory only; this count grants no source or proof authority.
    pub fn reference_value_count(&self) -> usize {
        self.values.len()
    }

    /// Exact identity as well as current live authority, not matching public bytes.
    pub fn authorizes_bundle(
        &self,
        bundle: &NativeVerificationBundle,
        authority: &SourceGenerationAuthority,
    ) -> bool {
        std::ptr::eq(self.bundle, bundle)
            && std::ptr::eq(self.authority, authority)
            && authority.authorizes_bundle(bundle)
    }

    pub(crate) fn belongs_to(&self, bundle: &NativeVerificationBundle) -> bool {
        self.authorizes_bundle(bundle, self.authority)
    }

    pub(crate) fn matches_module(&self, module: &Module) -> bool {
        std::ptr::eq(&self.bundle.module, module)
    }

    pub(crate) fn parameter(&self, function: FuncId, value: ValueId) -> Option<&Ty> {
        self.parameters.get(&(function, value)).map(|fact| &fact.pointee)
    }

    pub(crate) fn load(
        &self,
        function: FuncId,
        result: ValueId,
        path: &[u32],
    ) -> Option<&SourceReferenceLoadFact> {
        let fact = self.loads.get(&(function, result))?;
        if path.len() > MAX_POINTEE_DEPTH {
            return None;
        }
        let mut selected = &fact.pointee;
        for field in path {
            selected = match selected {
                Ty::Tuple(fields) => fields.get(*field as usize)?,
                Ty::Struct(id) => {
                    let definition = self.bundle.module.structs.get(id.as_usize())?;
                    if definition.id != *id {
                        return None;
                    }
                    &definition.fields.get(*field as usize)?.ty
                }
                _ => return None,
            };
        }
        Some(fact)
    }

    pub(crate) fn reference_value(
        &self,
        function: FuncId,
        result: ValueId,
    ) -> Option<&SourceReferenceValueFact> {
        self.values.get(&(function, result))
    }

    pub(crate) fn initialized_value(
        &self,
        function: FuncId,
        result: ValueId,
    ) -> Option<&SourceInitializedValueFact> {
        self.initialized.get(&(function, result))
    }

    pub(crate) fn initialized_parameter(
        &self,
        function: FuncId,
        value: ValueId,
    ) -> Option<&SourceInitializedParameterFact> {
        self.initialized_parameters.get(&(function, value))
    }
}

const MAX_POINTEE_DEPTH: usize = 64;
const MAX_POINTEE_NODES: usize = 16_384;

/// The types an initialized-value record may name: the reference pointee shape
/// (`bool`, integers, `Unit`, bounded Struct/Tuple products of them) plus a
/// `Sequence` whose element is `bool` or an integer. Pointers, fat pointers,
/// floats, `Char`, arrays, enums, closures, records, sets, maps and unions are
/// refused. A bounded logical shape check only, like [`supported_pointee`]: the
/// live-source contract, not this check, establishes initializedness.
fn initialized_value_type(module: &Module, ty: &Ty) -> bool {
    match ty {
        Ty::Sequence(element) => module
            .types
            .get(element.as_usize())
            .is_some_and(|element| matches!(element, Ty::Bool) || element.is_integer()),
        ty => supported_pointee(module, ty),
    }
}

/// A bounded logical shape check, not evidence about a Rust source type or its
/// padding. Only the separate live-source contract establishes initializedness.
fn supported_pointee(module: &Module, ty: &Ty) -> bool {
    fn walk(module: &Module, ty: &Ty, depth: usize, work: &mut usize) -> bool {
        if depth == 0 || *work == 0 {
            return false;
        }
        *work -= 1;
        match ty {
            Ty::Bool | Ty::Unit => true,
            ty if ty.is_integer() => true,
            Ty::Tuple(fields) => fields.iter().all(|field| walk(module, field, depth - 1, work)),
            Ty::Struct(id) => module.structs.get(id.as_usize()).is_some_and(|definition| {
                definition.id == *id
                    && definition
                        .fields
                        .iter()
                        .all(|field| walk(module, &field.ty, depth - 1, work))
            }),
            _ => false,
        }
    }
    let mut work = MAX_POINTEE_NODES;
    walk(module, ty, MAX_POINTEE_DEPTH, &mut work)
}
