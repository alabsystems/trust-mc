// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed trust_ir semantics coverage metadata for production routing.

use trust_ir::inst::{BinOp, Inst};

use trust_ir::dialect::trust_rust::is_thread_local_addr;

/// Coarse trust_ir semantics families tracked by the BMC translator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SemanticsFamily {
    IntegerArithmetic,
    Division,
    MemoryProvenance,
    SafetyProperties,
    ControlFlow,
    Select,
    Calls,
    Casts,
    Aggregates,
    Floats,
    Atomics,
    ProofAnnotations,
}

/// Current support status for a trust_ir semantics family.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SemanticsStatus {
    /// Translator emits typed constraints with the intended semantics.
    Implemented,
    /// Translator emits conservative typed constraints but is not complete.
    Conservative,
    /// Translator emits a typed, always-failing unsupported-semantics VC.
    FailClosedUnsupported,
    /// Metadata is preserved but cannot discharge obligations without checked evidence.
    MetadataOnly,
}

/// One row in the public trust_ir semantics coverage matrix.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SemanticsCoverage {
    pub family: SemanticsFamily,
    pub status: SemanticsStatus,
    pub notes: &'static str,
}

/// Public trust_ir semantics coverage matrix.
///
/// This is intentionally typed data, not a parsed report string, so production
/// callers can route or reject trust_ir inputs without depending on mutable SMT-LIB
/// text.
pub const SEMANTICS_COVERAGE: &[SemanticsCoverage] = &[
    SemanticsCoverage {
        family: SemanticsFamily::IntegerArithmetic,
        status: SemanticsStatus::Implemented,
        notes: "integer add/sub/mul/div/rem/bitwise plus overflow/div-zero obligations",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Division,
        status: SemanticsStatus::Implemented,
        notes: "integer division and remainder emit typed signed/unsigned div-zero plus signed-overflow obligations",
    },
    SemanticsCoverage {
        family: SemanticsFamily::MemoryProvenance,
        status: SemanticsStatus::Conservative,
        notes: "BMC uses array-backed regions; CHC diagnostic lowering has stack/borrow/provenance shortcuts (including ValidBorrow) that are non-authoritative, while the driver proof-grade bundle gate rejects public borrow, alloca, GEP, and unchecked pointer-cast shapes",
    },
    SemanticsCoverage {
        family: SemanticsFamily::SafetyProperties,
        status: SemanticsStatus::Implemented,
        notes: "assume/assert/return/unreachable produce typed constraints and violations",
    },
    SemanticsCoverage {
        family: SemanticsFamily::ControlFlow,
        status: SemanticsStatus::Conservative,
        notes: "CHC lowers branch, conditional branch, and scalar switch edges; BMC lowers acyclic CFGs (branch/conditional branch/scalar switch with guarded paths and block-parameter joins) and fails closed on loops (back-edges) and malformed blocks",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Select,
        status: SemanticsStatus::Implemented,
        notes: "single-instruction value selection is lowered to typed ite expressions",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Calls,
        status: SemanticsStatus::Conservative,
        notes: "bounded acyclic scalar direct calls inline typed return/safety summaries; the diagnostic name-only wrapping intrinsic shortcut is non-authoritative and rejected by the driver proof-grade gate; unknown, recursive, and indirect calls fail closed",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Casts,
        status: SemanticsStatus::Conservative,
        notes: "diagnostic lanes lower several integer, bool, and pointer/newtype casts conservatively; the driver proof-grade bundle gate currently admits only integer Trunc/ZExt/SExt and rejects provenance-, aggregate-, transmute-, and float-sensitive casts",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Aggregates,
        status: SemanticsStatus::Conservative,
        notes: "scalar struct/tuple field extract/insert lowers structurally; CHC diagnostic ExtractElement havocs the value and relies on an external bounds assertion, so the driver proof-grade bundle gate rejects it until bounds are internally bound",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Floats,
        status: SemanticsStatus::FailClosedUnsupported,
        notes: "float constants lower to exact IEEE-754 bit patterns (fail-closed when no exact encoding exists); floating arithmetic and comparisons bind unconstrained placeholders and emit unsupported-semantics VCs — never bit-level arithmetic or bit-equality",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Atomics,
        status: SemanticsStatus::Conservative,
        notes: "atomic load/store/rmw/cmpxchg use sequential array-backed semantics; fences fail closed",
    },
    SemanticsCoverage {
        family: SemanticsFamily::ProofAnnotations,
        status: SemanticsStatus::Conservative,
        notes: "BMC safety claims are metadata-only; CHC diagnostic lowering consumes Wrapping and ValidBorrow; the ordinary proof-grade gate rejects both, the exact live-source authority admits only Wrapping, and ValidBorrow remains rejected",
    },
];

/// Return the coverage row for a family.
#[must_use]
pub fn coverage_for_family(family: SemanticsFamily) -> &'static SemanticsCoverage {
    SEMANTICS_COVERAGE
        .iter()
        .find(|row| row.family == family)
        .expect("every SemanticsFamily must have a coverage row")
}

/// Classify the semantics family of a trust_ir instruction.
#[must_use]
pub fn family_for_inst(inst: &Inst) -> SemanticsFamily {
    match inst {
        Inst::BinOp { op, .. } => match op {
            BinOp::FAdd | BinOp::FSub | BinOp::FMul | BinOp::FDiv | BinOp::FRem => {
                SemanticsFamily::Floats
            }
            BinOp::SDiv | BinOp::UDiv | BinOp::SRem | BinOp::URem => SemanticsFamily::Division,
            _ => SemanticsFamily::IntegerArithmetic,
        },
        Inst::Load { .. }
        | Inst::Store { .. }
        | Inst::Alloca { .. }
        | Inst::HeapAlloc { .. }
        | Inst::GEP { .. }
        | Inst::PtrData { .. }
        | Inst::PtrMetadata { .. }
        | Inst::PtrFromParts { .. }
        | Inst::NullPtr
        | Inst::GlobalAddr { .. }
        | Inst::Undef { .. }
        | Inst::Borrow { .. }
        | Inst::BorrowMut { .. }
        | Inst::EndBorrow { .. }
        | Inst::Retain { .. }
        | Inst::Release { .. }
        | Inst::IsUnique { .. }
        | Inst::Dealloc { .. } => SemanticsFamily::MemoryProvenance,
        Inst::DialectOp(op) if is_thread_local_addr(op) => SemanticsFamily::MemoryProvenance,
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Invoke { .. }
        | Inst::Resume { .. } => SemanticsFamily::ControlFlow,
        Inst::Call { .. } | Inst::CallIndirect { .. } => SemanticsFamily::Calls,
        Inst::Cast { .. } => SemanticsFamily::Casts,
        Inst::ExtractField { .. }
        | Inst::InsertField { .. }
        | Inst::ExtractElement { .. }
        | Inst::InsertElement { .. }
        | Inst::SeqMapAddK { .. }
        | Inst::SeqMapNot { .. }
        | Inst::SeqMap { .. }
        | Inst::OpenFrame { .. }
        | Inst::BindSlot { .. }
        | Inst::LoadSlot { .. }
        | Inst::CloseFrame { .. }
        | Inst::CoroSuspend { .. }
        | Inst::LandingPad { .. }
        | Inst::DialectOp(_) => SemanticsFamily::Aggregates,
        Inst::FCmp { .. } => SemanticsFamily::Floats,
        Inst::AtomicLoad { .. }
        | Inst::AtomicStore { .. }
        | Inst::AtomicRMW { .. }
        | Inst::CmpXchg { .. }
        | Inst::Fence { .. } => SemanticsFamily::Atomics,
        Inst::UnOp { .. } | Inst::Overflow { .. } | Inst::ICmp { .. } => {
            SemanticsFamily::IntegerArithmetic
        }
        Inst::Const { value: trust_ir::constant::Constant::SymbolAddr { .. }, .. } => {
            SemanticsFamily::MemoryProvenance
        }
        Inst::Const { .. } => SemanticsFamily::IntegerArithmetic,
        Inst::Assume { .. } | Inst::Assert { .. } | Inst::Return { .. } | Inst::Unreachable => {
            SemanticsFamily::SafetyProperties
        }
        Inst::Copy { .. } => SemanticsFamily::Select,
        Inst::Select { .. } => SemanticsFamily::Select,
    }
}
