// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed trust_ir semantics coverage metadata for production routing.

use trust_ir::inst::{BinOp, Inst, UnOp};

use trust_ir::dialect::trust_rust::is_thread_local_addr;

/// Coarse trust_ir semantics families tracked by the BMC translator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SemanticsFamily {
    IntegerArithmetic,
    /// `CtPop`/`CtLz`/`CtTz`/`BSwap`/`BitReverse`: total integer ops with no
    /// exact encoding in either lane.
    BitIntrinsics,
    Division,
    MemoryProvenance,
    SafetyProperties,
    ControlFlow,
    Select,
    Calls,
    Casts,
    Aggregates,
    Closures,
    Floats,
    Atomics,
    ProofAnnotations,
    /// trust-ir's tensor region (wire v67-v70): the six `Inst::Tensor*`
    /// instructions and a `Const` that builds a `Constant::TensorBlob`. No
    /// lane models a tensor value (`crate::tensor_region`).
    Tensors,
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
        notes: "integer add/sub/mul/div/rem/bitwise and exact modular rotates plus overflow/div-zero obligations; integer Neg (with its INT_MIN obligation, overflow policy and Wrapping behavior) and integer Not are exact in both lanes; BMC also exactly models canonical boolean BAnd/BOr/BXor (BXor with true is scalar boolean negation)",
    },
    SemanticsCoverage {
        family: SemanticsFamily::BitIntrinsics,
        status: SemanticsStatus::FailClosedUnsupported,
        notes: "ctpop/ctlz/cttz/bswap/bitreverse bind an unconstrained placeholder and fail closed by name in both main lanes (BMC unsupported-semantics VC, CHC UnaryOperation error rule); only the CHC direct-call summary uses them, as the total ops trust-ir defines (havoc result, no error condition)",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Division,
        status: SemanticsStatus::Implemented,
        notes: "integer division and remainder emit typed signed/unsigned div-zero plus signed-overflow obligations",
    },
    SemanticsCoverage {
        family: SemanticsFamily::MemoryProvenance,
        status: SemanticsStatus::Conservative,
        notes: "BMC uses array-backed regions; CHC diagnostic lowering has stack/borrow/provenance shortcuts (including ValidBorrow) that are non-authoritative, while the driver proof-grade bundle gate rejects public borrow, alloca, GEP, and unchecked pointer-cast shapes; MemCopy/MemSet of one whole object of a stack cell are exact in a size independent of the byte count (CHC: any object starting at the pointer, with exact in-bounds and memcpy-overlap UB; BMC: a whole single-cell Alloca), a defined lane run of a tracked CHC cell havocs it and fails closed (no lambda arrays on the CHC path), and through any other pointer they havoc every cell they could write and fail closed (BMC always, CHC whenever memory bounds are checked)",
    },
    SemanticsCoverage {
        family: SemanticsFamily::SafetyProperties,
        status: SemanticsStatus::Implemented,
        notes: "assume/assert/return/unreachable produce typed constraints and violations",
    },
    SemanticsCoverage {
        family: SemanticsFamily::ControlFlow,
        status: SemanticsStatus::Conservative,
        notes: "CHC lowers branch, conditional branch, and scalar switch edges; BMC lowers acyclic CFGs (branch/conditional branch/scalar switch with guarded paths and block-parameter joins) and fails closed on loops (back-edges) and malformed blocks; both lanes refuse the exception terminators (`Invoke`, `AssertInvoke`, `Resume`) by name",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Select,
        status: SemanticsStatus::Implemented,
        notes: "single-instruction value selection is lowered to typed ite expressions",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Calls,
        status: SemanticsStatus::Conservative,
        notes: "bounded acyclic scalar direct calls inline typed return/safety summaries; the diagnostic name-only wrapping intrinsic shortcut is non-authoritative and rejected by the driver proof-grade gate; unknown, recursive, and indirect calls fail closed, and so do drop glue (`Drop`, `DropInvoke`), the unwinding indirect call (`InvokeIndirect`) and the no-unwind boundary calls (`CallCannotUnwind`, `CallIndirectCannotUnwind`) in both lanes",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Casts,
        status: SemanticsStatus::Conservative,
        notes: "diagnostic lanes lower several integer, bool, and pointer/newtype casts conservatively; the driver proof-grade bundle gate currently admits only integer Trunc/ZExt/SExt and rejects provenance-, aggregate-, transmute-, and float-sensitive casts",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Aggregates,
        status: SemanticsStatus::Conservative,
        notes: "MakeAggregate construction fails closed except at a non-empty array type, where it is exact; a fixed-size array is one SMT array per element leaf in CHC, in constant size whatever its length: a uniform array (ArraySplat, constant Splat) is a constant array, InsertElement is store and ExtractElement is select, each access carrying its own in-bounds error rule (a summarized callee's read too); scalar struct/tuple field extract/insert lowers structurally; a vector read is a fresh value under its lane count's bounds rule, and a read with no known length (a sequence) fails closed with memory checks on; the driver proof-grade bundle gate admits ExtractElement exactly where it is such a select (a tracked non-empty array whose element type is the result type, an integer index, a block no loop reaches, and no call folding a callee's read into a block a loop reaches: docs/DECISION_QUEUE.md TMC-1) and refuses the rest by name (untyped_array, not_an_smt_array for vector, sequence, empty and untracked-element arrays, element_type_mismatch, unmodeled_index, shape_only_array, shape_only_array_in_callee)",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Closures,
        status: SemanticsStatus::FailClosedUnsupported,
        notes: "runtime MakeClosure construction binds an opaque closure value and fails closed by name in both lanes; its ordered captures remain SSA reads and pointer escapes, and indirect application remains refused in the Calls family",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Floats,
        status: SemanticsStatus::FailClosedUnsupported,
        notes: "float constants lower to exact IEEE-754 bit patterns (fail-closed when no exact encoding exists); floating arithmetic and comparisons bind unconstrained placeholders and emit unsupported-semantics VCs — never bit-level arithmetic or bit-equality",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Atomics,
        status: SemanticsStatus::Conservative,
        notes: "atomic load/store/rmw/cmpxchg use sequential array-backed semantics, a weak cmpxchg succeeding only on equality AND an unconstrained choice (spurious failure); fences fail closed",
    },
    SemanticsCoverage {
        family: SemanticsFamily::Tensors,
        status: SemanticsStatus::FailClosedUnsupported,
        notes: "the trust-ir v67-v70 tensor region (Ty::Tensor, TensorContract, TensorMap, TensorReduce, TensorView, TensorGather, TensorScatter, Constant::TensorBlob, a non-empty Module.blobs) has no SMT value carrier in either lane: the module input and the native-bundle boundary refuse a module storing any of them by name before translation, each translator arm fails closed by name if reached, and the driver proof-grade bundle gate refuses them before admission",
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
        // v70 `TensorBlob`: a content-addressed tensor constant, the tensor
        // region's one constant, at any depth of an `Inst::Const` value or an
        // `Inst::Switch` case (refused in both lanes, as its type is).
        inst if crate::inst_carries_tensor_blob(inst) => SemanticsFamily::Tensors,
        // Exhaustive over `BinOp`/`UnOp` (no wildcard): a new operator must be
        // placed in a family before this compiles. A family's row states what
        // the lanes DO with its members, so an op both lanes refuse belongs in a
        // fail-closed family, never in an `Implemented` one.
        Inst::BinOp { op, .. } => match op {
            BinOp::FAdd
            | BinOp::FSub
            | BinOp::FMul
            | BinOp::FDiv
            | BinOp::FRem
            | BinOp::FMin
            | BinOp::FMax
            | BinOp::FCopySign => SemanticsFamily::Floats,
            BinOp::SDiv | BinOp::UDiv | BinOp::SRem | BinOp::URem => SemanticsFamily::Division,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::And
            | BinOp::Or
            | BinOp::Xor
            | BinOp::Shl
            | BinOp::LShr
            | BinOp::AShr
            | BinOp::BAnd
            | BinOp::BOr
            | BinOp::BXor
            | BinOp::RotL
            | BinOp::RotR => SemanticsFamily::IntegerArithmetic,
        },
        Inst::UnOp { op, .. } => match op {
            UnOp::FNeg | UnOp::FAbs | UnOp::FSqrt | UnOp::FFloor | UnOp::FCeil | UnOp::FTrunc => {
                SemanticsFamily::Floats
            }
            UnOp::Neg | UnOp::Not => SemanticsFamily::IntegerArithmetic,
            UnOp::CtPop | UnOp::CtLz | UnOp::CtTz | UnOp::BSwap | UnOp::BitReverse => {
                SemanticsFamily::BitIntrinsics
            }
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
        | Inst::Dealloc { .. }
        | Inst::MemCopy { .. }
        | Inst::MemSet { .. } => SemanticsFamily::MemoryProvenance,
        Inst::DialectOp(op) if is_thread_local_addr(op) => SemanticsFamily::MemoryProvenance,
        Inst::Br { .. }
        | Inst::CondBr { .. }
        | Inst::Switch { .. }
        | Inst::Invoke { .. }
        // v54 `AssertInvoke`: a sited check with `Invoke`'s unwind edge, which
        // both lanes refuse by name, as they refuse `Invoke`.
        | Inst::AssertInvoke { .. }
        | Inst::Resume { .. } => SemanticsFamily::ControlFlow,
        // A v47 `Drop` runs the type's drop glue: a destructor CALL whose body is
        // not in the node, which both lanes refuse by name. Its v55 unwinding
        // twin `DropInvoke`, the v56 `InvokeIndirect` and the v53 no-unwind
        // boundary calls are refused by name in both lanes too.
        Inst::Call { .. }
        | Inst::CallIndirect { .. }
        | Inst::Drop { .. }
        | Inst::CallCannotUnwind { .. }
        | Inst::CallIndirectCannotUnwind { .. }
        | Inst::DropInvoke { .. }
        | Inst::InvokeIndirect { .. } => SemanticsFamily::Calls,
        Inst::Cast { .. } => SemanticsFamily::Casts,
        Inst::MakeClosure { .. } => SemanticsFamily::Closures,
        Inst::MakeAggregate { .. }
        // v50 `[value; n]`: an aggregate construction (CHC models a trackable
        // array's lanes exactly, anything else as one opaque value; BMC binds one
        // opaque value), never a fail-closed family member.
        | Inst::ArraySplat { .. }
        | Inst::ExtractField { .. }
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
        Inst::Overflow { .. } | Inst::ICmp { .. } => SemanticsFamily::IntegerArithmetic,
        Inst::Const { value: trust_ir::constant::Constant::SymbolAddr { .. }, .. } => {
            SemanticsFamily::MemoryProvenance
        }
        // v50 `Splat`: the uniform array literal `[elem; len]` is an aggregate
        // construction, the constant twin of `ArraySplat` above.
        Inst::Const { value: trust_ir::constant::Constant::Splat { .. }, .. } => {
            SemanticsFamily::Aggregates
        }
        Inst::Const { .. } => SemanticsFamily::IntegerArithmetic,
        Inst::Assume { .. } | Inst::Assert { .. } | Inst::Return { .. } | Inst::Unreachable => {
            SemanticsFamily::SafetyProperties
        }
        Inst::Copy { .. } => SemanticsFamily::Select,
        Inst::Select { .. } => SemanticsFamily::Select,
        // trust-ir v67-v69 tensor region: no lane models a tensor value, so
        // these are a fail-closed family of their own, never an aggregate.
        Inst::TensorContract { .. }
        | Inst::TensorMap { .. }
        | Inst::TensorReduce { .. }
        | Inst::TensorView { .. }
        | Inst::TensorGather { .. }
        | Inst::TensorScatter { .. } => SemanticsFamily::Tensors,
    }
}
