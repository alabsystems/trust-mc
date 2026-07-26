// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! Assign statement analysis for uninitialized memory checking.
//!
//! Handles the complex analysis of `StatementKind::Assign` for determining
//! which memory initialization operations are needed: deref stores, pointer
//! creation, union assignments, and layout compatibility checks.

use crate::{
    intrinsics::Intrinsic,
    kani_middle::transform::{
        body::InsertPosition,
        check_uninit::{
            PointeeInfo, relevant_instruction::MemoryInitOp, ty_layout::LayoutComputationError,
        },
    },
};
use rustc_public::mir::{
    AggregateKind, CastKind, Operand, Place, ProjectionElem, Rvalue, mono::InstanceKind,
};
use rustc_public::ty::{AdtKind, RigidTy, TyKind};

use super::CheckUninitVisitor;
use super::intrinsic_skip::can_skip_intrinsic;

impl CheckUninitVisitor {
    /// Analyze an Assign statement for memory initialization operations.
    ///
    /// This handles:
    /// - Union-as-subfield layout computation fallback
    /// - Deref store analysis (*ptr = val)
    /// - New pointer creation via AddressOf
    /// - Union field assignments (Use, Aggregate, Cast)
    pub(super) fn analyze_assign(&mut self, place: &Place, rvalue: &Rvalue) {
        // Fallback check for edge cases where union-as-subfield layout computation fails.
        // Most unions are now handled by ty_layout.rs, but this catches unsupported cases.
        if let Err(reason @ LayoutComputationError::UnionAsField(_)) =
            PointeeInfo::from_ty(place.ty(&self.locals).expect("place should have valid type"))
        {
            self.push_target(MemoryInitOp::Unsupported {
                reason: format!(
                    "Checking memory initialization of type {} is not supported. {}",
                    place.ty(&self.locals).expect("place should have valid type"),
                    reason
                ),
            });
            return;
        }

        // Check whether we are assigning into a dereference (*ptr = _).
        if let Some(place_without_deref) = try_remove_topmost_deref(place) {
            // First, check that we are not dereferencing extra pointers along the way
            // (e.g., **ptr = _). If yes, check whether these pointers are initialized.
            let mut place_to_add_projections =
                Place { local: place_without_deref.local, projection: vec![] };
            for projection_elem in &place_without_deref.projection {
                // If the projection is Deref and the current type is raw pointer, check
                // if it points to initialized memory.
                if *projection_elem == ProjectionElem::Deref
                    && let TyKind::RigidTy(RigidTy::RawPtr(..)) = place_to_add_projections
                        .ty(&self.locals)
                        .expect("place should have valid type")
                        .kind()
                {
                    self.push_target(MemoryInitOp::Check {
                        operand: Operand::Copy(place_to_add_projections.clone()),
                    });
                }
                place_to_add_projections.projection.push(projection_elem.clone());
            }
            if place_without_deref
                .ty(&self.locals)
                .expect("place should have valid type")
                .kind()
                .is_raw_ptr()
            {
                self.push_target(MemoryInitOp::Set {
                    operand: Operand::Copy(place_without_deref),
                    value: true,
                    position: InsertPosition::After,
                });
            }
        }

        // Check whether Rvalue creates a new initialized pointer previously not captured inside shadow memory.
        if place.ty(&self.locals).expect("place should have valid type").kind().is_raw_ptr()
            && let Rvalue::AddressOf(..) = rvalue
        {
            self.push_target(MemoryInitOp::Set {
                operand: Operand::Copy(place.clone()),
                value: true,
                position: InsertPosition::After,
            });
        }

        // NOTE: ADTs with unions as subfields are now supported via ty_layout.rs
        // UnionAsField handling. The type layout code computes merged data bytes
        // from all union fields. See #1826.
        let is_inside_union = {
            let mut place_to_add_projections = Place { local: place.local, projection: vec![] };
            let mut contains_union = place_to_add_projections
                .ty(&self.locals)
                .expect("place should have valid type")
                .kind()
                .is_union();
            for projection_elem in &place.projection {
                if place_to_add_projections
                    .ty(&self.locals)
                    .expect("place should have valid type")
                    .kind()
                    .is_union()
                {
                    contains_union = true;
                    break;
                }
                place_to_add_projections.projection.push(projection_elem.clone());
            }
            contains_union
        };

        // Need to copy some information about union initialization, since lvalue is
        // either a union or a field inside a union.
        if is_inside_union {
            self.analyze_union_assign(place, rvalue);
        }
    }

    /// Analyze a Call terminator for memory initialization operations.
    ///
    /// Handles intrinsic calls (atomic ops, copy, volatile ops, etc.),
    /// foreign item calls (alloc/dealloc), and regular calls with union arguments.
    ///
    /// Returns `Some(reason)` when the call instance cannot be resolved.
    pub(super) fn analyze_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
    ) -> Option<String> {
        let instance = match try_resolve_instance(&self.locals, func) {
            Ok(instance) => instance,
            Err(reason) => {
                return Some(reason);
            }
        };
        match instance.kind {
            InstanceKind::Intrinsic => {
                self.analyze_intrinsic_call(&instance, args);
            }
            InstanceKind::Item => {
                self.analyze_item_call(&instance, args, destination);
            }
            _ => {} // external enum: InstanceKind
        }
        None
    }

    /// Analyze an intrinsic call for memory initialization operations.
    fn analyze_intrinsic_call(
        &mut self,
        instance: &rustc_public::mir::mono::Instance,
        args: &[Operand],
    ) {
        match Intrinsic::from_instance(instance) {
            intrinsic_name if can_skip_intrinsic(&intrinsic_name) => {
                /* Intrinsics that can be safely skipped */
            }
            Intrinsic::AtomicAnd
            | Intrinsic::AtomicCxchg
            | Intrinsic::AtomicCxchgWeak
            | Intrinsic::AtomicLoad
            | Intrinsic::AtomicMax
            | Intrinsic::AtomicMin
            | Intrinsic::AtomicNand
            | Intrinsic::AtomicOr
            | Intrinsic::AtomicStore
            | Intrinsic::AtomicUmax
            | Intrinsic::AtomicUmin
            | Intrinsic::AtomicXadd
            | Intrinsic::AtomicXchg
            | Intrinsic::AtomicXor
            | Intrinsic::AtomicXsub => {
                self.push_target(MemoryInitOp::Check { operand: args[0].clone() });
            }
            Intrinsic::CompareBytes => {
                self.push_target(MemoryInitOp::CheckSliceChunk {
                    operand: args[0].clone(),
                    count: args[2].clone(),
                });
                self.push_target(MemoryInitOp::CheckSliceChunk {
                    operand: args[1].clone(),
                    count: args[2].clone(),
                });
            }
            Intrinsic::Copy => {
                self.push_target(MemoryInitOp::Copy {
                    from: args[0].clone(),
                    to: args[1].clone(),
                    count: args[2].clone(),
                });
            }
            Intrinsic::VolatileCopyMemory | Intrinsic::VolatileCopyNonOverlappingMemory => {
                // dst comes before src for volatile copy.
                self.push_target(MemoryInitOp::Copy {
                    from: args[1].clone(),
                    to: args[0].clone(),
                    count: args[2].clone(),
                });
            }
            Intrinsic::TypedSwap => {
                self.push_target(MemoryInitOp::Check { operand: args[0].clone() });
                self.push_target(MemoryInitOp::Check { operand: args[1].clone() });
            }
            Intrinsic::VolatileLoad | Intrinsic::UnalignedVolatileLoad => {
                self.push_target(MemoryInitOp::Check { operand: args[0].clone() });
            }
            Intrinsic::VolatileStore => {
                self.push_target(MemoryInitOp::Set {
                    operand: args[0].clone(),
                    value: true,
                    position: InsertPosition::After,
                });
            }
            Intrinsic::WriteBytes => self.push_target(MemoryInitOp::SetSliceChunk {
                operand: args[0].clone(),
                count: args[2].clone(),
                value: true,
                position: InsertPosition::After,
            }),
            intrinsic => {
                self.push_target(MemoryInitOp::Unsupported {
                    reason: format!(
                        "trust_mc does not support reasoning about memory initialization of intrinsic `{intrinsic:?}`."
                    ),
                });
            }
        }
    }

    /// Analyze an Item (non-intrinsic) call for memory initialization operations.
    fn analyze_item_call(
        &mut self,
        instance: &rustc_public::mir::mono::Instance,
        args: &[Operand],
        destination: &Place,
    ) {
        if instance.is_foreign_item() {
            match instance.name().as_str() {
                "alloc::alloc::__rust_alloc" | "alloc::alloc::__rust_realloc" => {
                    /* Memory is uninitialized, nothing to do here. */
                }
                "alloc::alloc::__rust_alloc_zeroed" => {
                    self.push_target(MemoryInitOp::SetSliceChunk {
                        operand: Operand::Copy(destination.clone()),
                        count: args[0].clone(),
                        value: true,
                        position: InsertPosition::After,
                    });
                }
                "alloc::alloc::__rust_dealloc" => {
                    self.push_target(MemoryInitOp::SetSliceChunk {
                        operand: args[0].clone(),
                        count: args[1].clone(),
                        value: false,
                        position: InsertPosition::After,
                    });
                }
                _ => {} // non-enum: Option<&str> (intrinsic name)
            }
        } else {
            let union_args: Vec<_> = args
                .iter()
                .enumerate()
                .filter(|(_, arg)| {
                    arg.ty(&self.locals).expect("arg should have valid type").kind().is_union()
                })
                .collect();
            if !union_args.is_empty() {
                for (idx, operand) in union_args {
                    self.push_target(MemoryInitOp::StoreArgument {
                        operand: operand.clone(),
                        argument_no: idx + 1, // since arguments are 1-indexed
                    });
                }
            }
        }
    }

    /// Analyze assignment into a union or union field.
    fn analyze_union_assign(&mut self, place: &Place, rvalue: &Rvalue) {
        match rvalue {
            Rvalue::Use(operand) => {
                // This is a union-to-union assignment, so we need to copy the
                // initialization state.
                if place.ty(&self.locals).expect("place should have valid type").kind().is_union() {
                    self.push_target(MemoryInitOp::AssignUnion {
                        lvalue: place.clone(),
                        rvalue: operand.clone(),
                    });
                } else {
                    // This is assignment to a field of a union.
                    self.push_target(MemoryInitOp::SetRef {
                        operand: Operand::Copy(place.clone()),
                        value: true,
                        position: InsertPosition::After,
                    });
                }
            }
            Rvalue::Aggregate(AggregateKind::Adt(adt_def, _, _, _, union_field), _) => {
                // Create a union from scratch as an aggregate. We handle it here because we
                // need to know which field is getting assigned.
                if adt_def.kind() == AdtKind::Union {
                    self.push_target(MemoryInitOp::CreateUnion {
                        operand: Operand::Copy(place.clone()),
                        field: union_field.expect("union aggregate should have field index"),
                    });
                }
            }
            // #1827: Handle Rvalue::Cast for union assignments.
            // Transmute to a union reinterprets the source bytes as union bytes.
            Rvalue::Cast(cast_kind, operand, _) => {
                match cast_kind {
                    CastKind::Transmute => {
                        // Transmute to union: copy init state if same type, else mark initialized.
                        if let (Ok(dest_ty), Ok(src_ty)) =
                            (place.ty(&self.locals), operand.ty(&self.locals))
                        {
                            if dest_ty == src_ty && dest_ty.kind().is_union() {
                                self.push_target(MemoryInitOp::AssignUnion {
                                    lvalue: place.clone(),
                                    rvalue: operand.clone(),
                                });
                            } else {
                                // Transmute from different type: mark as initialized
                                self.push_target(MemoryInitOp::SetRef {
                                    operand: Operand::Copy(place.clone()),
                                    value: true,
                                    position: InsertPosition::After,
                                });
                            }
                        }
                        // If types unavailable, skip — no init tracking emitted.
                    }
                    _ => self.push_target(MemoryInitOp::Unsupported {
                        // external enum: CastKind
                        reason: format!(
                            "Performing a union assignment with unsupported cast kind: {:?}",
                            cast_kind
                        ),
                    }),
                }
            }
            _ => self // external enum: Rvalue
                .push_target(MemoryInitOp::Unsupported {
                    reason:
                        "Performing a union assignment with a non-supported construct as an Rvalue"
                            .to_string(),
                }),
        }
    }
}

/// Try removing a topmost deref projection from a place if it exists, returning a place without it.
pub(super) fn try_remove_topmost_deref(place: &Place) -> Option<Place> {
    let (projection_elem, remaining_projection) = place.projection.split_last()?;
    if *projection_elem == ProjectionElem::Deref {
        Some(Place { local: place.local, projection: remaining_projection.to_vec() })
    } else {
        None
    }
}

/// Try retrieving instance for the given function operand.
pub(super) fn try_resolve_instance(
    locals: &[rustc_public::mir::LocalDecl],
    func: &Operand,
) -> Result<rustc_public::mir::mono::Instance, String> {
    let ty = func.ty(locals).expect("func operand should have valid type");
    match ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => {
            Ok(rustc_public::mir::mono::Instance::resolve(def, &args)
                .expect("should resolve FnDef instance"))
        }
        _ => Err(format!(
            // external enum: TyKind
            "trust_mc was not able to resolve the instance of the function operand `{ty:?}`. Currently, memory initialization checks in presence of function pointers and vtable calls are not supported. For more information about planned support, see https://github.com/model-checking/kani/issues/3300."
        )),
    }
}
