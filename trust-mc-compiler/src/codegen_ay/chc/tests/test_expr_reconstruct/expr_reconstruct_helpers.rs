// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_public::mir::{
    Body, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};

fn places_from_operand(op: &Operand) -> Vec<&Place> {
    match op {
        Operand::Copy(place) | Operand::Move(place) => vec![place],
        Operand::Constant(_) => vec![],
    }
}

fn place_has_field_and_index(place: &Place, local_idx: usize) -> bool {
    place.local == local_idx
        && place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(_, _)))
        && place.projection.iter().any(|proj| {
            matches!(proj, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
        })
}

pub(super) fn find_field_index_place(body: &Body, local_idx: usize) -> Option<Place> {
    let mut best_match: Option<Place> = None;
    let mut update_best = |candidate: &Place| {
        let should_replace = match &best_match {
            Some(best) => candidate.projection.len() > best.projection.len(),
            None => true,
        };
        if should_replace {
            best_match = Some(candidate.clone());
        }
    };

    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(dest, rvalue) = &stmt.kind {
                if place_has_field_and_index(dest, local_idx) {
                    update_best(dest);
                }

                let source_places: Vec<&Place> = match rvalue {
                    Rvalue::Use(op) => places_from_operand(op),
                    Rvalue::Ref(_, _, place)
                    | Rvalue::AddressOf(_, place)
                    | Rvalue::CopyForDeref(place)
                    | Rvalue::Discriminant(place)
                    | Rvalue::Len(place) => vec![place],
                    Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                        let mut places = places_from_operand(lhs);
                        places.extend(places_from_operand(rhs));
                        places
                    }
                    Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) | Rvalue::Repeat(op, _) => {
                        places_from_operand(op)
                    }
                    _ => vec![],
                };

                for place in source_places {
                    if place_has_field_and_index(place, local_idx) {
                        update_best(place);
                    }
                }
            }
        }

        if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
            if place_has_field_and_index(destination, local_idx) {
                update_best(destination);
            }

            for place in places_from_operand(func) {
                if place_has_field_and_index(place, local_idx) {
                    update_best(place);
                }
            }

            for arg in args {
                for place in places_from_operand(arg) {
                    if place_has_field_and_index(place, local_idx) {
                        update_best(place);
                    }
                }
            }
        }
    }

    best_match
}
