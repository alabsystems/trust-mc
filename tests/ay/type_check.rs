// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT

// kani-expect: PROOF

use std::any::TypeId;

#[kani::proof]
fn check_type_id_same_type_equal() {
    let id1 = TypeId::of::<u32>();
    let id2 = TypeId::of::<u32>();
    kani::assert(id1 == id2, "TypeId::of::<u32>() must be deterministic");
}

#[kani::proof]
fn check_type_id_different_types_distinct() {
    let id_u32 = TypeId::of::<u32>();
    let id_i32 = TypeId::of::<i32>();
    kani::assert(id_u32 != id_i32, "TypeId of u32 and i32 must differ");
}

#[kani::proof]
fn check_type_id_bool_vs_u8() {
    let id_bool = TypeId::of::<bool>();
    let id_u8 = TypeId::of::<u8>();
    kani::assert(id_bool != id_u8, "TypeId of bool and u8 must differ");
}

#[kani::proof]
fn check_type_id_matches_type_true() {
    let id = TypeId::of::<u32>();
    kani::assert(
        id == TypeId::of::<u32>(),
        "existing TypeId should match the same concrete type",
    );
}

#[kani::proof]
fn check_type_id_matches_type_false() {
    let id = TypeId::of::<u32>();
    kani::assert(
        id != TypeId::of::<i32>(),
        "existing TypeId should not match a different concrete type",
    );
}
