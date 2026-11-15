// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Three CHC regressions of the 2026-09-24 row (row 72, ay f28345ff1), each a
// safe program Kani proves, and each paired with a bug the same encoding must
// still find — so a recovered proof cannot come from a dropped check.
//
// * Zero-sized array payload (`expected/niche2/main.rs`). `Foo::B([i32; 0])` is
//   omitted from the BV-flattened enum's state vars. The whole-`Foo` read had
//   no value for the omitted Array field, fell to a raw tag|payload concat, and
//   the `Option<Foo>` payload coercion rebuilt `B` with ZERO arguments; since
//   ay ad07c5cc63 validates constructor signatures that is a codegen panic
//   (`unsupported`).
// * `Option<Infallible>` residual (`prusti/Fibonacci_sequence.rs`,
//   `FunctionSymbols/issue1243.rs`). `?` on an `Option` inside `try_fold` moves
//   the zero-sized residual out of `ControlFlow::Break`; the read had no value
//   for a zero-sized Datatype and the flattened destination fell to
//   `flatten_self_loop_fallback`, a translation drop that demoted the proof.
// * Disputed scalarizer column (`prusti/Selection_sort.rs`). The entry rule
//   stores the whole array at constant indices; `collapse_mid_aliases` (per
//   variable since e7e27b632) hands the loop head's column the stored-to
//   `__mid_bb0` var, which is itself a constant-index candidate, while the loop
//   indexes the array symbolically. Expanding the recognised name alone widened
//   that one application: `ChcParseError` "Predicate 'main__bb8' expected
//   argument sort (_ BitVec 32), got (Array (_ BitVec 64) (_ BitVec 32))".
//   (`SIMD/simd_bitmask_equiv.rs` prints the same error from a different pass:
//   constant folding also removes relation arguments by name. Not covered here.)
//
// Oracles, each confirmed with Kani 0.67.0 (kani-src at the corpus rev):
//   safe_zst_array_payload_roundtrips      SUCCESSFUL
//   bug_zst_array_payload_wrong_value      FAILED
//   safe_option_residual_nth               SUCCESSFUL
//   bug_option_residual_nth_wrong_value    FAILED
//   safe_selection_sort_symbolic_index     SUCCESSFUL
//   bug_selection_sort_wrong_order         FAILED

enum Foo {
    A(i32),
    B([i32; 0]),
}

fn get_a(x: i32) -> Option<Foo> {
    Some(Foo::A(x))
}

fn get_b() -> Option<Foo> {
    Some(Foo::B([]))
}

#[kani::proof]
fn safe_zst_array_payload_roundtrips() {
    match get_a(10) {
        Some(Foo::A(x)) => assert!(x == 10),
        _ => assert!(false),
    }
    match get_b() {
        Some(Foo::B(_)) => {}
        _ => assert!(false),
    }
}

#[kani::proof]
fn bug_zst_array_payload_wrong_value() {
    match get_a(10) {
        Some(Foo::A(x)) => assert!(x == 11),
        _ => {}
    }
}

struct Fib {
    prev: usize,
    curr: usize,
}

impl Iterator for Fib {
    type Item = usize;
    fn next(&mut self) -> Option<usize> {
        let x = self.prev;
        self.prev = self.curr;
        self.curr += x;
        Some(x)
    }
}

#[kani::proof]
fn safe_option_residual_nth() {
    let mut fib = Fib { prev: 0, curr: 1 };
    assert!(fib.nth(10).unwrap() == 55);
}

#[kani::proof]
fn bug_option_residual_nth_wrong_value() {
    let mut fib = Fib { prev: 0, curr: 1 };
    assert!(fib.nth(10).unwrap() == 54);
}

fn selection_sort(array: &mut [i32]) {
    let mut min;
    for i in 0..array.len() {
        min = i;
        for j in (i + 1)..array.len() {
            if array[j] < array[min] {
                min = j;
            }
        }
        let tmp = array[i];
        array[i] = array[min];
        array[min] = tmp;
    }
}

#[kani::proof]
fn safe_selection_sort_symbolic_index() {
    let mut array = [9, 4, 8, 3];
    selection_sort(&mut array);
    assert!(array == [3, 4, 8, 9]);
}

#[kani::proof]
fn bug_selection_sort_wrong_order() {
    let mut array = [9, 4, 8, 3];
    selection_sort(&mut array);
    assert!(array == [3, 4, 9, 8]);
}
