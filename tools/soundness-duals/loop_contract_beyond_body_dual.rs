// Oracle: corpus-rev Kani -Z loop-contracts (see the manifest entry for the
// measured verdict of every harness).
//
// WHY THIS FILE EXISTS: design 5 (docs/chc-hole-fix-designs-2026-09-24.md,
// "Legacy loop-contract latch"), review of fix/chc-loop-contract-latch. The CHC
// lane checks a loop contract only inside the body it encodes (the harness plus
// what `FunctionInlinePass` inlined into it). A contracted loop anywhere else
// runs raw: walked with its register call answering `{ true }`, or dropped with
// a callee the walker havocs. The first cut of design 5 booked a havocked
// callee only when it reached the loop through LOCAL bodies, closures and fn
// items named in generic arguments, so every `*_bug` row below, which Kani
// FAILS on "Check invariant after step", was a clean SUCCESSFUL:
//
// * `generic_chain_deep_bug`: a plain call chain to `.chain().step_by().count()`
//   over a local iterator. Only NON-LOCAL std code (`Iterator::count` and the
//   adapters) reaches the contracted `next`.
// * `generic_fold_at_depth_bug`: `Iterator::fold` over the local iterator,
//   havocked at the walker's inline-depth limit.
// * `vtable_iter_bug`: `count()` on a `Box<dyn Iterator>` made from the local
//   iterator: `next` is reached only through the vtable, inside std.
// * `fn_pointer_map_bug`: `Option::map` given a fn pointer to a contracted fn.
//
// `havocked_local_fold_bug` was already booked (the havocked callee reaches the
// loop through local bodies); it guards that path. `generic_chain_deep_safe`
// has a valid invariant: a demoted FAILED is tolerated, a Genuine one is not.
// `unrelated_control` reaches no loop contract in a crate that has them, and a
// fn pointer is taken there: it must stay SUCCESSFUL.

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

/// Yields once; its contracted loop breaks the invariant on the reachable
/// state i == 2.
struct BadIter {
    n: u32,
}

impl Iterator for BadIter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.n == 0 {
            return None;
        }
        self.n = 0;
        let mut i: u32 = 0;
        #[kani::loop_invariant(i <= 1)]
        #[kani::loop_modifies(&i)]
        while i < 4 {
            i = i.wrapping_add(1);
        }
        Some(i)
    }
}

/// Yields once; its contracted loop keeps a valid invariant.
struct GoodIter {
    n: u32,
}

impl Iterator for GoodIter {
    type Item = u32;
    fn next(&mut self) -> Option<u32> {
        if self.n == 0 {
            return None;
        }
        self.n = 0;
        let mut i: u32 = 0;
        #[kani::loop_invariant(i <= 4)]
        #[kani::loop_modifies(&i)]
        while i < 4 {
            i = i.wrapping_add(1);
        }
        Some(i)
    }
}

fn bad_chain_count() -> usize {
    BadIter { n: 1 }.chain(BadIter { n: 1 }).step_by(2).count()
}

fn good_chain_count() -> usize {
    GoodIter { n: 1 }.chain(GoodIter { n: 1 }).step_by(2).count()
}

fn h1() -> usize { h2() }
fn h2() -> usize { h3() }
fn h3() -> usize { h4() }
fn h4() -> usize { h5() }
fn h5() -> usize { h6() }
fn h6() -> usize { h7() }
fn h7() -> usize { h8() }
fn h8() -> usize { h9() }
fn h9() -> usize { h10() }
fn h10() -> usize { h11() }
fn h11() -> usize { bad_chain_count() }

fn g1() -> usize { g2() }
fn g2() -> usize { g3() }
fn g3() -> usize { g4() }
fn g4() -> usize { g5() }
fn g5() -> usize { g6() }
fn g6() -> usize { g7() }
fn g7() -> usize { g8() }
fn g8() -> usize { g9() }
fn g9() -> usize { g10() }
fn g10() -> usize { g11() }
fn g11() -> usize { good_chain_count() }

#[kani::proof]
fn generic_chain_deep_bug() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let _ = h1();
    assert!(x + 1 <= 10);
}

#[kani::proof]
fn generic_chain_deep_safe() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let _ = g1();
    assert!(x + 1 <= 10);
}

fn f1() -> u32 { f2() }
fn f2() -> u32 { f3() }
fn f3() -> u32 { f4() }
fn f4() -> u32 { f5() }
fn f5() -> u32 { BadIter { n: 1 }.fold(0u32, |a, x| a.wrapping_add(x)) }

#[kani::proof]
fn generic_fold_at_depth_bug() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let f: fn() -> u32 = f1;
    let _ = f();
    assert!(x + 1 <= 10);
}

fn l1() -> u32 { l2() }
fn l2() -> u32 { l3() }
fn l3() -> u32 { l4() }
fn l4() -> u32 { BadIter { n: 1 }.fold(0u32, |a, x| a.wrapping_add(x)) }

#[kani::proof]
fn havocked_local_fold_bug() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let f: fn() -> u32 = l1;
    let _ = f();
    assert!(x + 1 <= 10);
}

fn v5() -> usize {
    let b: Box<dyn Iterator<Item = u32>> = Box::new(BadIter { n: 1 });
    b.count()
}
fn v4() -> usize { v5() }
fn v3() -> usize { v4() }
fn v2() -> usize { v3() }
fn v1() -> usize { v2() }

#[kani::proof]
fn vtable_iter_bug() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let f: fn() -> usize = v1;
    let _ = f();
    assert!(x + 1 <= 10);
}

fn contracted_arg(x: u32) -> u32 {
    let mut i: u32 = 0;
    #[kani::loop_invariant(i <= 1)]
    #[kani::loop_modifies(&i)]
    while i < 4 {
        i = i.wrapping_add(1);
    }
    i ^ x
}

fn p5() -> Option<u32> {
    let f: fn(u32) -> u32 = contracted_arg;
    Some(1u32).map(f)
}
fn p4() -> Option<u32> { p5() }
fn p3() -> Option<u32> { p4() }
fn p2() -> Option<u32> { p3() }
fn p1() -> Option<u32> { p2() }

#[kani::proof]
fn fn_pointer_map_bug() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let f: fn() -> Option<u32> = p1;
    let _ = f();
    assert!(x + 1 <= 10);
}

fn plain(x: u32) -> u32 {
    x.wrapping_mul(2)
}

#[kani::proof]
fn unrelated_control() {
    let x: u32 = kani::any();
    kani::assume(x < 10);
    let f: fn(u32) -> u32 = plain;
    assert!(f(x) < 20);
}
