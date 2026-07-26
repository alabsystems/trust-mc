// P2-S1 precision dual: a contract relying on a PROMOTED CONSTANT (the
// `Foo(1)` temporary inside the contract closure is lifted to a const
// allocation — same shape as Kani's FunctionContracts/promoted_constants.rs
// `check_promoted`). Promoted constants are immutable and must STAY PINNED in
// contract mode — this harness must verify SUCCESSFULLY both before and after
// the static-havoc fix.

extern crate kani;

#[derive(PartialEq, Eq, kani::Arbitrary)]
pub struct Foo(u8);

/// Contract uses a temporary that is promoted to a const static.
#[kani::requires(foo == Foo(1))]
pub fn foo_promoted(foo: Foo) -> Foo {
    assert!(foo.0 == 1);
    foo
}

#[kani::proof_for_contract(foo_promoted)]
fn check_promoted() {
    let _ = foo_promoted(kani::any());
}
