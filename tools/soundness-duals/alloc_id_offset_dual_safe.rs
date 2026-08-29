// Oracle: MUST be SUCCESSFUL.
//
// The non-vacuity twin of alloc_id_offset_dual.rs. Same shape, TRUE assertion.
// It is the witness that the twin's FAILURE comes from the two fields being
// distinguished again, not from the harness failing wholesale — and that the
// fail-closed guard did not simply throw away all allocation provenance.
//
// It also pins the Rc half: `Rc<T>` keeps its payload at +16, and every read of
// it used to return an unconstrained value, reported as a CERTIFIED-Genuine
// false bug.

use std::rc::Rc;

#[repr(C)]
struct S {
    a: u8,
    b: u8,
}

#[kani::proof]
fn safe_distinct_fields_differ() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let pa: &u8 = &s.a;
    let pb: &u8 = &s.b;
    assert!(*pa != *pb);
}

#[kani::proof]
fn safe_rc_payload_roundtrips() {
    let rc: Rc<u8> = Rc::new(7);
    assert!(*rc == 7);
}
