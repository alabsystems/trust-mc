// Oracle: MUST FAIL.
//
// Two DISTINCT fields of one heap allocation, read through references. The
// assertion is FALSE (1 != 2) and must be refuted.
//
// WHY THIS FILE EXISTS — it was a FALSE PROOF, not a false positive:
//
//     assert!(*pa == *pb)   FALSE  ->  SUCCESSFUL, 0 of 18 failed,
//                                      [AY:PROOF_QUALIFIERS:clean]
//     assert!(*pa != *pb)   TRUE   ->  FAILED
//
// Both directions wrong is the signature of ONE SHARED CELL: `known_alloc_ids`
// maps a local to an OBJECT ID with an implicit offset of ZERO, so the address
// minted from it in `known_deref_base_addr_expr` is always `obj ++ 0`. `&s.a`
// (offset 0) and `&s.b` (offset 1) therefore became the same address, `*pa ==
// *pb` collapsed to a tautology, and the encoder proved a false assertion with
// a clean qualifier.
//
// `Box<u8>` hid this because its payload sits at offset 0 — the one case the
// rebase gets right. `Rc<T>` keeps its payload at +16, so every Rc deref read a
// cell nothing had written, which surfaced separately as a CERTIFIED-Genuine
// false bug on `Rc::new(7); assert!(*rc == 7)`.
//
// If this file ever reports SUCCESSFUL, the offset-blind rebase is back.

#[repr(C)]
struct S {
    a: u8,
    b: u8,
}

#[kani::proof]
fn bug_distinct_fields_collapse() {
    let s: Box<S> = Box::new(S { a: 1, b: 2 });
    let pa: &u8 = &s.a;
    let pb: &u8 = &s.b;
    assert!(*pa == *pb);
}
