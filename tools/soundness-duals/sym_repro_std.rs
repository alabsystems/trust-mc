// ADVERSARIAL SOUNDNESS AUDIT — LATENT FALSE SAFE
// Family: symbolic byte-offset OOB DEREF, stack-provenance (keystone #52)
//
// A symbolic offset is added to a real stack allocation's exposed address with
// PLAIN INTEGER arithmetic, then the integer is transmuted back to a raw
// pointer and DEREFERENCED. When i >= 4 the read is out of bounds of `a` =>
// UB in real Rust; Kani reports a "dereference failure ... pointer out of
// bounds". trust-mc proves VERIFICATION: SUCCESSFUL.
//
// MECHANISM (dropped reachable error edge):
//   * `base + i` is a whole-width 64-bit bvadd, so its high 32 bits (the
//     split-pointer obj_id lane) become SYMBOLIC (the symbolic `i` smears into
//     the id bits).  Unlike ptr.add()/wrapping_add() (which route through
//     step_split_pointer and keep the obj_id lane const), integer arithmetic
//     followed by `transmute::<usize,*const u8>` does NOT preserve the lane.
//   * cast_dispatch.rs:243  — CastKind::Transmute with src_sort == target_sort
//     (BV64 == BV64) returns the operand UNCHANGED: no obj_valid invalidation
//     (contrast the `as` cast = PointerWithExposedProvenance, which invalidates
//     obj_valid at cast_dispatch.rs:54-67 and WOULD catch this).
//   * At the deref, load_from_memory -> heap_access_checks
//     (codegen_expr_heap.rs:294-324).  const_obj_id_u32(symbolic obj_id) = None,
//     so at codegen_expr_heap.rs:316-318 `alloc_size = None`
//     ("unconstrained obj_id — skip bounds check") and the bounds error edge
//     `end_offset <= alloc_size` (lines 319-324) is NEVER emitted.
//   * The remaining checks are vacuous: obj_valid = const_array(true) at the
//     entry rule (codegen_rules_entry.rs:379-384) so obj_valid.select(symbolic)
//     = true; u8 alignment = 1 so no alignment clause; the no-wrap clause is
//     satisfiable.  => translate_chc emits NO reachable error rule for the OOB
//     deref.  No offset_provenance_unresolved demotion fires either (that net
//     lives only in ptr_offset_alloc_bound_check, on the BinOp::Offset path,
//     which this program never takes).
//
// Witness: i = 4 (or any i >= 4).  Real Rust reads a[4] which does not exist.

use std::mem::transmute;

#[kani::proof]
fn symbolic_offset_oob_deref() {
    let a: [u8; 4] = [10, 20, 30, 40];
    let base: usize = a.as_ptr() as usize; // PointerExposeAddress (no invalidation)
    let i: usize = kani::any();
    // Plain integer arithmetic (wrapping to dodge the debug overflow assert):
    // NOT ptr::add — so no step_split_pointer, no offset alloc-bound check,
    // no provenance demotion. The symbolic `i` smears into the obj_id lane.
    let addr: usize = base.wrapping_add(i);
    let p: *const u8 = unsafe { transmute::<usize, *const u8>(addr) };
    // OOB / invalid dereference whenever i >= 4  (UB in real Rust).
    let v: u8 = unsafe { *p };
    std::hint::black_box(v);
}
