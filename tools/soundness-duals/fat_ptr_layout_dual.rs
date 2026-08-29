// Oracle: MUST FAIL.
//
// Guards a PRECISION fix from becoming a false proof. `Layout::for_value_raw`
// on an unsized pointee used to leave its destination UNCONSTRAINED, because
// `split_pointer` accepts only a bv64 address while the argument is a FAT
// pointer (bv128, laid out `[metadata : upper | data : lower]`). Every
// `Box<[T]>` / `Box<str>` therefore took the fallback, the dynamic size was
// never bound, and dropping a `Box<[u8]>` produced a FALSE counterexample.
//
// The fix takes the data half via `PtrRepr::classify(..).into_data()` before
// splitting, which BINDS a formerly-free bv128. That is exactly the shape that
// accidentally discharges the obligations the value feeds — the dealloc
// size/align checks. This file is the standing check that it did not.
//
// NOTE: only the SIZE mismatch is asserted here. The ALIGN mismatch is a
// SEPARATE, PRE-EXISTING missed bug (A/B-verified: clean PROOF both with and
// without the layout fix) — `obj_align` does not exist anywhere in the tree, so
// there is nothing for a dealloc to compare against. Do not add an align
// harness to this file until that is built; it would fail the wall for a reason
// unrelated to what this dual guards.
//
// The dealloc below is genuine UB: allocated with size 4, freed with size 8.
// It must stay a `Genuine` counterexample. If it ever reports SUCCESSFUL, the
// layout binding has folded the dealloc obligations into constants.

use std::alloc::{Layout, alloc, dealloc};

#[kani::proof]
fn bug_dealloc_layout_size_mismatch() {
    unsafe {
        let l = Layout::from_size_align(4, 1).unwrap();
        let p = alloc(l);
        let wrong = Layout::from_size_align(8, 1).unwrap();
        dealloc(p, wrong);
    }
}
