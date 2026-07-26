// SOUNDNESS DUAL — offset non-ZST isize-overflow (obligation-1 must-fail).
//
// Marker: offset_isize_overflow_precise_dual (grep-anchor for the fix).
//
// A non-ZST offset with `count = isize::MAX + 1`. The `count` itself does
// not fit isize (it is `isize::MAX + 1` as a usize), so the `to_isize`
// conversion in the offset model fails: obligation (1) is VIOLATED
// regardless of allocation size / provenance. This is the core missed-bug
// guard for obligation (1): a genuine isize-overflow must still produce a
// counterexample after the ZST demotion-removal.
//
// MUST be FAILED (Kani message: "Offset value overflows isize"). If this
// flips to SUCCESSFUL, the precise overflow obligation was lost.
#[kani::proof]
fn dual_offset_nonzst_overflow() {
    let mut x = 7i32;
    let ptr: *mut i32 = &mut x as *mut i32;
    let count: usize = (isize::MAX as usize) + 1;
    let _ = unsafe { ptr.add(count) };
}
