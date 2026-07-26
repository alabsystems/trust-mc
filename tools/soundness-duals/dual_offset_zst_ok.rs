// SOUNDNESS DUAL — offset ZST discharge (isize-overflow obligation-1 fix).
//
// Marker: offset_isize_overflow_precise_dual (grep-anchor for the fix).
//
// A ZST offset with `count = isize::MAX + 1`. Per the Rust/Kani `offset`
// model, an offset on a ZST is ALWAYS safe: the byte offset is
// `count * size_of::<()>() == count * 0 == 0`, so obligation (1)
// (isize-overflow of the byte product) is trivially satisfied, and
// obligation (2) (in-bounds) is trivially satisfied because the result
// address equals the base. There is NO other UB in this harness.
//
// MUST be SUCCESSFUL. If this flips to FAILED, the fix wrongly kept the
// fail-closed provenance demotion on a ZST offset site (the spurious FP
// this change removes).
#[kani::proof]
fn dual_offset_zst_ok() {
    let mut x = ();
    let ptr: *mut () = &mut x as *mut ();
    let count: usize = (isize::MAX as usize) + 1;
    let _ = unsafe { ptr.add(count) };
}
