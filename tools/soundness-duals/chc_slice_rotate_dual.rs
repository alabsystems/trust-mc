// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and the `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: the CHC bit-intrinsic handlers matched a callee by
// its last path segment, so `<[T]>::rotate_left(&mut self, mid)` (and
// `rotate_right`, and `VecDeque`'s) was taken for the INTEGER rotation: the
// slice's fat pointer was rotated into the call's unit result and the slice
// was left untouched. `[Some(1), None, Some(3)].rotate_left(1)` then
// `assert!(a[0].is_some())` was a clean PROOF of a false assertion on the
// baseline a15de6272 and on the first fix/chc-false-certificates bundle (ay
// 09b0371c6, chc, 30 s; review probe e2_enum_swap.rs `rotate_bug`); the u8
// variants were saved only by a booking. The handlers now take numeric paths
// only (bit_intrinsics.rs `is_numeric_bit_path`); the slice call is an
// unmodeled call that fails closed.
//
// In its own file, and with the enum rows only: a `[u8; N]` rotation books a
// type-sort fallback that the driver applies to every harness of the file,
// which demoted the baseline's clean proof out of view.

#[kani::proof]
fn bug_rotate_enum_array() {
    let mut a: [Option<u8>; 3] = [Some(1), None, Some(3)];
    a.rotate_left(1);
    assert!(a[0].is_some());
}

#[kani::proof]
fn safe_rotate_enum_array() {
    let mut a: [Option<u8>; 3] = [Some(1), None, Some(3)];
    a.rotate_left(1);
    assert!(a[0].is_none());
}
