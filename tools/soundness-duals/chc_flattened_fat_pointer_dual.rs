// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: a struct whose only field is a slice reference
// (`struct G<'a>(&'a [u8])`) flattens to that one leaf, the 128-bit fat
// pointer. A read through a reference to it, `(*(r.0))[i]` or a devirtualized
// `dyn` receiver's `self.0[i]`, started the Mem-level deref walk at that leaf
// with the struct's type, and the walk's `Field(0)` read the leaf through the
// type-blind bitvector selector, which takes any 128-bit container as a
// `Layout { size, align }`: field 0 is its HIGH word, the slice's LENGTH. The
// element was then loaded at address `len + i`, a cell no clause writes. On
// main c22e1022e the `safe_` rows below are false certificates and the `bug_`
// rows Genuine only through that free cell
// (wide_pointer_carriers.rs `slice_behind_dyn_*` is the original shape).
// fix/chc-false-certificates first resolved a flattened local's leading field
// projections before the walk (066fff8ab). Main's fix/chc-lost-writes
// (6b1bb26cc) closed the same reads earlier on the path: they resolve through
// the reference's target and never reach that walk (measured 2026-10-14 on
// the merged tree: the walk's leading-field case is reached 0 times on these
// rows and on the review probes, 25 times on the pre-merge bundle), so the
// branch's code was dropped. The rows stay as coverage.

trait Get {
    fn get(&self, i: usize) -> u8;
    fn len(&self) -> usize;
}

struct G<'a>(&'a [u8]);

impl<'a> Get for G<'a> {
    fn get(&self, i: usize) -> u8 {
        self.0[i]
    }
    fn len(&self) -> usize {
        self.0.len()
    }
}

#[kani::proof]
fn safe_dyn_index() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let d: &dyn Get = &g;
    assert!(d.get(2) == 3 && d.len() == 3);
}

#[kani::proof]
fn bug_dyn_index() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let d: &dyn Get = &g;
    assert!(d.get(1) == 3);
}

#[kani::proof]
fn safe_dyn_nondet_index() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let d: &dyn Get = &g;
    let i: usize = kani::any();
    kani::assume(i < 3);
    assert!(d.get(i) as usize == i + 1);
}

#[kani::proof]
fn bug_dyn_nondet_index() {
    let a = [1u8, 2, 3];
    let g = G(&a[..]);
    let d: &dyn Get = &g;
    let i: usize = kani::any();
    kani::assume(i < 3);
    assert!(d.get(i) != 3);
}

#[kani::proof]
fn safe_reference_field_index() {
    let a = [4u8, 5];
    let g = G(&a[..]);
    let r = &g;
    assert!(r.0[1] == 5 && r.0.len() == 2);
}

#[kani::proof]
fn bug_reference_field_index() {
    let a = [4u8, 5];
    let g = G(&a[..]);
    let r = &g;
    assert!(r.0[0] == 5);
}

#[kani::proof]
fn bug_dyn_out_of_bounds() {
    let a = [1u8, 2, 3];
    let g = G(&a[..2]);
    let d: &dyn Get = &g;
    let i: usize = kani::any();
    kani::assume(i < 3);
    let _ = d.get(i);
}
