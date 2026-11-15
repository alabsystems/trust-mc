// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: two heap-pointer conventions read as ADDRESSES.
// - The slice index stubs (`Index::index`, `IndexMut::index_mut`,
//   `get_unchecked`) put the ELEMENT in the returned reference's register
//   (call/codegen_call_slice_index.rs); pointee reads resolve through
//   `const_ref_values`. A cast of that reference read the element:
//   `&v[1] as *const u8 as usize == 3` for `v = vec![2u8, 3, 4]` was a clean
//   proof where Kani fails the assertion, its should_panic twin passed, and
//   `ptr::eq(&v[1], v.as_ptr().add(1))` FAILED certified Genuine.
// - `vec![e; n]` whose fill the encoder cannot materialize (a symbolic `n`)
//   returned a FREE buffer pointer: `*v.as_ptr()` read anything and
//   `v.as_ptr()` could equal `&x`, both certified Genuine.
// Measured on main c22e1022e and on fix/chc-false-certificates before the fix
// alike (ay 22db3bcc1, chc, 30 s), found probing the third review's heap-address
// findings (2026-09-28). An index result that reaches an address reader, and
// an unbound from_elem pointer, now fail closed; value readers stay exact.

#[kani::proof]
fn bug_index_addr_const() {
    let v = vec![2u8, 3, 4];
    assert!(&v[1] as *const u8 as usize == 3);
}

#[kani::proof]
fn safe_index_addr_nonnull() {
    let v = vec![2u8, 3, 4];
    assert!(&v[1] as *const u8 as usize != 0);
}

#[kani::proof]
fn safe_index_ptr_eq() {
    let v = vec![2u8, 3, 4];
    assert!(core::ptr::eq(&v[1], unsafe { v.as_ptr().add(1) }));
}

#[kani::proof]
fn bug_index_ptr_eq() {
    let v = vec![2u8, 3, 4];
    assert!(core::ptr::eq(&v[1], v.as_ptr()));
}

#[kani::proof]
fn safe_index_raw_cmp() {
    let v = vec![2u8, 3, 4];
    let p = &v[1] as *const u8;
    let q = unsafe { v.as_ptr().add(1) };
    assert!(p == q);
}

#[kani::proof]
fn safe_index_vs_stack() {
    let x = 1u8;
    let v = vec![2u8, 3, 4];
    let ax = &x as *const u8 as usize;
    let av = (&v[1] as *const u8) as usize;
    assert!(ax != av);
}

#[kani::proof]
fn safe_index_deref_raw() {
    let v = vec![2u8, 3, 4];
    let p = &v[1] as *const u8;
    assert!(unsafe { *p } == 3);
}

#[kani::proof]
fn bug_index_deref_raw() {
    let v = vec![2u8, 3, 4];
    let p = &v[1] as *const u8;
    assert!(unsafe { *p } == 2);
}

#[kani::proof]
fn bug_index_mut_addr_const() {
    let mut v = vec![2u8, 3, 4];
    let r = &mut v[1];
    assert!(r as *mut u8 as usize == 3);
}

#[kani::proof]
fn safe_index_mut_store() {
    let mut v = vec![2u8, 3, 4];
    v[1] = 9;
    v[2] += 1;
    assert!(v[1] == 9 && v[2] == 5);
}

#[kani::proof]
fn bug_index_mut_store() {
    let mut v = vec![2u8, 3, 4];
    v[1] = 9;
    assert!(v[1] == 3);
}

#[kani::proof]
fn safe_index_assert_eq() {
    let v = vec![2u8, 3, 4];
    assert_eq!(v[1], 3);
}

#[kani::proof]
fn bug_index_assert_eq() {
    let v = vec![2u8, 3, 4];
    assert_eq!(v[1], 4);
}

#[kani::proof]
fn safe_from_elem_nd_deref() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let v = vec![7u8; n];
    assert!(unsafe { *v.as_ptr() } == 7);
}

#[kani::proof]
fn safe_from_elem_nd_ptr_eq_stack() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let x = 1u8;
    let v = vec![7u8; n];
    assert!(!core::ptr::eq(v.as_ptr(), &x));
}

#[kani::proof]
fn safe_from_elem_nd_vs_stack() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let x = 1u8;
    let v = vec![7u8; n];
    assert!(v.as_ptr() as usize != &x as *const u8 as usize);
}

#[kani::proof]
fn safe_from_elem_nd_index() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let v = vec![7u8; n];
    assert!(v[0] == 7 && v.len() == n);
}

#[kani::proof]
fn bug_from_elem_nd_index() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let v = vec![7u8; n];
    assert!(v[0] == 8);
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_index_addr_const() {
    let v = vec![2u8, 3, 4];
    assert!(&v[1] as *const u8 as usize != 3);
}

#[kani::proof]
#[kani::should_panic]
fn sp_index_ptr_eq() {
    let v = vec![2u8, 3, 4];
    assert!(core::ptr::eq(&v[1], unsafe { v.as_ptr().add(1) }));
}

#[kani::proof]
#[kani::should_panic]
fn sp_from_elem_nd_ptr_eq_stack() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let x = 1u8;
    let v = vec![7u8; n];
    assert!(!core::ptr::eq(v.as_ptr(), &x));
}

#[kani::proof]
#[kani::should_panic]
fn sp_index_raw_cmp() {
    let v = vec![2u8, 3, 4];
    let p = &v[1] as *const u8;
    let q = unsafe { v.as_ptr().add(1) };
    assert!(p == q);
}

#[kani::proof]
#[kani::should_panic]
fn sp_index_vs_stack() {
    let x = 1u8;
    let v = vec![2u8, 3, 4];
    let ax = &x as *const u8 as usize;
    let av = (&v[1] as *const u8) as usize;
    assert!(ax != av);
}

#[kani::proof]
#[kani::should_panic]
fn sp_index_mut_addr_const() {
    let mut v = vec![2u8, 3, 4];
    let r = &mut v[1];
    assert!(r as *mut u8 as usize != 3);
}

#[kani::proof]
#[kani::should_panic]
fn sp_from_elem_nd_deref() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let v = vec![7u8; n];
    assert!(unsafe { *v.as_ptr() } == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_from_elem_nd_vs_stack() {
    let n: usize = kani::any();
    kani::assume(n > 0 && n < 4);
    let x = 1u8;
    let v = vec![7u8; n];
    assert!(v.as_ptr() as usize != &x as *const u8 as usize);
}

// A Cell method through an index result writes through the reference: main
// lost the write (`v[0].set(9); v[0].get() == 9` FAILED certified Genuine), so
// the harness fails closed.
#[kani::proof]
fn safe_vec_cell_set_get() {
    let v = vec![std::cell::Cell::new(0u32), std::cell::Cell::new(1u32)];
    v[0].set(9);
    assert!(v[0].get() == 9 && v[1].get() == 1);
}

#[kani::proof]
fn bug_vec_cell_set_get() {
    let v = vec![std::cell::Cell::new(0u32), std::cell::Cell::new(1u32)];
    v[0].set(9);
    assert!(v[0].get() == 0);
}

#[kani::proof]
fn safe_vec_cell_replace() {
    let v = vec![std::cell::Cell::new(4u32)];
    let old = v[0].replace(5);
    assert!(old == 4 && v[0].get() == 5);
}

#[kani::proof]
#[kani::should_panic]
fn sp_vec_cell_set_get() {
    let v = vec![std::cell::Cell::new(0u32), std::cell::Cell::new(1u32)];
    v[0].set(9);
    assert!(v[0].get() == 9 && v[1].get() == 1);
}

#[kani::proof]
#[kani::should_panic]
fn sp_vec_cell_replace() {
    let v = vec![std::cell::Cell::new(4u32)];
    let old = v[0].replace(5);
    assert!(old == 4 && v[0].get() == 5);
}

// Measured precision cost (fourth review of fix/chc-false-certificates,
// 2026-09-28): an index result handed to a crate function that reads its
// address fails closed (index_ref_value_escapes) where main was exact on this
// program; main is unsound on sibling shapes (safe_index_ptr_eq above is a
// Genuine false certificate there). The safe row expects Kani's SUCCESSFUL and is
// a known-red false failure (decision C7, 2026-10-14).
#[inline(never)]
fn addr_of_u8(r: &u8) -> usize {
    r as *const u8 as usize
}

#[kani::proof]
fn safe_index_addr_via_fn() {
    let v = vec![1u8, 2, 3];
    assert!(addr_of_u8(&v[1]) == addr_of_u8(&v[0]) + 1);
}

#[kani::proof]
fn bug_index_addr_via_fn() {
    let v = vec![1u8, 2, 3];
    assert!(addr_of_u8(&v[1]) == addr_of_u8(&v[0]));
}
