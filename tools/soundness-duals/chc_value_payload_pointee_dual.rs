// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: a narrow `Option<&scalar>` (or like enum) payload
// stores the POINTEE's value, read at the aggregate
// (stmt/codegen_stmt_value_ref_payload.rs). That value stands for every later
// read through the payload only when nothing writes or frees the pointee while
// the reference lives. No lane checks aliasing, and Kani and a debug build read
// the WRITTEN value, so these programs — undefined aliasing behaviour under
// Stacked and Tree Borrows — still have to see the write. The third review of
// fix/chc-false-certificates (2026-09-27; main c22e1022e and the branch bundle
// bb9a5efcfb57, ay 22db3bcc1, chc, 30 s) measured:
// - a write after the aggregate through the static itself, `Cell::set`, or a
//   callee that writes the static: bug_static_write_reads_old,
//   bug_cell_write_reads_old, bug_callee_static_write clean proofs on the
//   branch (main FAILED Genuine), and the safe twins FAILED certified Genuine
//   on both;
// - a pointee freed after the aggregate lost its use-after-free check on both:
//   bug_heap_uaf SUCCESSFUL where Kani reports a dead object.
// The aggregate now keeps the value only for a pointee rooted at a body local
// that dereferences nothing and that no pointer the body builds can write; any
// other pointee is a fresh value with a fail-closed booking
// (`enum_ref_payload_pointee_not_frozen`), so the safe rows here are
// false-failures, not proofs.

static mut G1: u8 = 1;
static mut G2: u8 = 1;
static mut G3: u8 = 1;
static mut G4: u8 = 1;
static mut G5: u8 = 1;
static mut G6: u8 = 1;

#[kani::proof]
fn safe_static_write_reads_new() {
    let o = Some(unsafe { &*core::ptr::addr_of!(G1) });
    unsafe { G1 = 2 };
    assert!(*o.unwrap() == 2);
}

#[kani::proof]
fn bug_static_write_reads_old() {
    let o = Some(unsafe { &*core::ptr::addr_of!(G2) });
    unsafe { G2 = 2 };
    assert!(*o.unwrap() == 1);
}

#[kani::proof]
fn bug_static_write_match() {
    let o = Some(unsafe { &*core::ptr::addr_of!(G3) });
    unsafe { G3 = 2 };
    match o {
        Some(r) => assert!(*r == 1),
        None => {}
    }
}

#[kani::proof]
fn bug_callee_static_write() {
    fn bump() {
        unsafe { G4 = 2 };
    }
    let o = Some(unsafe { &*core::ptr::addr_of!(G4) });
    bump();
    assert!(*o.unwrap() == 1);
}

#[kani::proof]
fn safe_cell_write_reads_new() {
    let c = core::cell::Cell::new(5u8);
    let o = Some(unsafe { &*c.as_ptr() });
    c.set(7);
    assert!(*o.unwrap() == 7);
}

#[kani::proof]
fn bug_cell_write_reads_old() {
    let c = core::cell::Cell::new(5u8);
    let o = Some(unsafe { &*c.as_ptr() });
    c.set(7);
    assert!(*o.unwrap() == 5);
}

#[kani::proof]
fn bug_heap_uaf() {
    let p = Box::into_raw(Box::new(5u8));
    let o = Some(unsafe { &*p });
    unsafe { drop(Box::from_raw(p)) };
    let v = *o.unwrap();
    assert!(v == 5 || v != 5);
}

#[kani::proof]
fn bug_vec_realloc_dangling() {
    let mut v: Vec<u8> = Vec::with_capacity(1);
    v.push(3);
    let p = v.as_ptr();
    let o = Some(unsafe { &*p });
    v.push(4);
    v.push(5);
    let x = *o.unwrap();
    assert!(x == 3 || x != 3);
}

// A pointee no write can reach keeps the value (the rows the value lane
// exists for).
#[kani::proof]
fn safe_local_pointee_frozen() {
    let m: u8 = kani::any();
    let o = Some(&m);
    assert!(*o.unwrap() == m);
}

#[kani::proof]
fn bug_local_pointee_frozen() {
    let m: u8 = kani::any();
    let o = Some(&m);
    assert!(*o.unwrap() == 1);
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_static_write_reads_new() {
    let o = Some(unsafe { &*core::ptr::addr_of!(G5) });
    unsafe { G5 = 2 };
    assert!(*o.unwrap() == 2);
}

#[kani::proof]
#[kani::should_panic]
fn sp_cell_write_reads_new() {
    let c = core::cell::Cell::new(5u8);
    let o = Some(unsafe { &*c.as_ptr() });
    c.set(7);
    assert!(*o.unwrap() == 7);
}

#[kani::proof]
#[kani::should_panic]
fn sp_heap_uaf() {
    let p = Box::into_raw(Box::new(5u8));
    let o = Some(unsafe { &*p });
    unsafe { drop(Box::from_raw(p)) };
    let v = *o.unwrap();
    if v == 5 {
        panic!("reached");
    }
}

#[kani::proof]
#[kani::should_panic]
fn sp_static_callee_write() {
    fn bump() {
        unsafe { G6 = 2 };
    }
    let o = Some(unsafe { &*core::ptr::addr_of!(G6) });
    bump();
    assert!(*o.unwrap() == 2);
}
