// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: the third review of fix/chc-false-certificates
// (finding 9) asked whether the escape analysis could admit a narrow
// `Option<&u8>` payload reference handed to a crate function that casts it to
// a raw pointer (`fn read_raw(r: &u8) -> u8 { unsafe { *(r as *const u8) } }`),
// where main was exact. It cannot: the slot holds the pointee's VALUE, not its
// address, and a raw pointer derived from the payload reference can WRITE the
// pointee. That write is aliasing UB, but neither Kani nor a debug build checks
// aliasing, and both read the written value, so a payload that kept the value
// read at the aggregate would miss it. Main c22e1022e (which resolves such a
// cast through the single producer's points-at edge) proves the bug row clean
// and certifies the safe twin Genuine; the branch fails closed on all of them
// (ay 22db3bcc1, chc, 30 s, 2026-09-28).
#![allow(invalid_reference_casting)]

fn read_raw(r: &u8) -> u8 {
    let p = r as *const u8;
    unsafe { *p }
}

fn write_raw(r: &u8, v: u8) {
    unsafe { *(r as *const u8 as *mut u8) = v }
}

#[inline(never)]
fn write_raw_ni(r: &u8, v: u8) {
    unsafe { *(r as *const u8 as *mut u8) = v }
}

#[kani::proof]
fn safe_read_raw_zero() {
    let m: u8 = 0;
    let o = Some(&m);
    assert!(read_raw(o.unwrap()) == 0);
}

#[kani::proof]
fn bug_write_raw_reads_old() {
    let m: u8 = 5;
    let o = Some(&m);
    write_raw(o.unwrap(), 2);
    assert!(*o.unwrap() == 5);
}

#[kani::proof]
fn safe_write_raw_reads_new() {
    let m: u8 = 5;
    let o = Some(&m);
    write_raw(o.unwrap(), 2);
    assert!(*o.unwrap() == 2);
}

#[kani::proof]
fn bug_write_raw_callee_reads_old() {
    let m: u8 = 5;
    let o = Some(&m);
    write_raw_ni(o.unwrap(), 2);
    assert!(*o.unwrap() == 5);
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_write_raw_reads_new() {
    let m: u8 = 5;
    let o = Some(&m);
    write_raw(o.unwrap(), 2);
    assert!(*o.unwrap() == 2);
}

#[kani::proof]
#[kani::should_panic]
fn sp_write_raw_callee_reads_new() {
    let m: u8 = 5;
    let o = Some(&m);
    write_raw_ni(o.unwrap(), 2);
    assert!(*o.unwrap() == 2);
}
