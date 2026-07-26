// P3-uninit dual (net-guard): a punned typed WRITE (the delayed-UB shape,
// task #24) must STILL hit the fail-closed punned-cast demotion — the
// pun-scan only exempts copy/mem-init/read flows, never deref writes.
// Oracle: must NOT prove (FAILED or Unknown, with chc_fallback demotion).
// kani-flags: -Z uninit-checks

#[kani::proof]
unsafe fn pun_write_still_demoted() {
    let mut x: u64 = kani::any();
    // Size-mismatched pun (8 -> 4) with a typed WRITE through it:
    // the (u16, u8) store re-shapes padding inside the u64 in ways the
    // scalar shadow model cannot track.
    let p = &mut x as *mut u64 as *mut (u16, u8);
    *p = (1u16, 2u8);
    let y = x;
    assert!(y == y);
}
