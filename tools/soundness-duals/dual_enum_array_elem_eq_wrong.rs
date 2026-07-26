// SOUNDNESS DUAL (missed-bug tripwire for the enum-element-read-eq fix).
//
// EXPECTED VERDICT: VERIFICATION:- FAILED (Genuine).
//
// The array holds `Some(7)`, but the assertion claims `Some(8)`. The equality
// is genuinely FALSE for every in-bounds index. A SUCCESS here would mean the
// enum-literal-consistency fix over-forced equality to true — a false-Safe
// channel that hides a real assertion violation. Never delete, never weaken.
#[kani::proof]
fn check() {
    let a = [Some(7u8); 5];
    let i: usize = kani::any();
    kani::assume(i < 5);
    assert_eq!(a[i], Some(8));
}
