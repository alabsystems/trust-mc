// SOUNDNESS DUAL (missed-bug tripwire) — MISSED-BUG C: vtable discriminant lost
// through a smart pointer (Box<dyn Trait>) whose Unsize coercion is HIDDEN from
// the harness body (it happens inside a helper).
//
// EXPECTED VERDICT: VERIFICATION:- FAILED. Real semantics: s = 7 + extra with
// extra in [1000, 2000) => s >= 1007, so assert!(s < 1000) is violated. If the
// hidden-coercion candidate is under-collected and the dispatch through the
// smartptr loses the concrete impl (Loud<Cat>), the violation is missed:
// false-Safe channel open. Never delete, never weaken.
//
// Sibling control (coercion VISIBLE in the harness body) survives at
//   audit/vtable-smartptr-discriminant-loss_control.rs
// Reconstructed 2026-07-19 from archived artifacts
//   audit/vtable_smartptr_discriminant_loss_repro__RNvCs6BtUL5QdGCf_39...5check
//     .symtab.{smt2,vc.json}
// (datatype Loud_Cat{fld_0, fld_1:bv32}; constants 1000/2000/7; the inlined
//  dispatch computes `bvadd 7 extra`).
//
// Property multiset (archived vc.json):
//   memory_safety x12
//   assertion "assertion failed: s < 1000"

trait Speak {
    fn sound(&self) -> u32;
}

struct Cat;
impl Speak for Cat {
    fn sound(&self) -> u32 {
        7
    }
}

struct Loud<T>(T, u32);
impl<T: Speak> Speak for Loud<T> {
    fn sound(&self) -> u32 {
        self.0.sound().wrapping_add(self.1)
    }
}

// The Box<Loud<Cat>> -> Box<dyn Speak> Unsize coercion happens HERE, outside
// the harness body, so harness-body candidate scans do not see it.
fn make_loud(extra: u32) -> Box<dyn Speak> {
    Box::new(Loud(Cat, extra))
}

#[kani::proof]
fn check() {
    let extra: u32 = kani::any();
    kani::assume(extra >= 1000 && extra < 2000);
    let b: Box<dyn Speak> = make_loud(extra);
    let s = b.sound();
    // Real Rust: s = 7 + extra >= 1007 -> must FAIL.
    assert!(s < 1000);
}
