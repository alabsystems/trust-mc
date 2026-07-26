// CONTROL — same trait/impls/assert, but the Unsize coercion is VISIBLE in the
// harness body. This makes trust-mc's dispatch correct (or soundly imprecise),
// so it should CEX/FAIL — demonstrating the repro's defect is specific to the
// hidden-coercion candidate under-collection, not to the trait shape itself.
//
// Here `Box::new(Loud(Cat, extra))` coerces to `Box<dyn Speak>` INSIDE `check`,
// so collect_dyn_trait_candidates Phase 2 (dyn_coercion.rs:205-241) scans the
// harness body, sees the `Box<Loud<Cat>> -> Box<dyn Speak>` Unsize cast, and
// adds `Loud<Cat>` as candidate id 1. try_capture_unsize_coercion_vtable pins
// the correct const vtable id on `b`. Dispatch resolves to `Loud<Cat>::sound`:
//   s = 7 + extra >= 1007  ->  assert!(s < 1000) is VIOLATED  ->  correct CEX.

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

#[kani::proof]
fn check() {
    let extra: u32 = kani::any();
    kani::assume(extra >= 1000 && extra < 2000);
    // Coercion visible in the harness body -> Loud<Cat> becomes a candidate.
    let b: Box<dyn Speak> = Box::new(Loud(Cat, extra));
    let s = b.sound();
    // Real Rust: s = 7 + extra >= 1007. trust-mc should also see this and CEX.
    assert!(s < 1000);
}
