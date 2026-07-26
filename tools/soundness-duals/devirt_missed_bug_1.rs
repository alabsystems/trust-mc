// SOUNDNESS DUAL (missed-bug tripwire) — MISSED-BUG B: dyn-coercion devirt
// under-collection on a NESTED field (`outer.inner`) coerced to &dyn Trait and
// dispatched cross-function.
//
// EXPECTED VERDICT: VERIFICATION:- FAILED. The true dynamic callee is
// Inner::id (returns inner_id); the assert compares against outer_id. If
// devirt under-collects candidates and resolves the dyn callsite to the
// parametric Outer<T> impl (which yields outer_id), the assert "passes" and a
// real bug is missed: false-Safe channel open. Never delete, never weaken.
//
// Reconstructed 2026-07-19 from archived artifacts
//   patches/devirt_missed_bug_1__RNvCsPKeZPc22za_19devirt_missed_bug_1
//     35check_inner_dyn_coercion_missed_bug.symtab.{smt2,vc.json}
// (datatypes Inner{fld_id:bv8}, Outer_Inner{fld_outer_id:bv8, fld_inner},
//  Dyn_Trait fat pointer, final check `_9 == zero_extend(outer_id)`).
//
// Property multiset (archived vc.json):
//   memory_safety x4
//   assertion "assertion failed: id_from_dyn(&outer.inner) == outer_id.into()"

pub trait Identity {
    fn id(&self) -> u16;
}

pub struct Inner {
    pub id: u8,
}

pub struct Outer<T> {
    pub outer_id: u8,
    pub inner: T,
}

impl Identity for Inner {
    fn id(&self) -> u16 {
        self.id.into()
    }
}

// Parametric impl: a naive devirt that picks this impl for the `&outer.inner`
// callsite reports outer_id and falsely satisfies the assert below.
impl<T: Identity> Identity for Outer<T> {
    fn id(&self) -> u16 {
        self.outer_id.into()
    }
}

// Dispatch happens cross-function: the dyn callsite is here, not in the harness.
fn id_from_dyn(x: &dyn Identity) -> u16 {
    x.id()
}

#[kani::proof]
fn check_inner_dyn_coercion_missed_bug() {
    let inner_id: u8 = kani::any();
    let outer_id: u8 = kani::any();
    let outer = Outer { outer_id, inner: Inner { id: inner_id } };
    // REAL bug: the true dynamic id is inner_id, which differs from outer_id
    // on some inputs -> must FAIL.
    assert!(id_from_dyn(&outer.inner) == outer_id.into());
}
