// gate-flags: -Zfunction-contracts
// fc-interior-mut DUAL (b) — FC-06 modifies-frame violation on the RECOVERED
// real (obj_id, offset) address.
//
// MUST stay VERIFICATION:- FAILED after the fc-interior-mut fix.
//
// `y: Cell<u32>` is NOT in the modifies clause (only &im.x is), but the body
// also writes im.y. The FC-06 frame check must fire on the recovered real
// store address (obj of `im`, offset of field y), proving the fix made the
// frame check PRECISE rather than dropped. Guards against repeating
// MISSED-BUG E (modifies-frame store offset-drop, fixed in 0c366f397 /
// 57975a98d): if pointer-identity recovery collapsed field offsets or the
// frame check were skipped when provenance is recovered, this would pass
// falsely.

use std::cell::Cell;

struct InteriorMutability {
    x: Cell<u32>,
    y: Cell<u32>,
}

#[kani::requires(im.x.get() < 100)]
#[kani::modifies(&im.x)]
#[kani::ensures(|_| im.x.get() < 101)]
fn modify(im: &InteriorMutability) {
    im.x.set(im.x.get() + 1);
    // BUG: writes a field OUTSIDE the declared modifies footprint.
    im.y.set(0);
}

#[kani::proof_for_contract(modify)]
fn harness_for_modify() {
    let im: InteriorMutability =
        InteriorMutability { x: Cell::new(kani::any()), y: Cell::new(kani::any()) };
    modify(&im)
}
