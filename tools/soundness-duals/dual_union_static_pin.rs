// Copyright Andrew Yates. Apache-2.0 OR MIT
//
// Soundness duals for the union-static zero-fill pin + BV-rooted array-index
// select (codegen_decl_static_alloc.rs scalar_from_alloc fallback +
// codegen_expr.rs bv_array_index_select).
//
// The fix REPLACES a demotion net (static_init_incomplete havoc) with a
// CONCRETE value pin, so these duals prove the pin is the REAL stored value,
// not a force-pass:
//   union_static_value_correct — MUST SUCCEED: a[1] really is 9.
//   union_static_value_wrong   — MUST FAIL (Genuine): a[1] == 10 is false.
//   union_transmute_padding_wrong — MUST FAIL: y == 257 requires padding == 1,
//     but the static image zero-fills padding (y == 256).

#[repr(C)]
#[derive(Clone, Copy)]
union Data {
    a: [u8; 3],
    b: u16,
}

static FOO: Data = Data { a: [7, 9, 11] };
static BAR: Data = Data { a: [0, 1, 0] };

#[kani::proof]
fn union_static_value_correct() {
    unsafe {
        assert!(FOO.a[1] == 9);
    }
}

#[kani::proof]
fn union_static_value_wrong() {
    unsafe {
        assert!(FOO.a[1] == 10);
    }
}

#[kani::proof]
fn union_transmute_padding_wrong() {
    // BAR bytes are [0, 1, 0, <uninit padding -> 0>]; as little-endian u32
    // that is 0x0000_0100 = 256. Asserting 257 must produce a Genuine CTREX.
    let y: u32 = unsafe { std::mem::transmute(BAR) };
    assert!(y == 257);
}
