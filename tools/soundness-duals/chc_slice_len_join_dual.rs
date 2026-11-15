// Oracle: corpus-rev Kani 4c0fce8c3, measured 2026-09-25: every `bug_` harness
// FAILS and every `safe_` harness is SUCCESSFUL.
//
// WHY THIS FILE EXISTS: design 4 of docs/chc-hole-fix-designs-2026-09-24.md
// predicted the array-to-slice length hole beyond loops. Measured on main
// 25905b622 (ay 643b2851f), strict dual gate, chc lane: bug_join_len_zero,
// bug_join_same_len_zero, bug_join_nonempty_is_empty, bug_raw_ptr_join_len_zero
// and bug_join_through_callee PROVED (SUCCESSFUL, [AY:PROOF_QUALIFIERS:clean]),
// safe_join_len_is_one_of_the_two FAILED certified Genuine (a false
// certificate), and the three other safe_ rows FAILED OverApproximation
// (ptr_metadata_unconstrained). The unsize cast `&[u8; N] -> &[u8]`
// zero-extended the thin operand into the wide slot, and a slice local with two
// definitions is read from that slot's high half, which was the zero padding.
// The `safe_` twins guard precision: a fix that merely havocs the length would
// turn them into false failures.

// A join of two array-backed slices must keep each path's own length.
#[kani::proof]
fn bug_join_len_zero() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    assert!(s.len() == 0);
}

#[kani::proof]
fn bug_join_same_len_zero() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 3] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    assert!(s.len() == 0);
}

#[kani::proof]
fn bug_join_nonempty_is_empty() {
    let a: [u8; 3] = [1, 2, 3];
    let b: [u8; 0] = [];
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    assert!(s.is_empty());
}

#[kani::proof]
fn safe_join_len_is_one_of_the_two() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    assert!(s.len() == 3 || s.len() == 5);
}

// The subslice borrow `rest = &(*bytes)[1..]` carries `len - 1`: the second
// trip round the loop must see length 2, not 0.
#[kani::proof]
fn bug_subslice_second_trip() {
    let a: [u8; 4] = kani::any();
    let mut bytes: &[u8] = &a;
    while let [_first, rest @ ..] = bytes {
        assert!(rest.len() != 2);
        bytes = rest;
    }
}

#[kani::proof]
fn safe_subslice_tracks_length() {
    let a: [u8; 4] = kani::any();
    let mut bytes: &[u8] = &a;
    let mut n: usize = 0;
    while let [_first, rest @ ..] = bytes {
        assert!(rest.len() + n + 1 == 4);
        bytes = rest;
        n += 1;
    }
}

// Vec-backed: `as_slice` on a Vec writes the Vec's length into the slot.
#[kani::proof]
fn bug_vec_backed_loop() {
    let v: Vec<u8> = vec![1, 2, 3];
    let mut bytes = v.as_slice();
    let mut n: u32 = 0;
    while let [_first, rest @ ..] = bytes {
        bytes = rest;
        n += 1;
    }
    assert!(n == 0);
}

// A join of two raw-pointer unsizes: the `*const [T; N] -> *const [T]` form.
#[kani::proof]
fn bug_raw_ptr_join_len_zero() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 4] = kani::any();
    let c: bool = kani::any();
    let p: *const [u8] = if c { &a as *const [u8; 3] } else { &b as *const [u8; 4] };
    assert!(p.len() == 0);
}

fn slice_len(s: &[u8]) -> usize {
    s.len()
}

// A joined slice passed to a callee reads its length inside the callee.
#[kani::proof]
fn bug_join_through_callee() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    assert!(slice_len(s) == 0);
}

// A from-end subslice (`[_, mid @ .., _]`) of a joined slice.
#[kani::proof]
fn bug_mid_subslice_join_len_zero() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    if let [_, mid @ .., _] = s {
        assert!(mid.len() == 0);
    }
}

#[kani::proof]
fn safe_mid_subslice_join_len() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    if let [_, mid @ .., _] = s {
        assert!(mid.len() + 2 == s.len());
    }
}

struct Dst<T: ?Sized> {
    hdr: u8,
    data: T,
}

// The field chain down a joined custom-DST reference keeps its length.
#[kani::proof]
fn bug_dst_tail_join_len_zero() {
    let d1: Dst<[u8; 2]> = Dst { hdr: 1, data: [0; 2] };
    let d2: Dst<[u8; 5]> = Dst { hdr: 2, data: [0; 5] };
    let c: bool = kani::any();
    let r: &Dst<[u8]> = if c { &d1 } else { &d2 };
    let s: &[u8] = &r.data;
    assert!(s.len() == 0);
}

#[kani::proof]
fn safe_dst_tail_join_len() {
    let d1: Dst<[u8; 2]> = Dst { hdr: 1, data: [0; 2] };
    let d2: Dst<[u8; 5]> = Dst { hdr: 2, data: [0; 5] };
    let c: bool = kani::any();
    let r: &Dst<[u8]> = if c { &d1 } else { &d2 };
    let s: &[u8] = &r.data;
    assert!(s.len() == 2 || s.len() == 5);
}

// Precision guard for the promoted-constant producers: `&str == "literal"`
// derefs a promoted `&&str`, whose inner wide pointer must carry the
// constant's length (an intermediate design 4 build read the first byte and
// failed every such comparison closed).
#[kani::proof]
fn safe_str_eq_literal() {
    let name: &str = "hello";
    assert!(name == "hello");
}

#[kani::proof]
fn bug_str_ne_literal() {
    let name: &str = "hello";
    assert!(name != "hello");
}

// The too-large direction. Every row above catches a length that is too SMALL
// (`len == 0`, `is_empty()`); a regression that wrote the LONGER arm's length
// on both paths would pass all of them, and it hides an out-of-bounds read.
// The two *_len_is_longer rows state it on the length alone. Each
// *_index_past_shorter row indexes one past the shorter arm on that arm's path;
// each safe_ twin indexes within the shorter arm (review of
// fix/chc-slice-length, 2026-09-26). The element read through a joined pointer
// fails closed (deref_through_path_merged_pointer, on main too), so the
// joined-index safe twins are NOT_GENUINE, not SUCCESSFUL.
#[kani::proof]
fn bug_join_short_arm_len_is_longer() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    if c {
        assert!(s.len() == 5);
    }
}

#[kani::proof]
fn bug_join_through_callee_len_is_longer() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    if c {
        assert!(slice_len(s) == 5);
    }
}

#[kani::proof]
fn bug_join_index_past_shorter() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    let _x = s[4];
}

#[kani::proof]
fn safe_join_index_within_shorter() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    let _x = s[2];
}

#[kani::proof]
fn bug_raw_ptr_join_index_past_shorter() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let p: *const [u8] = if c { &a as *const [u8; 3] } else { &b as *const [u8; 5] };
    let s: &[u8] = unsafe { &*p };
    let _x = s[4];
}

#[kani::proof]
fn safe_raw_ptr_join_index_within_shorter() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let p: *const [u8] = if c { &a as *const [u8; 3] } else { &b as *const [u8; 5] };
    let s: &[u8] = unsafe { &*p };
    let _x = s[2];
}

fn byte_at(s: &[u8], i: usize) -> u8 {
    s[i]
}

#[kani::proof]
fn bug_join_index_through_callee() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    let _x = byte_at(s, 4);
}

#[kani::proof]
fn safe_join_index_through_callee() {
    let a: [u8; 3] = kani::any();
    let b: [u8; 5] = kani::any();
    let c: bool = kani::any();
    let s: &[u8] = if c { &a } else { &b };
    let _x = byte_at(s, 2);
}

// `rest[2]` is in bounds on the first trip (length 3) and one past the end on
// the second (length 2).
#[kani::proof]
fn bug_rest_index_second_trip() {
    let a: [u8; 4] = kani::any();
    let mut bytes: &[u8] = &a;
    while let [_first, rest @ ..] = bytes {
        let _x = rest[2];
        bytes = rest;
    }
}

#[kani::proof]
fn safe_rest_index_first_trip() {
    let a: [u8; 4] = kani::any();
    let mut bytes: &[u8] = &a;
    let mut n: usize = 0;
    while let [_first, rest @ ..] = bytes {
        if n == 0 {
            let _x = rest[2];
        }
        bytes = rest;
        n += 1;
    }
}

#[kani::proof]
fn bug_dst_tail_join_index_past_shorter() {
    let d1: Dst<[u8; 2]> = Dst { hdr: 1, data: [0; 2] };
    let d2: Dst<[u8; 5]> = Dst { hdr: 2, data: [0; 5] };
    let c: bool = kani::any();
    let r: &Dst<[u8]> = if c { &d1 } else { &d2 };
    let _x = r.data[3];
}

#[kani::proof]
fn safe_dst_tail_join_index_within_shorter() {
    let d1: Dst<[u8; 2]> = Dst { hdr: 1, data: [0; 2] };
    let d2: Dst<[u8; 5]> = Dst { hdr: 2, data: [0; 5] };
    let c: bool = kani::any();
    let r: &Dst<[u8]> = if c { &d1 } else { &d2 };
    let _x = r.data[1];
}
