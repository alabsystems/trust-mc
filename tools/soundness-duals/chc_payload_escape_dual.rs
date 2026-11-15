// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
//
// WHY THIS FILE EXISTS: an enum payload slot that holds a pointee's VALUE (a
// narrow `Option<&u8>`-like aggregate, the slice iterator stub's element, an
// inlined `first()`) read by something that wants the reference's ADDRESS.
// The third review of fix/chc-false-certificates (2026-09-27; main c22e1022e
// and the branch bundle bb9a5efcfb57, ay 22db3bcc1, chc, 30 s) measured, on
// both bundles:
// - a call result's payload reaching an address reader through an
//   `Option::map` closure, `core::hint::black_box` or a move into a struct
//   (the guard was a denylist over copy/unwrap carriers):
//   safe_iter_map_addr, safe_first_map_ptr_eq, safe_iter_black_box,
//   safe_iter_struct64_ptr_eq FAILED certified Genuine, sp_iter_map_addr
//   passed;
// - a user enum with one narrow `&u8` payload moved into an array or a tuple
//   (the escape analysis keyed on the name `Option`): safe_custom_enum_array_val,
//   safe_custom_enum_array_ptr_eq, safe_custom_enum_tuple_ptr_eq FAILED
//   certified Genuine, sp_custom_enum_array_ptr_eq passed.
// Every reader of such a payload is now an admitted value reader or the
// harness books `enum_ref_payload_escapes` / `payload_value_fact_address_reader`
// (fail closed), and the narrow-payload check is by shape. The safe rows here
// are therefore false-failures, not proofs; what they pin is that none of them
// is a certified counterexample.
//
// read_raw: a payload reference handed to a crate-local function that casts it
// to a raw pointer and reads through it. The kani inliner inlines the callee,
// and its `&raw const (*r)` plus rustc's null check read the reference's
// ADDRESS, which the narrow slot does not hold: the harness fails closed
// (main was exact here through the single producer's points-at edge), a
// measured precision cost (docs/chc-hole-fix-designs-2026-09-24.md).

struct S64<'a> {
    o: Option<&'a u64>,
}

#[derive(Clone, Copy)]
enum MyOpt<'a> {
    Nope,
    Yes(&'a u8),
}

fn read_raw(r: &u8) -> u8 {
    let p = r as *const u8;
    unsafe { *p }
}

#[kani::proof]
fn safe_iter_map_addr() {
    let a = [1u8, 2, 3];
    let o = a.iter().next();
    let ad = o.map(|r| r as *const u8 as usize).unwrap();
    assert!(ad == a.as_ptr() as usize);
}

#[kani::proof]
fn safe_iter_map_addr64() {
    let a = [1u64, 2, 3];
    let o = a.iter().next();
    let ad = o.map(|r| r as *const u64 as usize).unwrap();
    assert!(ad == a.as_ptr() as usize);
}

#[kani::proof]
fn safe_first_map_ptr_eq() {
    let a = [1u8, 2, 3];
    let o = a.first();
    assert!(o.map(|r| core::ptr::eq(r, &a[0])).unwrap());
}

#[kani::proof]
fn safe_iter_black_box() {
    let a = [1u8, 2, 3];
    let o = a.first();
    let r = core::hint::black_box(o.unwrap());
    assert!(core::ptr::eq(r, &a[0]));
}

#[kani::proof]
fn safe_iter_struct64_ptr_eq() {
    let a = [1u64, 2, 3];
    let s = S64 { o: a.iter().next() };
    assert!(core::ptr::eq(s.o.unwrap(), &a[0]));
}

#[kani::proof]
fn safe_custom_enum_array_val() {
    let m: u8 = kani::any();
    let arr = [MyOpt::Yes(&m), MyOpt::Nope];
    if let MyOpt::Yes(r) = arr[0] {
        assert!(*r == m);
    }
}

#[kani::proof]
fn bug_custom_enum_array_val() {
    let m: u8 = kani::any();
    let arr = [MyOpt::Yes(&m), MyOpt::Nope];
    if let MyOpt::Yes(r) = arr[0] {
        assert!(*r == 1);
    }
}

#[kani::proof]
fn safe_custom_enum_array_ptr_eq() {
    let m: u8 = 9;
    let arr = [MyOpt::Yes(&m), MyOpt::Nope];
    if let MyOpt::Yes(r) = arr[0] {
        assert!(core::ptr::eq(r, &m));
    }
}

#[kani::proof]
fn safe_custom_enum_tuple_ptr_eq() {
    let m: u8 = 9;
    let t = (MyOpt::Yes(&m), 1u8);
    if let MyOpt::Yes(r) = t.0 {
        assert!(core::ptr::eq(r, &m));
    }
}

#[kani::proof]
fn safe_local_fn_read_raw() {
    let m: u8 = kani::any();
    let o = Some(&m);
    assert!(read_raw(o.unwrap()) == m);
}

#[kani::proof]
fn bug_local_fn_read_raw() {
    let m: u8 = kani::any();
    let o = Some(&m);
    assert!(read_raw(o.unwrap()) == 1);
}

// ---- should_panic twins: each body never panics ----

#[kani::proof]
#[kani::should_panic]
fn sp_iter_map_addr() {
    let a = [1u8, 2, 3];
    let o = a.iter().next();
    let ad = o.map(|r| r as *const u8 as usize).unwrap();
    assert!(ad == a.as_ptr() as usize);
}

#[kani::proof]
#[kani::should_panic]
fn sp_first_map_ptr_eq() {
    let a = [1u8, 2, 3];
    let o = a.first();
    assert!(o.map(|r| core::ptr::eq(r, &a[0])).unwrap());
}

#[kani::proof]
#[kani::should_panic]
fn sp_custom_enum_array_ptr_eq() {
    let m: u8 = 9;
    let arr = [MyOpt::Yes(&m), MyOpt::Nope];
    if let MyOpt::Yes(r) = arr[0] {
        assert!(core::ptr::eq(r, &m));
    }
}

#[kani::proof]
#[kani::should_panic]
fn sp_custom_enum_array_val() {
    let m: u8 = kani::any();
    let arr = [MyOpt::Yes(&m), MyOpt::Nope];
    if let MyOpt::Yes(r) = arr[0] {
        assert!(*r == m);
    }
}

// Measured precision cost (fourth review of fix/chc-false-certificates,
// 2026-09-28): a narrow Option<&u8> payload handed to a crate function that
// compares its address fails closed (enum_ref_payload_escapes) where main was
// exact on this program; main certifies Genuine false counterexamples on
// sibling shapes (the same comparison against the pointee itself). The safe row
// expects Kani's SUCCESSFUL and is a known-red false failure (decision C7).
#[inline(never)]
fn opt_same(o: Option<&u8>, b: &u8) -> bool {
    match o {
        Some(r) => core::ptr::eq(r, b),
        None => false,
    }
}

#[kani::proof]
fn safe_opt_payload_same_via_fn() {
    let m = 3u8;
    let n = 3u8;
    let o = Some(&m);
    assert!(!opt_same(o, &n));
}

#[kani::proof]
fn bug_opt_payload_same_via_fn() {
    let m = 3u8;
    let n = 3u8;
    let o = Some(&m);
    assert!(opt_same(o, &n));
}
