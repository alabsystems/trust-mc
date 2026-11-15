// Oracle: corpus-rev Kani (see the manifest entry for the measurement): every
// `bug_` harness FAILS, every `safe_` harness is SUCCESSFUL, and every `sp_`
// harness (`#[kani::should_panic]` over a program that never panics) FAILS.
// The engine may fail CLOSED on the `safe_` rows whose payload reaches a reader
// that takes it for an address (the second review's section at the end): those
// must never be certified Genuine; they expect Kani's SUCCESSFUL and are
// known-red false failures in the manifest (decision C7, 2026-10-14).
//
// WHY THIS FILE EXISTS: `translate_ty` gives `Option<&u8>` the payload sort
// `u8`, a VALUE slot. The aggregate `Some(&m)` put the reference itself in it,
// truncated to eight bits, and the pointee read through the unwrapped payload
// loaded typed memory at the zero-extended truncation (address 0, or the
// pointee's value): a cell no clause writes. With one producer the reference's
// points-at edge hid it; with two (`if b { Some(&m) } else { Some(&n) }`), a
// whole copy (`o.copied()`), `unwrap`, or a later reassignment, the edge is
// dropped and the free cell decided the verdict. On main c22e1022e every
// `safe_` row below is a false certificate and the `sp_` row an unsound pass;
// the `bug_` rows are Genuine only through the same free cell
// (review_r17_aggregate_field_join.rs `option_ref_payload_join_*` is the
// original shape). fix/chc-false-certificates stores the POINTEE's value in the
// slot and reads it back through the payload
// (stmt/codegen_stmt_value_ref_payload.rs).

#[kani::proof]
fn safe_none_join() {
    let m = 1u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { None };
    if let Some(r) = o {
        assert!(*r == 1);
    }
}

#[kani::proof]
fn bug_none_join() {
    let m = 1u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { None };
    if let Some(r) = o {
        assert!(*r == 2);
    }
}

#[kani::proof]
fn safe_u32_nondet_join() {
    let m: u32 = kani::any();
    let n: u32 = kani::any();
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    if let Some(r) = o {
        assert!(if b { *r == m } else { *r == n });
    }
}

#[kani::proof]
fn bug_u32_nondet_join() {
    let m: u32 = kani::any();
    let n: u32 = kani::any();
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    if let Some(r) = o {
        assert!(*r == m);
    }
}

#[kani::proof]
fn safe_bool_join() {
    let t = true;
    let f = false;
    let b: bool = kani::any();
    let o = if b { Some(&t) } else { Some(&f) };
    if let Some(r) = o {
        assert!(*r == b);
    }
}

#[kani::proof]
fn bug_bool_join() {
    let t = true;
    let f = false;
    let b: bool = kani::any();
    let o = if b { Some(&t) } else { Some(&f) };
    if let Some(r) = o {
        assert!(*r);
    }
}

#[kani::proof]
fn safe_copied_join() {
    let m = 3u8;
    let n = 4u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let v = o.copied().unwrap();
    assert!(v == 3 || v == 4);
}

#[kani::proof]
fn bug_copied_join() {
    let m = 3u8;
    let n = 4u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let v = o.copied().unwrap();
    assert!(v == 3);
}

#[kani::proof]
fn safe_array_element_join() {
    let a = [5u8, 6, 7];
    let i: usize = kani::any();
    kani::assume(i < 3);
    let c = 9u8;
    let b: bool = kani::any();
    let o = if b { Some(&a[i]) } else { Some(&c) };
    if let Some(r) = o {
        assert!(*r >= 5);
    }
}

#[kani::proof]
fn bug_array_element_join() {
    let a = [5u8, 6, 7];
    let i: usize = kani::any();
    kani::assume(i < 3);
    let c = 9u8;
    let b: bool = kani::any();
    let o = if b { Some(&a[i]) } else { Some(&c) };
    if let Some(r) = o {
        assert!(*r != 7);
    }
}

#[inline(never)]
fn pick<'a>(b: bool, x: &'a u8, y: &'a u8) -> Option<&'a u8> {
    if b { Some(x) } else { Some(y) }
}

#[kani::proof]
fn safe_callee_join() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    if let Some(r) = pick(b, &m, &n) {
        assert!((*r == 1) == b);
    }
}

#[kani::proof]
fn bug_callee_join() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    if let Some(r) = pick(b, &m, &n) {
        assert!(*r == 1);
    }
}

#[kani::proof]
fn safe_unwrap_then_reassign() {
    let m = 1u8;
    let n = 2u8;
    let mut o = Some(&m);
    let r = o.unwrap();
    o = Some(&n);
    assert!(*r == 1 && *o.unwrap() == 2);
}

#[kani::proof]
fn bug_unwrap_then_reassign() {
    let m = 1u8;
    let n = 2u8;
    let mut o = Some(&m);
    let r = o.unwrap();
    o = Some(&n);
    assert!(*r == 2 || o.is_none());
}

#[kani::proof]
#[kani::should_panic]
fn sp_join() {
    let m = 1u8;
    let n = 2u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    if let Some(r) = o {
        assert!((*r == 1) == b);
    }
}

// --- Second review of fix/chc-false-certificates (2026-09-27) ---------------
//
// A payload slot of 64 bits or more held the WHOLE reference on main, and every
// reader that uses it as an address (`ptr::eq`, `as *const`, a general enum's
// `&u64` field, the Option moved into an array, a Vec, a struct or through
// `as_ref`) was exact there. The first cut of the value-semantic fix stored the
// pointee value in those slots too and read it back as an address: the `_u64`
// safe rows below were FAILED [AY:CTREX_CAT:Genuine] and `sp_v64_ptr_eq`,
// `sp_v64_addr`, `sp_e3_ptr_eq` passed. Only a slot narrower than a pointer is
// value-semantic now.

#[derive(Clone, Copy)]
enum E3<'a> {
    A(&'a u64),
    B,
    C,
}

struct W64<'a> {
    o: Option<&'a u64>,
    t: u8,
}

#[kani::proof]
fn safe_v64_ptr_eq() {
    let m: u64 = 5;
    let o = Some(&m);
    let r = o.unwrap();
    assert!(core::ptr::eq(r, &m));
}

#[kani::proof]
fn bug_v64_ptr_eq() {
    let m: u64 = 5;
    let o = Some(&m);
    let r = o.unwrap();
    assert!(!core::ptr::eq(r, &m));
}

#[kani::proof]
fn safe_v64_addr() {
    let a = [1u64, 2];
    let o = Some(&a[1]);
    let r = o.unwrap();
    assert!(r as *const u64 == &a[1] as *const u64);
}

#[kani::proof]
fn safe_e3_ptr_eq() {
    let m = 5u64;
    let e = E3::A(&m);
    if let E3::A(r) = e {
        assert!(core::ptr::eq(r, &m));
    }
}

#[kani::proof]
fn safe_arr_opt_u64() {
    let m = 5u64;
    let n = 6u64;
    let arr = [Some(&m), Some(&n)];
    let i: usize = kani::any();
    kani::assume(i < 2);
    assert!(*arr[i].unwrap() == if i == 0 { 5 } else { 6 });
}

#[kani::proof]
fn bug_arr_opt_u64() {
    let m = 5u64;
    let n = 6u64;
    let arr = [Some(&m), Some(&n)];
    let i: usize = kani::any();
    kani::assume(i < 2);
    assert!(*arr[i].unwrap() == 5);
}

#[kani::proof]
fn safe_vec_opt_u64() {
    let m = 5u64;
    let v = vec![Some(&m)];
    assert!(*v[0].unwrap() == 5);
}

#[kani::proof]
fn safe_struct_field_opt_join_u64() {
    let m = 5u64;
    let n = 6u64;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let w = W64 { o, t: 1 };
    assert!(*w.o.unwrap() == if b { 5 } else { 6 } && w.t == 1);
}

#[kani::proof]
fn safe_opt_as_ref_u64() {
    let m = 5u64;
    let n = 6u64;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    assert!(**o.as_ref().unwrap() == if b { 5 } else { 6 });
}

#[kani::proof]
#[kani::should_panic]
fn sp_v64_ptr_eq() {
    let m: u64 = 5;
    let o = Some(&m);
    let r = o.unwrap();
    assert!(core::ptr::eq(r, &m));
}

#[kani::proof]
#[kani::should_panic]
fn sp_v64_addr() {
    let a = [1u64, 2];
    let o = Some(&a[1]);
    let r = o.unwrap();
    assert!(r as *const u64 == &a[1] as *const u64);
}

#[kani::proof]
#[kani::should_panic]
fn sp_e3_ptr_eq() {
    let m = 5u64;
    let e = E3::A(&m);
    if let E3::A(r) = e {
        assert!(core::ptr::eq(r, &m));
    }
}

// A NARROW payload (`Option<&u8>`, `Option<&u32>`) can never hold the address,
// so a reader that takes it for one (identity, a pointer cast, a closure or
// `unwrap_unchecked` over it, or a mix with a call result) fails closed: these
// safe rows were FAILED Genuine on main and on the first cut, and their
// `should_panic` twins passed. Not Genuine, never a clean pass.

#[kani::proof]
fn safe_nr_ptr_eq() {
    let m: u8 = 5;
    let o = Some(&m);
    let r = o.unwrap();
    assert!(core::ptr::eq(r, &m));
}

#[kani::proof]
fn safe_nr_ptr_eq_join() {
    let m = 5u8;
    let n = 6u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let r = o.unwrap();
    assert!(core::ptr::eq(r, &m) == b);
}

#[kani::proof]
fn safe_nr_addr() {
    let a = [1u8, 2];
    let o = Some(&a[0]);
    let r = o.unwrap();
    let p = r as *const u8;
    assert!(p == a.as_ptr());
}

#[kani::proof]
fn safe_nr_map() {
    let m = 5u8;
    let n = 6u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    assert!(o.map(|r| *r + 1) == Some(if b { 6 } else { 7 }));
}

#[kani::proof]
fn safe_nr_unchecked() {
    let m = 5u8;
    let n = 6u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let r = unsafe { o.unwrap_unchecked() };
    assert!(*r == if b { 5 } else { 6 });
}

#[kani::proof]
fn safe_nr_iter_mix() {
    let a = [3u8, 4, 5];
    let m = 9u8;
    let b: bool = kani::any();
    let o = if b { a.iter().next() } else { Some(&m) };
    let r = o.unwrap();
    assert!(*r == if b { 3 } else { 9 });
}

#[kani::proof]
fn safe_v32_ptr_eq() {
    let m: u32 = 5;
    let o = Some(&m);
    assert!(core::ptr::eq(o.unwrap(), &m));
}

#[kani::proof]
#[kani::should_panic]
fn sp_nr_ptr_eq() {
    let m: u8 = 5;
    let o = Some(&m);
    let r = o.unwrap();
    assert!(core::ptr::eq(r, &m));
}

#[kani::proof]
#[kani::should_panic]
fn sp_nr_addr() {
    let a = [1u8, 2];
    let o = Some(&a[0]);
    let r = o.unwrap();
    let p = r as *const u8;
    assert!(p == a.as_ptr());
}

#[kani::proof]
#[kani::should_panic]
fn sp_nr_map() {
    let m = 5u8;
    let n = 6u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    assert!(o.map(|r| *r + 1) == Some(if b { 6 } else { 7 }));
}

#[kani::proof]
#[kani::should_panic]
fn sp_nr_unchecked() {
    let m = 5u8;
    let n = 6u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let r = unsafe { o.unwrap_unchecked() };
    assert!(*r == if b { 5 } else { 6 });
}

#[kani::proof]
#[kani::should_panic]
fn sp_nr_iter_mix() {
    let a = [3u8, 4, 5];
    let m = 9u8;
    let b: bool = kani::any();
    let o = if b { a.iter().next() } else { Some(&m) };
    let r = o.unwrap();
    assert!(*r == if b { 3 } else { 9 });
}

// Value readers stay exact (the precision the escape rule must not cost).

#[inline(never)]
fn get_ni(x: &u8) -> u8 {
    *x
}

fn take(o: Option<&u8>) -> u8 {
    match o {
        Some(r) => *r,
        None => 0,
    }
}

#[kani::proof]
fn safe_nr_callee() {
    let m: u8 = kani::any();
    let o = Some(&m);
    let r = o.unwrap();
    assert!(get_ni(r) == m);
}

#[kani::proof]
fn safe_nr_callee_join() {
    let m = 5u8;
    let n = 6u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let r = o.unwrap();
    assert!(get_ni(r) == if b { 5 } else { 6 });
}

#[kani::proof]
fn bug_nr_callee_join() {
    let m = 5u8;
    let n = 6u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    let r = o.unwrap();
    assert!(get_ni(r) == 5);
}

#[kani::proof]
fn safe_nr_pass_fn() {
    let m = 7u8;
    let n = 8u8;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    assert!(take(o) == if b { 7 } else { 8 });
}

#[kani::proof]
fn safe_as_ref_u8() {
    let o: Option<u8> = Some(9);
    assert!(*o.as_ref().unwrap() == 9);
}

#[kani::proof]
fn bug_as_ref_u8() {
    let o: Option<u8> = Some(9);
    assert!(*o.as_ref().unwrap() == 8);
}

#[kani::proof]
fn safe_first_is_some() {
    let a = [3u8, 4, 5];
    assert!(a.first().is_some());
}

// Pre-existing on main, same mechanism: a payload whose convention the reader
// does not share. `is_some_and` walks its body with the `Option<&u64>`
// parameter read as `Option<u64>` while the aggregate kept the address;
// `a.iter().next()` stores the ELEMENT in the slot while `Some(&m)` keeps the
// address; `ptr::eq` over an iterator or `first()` payload compares the
// element with an address. Each was FAILED Genuine on main; each fails closed.

#[kani::proof]
fn safe_v64_is_some_and() {
    let m = 5u64;
    let n = 6u64;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    assert!(o.is_some_and(|r| *r == 5) == b);
}

#[kani::proof]
#[kani::should_panic]
fn sp_v64_is_some_and() {
    let m = 5u64;
    let n = 6u64;
    let b: bool = kani::any();
    let o = if b { Some(&m) } else { Some(&n) };
    assert!(o.is_some_and(|r| *r == 5) == b);
}

#[kani::proof]
fn safe_v64_iter_mix() {
    let a = [3u64, 4, 5];
    let m = 9u64;
    let b: bool = kani::any();
    let o = if b { a.iter().next() } else { Some(&m) };
    let r = o.unwrap();
    assert!(*r == if b { 3 } else { 9 });
}

#[kani::proof]
fn safe_iter_ptr_eq_u64() {
    let a = [3u64, 4, 5];
    assert!(core::ptr::eq(a.iter().next().unwrap(), &a[0]));
}

#[kani::proof]
fn safe_iter_ptr_eq_u8() {
    let a = [3u8, 4, 5];
    assert!(core::ptr::eq(a.iter().next().unwrap(), &a[0]));
}

#[kani::proof]
fn safe_first_ptr_eq() {
    let a = [3u8, 4, 5];
    assert!(core::ptr::eq(a.first().unwrap(), &a[0]));
}
