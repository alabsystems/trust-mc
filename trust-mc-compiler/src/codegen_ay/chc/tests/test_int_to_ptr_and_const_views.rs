// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Review of fix/chc-lost-writes round 3 (2026-09-28).
//!
//! - Finding 1: an integer-to-pointer lane (`with_exposed_provenance`, an `as`
//!   cast, an integer transmuted into a pointer) invalidates the object its
//!   result names and records `int_to_ptr_obj_invalidated` unless that object
//!   is the null object; an address joined back from `u32` halves carries a
//!   static's address through the untyped-view flow (`may_carry`).
//! - Finding 2: an immutable `MaybeUninit<[T; N]>` static is seeded (and read)
//!   as its content; a mutable one, an `UnsafeCell` with elements, the
//!   referent of a static's reference and a promoted constant read under a
//!   view their image does not seed record `static_memory_read_unseeded_view`.
//! - A pointer made from a provenance-less literal address that names a model
//!   object fails closed where it may be dereferenced
//!   (`const_pointer_names_model_object`, net 3); one never dereferenced, or
//!   the literal used as a number, records nothing.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const PROBE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    use core::cell::UnsafeCell;
    use core::mem::MaybeUninit;
    use core::ptr::addr_of;

    pub fn probe_exposed_roundtrip_box() {
        let bx: Box<[u16; 2]> = Box::new([1, 0x0102]);
        let p = addr_of!(*bx) as *const u16;
        let q = (p as usize + 2) as *const u16;
        kani::assert(unsafe { *q } == 0x0102, "the round trip reads element 1");
    }

    pub fn probe_small_constant_address() {
        let q = 0x1000 as *const u8;
        let v = unsafe { *q };
        kani::assert(v == v, "reading the null object fails memory safety");
    }

    pub fn probe_transmute_int_to_ptr_oob() {
        let bx: Box<[u16; 2]> = Box::new([1, 2]);
        let a = addr_of!(*bx) as *const u16 as usize;
        let q: *const u16 = unsafe { core::mem::transmute(a + 4) };
        let v = unsafe { *q };
        kani::assert(v == v, "the read is out of bounds");
    }

    pub fn probe_crafted_constant_names_model_object() {
        let bx: Box<u8> = Box::new(7);
        let q = unsafe { core::mem::transmute::<usize, *const u8>(0x2_0000_0000) };
        let v = unsafe { *q };
        kani::assert(v == 7 || v != 7, "an invalid pointer");
    }

    pub fn probe_literal_pointer_never_dereferenced() {
        let q = 0x2_0000_0000usize as *const u8;
        kani::assert(!q.is_null(), "a literal pointer compared, never read");
    }

    pub fn probe_literal_address_through_a_local() {
        let bx: Box<u8> = Box::new(7);
        let a: usize = 0x2_0000_0000;
        let q = a as *const u8;
        let v = unsafe { *q };
        kani::assert(v == 7 || v != 7, "an invalid pointer");
    }

    #[inline(never)]
    fn read_at(a: usize) -> u8 {
        unsafe { *(a as *const u8) }
    }
    pub fn probe_literal_address_handed_to_a_reader() {
        let bx: Box<u8> = Box::new(7);
        let v = read_at(0x2_0000_0000);
        kani::assert(v == 7 || v != 7, "an invalid pointer");
    }

    #[inline(never)]
    fn crafted() -> *const u8 {
        0x2_0000_0000usize as *const u8
    }
    pub fn probe_literal_pointer_returned_by_a_helper() {
        let bx: Box<u8> = Box::new(7);
        let v = unsafe { *crafted() };
        kani::assert(v == 7 || v != 7, "an invalid pointer");
    }

    pub fn probe_literal_pointers_beside_a_box() {
        let b = Box::new(5u32);
        let q = 0x1_0000_1000usize as *const u8;
        let r = 0x5_0000_1000usize as *const u8;
        let _ = (q, r);
        kani::assert(*b == 6, "an assertion the literal pointers do not touch");
    }

    static mut SP: *const u8 = core::ptr::null();
    #[inline(never)]
    fn read_sp() -> u8 {
        unsafe { *SP }
    }
    pub fn probe_literal_pointer_stored_in_a_static() {
        let bx: Box<u8> = Box::new(7);
        unsafe { SP = 0x2_0000_0000usize as *const u8; }
        let v = read_sp();
        kani::assert(v == 7 || v != 7, "an invalid pointer");
    }

    pub struct Four {
        pub arr: [u32; 4],
    }
    pub fn probe_literal_count_offsets_a_pointer() {
        let f = Four { arr: [0; 4] };
        let count: usize = 0x2_0000_0008;
        let bytes = count.checked_mul(core::mem::size_of::<Four>()).unwrap();
        let fits = isize::try_from(bytes).is_ok();
        let q = (&f as *const Four).wrapping_add(count);
        kani::assert(fits || !fits, "a count handed to the standard library");
        kani::assert(!q.is_null() || q.is_null(), "a pointer moved by it, never read");
    }

    pub struct ReadAt(pub u8);
    impl From<usize> for ReadAt {
        fn from(a: usize) -> Self {
            ReadAt(unsafe { *(a as *const u8) })
        }
    }
    pub fn probe_literal_into_a_harness_type() {
        let bx: Box<u8> = Box::new(7);
        let r: ReadAt = 0x2_0000_0000usize.into();
        kani::assert(r.0 == 7 || r.0 != 7, "an invalid pointer");
    }

    pub fn probe_literal_reference_formatted() {
        let bx: Box<u8> = Box::new(7);
        let q = 0x2_0000_0000usize as *const u8;
        let r = unsafe { &*q };
        println!("{}", r);
        kani::assert(true, "an invalid pointer read by the formatter");
    }

    pub fn probe_literal_as_a_number() {
        let a: u64 = 0x2_0000_0000;
        let b = a.checked_add(1).unwrap();
        kani::assert(b == 0x2_0000_0001, "integer arithmetic on the literal");
    }

    static SD: [u16; 2] = [1, 0x0102];
    pub fn probe_static_address_roundtrip() {
        let p = (addr_of!(SD) as usize) as *const u16;
        kani::assert(unsafe { *p.add(1) } == 0x0102, "element 1 of the static");
    }

    static mut SH: [u16; 2] = [1, 0x0102];
    pub fn probe_static_halves_transmute_bytes() {
        unsafe { SH[1] = 0x0304; }
        let addr = unsafe { addr_of!(SH) } as usize;
        let lo = addr as u32;
        let hi = (addr >> 32) as u32;
        let p: *const u8 =
            unsafe { core::mem::transmute(((hi as usize) << 32) | (lo as usize)) };
        kani::assert(unsafe { *p.add(2) } == 4, "byte 2 of the stored element");
    }

    static GM: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
    pub fn probe_maybeuninit_static_elements() {
        let p = GM.as_ptr() as *const u16;
        kani::assert(unsafe { *p } == 1, "element 0 of the content");
    }

    static mut GMM: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
    pub fn probe_mut_maybeuninit_static_elements() {
        let p = unsafe { GMM.as_ptr() } as *const u16;
        kani::assert(unsafe { *p.add(1) } == 0x0102, "element 1 of the content");
    }

    pub struct SyncCell<T>(pub UnsafeCell<T>);
    unsafe impl<T> Sync for SyncCell<T> {}
    static GU: SyncCell<[u16; 2]> = SyncCell(UnsafeCell::new([1, 0x0102]));
    pub fn probe_unsafecell_array_static_element() {
        let p = GU.0.get() as *const u16;
        kani::assert(unsafe { *p.add(1) } == 0x0102, "element 1 through get()");
    }

    static SR: &[u16; 2] = &[1, 0x0102];
    pub fn probe_static_ref_referent_bytes() {
        let p = SR as *const [u16; 2] as *const u8;
        kani::assert(unsafe { *p.add(2) } == 2, "a byte of the referent");
    }

    pub fn probe_static_ref_referent_element() {
        let p = SR as *const [u16; 2] as *const u16;
        kani::assert(unsafe { *p.add(1) } == 0x0102, "element 1 of the referent");
    }

    pub fn probe_promoted_array_bytes() {
        let r: &'static [u16; 2] = &[1, 0x0102];
        let p = r as *const [u16; 2] as *const u8;
        kani::assert(unsafe { *p.add(2) } == 2, "a byte of the promoted array");
    }

    pub fn probe_promoted_array_element() {
        let r: &'static [u16; 2] = &[1, 0x0102];
        let p = r as *const [u16; 2] as *const u16;
        kani::assert(unsafe { *p.add(1) } == 0x0102, "element 1 of the promoted array");
    }

    pub fn probe_promoted_array_bytes_misread() {
        let r: &'static [u16; 2] = &[1, 0x0102];
        let p = r as *const [u16; 2] as *const u8;
        kani::assert(unsafe { *p.add(1) } == 0x02, "byte 1 is 0x00, not element 1");
    }

    pub fn probe_str_literal_bytes() {
        let s: &'static str = "abc";
        let p = s.as_ptr() as *const u8;
        kani::assert(unsafe { *p.add(1) } == b'b', "the second byte of the literal");
    }

    const NATIVE_NONE_BOOL_BYTE: u8 = unsafe { core::mem::transmute(None::<bool>) };
    pub fn probe_compound_none_raw_safe() {
        let value = &(9u8, None::<bool>);
        kani::assert(value.1.is_none(), "the typed value is None");
        let byte = unsafe { core::ptr::addr_of!(value.1).cast::<u8>().read() };
        kani::assert(byte == NATIVE_NONE_BOOL_BYTE, "the initialized native niche byte");
    }
    pub fn probe_compound_none_raw_bug() {
        let value = &(9u8, None::<bool>);
        kani::assert(value.1.is_none(), "the typed value is None");
        let byte = unsafe { core::ptr::addr_of!(value.1).cast::<u8>().read() };
        kani::assert(byte == 0, "native None is not the canonical typed zero");
    }
    pub fn probe_nested_none_raw_safe() {
        let value = &(123u64, (9u8, None::<bool>));
        let byte = unsafe { core::ptr::addr_of!(value.1.1).cast::<u8>().read() };
        kani::assert(byte == NATIVE_NONE_BOOL_BYTE, "nested initialized native niche byte");
    }
    pub fn probe_nested_none_raw_bug() {
        let value = &(123u64, (9u8, None::<bool>));
        let byte = unsafe { core::ptr::addr_of!(value.1.1).cast::<u8>().read() };
        kani::assert(byte == 0, "nested native None is not the canonical typed zero");
    }
"#;

fn solve_with_reasons(fn_name: &str) -> (String, std::collections::BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = crate::codegen_ay::emit_chc(&vc).to_string();
        verdict = Some(
            run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .unwrap_or_else(|e| panic!("AY failed on {fn_name}: {e}")),
        );
    });
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (verdict.expect("the probe was encoded"), reasons)
}

const INT_TO_PTR: &str = "int_to_ptr_obj_invalidated";
const UNSEEDED: &str = "static_memory_read_unseeded_view";

#[test]
fn test_compound_native_none_byte_safe() {
    let (verdict, reasons) = solve_with_reasons("probe_compound_none_raw_safe");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat");
}

#[test]
fn test_compound_native_none_byte_bug() {
    let (verdict, reasons) = solve_with_reasons("probe_compound_none_raw_bug");
    assert!(reasons.is_empty(), "a concrete native byte must have no encoding debt: {reasons:?}");
    assert_eq!(verdict, "sat");
}

#[test]
fn test_nested_native_none_byte_safe() {
    let (verdict, reasons) = solve_with_reasons("probe_nested_none_raw_safe");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat");
}

#[test]
fn test_nested_native_none_byte_bug() {
    let (verdict, reasons) = solve_with_reasons("probe_nested_none_raw_bug");
    assert!(reasons.is_empty(), "a concrete native byte must have no encoding debt: {reasons:?}");
    assert_eq!(verdict, "sat");
}
const CONST_OBJECT: &str = "const_pointer_names_model_object";

/// Finding 1: the round trip invalidates the Box's object; the failure it
/// causes must not be evidence.
#[test]
fn test_int_to_ptr_invalidation_of_a_live_object_is_recorded() {
    let (_verdict, reasons) = solve_with_reasons("probe_exposed_roundtrip_box");
    assert!(reasons.contains_key(INT_TO_PTR), "got {reasons:?}");
}

/// The null object holds nothing: its invalidation is exact and records nothing.
#[test]
fn test_int_to_ptr_invalidation_of_the_null_object_is_not_recorded() {
    let (verdict, reasons) = solve_with_reasons("probe_small_constant_address");
    assert!(!reasons.contains_key(INT_TO_PTR), "got {reasons:?}");
    assert_eq!(verdict, "sat", "reading the null object fails memory safety");
}

/// Finding 1 (same lane): an integer transmuted into a pointer takes the
/// integer-to-pointer lane, so the out-of-bounds round trip fails (it verified
/// on main). Since the landing of fix/chc-lost-writes on main's address layout,
/// the box's exposed address moved by a constant names the box again
/// (`int_operand_is_exposed_address`), so the pointer is the box's at offset 4
/// and the read fails its bound with no invalidation; a number that is not an
/// exposed address is still invalidated
/// (`test_heap_views_and_lanes::test_transmute_into_a_pointer_invalidates_its_object`).
#[test]
fn test_int_to_ptr_transmute_takes_the_cast_lane() {
    let (verdict, reasons) = solve_with_reasons("probe_transmute_int_to_ptr_oob");
    assert!(!reasons.contains_key(INT_TO_PTR), "got {reasons:?}");
    assert_eq!(verdict, "sat", "the out-of-bounds round trip must fail; reasons {reasons:?}");
}

/// A dereferenced pointer made from a provenance-less literal naming a model
/// object fails closed, whether the MIR keeps the transmute or folds it into
/// a pointer constant. Main recorded nothing and read the Box.
#[test]
fn test_constant_address_naming_a_model_object_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_crafted_constant_names_model_object");
    assert!(reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

/// Net 3 fails closed only where such a pointer may be read: one compared and
/// never dereferenced records nothing and its proof stands.
#[test]
fn test_literal_pointer_never_dereferenced_records_nothing() {
    let (verdict, reasons) = solve_with_reasons("probe_literal_pointer_never_dereferenced");
    assert!(!reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
    assert!(!reasons.contains_key(INT_TO_PTR), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "the literal pointer is not null");
}

/// A literal address names no object in Kani: it invalidates nothing, so an
/// unrelated assertion failure beside it keeps no reason against its
/// certificate (the integer-to-pointer lane recorded one on the first cut,
/// and main certified it).
#[test]
fn test_literal_pointers_invalidate_nothing() {
    let (verdict, reasons) = solve_with_reasons("probe_literal_pointers_beside_a_box");
    assert!(!reasons.contains_key(INT_TO_PTR), "got {reasons:?}");
    assert!(!reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
    assert_eq!(verdict, "sat", "the assertion fails");
}

/// Stored where another body loads it, such a pointer fails closed.
#[test]
fn test_literal_pointer_stored_in_a_static_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_literal_pointer_stored_in_a_static");
    assert!(reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

/// The literal reaches the cast through a local.
#[test]
fn test_literal_address_through_a_local_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_literal_address_through_a_local");
    assert!(reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

/// The literal is handed as an integer to a helper that makes and reads the
/// pointer.
#[test]
fn test_literal_address_handed_to_a_reader_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_literal_address_handed_to_a_reader");
    assert!(reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

/// A helper returns the pointer its literal makes; its caller reads it.
#[test]
fn test_literal_pointer_returned_by_a_helper_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_literal_pointer_returned_by_a_helper");
    assert!(reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

/// The literal used as a number, handed to the standard library's integer
/// arithmetic, records nothing.
/// A literal count handed to the standard library (`checked_mul`, `try_from`,
/// `Result::is_ok`) and moving a pointer to a harness type, never read,
/// records nothing: the shape of `ptr-offset-overflow-bytes/main.rs`, a
/// parity unit a leaf-name list lost (`is_err` was not on it), and then an
/// exemption that required standard-library generic arguments of
/// `<*const Foo>::offset` too.
#[test]
fn test_literal_count_handed_to_the_standard_library_records_nothing() {
    let (_verdict, reasons) = solve_with_reasons("probe_literal_count_offsets_a_pointer");
    assert!(!reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

/// `into` is the standard library's blanket impl, but it calls the harness's
/// `From`, which makes a pointer of the number and reads it: fails closed.
#[test]
fn test_literal_into_a_harness_type_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_literal_into_a_harness_type");
    assert!(reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

/// A reference made through such a pointer counts as a read: the
/// formatting machinery it is handed to reads it where no scan looks.
#[test]
fn test_literal_reference_formatted_fails_closed() {
    let (_verdict, reasons) = solve_with_reasons("probe_literal_reference_formatted");
    assert!(reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
}

#[test]
fn test_literal_as_a_number_records_nothing() {
    let (verdict, reasons) = solve_with_reasons("probe_literal_as_a_number");
    assert!(!reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "integer arithmetic on the literal");
}

/// Finding 1 (net 2): the static's address survives the u32 halves.
#[test]
fn test_static_address_through_u32_halves_is_followed() {
    let (_verdict, reasons) = solve_with_reasons("probe_static_halves_transmute_bytes");
    assert!(reasons.contains_key(UNSEEDED), "got {reasons:?}");
}

/// Finding 2: an immutable MaybeUninit static's content cells are seeded.
#[test]
fn test_immutable_maybeuninit_static_reads_its_content_exactly() {
    let (verdict, reasons) = solve_with_reasons("probe_maybeuninit_static_elements");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "element 0 is seeded");
}

/// Finding 2: a mutable one is not seeded as its content, so the element
/// read is not evidence.
#[test]
fn test_mutable_maybeuninit_static_element_is_not_evidence() {
    let (_verdict, reasons) = solve_with_reasons("probe_mut_maybeuninit_static_elements");
    assert!(reasons.contains_key(UNSEEDED), "got {reasons:?}");
}

/// Finding 2: an UnsafeCell whose content has elements is not the same cells.
#[test]
fn test_unsafecell_array_static_element_is_not_evidence() {
    let (_verdict, reasons) = solve_with_reasons("probe_unsafecell_array_static_element");
    assert!(reasons.contains_key(UNSEEDED), "got {reasons:?}");
}

/// Finding 2: the referent of a static's reference, read as bytes.
#[test]
fn test_static_ref_referent_bytes_are_not_evidence() {
    let (_verdict, reasons) = solve_with_reasons("probe_static_ref_referent_bytes");
    assert!(reasons.contains_key(UNSEEDED), "got {reasons:?}");
}

/// Finding 2: a promoted constant, read as bytes.
#[test]
fn test_promoted_array_bytes_are_not_evidence() {
    let (_verdict, reasons) = solve_with_reasons("probe_promoted_array_bytes");
    assert!(reasons.contains_key(UNSEEDED), "got {reasons:?}");
}

/// The promoted constant's element view stays exact.
#[test]
fn test_promoted_array_element_stays_exact() {
    let (verdict, reasons) = solve_with_reasons("probe_promoted_array_element");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "element 1 is seeded");
}

/// A string literal's bytes are its elements.
#[test]
fn test_str_literal_bytes_stay_exact() {
    let (verdict, reasons) = solve_with_reasons("probe_str_literal_bytes");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "the literal's bytes are seeded");
}

/// A byte read of a constant `[u16; 2]` through a pointer carrying the
/// array's value fact selected element 1 for byte 1, so a false assertion
/// verified on main (a missed bug). The element read is refused for a pointee
/// encoded unlike the element; the byte is read from memory and can differ.
#[test]
fn test_narrower_read_of_a_constant_array_is_not_an_element_read() {
    let (verdict, reasons) = solve_with_reasons("probe_promoted_array_bytes_misread");
    assert_eq!(verdict, "sat", "byte 1 is not element 1; the assertion must fail");
    assert!(reasons.contains_key(UNSEEDED), "got {reasons:?}");
}

/// Found beside finding 2: `*r` for the reference to `static R: &[u16; 2]`
/// selected the referent's element 0 as the loaded POINTER (the value fact is
/// one level further in), so the element read's alignment check failed,
/// certified Genuine on main. The element read is refused for a pointer
/// pointee; the static's lane answers with the referent's address.
#[test]
fn test_static_ref_referent_element_read_stays_exact() {
    let (verdict, reasons) = solve_with_reasons("probe_static_ref_referent_element");
    assert!(!reasons.contains_key(UNSEEDED), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "element 1 of the referent is seeded");
}

/// A static's minted address is a constant of the MODEL, not a literal of the
/// program: exposed and rebuilt it names the static, so the model-object rule
/// must not fire and the element read stays exact (main proves it).
#[test]
fn test_static_address_roundtrip_is_not_a_model_object_literal() {
    let (verdict, reasons) = solve_with_reasons("probe_static_address_roundtrip");
    assert!(!reasons.contains_key(CONST_OBJECT), "got {reasons:?}");
    assert_eq!(verdict, "unsat", "element 1 of the static");
}
