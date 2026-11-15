// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL -- memory the entry rule seeds under fewer views than a raw
//! read can take: a `MaybeUninit` / `ManuallyDrop` / `UnsafeCell` static read
//! as its content's elements or fields, the anonymous allocation a static's
//! reference holds (`static R: &[u16; 2] = &[..]`), and a promoted constant,
//! read under a byte view (review of fix/chc-lost-writes round 3, finding 2).
//!
//! The untyped-view net 2 treated a wrapper keyed like its content as the same
//! cells, but the image of a `MaybeUninit<[u16; 2]>` static (a union) seeded no
//! element cell; it did not follow the referent of a static's reference or a
//! promoted constant at all. Each read selected a cell nothing constrains, a
//! free value certified Genuine. Now: an immutable static's `MaybeUninit` /
//! `ManuallyDrop` image is seeded as its content, and read exactly; a mutable
//! one, and an `UnsafeCell` whose content has elements or fields, counts as
//! unseeded; the referent of a static's pointer and a promoted constant are
//! followed like a static (in a body that may reinterpret a pointer), and a
//! view their image does not seed records `static_memory_read_unseeded_view`
//! (SoundHavoc: proofs stand, no Genuine certificate).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3):
//!   safe_maybeuninit_array_static_base_elem      -> SUCCESSFUL
//!   bug_maybeuninit_array_static_base_elem       -> FAILED ('assertion failed: unsafe { *p } == 2')
//!   safe_maybeuninit_array_static_elem1          -> SUCCESSFUL
//!   bug_maybeuninit_array_static_elem1           -> FAILED ('assertion failed: unsafe { *p.add(1) } == 1')
//!   safe_maybeuninit_array_static_bytes          -> SUCCESSFUL
//!   bug_maybeuninit_array_static_bytes           -> FAILED ('assertion failed: unsafe { *p.add(2) } == 1')
//!   safe_maybeuninit_u32_static                  -> SUCCESSFUL
//!   bug_maybeuninit_u32_static                   -> FAILED ('assertion failed: unsafe { *p } == 8')
//!   safe_array_static_base_elem_retyped          -> SUCCESSFUL
//!   bug_array_static_base_elem_retyped           -> FAILED ('assertion failed: unsafe { *p } == 2')
//!   safe_mut_maybeuninit_after_store             -> SUCCESSFUL
//!   bug_mut_maybeuninit_after_store              -> FAILED ('assertion failed: unsafe { *p } == 1')
//!   safe_manuallydrop_array_static_elem1         -> SUCCESSFUL
//!   bug_manuallydrop_array_static_elem1          -> FAILED ('assertion failed: unsafe { *p.add(1) } == 1')
//!   safe_unsafecell_array_static_elem1           -> SUCCESSFUL
//!   bug_unsafecell_array_static_elem1            -> FAILED ('assertion failed: unsafe { *p.add(1) } == 1')
//!   safe_unsafecell_struct_static_field          -> SUCCESSFUL
//!   bug_unsafecell_struct_static_field           -> FAILED ('assertion failed: unsafe { (*p).y } == 1')
//!   safe_unsafecell_u32_static                   -> SUCCESSFUL
//!   bug_unsafecell_u32_static                    -> FAILED ('assertion failed: unsafe { *p } == 10')
//!   safe_static_array_ref_backing_bytes          -> SUCCESSFUL
//!   bug_static_array_ref_backing_bytes           -> FAILED ('assertion failed: unsafe { *p.add(2) } == 1')
//!   safe_static_array_ref_backing_elem           -> SUCCESSFUL
//!   bug_static_array_ref_backing_elem            -> FAILED ('assertion failed: unsafe { *p.add(1) } == 1')
//!   safe_static_slice_backing_bytes              -> SUCCESSFUL
//!   bug_static_slice_backing_bytes               -> FAILED ('assertion failed: unsafe { *p.add(2) } == 1')
//!   safe_static_struct_ref_field                 -> SUCCESSFUL
//!   bug_static_struct_ref_field                  -> FAILED ('assertion failed: unsafe { (*p).y } == 1')
//!   safe_static_struct_ref_bytes                 -> SUCCESSFUL
//!   bug_static_struct_ref_bytes                  -> FAILED ('assertion failed: unsafe { *p } == 1')
//!   safe_ref_u32                                 -> SUCCESSFUL
//!   bug_ref_u32                                  -> FAILED ('assertion failed: *RU == 6')
//!   safe_ref_array_index                         -> SUCCESSFUL
//!   bug_ref_array_index                          -> FAILED ('assertion failed: RA[1] == 1')
//!   safe_ref_u8_array_raw_elem                   -> SUCCESSFUL
//!   bug_ref_u8_array_raw_elem                    -> FAILED ('assertion failed: unsafe { *p.add(3) } == 3')
//!   safe_ref_tuple_field                         -> SUCCESSFUL
//!   bug_ref_tuple_field                          -> FAILED ('assertion failed: RT.1 == 1')
//!   safe_ref_struct_field                        -> SUCCESSFUL
//!   bug_ref_struct_field                         -> FAILED ('assertion failed: SP2.y == 1')
//!   safe_ref_struct_array_field                  -> SUCCESSFUL
//!   bug_ref_struct_array_field                   -> FAILED ('assertion failed: RPA[1].y == 2')
//!   safe_promoted_array_bytes                    -> SUCCESSFUL
//!   bug_promoted_array_bytes                     -> FAILED ('assertion failed: unsafe { *p.add(2) } == 1')
//!   bug_promoted_array_bytes_misread             -> FAILED ('assertion failed: unsafe { *p.add(1) } == 0x02')
//!   safe_promoted_array_bytes_byte1              -> SUCCESSFUL
//!   safe_promoted_u32_array_as_u16               -> SUCCESSFUL
//!   bug_promoted_u32_array_as_u16                -> FAILED ('assertion failed: unsafe { *p.add(1) } == 0x0001')
//!   safe_promoted_array_elem                     -> SUCCESSFUL
//!   bug_promoted_array_elem                      -> FAILED ('assertion failed: unsafe { *p.add(1) } == 1')
//!   safe_promoted_tuple_direct_field             -> SUCCESSFUL
//!   bug_promoted_tuple_direct_field              -> FAILED ('assertion failed: t.1 == 1')
//!   safe_promoted_struct_array_raw_field         -> SUCCESSFUL
//!   bug_promoted_struct_array_raw_field          -> FAILED ('assertion failed: unsafe { (*p.add(1)).y } == 2')
//!   safe_str_literal_bytes                       -> SUCCESSFUL
//!   bug_str_literal_bytes                        -> FAILED ('assertion failed: unsafe { *p.add(1) } == b'c'')
//!   safe_byte_literal_read_as_u32                -> SUCCESSFUL
//!   bug_byte_literal_read_as_u32                 -> FAILED ('assertion failed: unsafe { p.read_unaligned() } == 0x0102_0304')
//!
#![allow(unused, static_mut_refs)]
use std::cell::UnsafeCell;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::ptr::addr_of;

// ---- MaybeUninit<[u16; 2]> in an immutable static: seeded as its content ----

static GM1: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
static GM2: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
static GM3: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
static GM4: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
static GM5: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
static GM6: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);

#[kani::proof]
fn safe_maybeuninit_array_static_base_elem() {
    let p = GM1.as_ptr() as *const u16;
    assert!(unsafe { *p } == 1);
}

#[kani::proof]
fn bug_maybeuninit_array_static_base_elem() {
    let p = GM2.as_ptr() as *const u16;
    assert!(unsafe { *p } == 2);
}

#[kani::proof]
fn safe_maybeuninit_array_static_elem1() {
    let p = GM3.as_ptr() as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

#[kani::proof]
fn bug_maybeuninit_array_static_elem1() {
    let p = GM4.as_ptr() as *const u16;
    assert!(unsafe { *p.add(1) } == 1);
}

#[kani::proof]
fn safe_maybeuninit_array_static_bytes() {
    let p = GM5.as_ptr() as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn bug_maybeuninit_array_static_bytes() {
    let p = GM6.as_ptr() as *const u8;
    assert!(unsafe { *p.add(2) } == 1);
}

static GM7: MaybeUninit<u32> = MaybeUninit::new(7);
static GM8: MaybeUninit<u32> = MaybeUninit::new(7);

#[kani::proof]
fn safe_maybeuninit_u32_static() {
    let p = GM7.as_ptr();
    assert!(unsafe { *p } == 7);
}

#[kani::proof]
fn bug_maybeuninit_u32_static() {
    let p = GM8.as_ptr();
    assert!(unsafe { *p } == 8);
}

// ---- a plain array static read at its base through a re-typed pointer ----

static GP1: [u16; 2] = [1, 0x0102];
static GP2: [u16; 2] = [1, 0x0102];

#[kani::proof]
fn safe_array_static_base_elem_retyped() {
    let p = addr_of!(GP1) as *const u16;
    assert!(unsafe { *p } == 1);
}

#[kani::proof]
fn bug_array_static_base_elem_retyped() {
    let p = addr_of!(GP2) as *const u16;
    assert!(unsafe { *p } == 2);
}

// ---- a mutable MaybeUninit static: not seeded as its content ----

static mut GMM1: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);
static mut GMM2: MaybeUninit<[u16; 2]> = MaybeUninit::new([1, 0x0102]);

#[kani::proof]
fn safe_mut_maybeuninit_after_store() {
    unsafe {
        GMM1 = MaybeUninit::new([5, 6]);
    }
    let p = unsafe { GMM1.as_ptr() } as *const u16;
    assert!(unsafe { *p } == 5);
}

#[kani::proof]
fn bug_mut_maybeuninit_after_store() {
    unsafe {
        GMM2 = MaybeUninit::new([5, 6]);
    }
    let p = unsafe { GMM2.as_ptr() } as *const u16;
    assert!(unsafe { *p } == 1);
}

// ---- ManuallyDrop<[u16; 2]> in an immutable static ----

static GD1: ManuallyDrop<[u16; 2]> = ManuallyDrop::new([1, 0x0102]);
static GD2: ManuallyDrop<[u16; 2]> = ManuallyDrop::new([1, 0x0102]);

#[kani::proof]
fn safe_manuallydrop_array_static_elem1() {
    let p = addr_of!(GD1) as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

#[kani::proof]
fn bug_manuallydrop_array_static_elem1() {
    let p = addr_of!(GD2) as *const u16;
    assert!(unsafe { *p.add(1) } == 1);
}

// ---- UnsafeCell content with elements or fields: not seeded as the content ----

struct SyncCell<T>(UnsafeCell<T>);
unsafe impl<T> Sync for SyncCell<T> {}

#[derive(Clone, Copy)]
struct Pt {
    x: u16,
    y: u32,
}

static GU1: SyncCell<[u16; 2]> = SyncCell(UnsafeCell::new([1, 0x0102]));
static GU2: SyncCell<[u16; 2]> = SyncCell(UnsafeCell::new([1, 0x0102]));
static GU3: SyncCell<Pt> = SyncCell(UnsafeCell::new(Pt { x: 1, y: 0x0102_0304 }));
static GU4: SyncCell<Pt> = SyncCell(UnsafeCell::new(Pt { x: 1, y: 0x0102_0304 }));
static GU5: SyncCell<u32> = SyncCell(UnsafeCell::new(9));
static GU6: SyncCell<u32> = SyncCell(UnsafeCell::new(9));

#[kani::proof]
fn safe_unsafecell_array_static_elem1() {
    let p = GU1.0.get() as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

#[kani::proof]
fn bug_unsafecell_array_static_elem1() {
    let p = GU2.0.get() as *const u16;
    assert!(unsafe { *p.add(1) } == 1);
}

#[kani::proof]
fn safe_unsafecell_struct_static_field() {
    let p = GU3.0.get();
    assert!(unsafe { (*p).y } == 0x0102_0304);
}

#[kani::proof]
fn bug_unsafecell_struct_static_field() {
    let p = GU4.0.get();
    assert!(unsafe { (*p).y } == 1);
}

#[kani::proof]
fn safe_unsafecell_u32_static() {
    let p = GU5.0.get();
    assert!(unsafe { *p } == 9);
}

#[kani::proof]
fn bug_unsafecell_u32_static() {
    let p = GU6.0.get();
    assert!(unsafe { *p } == 10);
}

// ---- the anonymous allocation a static's reference holds ----

static SR1: &[u16; 2] = &[1, 0x0102];
static SR2: &[u16; 2] = &[1, 0x0102];
static SS1: &[u16] = &[1, 0x0102];
static SS2: &[u16] = &[1, 0x0102];
static SP1: &Pt = &Pt { x: 1, y: 0x0102_0304 };
static SP2: &Pt = &Pt { x: 1, y: 0x0102_0304 };

#[kani::proof]
fn safe_static_array_ref_backing_bytes() {
    let p = SR1 as *const [u16; 2] as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn bug_static_array_ref_backing_bytes() {
    let p = SR2 as *const [u16; 2] as *const u8;
    assert!(unsafe { *p.add(2) } == 1);
}

#[kani::proof]
fn safe_static_array_ref_backing_elem() {
    let p = SR1 as *const [u16; 2] as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

#[kani::proof]
fn bug_static_array_ref_backing_elem() {
    let p = SR2 as *const [u16; 2] as *const u16;
    assert!(unsafe { *p.add(1) } == 1);
}

#[kani::proof]
fn safe_static_slice_backing_bytes() {
    let p = SS1.as_ptr() as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn bug_static_slice_backing_bytes() {
    let p = SS2.as_ptr() as *const u8;
    assert!(unsafe { *p.add(2) } == 1);
}

#[kani::proof]
fn safe_static_struct_ref_field() {
    let p = SP1 as *const Pt;
    assert!(unsafe { (*p).y } == 0x0102_0304);
}

#[kani::proof]
fn bug_static_struct_ref_field() {
    let p = SP2 as *const Pt;
    assert!(unsafe { (*p).y } == 1);
}

#[kani::proof]
fn safe_static_struct_ref_bytes() {
    let p = SP1 as *const Pt as *const u8;
    assert!(unsafe { *p } == 4);
}

#[kani::proof]
fn bug_static_struct_ref_bytes() {
    let p = SP2 as *const Pt as *const u8;
    assert!(unsafe { *p } == 1);
}

// ---- reads through a static's reference by shape (a value fact of the wrong
// level answered some of them on main: an element as the pointer, the shared
// promoted object as the referent) ----

static RU: &u32 = &5;
static RA: &[u16; 2] = &[1, 0x0102];
static RA8: &[u8; 4] = &[1, 2, 3, 4];
static RT: &(u8, u32) = &(1, 0x0102_0304);
static RPA: &[Pt; 2] = &[Pt { x: 1, y: 2 }, Pt { x: 3, y: 4 }];

#[kani::proof]
fn safe_ref_u32() {
    assert!(*RU == 5);
}

#[kani::proof]
fn bug_ref_u32() {
    assert!(*RU == 6);
}

#[kani::proof]
fn safe_ref_array_index() {
    assert!(RA[1] == 0x0102);
}

#[kani::proof]
fn bug_ref_array_index() {
    assert!(RA[1] == 1);
}

#[kani::proof]
fn safe_ref_u8_array_raw_elem() {
    let p = RA8 as *const [u8; 4] as *const u8;
    assert!(unsafe { *p.add(3) } == 4);
}

#[kani::proof]
fn bug_ref_u8_array_raw_elem() {
    let p = RA8 as *const [u8; 4] as *const u8;
    assert!(unsafe { *p.add(3) } == 3);
}

#[kani::proof]
fn safe_ref_tuple_field() {
    assert!(RT.1 == 0x0102_0304);
}

#[kani::proof]
fn bug_ref_tuple_field() {
    assert!(RT.1 == 1);
}

#[kani::proof]
fn safe_ref_struct_field() {
    assert!(SP1.y == 0x0102_0304);
}

#[kani::proof]
fn bug_ref_struct_field() {
    assert!(SP2.y == 1);
}

#[kani::proof]
fn safe_ref_struct_array_field() {
    assert!(RPA[1].y == 4);
}

#[kani::proof]
fn bug_ref_struct_array_field() {
    assert!(RPA[1].y == 2);
}

// ---- promoted constants ----

#[kani::proof]
fn safe_promoted_array_bytes() {
    let r: &'static [u16; 2] = &[1, 0x0102];
    let p = r as *const [u16; 2] as *const u8;
    assert!(unsafe { *p.add(2) } == 2);
}

#[kani::proof]
fn bug_promoted_array_bytes() {
    let r: &'static [u16; 2] = &[1, 0x0102];
    let p = r as *const [u16; 2] as *const u8;
    assert!(unsafe { *p.add(2) } == 1);
}

// The byte pointer carried the array's value fact, and a read through it
// selected ELEMENT `k` for byte `k`: byte 1 of `[1, 0x0102]` came back as
// `0x0102` truncated to `0x02` and the bug verified on main.
#[kani::proof]
fn bug_promoted_array_bytes_misread() {
    let r: &'static [u16; 2] = &[1, 0x0102];
    let p = r as *const [u16; 2] as *const u8;
    assert!(unsafe { *p.add(1) } == 0x02);
}

#[kani::proof]
fn safe_promoted_array_bytes_byte1() {
    let r: &'static [u16; 2] = &[1, 0x0102];
    let p = r as *const [u16; 2] as *const u8;
    assert!(unsafe { *p.add(1) } == 0x00);
}

#[kani::proof]
fn safe_promoted_u32_array_as_u16() {
    let r: &'static [u32; 2] = &[0x0003_0004, 0x0001_0002];
    let p = r as *const [u32; 2] as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0003);
}

#[kani::proof]
fn bug_promoted_u32_array_as_u16() {
    let r: &'static [u32; 2] = &[0x0003_0004, 0x0001_0002];
    let p = r as *const [u32; 2] as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0001);
}

#[kani::proof]
fn safe_promoted_array_elem() {
    let r: &'static [u16; 2] = &[1, 0x0102];
    let p = r as *const [u16; 2] as *const u16;
    assert!(unsafe { *p.add(1) } == 0x0102);
}

#[kani::proof]
fn bug_promoted_array_elem() {
    let r: &'static [u16; 2] = &[1, 0x0102];
    let p = r as *const [u16; 2] as *const u16;
    assert!(unsafe { *p.add(1) } == 1);
}

// A direct field read of a promoted tuple in a body that also casts it.
#[kani::proof]
fn safe_promoted_tuple_direct_field() {
    let t: &'static (u8, u32) = &(1, 0x0102_0304);
    let _b = t as *const (u8, u32) as *const u8;
    assert!(t.1 == 0x0102_0304);
}

#[kani::proof]
fn bug_promoted_tuple_direct_field() {
    let t: &'static (u8, u32) = &(1, 0x0102_0304);
    let _b = t as *const (u8, u32) as *const u8;
    assert!(t.1 == 1);
}

#[kani::proof]
fn safe_promoted_struct_array_raw_field() {
    let a: &'static [Pt; 2] = &[Pt { x: 1, y: 2 }, Pt { x: 3, y: 0x0102_0304 }];
    let p = a as *const [Pt; 2] as *const Pt;
    assert!(unsafe { (*p.add(1)).y } == 0x0102_0304);
}

#[kani::proof]
fn bug_promoted_struct_array_raw_field() {
    let a: &'static [Pt; 2] = &[Pt { x: 1, y: 2 }, Pt { x: 3, y: 0x0102_0304 }];
    let p = a as *const [Pt; 2] as *const Pt;
    assert!(unsafe { (*p.add(1)).y } == 2);
}

#[kani::proof]
fn safe_str_literal_bytes() {
    let s: &'static str = "abc";
    let p = s.as_ptr();
    assert!(unsafe { *p.add(1) } == b'b');
}

#[kani::proof]
fn bug_str_literal_bytes() {
    let s: &'static str = "abc";
    let p = s.as_ptr();
    assert!(unsafe { *p.add(1) } == b'c');
}

#[kani::proof]
fn safe_byte_literal_read_as_u32() {
    let b: &'static [u8; 4] = b"\x01\x02\x03\x04";
    let p = b as *const [u8; 4] as *const u32;
    assert!(unsafe { p.read_unaligned() } == 0x0403_0201);
}

#[kani::proof]
fn bug_byte_literal_read_as_u32() {
    let b: &'static [u8; 4] = b"\x01\x02\x03\x04";
    let p = b as *const [u8; 4] as *const u32;
    assert!(unsafe { p.read_unaligned() } == 0x0102_0304);
}
