// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! `String::from_utf8` is a stub (StringFromUtf8). The inline pass keeps every
//! `String::` call as a Call terminator; without the stub the BMC mini-inliner
//! descended into `run_utf8_validation` (109 blocks, over the 64-block cap),
//! recorded an unsupported `Call terminator`, and every check came back
//! UNDETERMINED. With concrete bytes the stub decides Ok/Err at codegen time;
//! with symbolic bytes it answers Ok-or-Err nondeterministically, an Ok
//! carrying exactly the input bytes.
//!
//! The Vecs are push-built on purpose: `vec![...]` is modeled with a SYMBOLIC
//! data array in BMC (codegen_slice_into_vec), so its bytes are never concrete.
//! The Ok payload is consumed through `match`, not `unwrap()`: the inline pass
//! inlines `Result::unwrap`, whose `unwrap_failed` Debug-formatting of
//! `FromUtf8Error` leaves unconstrained assignments that demote the proof.
//!
//! The two `*_fails` harnesses are the discriminating controls. Measured with
//! ay 0.19.0+build.9046 they report INCONCLUSIVE (fail-closed), NOT FAILED:
//! the counterexample exists but ay's strict model validation rejects every
//! model of a `Result<String, FromUtf8Error>` value ("datatype-field rejected"
//! / "arrays-read-conflict-uneval") — a datatype nested inside a datatype with
//! an Array field. A plain `Vec<u8>` counterexample of the same shape IS
//! confirmed (FAILED), so the limitation is the nesting, not the stub. They
//! must never report SUCCESSFUL.

#[kani::proof]
fn from_utf8_valid_is_ok() {
    let mut v: Vec<u8> = Vec::new();
    v.push(b'a');
    v.push(b'b');
    match String::from_utf8(v) {
        Ok(s) => assert_eq!(s.len(), 2),
        Err(_) => assert!(false, "valid UTF-8 must be Ok"),
    }
}

#[kani::proof]
fn from_utf8_invalid_is_err() {
    let mut v: Vec<u8> = Vec::new();
    v.push(0xff);
    v.push(b'b');
    assert!(String::from_utf8(v).is_err());
}

// Symbolic bytes: the stub may answer Ok or Err, but an Ok carries exactly the
// input bytes — length included.
#[kani::proof]
fn from_utf8_symbolic_ok_keeps_len() {
    let mut v: Vec<u8> = Vec::new();
    v.push(kani::any());
    v.push(kani::any());
    if let Ok(s) = String::from_utf8(v) {
        assert_eq!(s.len(), 2);
    }
}

// Deliberately broken: "ab" has 2 bytes, not 3 — must not PROVE (see header).
#[kani::proof]
fn from_utf8_valid_wrong_len_fails() {
    let mut v: Vec<u8> = Vec::new();
    v.push(b'a');
    v.push(b'b');
    match String::from_utf8(v) {
        Ok(s) => assert_eq!(s.len(), 3),
        Err(_) => assert!(false, "valid UTF-8 must be Ok"),
    }
}

// Deliberately broken: 0xff is not UTF-8, so `is_ok()` is false — must not
// PROVE (see header).
#[kani::proof]
fn from_utf8_invalid_claimed_ok_fails() {
    let mut v: Vec<u8> = Vec::new();
    v.push(0xff);
    v.push(b'b');
    assert!(String::from_utf8(v).is_ok());
}
