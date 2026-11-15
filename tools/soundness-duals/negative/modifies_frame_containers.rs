// kani-flags: -Z function-contracts
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// NEGATIVE PACK: modifies-frame checks on stores made inside model-handled
// container calls (variants of negative/modifies_frame_residual.rs::
// vec_push_outside_must_fail).
//
// Found while fixing that row (2026-09-12): the BMC frame check classified only
// direct assignments, so a store made inside a Vec/String model or stub call
// outside the footprint was never accused (vec_push_outside_must_fail verified
// SUCCESSFUL on bundle 31793ccc3). These cover the other container operations the
// models handle, a raw write through Vec::as_mut_ptr and Option::take, each with
// an in-footprint twin. Measured on bundle ebf198615: every must-fail FAILED in
// CHC and FAILED or INCONCLUSIVE in BMC (vecdeque_pop: UndecidedModel); no safe
// twin failed with a Genuine certificate.
//
// Oracle (per harness):
//   *_outside_must_fail -> never SUCCESSFUL (the store is outside the modifies set)
//   *_inside_safe       -> never a Genuine counterexample
#[repr(C)]
struct Pair { a: u32, b: u32 }

#[kani::modifies(&p.a)]
fn vec_insert_outside(p: &mut Pair, w: &mut Vec<u8>) { p.a = 1; w.insert(0, 9); }
#[kani::proof_for_contract(vec_insert_outside)]
fn vec_insert_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut w: Vec<u8> = vec![1, 2]; vec_insert_outside(&mut p, &mut w); }

#[kani::modifies(w)]
fn vec_insert_inside(w: &mut Vec<u8>) { w.insert(0, 9); }
#[kani::proof_for_contract(vec_insert_inside)]
fn vec_insert_inside_safe() { let mut w: Vec<u8> = vec![1, 2]; vec_insert_inside(&mut w); }

#[kani::modifies(&p.a)]
fn vec_clear_outside(p: &mut Pair, w: &mut Vec<u8>) { p.a = 1; w.clear(); }
#[kani::proof_for_contract(vec_clear_outside)]
fn vec_clear_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut w: Vec<u8> = vec![1, 2]; vec_clear_outside(&mut p, &mut w); }

#[kani::modifies(w)]
fn vec_clear_inside(w: &mut Vec<u8>) { w.clear(); }
#[kani::proof_for_contract(vec_clear_inside)]
fn vec_clear_inside_safe() { let mut w: Vec<u8> = vec![1, 2]; vec_clear_inside(&mut w); }

#[kani::modifies(&p.a)]
fn vec_extend_outside(p: &mut Pair, w: &mut Vec<u8>) { p.a = 1; w.extend_from_slice(&[3, 4]); }
#[kani::proof_for_contract(vec_extend_outside)]
fn vec_extend_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut w: Vec<u8> = vec![1, 2]; vec_extend_outside(&mut p, &mut w); }

#[kani::modifies(&p.a)]
fn vec_truncate_outside(p: &mut Pair, w: &mut Vec<u8>) { p.a = 1; w.truncate(1); }
#[kani::proof_for_contract(vec_truncate_outside)]
fn vec_truncate_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut w: Vec<u8> = vec![1, 2]; vec_truncate_outside(&mut p, &mut w); }

#[kani::modifies(&p.a)]
fn vec_as_mut_ptr_write_outside(p: &mut Pair, w: &mut Vec<u8>) { p.a = 1; unsafe { *w.as_mut_ptr() = 9; } }
#[kani::proof_for_contract(vec_as_mut_ptr_write_outside)]
fn vec_as_mut_ptr_write_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut w: Vec<u8> = vec![1, 2]; vec_as_mut_ptr_write_outside(&mut p, &mut w); }

#[kani::modifies(&p.a)]
fn string_push_str_outside(p: &mut Pair, s: &mut String) { p.a = 1; s.push_str("xy"); }
#[kani::proof_for_contract(string_push_str_outside)]
fn string_push_str_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut s = String::new(); string_push_str_outside(&mut p, &mut s); }

#[kani::modifies(s)]
fn string_push_str_inside(s: &mut String) { s.push_str("xy"); }
#[kani::proof_for_contract(string_push_str_inside)]
fn string_push_str_inside_safe() { let mut s = String::new(); string_push_str_inside(&mut s); }

#[kani::modifies(&p.a)]
fn vecdeque_pop_outside(p: &mut Pair, d: &mut std::collections::VecDeque<u8>) { p.a = 1; let _ = d.pop_front(); }
#[kani::proof_for_contract(vecdeque_pop_outside)]
fn vecdeque_pop_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut d = std::collections::VecDeque::new(); d.push_back(5u8); vecdeque_pop_outside(&mut p, &mut d); }

#[kani::modifies(&p.a)]
fn option_take_outside(p: &mut Pair, o: &mut Option<u32>) { p.a = 1; let _ = o.take(); }
#[kani::proof_for_contract(option_take_outside)]
fn option_take_outside_must_fail() { let mut p = Pair { a: kani::any(), b: kani::any() }; let mut o: Option<u32> = Some(kani::any()); option_take_outside(&mut p, &mut o); }

#[kani::modifies(o)]
fn option_take_inside(o: &mut Option<u32>) { let _ = o.take(); }
#[kani::proof_for_contract(option_take_inside)]
fn option_take_inside_safe() { let mut o: Option<u32> = Some(kani::any()); option_take_inside(&mut o); }
