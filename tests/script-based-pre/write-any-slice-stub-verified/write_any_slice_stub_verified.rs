// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

#![allow(unused)]

extern crate kani;

#[kani::requires(!xs.is_empty())]
#[kani::modifies(xs)]
#[kani::ensures(|_| true)]
fn havoc_slice(xs: &mut [u32]) {
    xs[0] = 1;
}

#[kani::requires(!xs.is_empty())]
#[kani::modifies(xs)]
#[kani::ensures(|_| true)]
fn wrapper(xs: &mut [u32]) {
    havoc_slice(xs);
}

#[kani::proof_for_contract(havoc_slice)]
fn prove_havoc_slice() {
    let mut data = [0_u32; 2];
    havoc_slice(&mut data[..]);
}

#[kani::proof_for_contract(wrapper)]
#[kani::stub_verified(havoc_slice)]
fn reaches_write_any_slice_model() {
    let mut data = [0_u32; 2];
    wrapper(&mut data[..]);
}
