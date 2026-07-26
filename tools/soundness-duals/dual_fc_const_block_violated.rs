// Violated-ensures dual for const_block.rs check_first (kani-flags: -Z function-contracts)
// first() returns Enum::First but the ensures claims Enum::Second. GENUINE
// violation -> MUST fail-Genuine, proving the enum-discriminant ensures check
// is a LIVE error rule.
#![feature(ptr_alignment_type)]
#[derive(PartialEq)]
enum Enum { First, Second }
#[kani::ensures(|result| *result == Enum::Second)] // WRONG: first() returns First
const fn first() -> Enum { const { Enum::First } }
#[kani::proof_for_contract(first)]
pub fn check_first() { let _ = first(); }
