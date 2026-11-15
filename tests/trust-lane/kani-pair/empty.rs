// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! T1 vacuity case: a harness with nothing to check. A proof of nothing is
//! never a CLEAN proof. The compiler certifies this body obligation-free (the
//! walk sees every reachable statement and terminator), so under D16's second
//! step the driver reports it as a visible non-clean success.
//! Expected: VERIFICATION:- SUCCESSFUL (no checks — compiler-certified
//! obligation-free), [AY:VACUOUS:no-checks], the proof qualifier
//! no_checks=compiler_certified_obligation_free, exit 0.

#[kani::proof]
fn harness_with_no_checks() {}
