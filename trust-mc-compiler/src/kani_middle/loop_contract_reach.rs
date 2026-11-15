// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Design 5 backstop (docs/chc-hole-fix-designs-2026-09-24.md, "Legacy
//! loop-contract latch"): which items a harness reaches can reach a loop
//! contract, read off the reachability collector's call graph.
//!
//! The CHC lane checks a loop contract only inside the body it encodes: the
//! harness plus whatever `FunctionInlinePass` inlined into it. Anywhere else
//! the loop runs raw. The inline walker walks a callee's RAW body, where the
//! register call answers `{ true }`, or havocs the callee with the loop in it,
//! or bails out of the arm that holds it. So a harness whose encoded body can
//! still reach a loop contract through one of its calls must never report
//! SUCCESSFUL. The walker's own sites book the register calls they meet
//! (`codegen_call_virtual_inline/loop_contract_scan.rs`); this is the view that
//! does not depend on which bodies the walker happens to walk.
//!
//! The collector visits every body the harness can reach through the transform
//! pipeline, non-local generic code included, and records per edge whether the
//! target is called directly, reified to a function pointer, a vtable method,
//! or held in a constant or static. It does NOT follow a function it abstracts
//! at the stub boundary (a collection method of the standard-library set, or any std
//! function the AY stub registry models): no edge, no node. So the graph gives
//! three answers for a function:
//!
//! * `reaching`: it has a path to a `kani_register_loop_contract` instance
//!   (register instances included). A yes is final.
//! * `clear`: the collector read its body and everything it reaches, found no
//!   register instance, and met no abstracted function on the way. A no is
//!   final: the transformed bodies are the program Kani checks.
//! * neither: the graph cannot say (its reach passes an abstracted function,
//!   or the collector never read it). The CHC side then reads raw bodies
//!   (`loop_contract_scan::Scan`).
//!
//! `address_taken` lists every function that is the target of an edge that is
//! not a direct call: a fn-pointer reification, a vtable method, a pointer held
//! in an allocation. If one of them can reach a loop contract, a call through
//! ANY pointer or `dyn` receiver the harness makes, however deep in non-local
//! code, may run it.
//!
//! LIMIT, stated: a coercion or reification made only inside a function the
//! collector abstracts is not seen (the same limit as `dyn_universe.rs`), and
//! neither is a fn pointer to an abstracted function held in a constant.

use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use std::collections::HashSet;

use crate::kani_middle::attributes;

/// The `kanitool::fn_marker` of the loop-contract register fn, which the
/// loop-contract macro also puts in the fn's name
/// (`kani_register_loop_contract<loop id>`).
pub(crate) const REGISTER_MARKER: &str = "kani_register_loop_contract";

/// Is `instance` a loop-contract register fn?
pub(crate) fn is_register_instance(instance: Instance) -> bool {
    instance.def.name().contains(REGISTER_MARKER)
        || attributes::fn_marker(instance.def).as_deref() == Some(REGISTER_MARKER)
}

/// What the collector's call graph says about the loop contracts a harness
/// can reach (see the module docs).
#[derive(Clone, Debug, Default)]
pub(crate) struct LoopContractReach {
    reaching: HashSet<Instance>,
    clear: HashSet<Instance>,
    address_taken: HashSet<Instance>,
}

impl LoopContractReach {
    pub(crate) fn new(
        reaching: HashSet<Instance>,
        clear: HashSet<Instance>,
        address_taken: HashSet<Instance>,
    ) -> Self {
        Self { reaching, clear, address_taken }
    }

    /// Can a call of `instance` reach a loop contract? `None` when the graph
    /// cannot say (see the module docs).
    pub(crate) fn reaches(&self, instance: &Instance) -> Option<bool> {
        if self.reaching.contains(instance) {
            Some(true)
        } else if self.clear.contains(instance) {
            Some(false)
        } else {
            None
        }
    }

    /// Every function whose address the harness takes (see the module docs).
    pub(crate) fn address_taken(&self) -> impl Iterator<Item = Instance> + '_ {
        self.address_taken.iter().copied()
    }

    /// Does the graph show the harness reaching any loop contract?
    pub(crate) fn any(&self) -> bool {
        !self.reaching.is_empty()
    }
}
