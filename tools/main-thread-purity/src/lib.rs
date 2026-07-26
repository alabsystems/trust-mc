// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// `main_thread_purity` — a forbidden-call REACHABILITY checker for trust-mc.
//
// ## What this is
//
// trust-mc's BMC/CHC backends prove things about *values and reachable states*.
// They cannot observe a *runtime hang*: a wedge where the UI/main thread issues
// an unbounded blocking syscall and the process never makes progress. That class
// of bug is not a property of any single function's value-space — it is a
// REACHABILITY property of the whole monomorphized call graph: "from a UI/main
// thread root, can control ever reach a blocking leaf?"
//
// This crate answers exactly that query. It is modeled on, and designed to drop
// directly behind, the real trust-mc reachability collector in
//   trust-mc-compiler/src/kani_middle/reachability.rs
// which already:
//   * builds a `CallGraph` of `MonoItem`s with a worklist (`reachable_items`),
//   * follows BOTH `TerminatorKind::Call` and `TerminatorKind::Drop` edges
//     (`MonoItemsFnCollector::visit_terminator`, lines ~490-520), tagging each
//     edge with a `CollectionReason` (`DirectCall`/`IndirectCall`/`StaticDrop`),
//   * keeps `back_edges` for reverse traversal (used by `dump_reason`), and
//   * classifies callees by their `Instance::name()` path string against a
//     prefix list (`is_prefix_abstracted`, lines ~704-726) using the
//     trailing-`::` strip discipline for the `<… as …>::method` impl-path case.
//
// The ONLY new pieces this checker adds on top of that existing substrate are:
//   (1) a SEED SET of UI/main-thread roots (winit `ApplicationHandler` methods,
//       `fn main` after `run_app` returns, and every `Drop` transitively reached
//       from those) — in place of `#[kani::proof]` harnesses;
//   (2) a FORBIDDEN-CALL (deny) set of unbounded-blocking leaf operations; and
//   (3) a reachability query that reports each seed -> forbidden-leaf witness
//       path, flagging the via-`Drop` case as the high-severity architectural
//       smell (the call is invisible at its site — the programmer wrote `}`).
//
// ## How it maps onto the real types
//
//   this crate            trust-mc reachability.rs
//   ----------            ------------------------
//   ItemPath(String)      `Node`'s `instance.name()` / `def_path_str()` string
//   EdgeReason            `CollectionReason` (DirectCall/IndirectCall/StaticDrop)
//   CallGraph             `CallGraph { nodes, edges, back_edges }`
//   matches_prefix()      `is_prefix_abstracted()` (same trailing-`::` guard)
//   Policy::deny          a new sibling of `ABSTRACT_FUNCTION_PREFIXES`
//   Policy::seed          UI roots, found like `filter_crate_items` finds proofs
//   analyze()             a `reachable_items`-shaped worklist, but recording the
//                         witness path to the forbidden leaf instead of codegen.

pub mod analysis;
pub mod fixtures;
pub mod graph;
pub mod path;
pub mod policy;

pub use analysis::{analyze, Finding, Severity};
pub use graph::{CallGraph, Edge, EdgeReason};
pub use policy::Policy;
