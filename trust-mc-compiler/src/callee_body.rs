// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The one way codegen fetches a callee's MIR body.
//!
//! Every codegen consumer that executes, inlines, walks or summarises a callee from its MIR
//! — the BMC mini-inliner and its closure, fn-pointer and iterator-adapter callers, the CHC
//! fn-inline and nested walkers, the dyn-callable, `Fn`-trait and fn-pointer resolvers, the
//! drop-glue, coroutine, collection and `block_on` models, the uninterpreted-function
//! summaries — takes the body from [`CalleeBody::callee_body`], never from
//! `Instance::body` or `FnDef::body` directly. The guard it adds is
//! [`crate::intrinsics::is_modelled_renamed_intrinsic`]: a float intrinsic Trust core renamed
//! reaches trust-mc's model or fails closed, and never runs Trust's fallback body.
//!
//! Why one choke point: on the frozen nightly `minnumf32` has no body, so every one of those
//! consumers finds nothing to inline and the call reaches the model. On Trust the same call is
//! `minimum_number_nsz_f32`, which carries a fallback body returning `y` whenever the arguments
//! compare equal — one of the results the intrinsic may produce, not the only one. The first
//! repair guarded the mini-inliner, `FunctionInlinePass` and the two CHC walkers; the second
//! review reached the body anyway through `&dyn Fn = &intrinsics::minimum_number_nsz_f32`
//! (`dyn_callable_resolver`), through `Box<dyn Fn>`, and through the `Fn`-trait and fn-pointer
//! resolvers, and proved `f(-0.0, 0.0).is_sign_positive()` on the Trustc route where the nightly
//! route fails closed. Twenty-odd raw fetch sites cannot each remember the rule, so the rule
//! lives here and a source scan (`tests`) refuses a raw `.body()` on a callee anywhere under
//! `codegen_ay`.
//!
//! `FnDef::body` is guarded too: the def of a renamed intrinsic carries the same fallback body.
//! Coroutine and closure defs are not intrinsics and keep their raw `body()`.
//!
//! The second rule this choke point carries: the body is the one the unit RUNS. While a CHC
//! harness translation is in progress the unit's `#[kani::stub]`s are applied to every body
//! fetched here (`kani_middle::transform::stub_aware_instance_body`): a stubbed instance runs
//! its stub's body, and a call site naming a stubbed function names the stub, so no handler
//! keyed on the original's path claims it.

use rustc_public::mir::Body;
use rustc_public::mir::mono::Instance;
use rustc_public::ty::FnDef;

/// A callee's MIR body, or `None` when codegen must not see one.
pub(crate) trait CalleeBody {
    /// The body codegen may inline, walk or summarise. `None` for an instance or def with no
    /// MIR, and for a float intrinsic Trust core renamed (its model decides the call).
    fn callee_body(&self) -> Option<Body>;
}

impl CalleeBody for Instance {
    fn callee_body(&self) -> Option<Body> {
        if crate::intrinsics::is_modelled_renamed_intrinsic(self) {
            return None;
        }
        // The body as the unit runs it: with its `#[kani::stub]`s applied
        // while a CHC harness translation has installed them
        // (`kani_middle::transform::stub_aware_instance_body`).
        crate::kani_middle::transform::stub_aware_instance_body(self)
    }
}

impl CalleeBody for FnDef {
    fn callee_body(&self) -> Option<Body> {
        if is_modelled_renamed_intrinsic_def(self) {
            return None;
        }
        crate::kani_middle::transform::stub_aware_def_body(self)
    }
}

/// The MIR the transformation pipeline transforms for a REACHABLE instance, a renamed float
/// intrinsic's fallback body included. Reachability visits every instance a harness can
/// reach and runs the passes over each body it has; on Trust that includes
/// `minimum_number_nsz_f32` itself. That transformed body is an entry in the pipeline's cache,
/// not a call site: codegen reaches a callee's body only through [`CalleeBody::callee_body`],
/// which refuses the renamed intrinsic, so the cached body is never inlined, walked or
/// summarised. Refusing it here instead made reachability panic (`instance should have body`)
/// on every Trust-route harness that calls `f32::min`.
pub(crate) fn transform_input_body(instance: &Instance) -> Option<Body> {
    instance.body()
}

/// [`crate::intrinsics::is_modelled_renamed_intrinsic`] for a def without its generic
/// arguments: `fabs::<T>` is refused at every `T`, since without the arguments no width can
/// be named and every width of it is modelled. On the frozen nightly no def matches.
pub(crate) fn is_modelled_renamed_intrinsic_def(def: &FnDef) -> bool {
    let Some(intrinsic) = def.as_intrinsic() else {
        return false;
    };
    let name = intrinsic.fn_name();
    name == "fabs" || crate::intrinsics::nightly_float_intrinsic_name(&name, None).is_some()
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    fn collect_rs_files(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_rs_files(&path, out);
            } else if path.extension() == Some("rs".as_ref()) {
                out.push(path);
            }
        }
    }

    /// Production code under `codegen_ay` (and the transform entry points codegen fetches
    /// through) never calls `.body()` on a callee: every fetch goes through
    /// [`super::CalleeBody::callee_body`]. Coroutine and closure defs are the only receivers
    /// allowed a raw `body()`, by name.
    #[test]
    fn codegen_fetches_every_callee_body_through_the_guard() {
        let compiler_src =
            Path::new(concat!(env!("CARGO_MANIFEST_DIR"), "/../trust-mc-compiler/src"));
        let mut files = Vec::new();
        collect_rs_files(&compiler_src.join("codegen_ay"), &mut files);
        files.push(compiler_src.join("kani_middle/transform/mod.rs"));
        let mut violations = Vec::new();
        for path in &files {
            let rel =
                path.strip_prefix(compiler_src).unwrap_or(path).to_string_lossy().into_owned();
            if rel.contains("/tests/")
                || rel.ends_with("/tests.rs")
                || rel.ends_with("_test.rs")
                || rel.ends_with("_tests.rs")
            {
                continue;
            }
            let Ok(content) = std::fs::read_to_string(path) else { continue };
            let lines: Vec<&str> = content.lines().collect();
            let mut in_test_module = false;
            for (i, line) in lines.iter().enumerate() {
                let trimmed = line.trim_start();
                // An inline `#[cfg(test)] mod … {` runs to the end of the file by convention;
                // an out-of-line `#[cfg(test)] mod …;` declares nothing here.
                if trimmed.starts_with("#[cfg(test)]")
                    && lines.get(i + 1).is_some_and(|next| {
                        let next = next.trim_start();
                        next.starts_with("mod ") && next.trim_end().ends_with('{')
                    })
                {
                    in_test_module = true;
                }
                if in_test_module || trimmed.starts_with("//") {
                    continue;
                }
                if !line.contains(".body()") {
                    continue;
                }
                let allowed = ["coroutine_def.body()", "closure_def.body()"];
                let stripped = allowed.iter().fold(line.to_string(), |acc, ok| acc.replace(ok, ""));
                if stripped.contains(".body()") {
                    violations.push(format!("  {rel}:{}: {}", i + 1, line.trim()));
                }
            }
        }
        assert!(
            violations.is_empty(),
            "raw callee body fetches; use `CalleeBody::callee_body` (crate::callee_body):\n{}",
            violations.join("\n")
        );
    }
}
