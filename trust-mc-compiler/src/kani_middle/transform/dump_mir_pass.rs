// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Global transformation pass, which does not modify bodies but dumps MIR whenever the appropriate debug flag is passed.

use crate::kani_middle::reachability::CallGraph;
use crate::kani_middle::transform::GlobalPass;
use crate::kani_queries::QueryDb;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::mono::{Instance, MonoItem};
use rustc_session::config::OutputType;
use std::fs::File;
use std::io::BufWriter;
use std::io::Write;
use trust_mc_metadata::ArtifactType;

use super::BodyTransformation;

/// Dump all MIR bodies.
#[derive(Debug, Clone)]
pub(crate) struct DumpMirPass {
    pub(super) enabled: bool,
}

impl DumpMirPass {
    pub(crate) fn new(tcx: TyCtxt) -> Self {
        Self { enabled: tcx.sess.opts.output_types.contains_key(&OutputType::Mir) }
    }
}

impl GlobalPass for DumpMirPass {
    fn is_enabled(&self, _query_db: &QueryDb) -> bool {
        self.enabled
    }

    fn transform(
        &mut self,
        tcx: TyCtxt,
        _call_graph: &CallGraph,
        starting_items: &[MonoItem],
        instances: Vec<Instance>,
        transformer: &mut BodyTransformation,
    ) -> bool {
        // Create output buffer.
        let file_path = {
            let base_path = tcx.output_filenames(()).path(OutputType::Object);
            let base_name = base_path.as_path();
            let entry_point = (starting_items.len() == 1).then_some(starting_items[0].clone());
            // If there is a single entry point, use it as a file name.
            if let Some(MonoItem::Fn(starting_instance)) = entry_point {
                let mangled_name = starting_instance.mangled_name();
                let stem = base_name.file_stem().expect("output path should have file stem");
                let stem_str = stem.to_str().expect("output path file stem should be valid UTF-8");
                let file_stem = format!("{stem_str}_{mangled_name}");
                base_name.with_file_name(file_stem).with_extension(ArtifactType::ModelBase)
            } else {
                // Otherwise, use the object output path from the compiler.
                base_name.with_extension(ArtifactType::ModelBase)
            }
        };
        let out_file = File::create(file_path.with_extension("kani.mir"))
            .expect("failed to create MIR dump file");
        let mut writer = BufWriter::new(out_file);

        // For each def_id, dump their MIR.
        for instance in &instances {
            writeln!(writer, "// Item: {} ({})", instance.name(), instance.mangled_name())
                .expect("failed to write MIR item header");
            let _ = transformer.body_ref(tcx, *instance).dump(&mut writer, &instance.name());
        }

        // This pass just reads the MIR and thus never modifies it.
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dump_mir_pass_debug() {
        let pass = DumpMirPass { enabled: false };
        let dbg = format!("{:?}", pass);
        assert!(dbg.contains("DumpMirPass"));
        assert!(dbg.contains("false"));
    }

    #[test]
    fn test_dump_mir_pass_clone() {
        let pass = DumpMirPass { enabled: true };
        let cloned = pass.clone();
        assert!(cloned.enabled);
        assert!(pass.enabled, "original should remain valid after clone");
    }

    #[test]
    fn test_dump_mir_pass_disabled() {
        let pass = DumpMirPass { enabled: false };
        assert!(!pass.enabled);
    }

    #[test]
    fn test_dump_mir_pass_enabled() {
        let pass = DumpMirPass { enabled: true };
        assert!(pass.enabled);
    }
}
