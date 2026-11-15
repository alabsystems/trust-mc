// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::kani_middle::transform::body::MutableBody;
use crate::kani_middle::transform::inline::body_inline::{inline_drop_shim, inline_function};
use std::collections::HashSet;

const SOURCE: &str = r#"
    #[inline(never)]
    pub fn child(flag: bool, value: u8) -> u8 {
        let local = core::hint::black_box(value);
        if flag { local } else { 0 }
    }
    pub fn caller(flag: bool, value: u8) -> u8 { child(flag, value) }
    pub fn projected(flag: bool, value: u8) -> (u8, u8) { (child(flag, value), value) }
    #[inline(never)]
    pub unsafe fn shim(value: *mut u8) { unsafe { *value = 3; } }
    pub fn drop_owner(mut value: u8) { unsafe { shim(&raw mut value); } }
"#;

fn call_site(body: &Body) -> (usize, Vec<Operand>, Place, Option<usize>) {
    body.blocks
        .iter()
        .enumerate()
        .find_map(|(bb, block)| match &block.terminator.kind {
            TerminatorKind::Call { args, destination, target, .. } => {
                Some((bb, args.clone(), destination.clone(), *target))
            }
            _ => None,
        })
        .expect("direct child call")
}

fn markers(block: &BasicBlock, live: bool) -> HashSet<usize> {
    block
        .statements
        .iter()
        .filter_map(|statement| match statement.kind {
            StatementKind::StorageLive(local) if live => Some(local),
            StatementKind::StorageDead(local) if !live => Some(local),
            _ => None,
        })
        .collect()
}

#[test]
fn test_inline_storage_return_ends_owned_slots_and_preserves_explicit_activation() {
    with_test_tcx_for_source(SOURCE, |tcx| {
        let child = find_instance_by_suffix(tcx, "child");
        let mut callee = child.body().expect("child body");
        assert!(callee.locals().len() > 3);
        let explicit_local = callee.locals().len() - 1;
        callee.blocks[0].statements.insert(
            0,
            crate::rustc_compat::mir_statement(
                StatementKind::StorageLive(explicit_local),
                dummy_span(),
            ),
        );
        let caller = find_instance_by_suffix(tcx, "caller").body().expect("caller body");
        let (bb, args, destination, target) = call_site(&caller);
        let first_local = caller.locals().len();
        let first_block = caller.blocks.len();
        let mut caller = MutableBody::from(caller);
        inline_function(
            tcx,
            child,
            &mut caller,
            bb,
            &callee,
            &args,
            &destination,
            target,
            dummy_span(),
        );
        let owned: HashSet<_> = (first_local..caller.locals().len()).collect();
        let explicit_mapped = first_local + explicit_local - 1;
        let entry_lives = markers(&caller.blocks()[bb], true);
        assert!(!entry_lives.contains(&explicit_mapped));
        for local in owned.iter().filter(|&&local| local != explicit_mapped) {
            assert!(entry_lives.contains(local));
        }
        assert!(markers(&caller.blocks()[first_block], true).contains(&explicit_mapped));
        let mut returns = 0;
        for (index, original) in callee.blocks.iter().enumerate() {
            if matches!(original.terminator.kind, TerminatorKind::Return) {
                returns += 1;
                let dead = markers(&caller.blocks()[first_block + index], false);
                assert!(owned.is_subset(&dead));
                assert!(!dead.contains(&destination.local));
            }
        }
        assert!(returns > 0);
    });
}

#[test]
fn test_inline_storage_projected_result_is_copied_before_its_temporary_dies() {
    with_test_tcx_for_source(SOURCE, |tcx| {
        let child = find_instance_by_suffix(tcx, "child");
        let callee = child.body().expect("child body");
        let caller = find_instance_by_suffix(tcx, "projected").body().expect("caller body");
        let (bb, args, _, target) = call_site(&caller);
        let destination =
            Place { local: 0, projection: vec![ProjectionElem::Field(0, callee.locals()[0].ty)] };
        let return_temp = caller.locals().len();
        let first_block = caller.blocks.len();
        let post_return = first_block + callee.blocks.len();
        let mut caller = MutableBody::from(caller);
        inline_function(
            tcx,
            child,
            &mut caller,
            bb,
            &callee,
            &args,
            &destination,
            target,
            dummy_span(),
        );
        for (index, original) in callee.blocks.iter().enumerate() {
            if matches!(original.terminator.kind, TerminatorKind::Return) {
                let block = &caller.blocks()[first_block + index];
                assert!(!markers(block, false).contains(&return_temp));
                assert!(
                    matches!(block.terminator.kind, TerminatorKind::Goto { target } if target == post_return)
                );
            }
        }
        let post = &caller.blocks()[post_return];
        assert!(
            matches!(&post.statements[0].kind, StatementKind::Assign(place, _) if place == &destination)
        );
        assert!(
            matches!(post.statements[1].kind, StatementKind::StorageDead(local) if local == return_temp)
        );
        assert!(!markers(post, false).contains(&destination.local));
    });
}

#[test]
fn test_inline_storage_drop_shim_ends_its_frame_without_ending_caller_storage() {
    with_test_tcx_for_source(SOURCE, |tcx| {
        let shim = find_instance_by_suffix(tcx, "shim");
        let callee = shim.body().expect("shim body");
        let caller = find_instance_by_suffix(tcx, "drop_owner").body().expect("caller body");
        let (bb, _, _, target) = call_site(&caller);
        let first_local = caller.locals().len();
        let first_block = caller.blocks.len();
        let mut caller = MutableBody::from(caller);
        inline_drop_shim(
            tcx,
            shim,
            &mut caller,
            bb,
            &callee,
            &Place::from(1),
            target.expect("return target"),
        );
        let owned: HashSet<_> = (first_local..caller.locals().len()).collect();
        assert!(owned.is_subset(&markers(&caller.blocks()[bb], true)));
        let mut returns = 0;
        for (index, original) in callee.blocks.iter().enumerate() {
            if matches!(original.terminator.kind, TerminatorKind::Return) {
                returns += 1;
                let dead = markers(&caller.blocks()[first_block + index], false);
                assert!(owned.is_subset(&dead));
                assert!(!dead.contains(&1), "caller pointee outlives the shim frame");
            }
        }
        assert!(returns > 0);
    });
}
