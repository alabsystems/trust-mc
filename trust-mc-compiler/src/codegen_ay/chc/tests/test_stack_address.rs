// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Stack allocation addresses observed through base-address state variables
//! (chc/heap/stack_address.rs).

#![allow(clippy::unwrap_used)]

use ay_bindings::{Expr, Sort};

use super::common::*;

const SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_cross_alloc_lt(a: u8, b: u8) -> bool {
        let x = a;
        let y = b;
        let px: *const u8 = &x;
        let py: *const u8 = &y;
        px < py
    }

    // Equality is identity, not an address observation.
    pub fn probe_no_address_observation(a: u8) -> bool {
        let x = a;
        let px: *const u8 = &x;
        px == px
    }

    // At opt-level=0 rustc checks `*px` for null (and alignment) by casting the
    // pointer to usize; those casts decide nothing a stack identity term does not.
    pub fn probe_deref_checks_do_not_observe(a: u32) -> u32 {
        let x = a;
        let px: *const u32 = &x;
        unsafe { *px }
    }

    // Reading a u32 out of a u8 local: the alignment check requires 4 > 1. Every
    // base is 2^48-aligned (Kani's layout), so the identity term's offset answers
    // it.
    pub fn probe_overaligned_deref_observes(a: u8) -> u32 {
        let x = [a; 4];
        let px = &x as *const [u8; 4] as *const u32;
        unsafe { *px }
    }

    // A u8 local elsewhere in the body does not make the u32 deref's alignment
    // check an observation: the checked pointer points into `x`.
    pub fn probe_mixed_alignment_checks_do_not_observe(a: u32, flag: bool) -> u32 {
        let x = a;
        let mut z = flag;
        let pz: *mut bool = &mut z;
        unsafe { *pz = true };
        let px: *const u32 = &x;
        unsafe { *px }
    }

    // Two pointers into one array compare exactly on offsets: no base.
    pub fn probe_same_array_order(a: [u8; 4]) -> bool {
        let x = a;
        let p: *const u8 = &x[0];
        let q: *const u8 = &x[3];
        p < q
    }

    // A pointer-to-integer cast the program itself uses.
    pub fn probe_program_cast_observes(a: u32) -> usize {
        let x = a;
        let px: *const u32 = &x;
        let v = unsafe { *px } as usize;
        (px as usize).wrapping_add(v)
    }
"#;

fn mem_config() -> ChcConfig {
    ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() }
}

#[test]
fn test_observed_address_of_a_tracked_constant_pointer_is_base_plus_offset() {
    let base = Expr::var("base_5", Sort::bitvec(16));
    let table = vec![(5u32, base.clone(), Expr::var("r_5", Sort::bitvec(48)))];
    let ptr = Expr::bitvec_const(5u128, 32).concat(Expr::bitvec_const(8u128, 32));
    let (addr, tracked) = ChcCtx::stack_observed_address(&table, &ptr, ptr.clone());
    assert_eq!(tracked, Expr::bool_const(true));
    let text = addr.to_string();
    assert!(text.contains("base_5"), "observed address must read the base: {text}");
}

#[test]
fn test_observed_address_of_an_untracked_constant_pointer_is_the_default() {
    let table =
        vec![(5u32, Expr::var("base_5", Sort::bitvec(16)), Expr::var("r_5", Sort::bitvec(48)))];
    let ptr = Expr::bitvec_const(6u128, 32).concat(Expr::bitvec_const(0u128, 32));
    let (addr, tracked) = ChcCtx::stack_observed_address(&table, &ptr, ptr.clone());
    assert_eq!(tracked, Expr::bool_const(false));
    assert_eq!(addr, ptr);
}

#[test]
fn test_observed_address_of_a_symbolic_pointer_is_guarded_by_its_object_lane() {
    let table = vec![
        (5u32, Expr::var("base_5", Sort::bitvec(16)), Expr::var("r_5", Sort::bitvec(48))),
        (6u32, Expr::var("base_6", Sort::bitvec(16)), Expr::var("r_6", Sort::bitvec(48))),
    ];
    let ptr = Expr::var("p", Sort::bitvec(64));
    let (addr, tracked) = ChcCtx::stack_observed_address(&table, &ptr, ptr.clone());
    let (addr, tracked) = (addr.to_string(), tracked.to_string());
    assert!(addr.contains("base_5") && addr.contains("base_6"), "{addr}");
    assert!(tracked.contains("extract") || tracked.contains("_ extract"), "{tracked}");
}

#[test]
fn test_cross_allocation_order_reads_bases_and_same_allocation_order_reads_offsets() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_cross_alloc_lt");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_cross_alloc_lt", mem_config());
        chc_ctx.collect_state_vars();

        let tracked: Vec<usize> = chc_ctx.heap_state.stack_bases.iter().map(|b| b.local).collect();
        assert_eq!(tracked.len(), 2, "exactly the two compared locals are tracked: {tracked:?}");
        assert_eq!(
            chc_ctx.stack_base_state_indices().len(),
            tracked.len(),
            "every tracked local has a state variable"
        );

        let entry = chc_ctx.stack_base_entry_constraints();
        // Per local: the base is `region << 48`, the region is not 0 and not a
        // tracked id; one pair of distinct regions.
        assert!(entry.len() >= 3 * tracked.len() + 1, "entry constraints: {}", entry.len());
        assert!(
            entry.iter().any(|c| c.to_string().contains("extract 47 0")),
            "the base's in-region offset is zero: {entry:?}"
        );

        let pa = chc_ctx.get_or_create_local_address(tracked[0]).unwrap();
        let pb = chc_ctx.get_or_create_local_address(tracked[1]).unwrap();
        let (l, r) = chc_ctx.ptr_order_operands(pa.clone(), pb.clone());
        assert!(l.to_string().contains("__stack_base_"), "cross-allocation lhs: {l}");
        assert!(r.to_string().contains("__stack_base_"), "cross-allocation rhs: {r}");

        let pa1 = pa.clone().bvadd(Expr::bitvec_const(1u128, 64));
        let (l, r) = chc_ctx.ptr_order_operands(pa.clone(), pa1.clone());
        assert_eq!((l, r), (pa.clone(), pa1), "one allocation compares identities");

        let as_int = chc_ctx.ptr_to_int_value(pa.clone());
        assert!(as_int.to_string().contains("__stack_base_"), "cast reads the base: {as_int}");
        let back = chc_ctx.int_to_ptr_value(as_int);
        assert!(back.to_string().contains("ite"), "exposed provenance maps back: {back}");
    });
}

#[test]
fn test_a_body_that_observes_no_address_tracks_no_base() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_no_address_observation");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_no_address_observation", mem_config());
        chc_ctx.collect_state_vars();
        assert!(chc_ctx.heap_state.stack_bases.is_empty());
        assert!(chc_ctx.stack_base_entry_constraints().is_empty());
        let pa = chc_ctx.get_or_create_local_address(2).unwrap();
        // No base: an untracked object's address is its region (its id) over
        // the offset, Kani's `id << 48 | offset`.
        let as_int = chc_ctx.ptr_to_int_value(pa.clone());
        let expected = crate::codegen_ay::chc::pointer_step::identity_address_view(pa.clone());
        assert_eq!(
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&expected).unwrap_or(expected),
            as_int,
            "no base: an address is the address view of the identity"
        );
        let back = chc_ctx.int_to_ptr_value(as_int);
        assert_eq!(
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&back).unwrap_or(back),
            trust_mc_core::chc_const_prop::eval::try_eval_to_const(&pa).unwrap_or(pa),
            "and back"
        );
    });
}

#[test]
fn test_rustc_deref_checks_are_not_address_observations() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_checks_do_not_observe");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_deref_checks_do_not_observe", mem_config());
        let checks = chc_ctx.rustc_pointer_check_casts();
        assert_eq!(checks.len(), 2, "one null-check cast and one alignment-check cast: {checks:?}");
        assert!(checks.values().any(|c| c.required_align.is_none()), "null check: {checks:?}");
        assert!(
            checks.values().any(|c| c.required_align == Some(4)),
            "alignment check requires 4: {checks:?}"
        );
        assert!(
            checks.values().all(|c| matches!(
                c.root,
                crate::codegen_ay::chc::heap::stack_address::PtrRoot::StackLocal(_)
            )),
            "both checks resolve to x: {checks:?}"
        );
        chc_ctx.collect_state_vars();
        assert!(chc_ctx.heap_state.stack_bases.is_empty(), "checks alone track nothing");
    });
}

#[test]
fn test_an_overaligned_deref_check_is_decided_by_the_identity() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_overaligned_deref_observes");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_overaligned_deref_observes", mem_config());
        chc_ctx.collect_state_vars();
        assert!(
            chc_ctx.heap_state.stack_bases.is_empty(),
            "a 2^48-aligned base decides every alignment check on the offset"
        );
    });
}

#[test]
fn test_a_program_pointer_to_integer_cast_is_an_address_observation() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_program_cast_observes");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_program_cast_observes", mem_config());
        chc_ctx.collect_state_vars();
        assert_eq!(chc_ctx.heap_state.stack_bases.len(), 1, "x is tracked");
    });
}

#[test]
fn test_an_alignment_check_is_judged_by_the_local_it_points_into() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_mixed_alignment_checks_do_not_observe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_mixed_alignment_checks_do_not_observe",
            mem_config(),
        );
        chc_ctx.collect_state_vars();
        assert!(chc_ctx.heap_state.stack_bases.is_empty(), "no check observes an address");
    });
}

#[test]
fn test_a_comparison_within_one_allocation_tracks_no_base() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_same_array_order");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_same_array_order", mem_config());
        chc_ctx.collect_state_vars();
        assert!(chc_ctx.heap_state.stack_bases.is_empty(), "one allocation needs no base");
    });
}

const WRAP_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_wrapping_round_trip(a: [u8; 4], k: usize) -> bool {
        let p = a.as_ptr();
        let q = p.wrapping_byte_add(k).wrapping_byte_sub(k);
        q == p
    }
"#;

/// Object 5, offset `off`, as an identity term.
fn identity(object: u128, off: u128) -> Expr {
    Expr::bitvec_const(((off >> 32) << 48) | (object << 32) | (off & 0xFFFF_FFFF), 64)
}

#[test]
fn test_a_wrapping_step_inside_kanis_object_range_keeps_object_and_address() {
    // Kani's object range is [0, 2^48): a step of 2^47 bytes from the base is the
    // object over offset 2^47, and its address is the base's plus 2^47. The
    // fifth round's windows were centered on the base and marked this step as
    // landed in the next window (first review of the sixth round, finding 1).
    with_test_ay_ctx_for_source(WRAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_round_trip");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrapping_round_trip", mem_config());
        let p = identity(5, 0);
        let k = Expr::bitvec_const(1u128 << 47, 64);
        let q = chc_ctx.step_wrapping_address(p, k, false);
        assert_eq!(q, identity(5, 1 << 47), "same object, offset 2^47, not far");
        let addr = chc_ctx.ptr_to_int_value(q);
        assert_eq!(addr, Expr::bitvec_const((5u128 << 48) | (1u128 << 47), 64));
        assert!(
            chc_ctx.pending_far_observations.borrow().is_empty(),
            "an address inside the object range is no fail-closed observation"
        );
    });
}

#[test]
fn test_a_step_past_kanis_object_range_is_far_and_comes_back_exactly() {
    // A step of 2^48 bytes leaves the object range: same object, the FAR bit,
    // the low 48 offset bits. Stepping back by 2^48 is the original pointer: the
    // far constant's full offset is remembered. The fifth round gave the far
    // pointer the window it reached as its object and marked the way back as
    // landed (finding 2).
    with_test_ay_ctx_for_source(WRAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_round_trip");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrapping_round_trip", mem_config());
        let p = identity(5, 8);
        let k = Expr::bitvec_const(1u128 << 62, 64);
        let far = chc_ctx.step_wrapping_address(p.clone(), k.clone(), false);
        let far_object = 5u128 | u128::from(super::super::heap::stack_address::FAR_BIT);
        assert_eq!(far, identity(far_object, 8), "same object, FAR bit, offset 8 mod 2^48");
        let back = chc_ctx.step_wrapping_address(far, k, true);
        assert_eq!(back, p, "the round trip is exactly the original pointer");
    });
}

#[test]
fn test_a_far_pointers_address_is_a_fail_closed_observation() {
    // Kani answers a far pointer's address with a 48-bit wrap under a symbolic
    // count and with the 64-bit sum under a literal one (finding 7): its
    // observation is recorded for the block's cut, never answered.
    with_test_ay_ctx_for_source(WRAP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapping_round_trip");
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_wrapping_round_trip", mem_config());
        assert!(chc_ctx.far_pointers_possible(), "the body steps a pointer");
        let far = chc_ctx.step_wrapping_address(
            identity(5, 0),
            Expr::bitvec_const(1u128 << 48, 64),
            false,
        );
        chc_ctx.far_observation_range_active.set(true);
        let _ = chc_ctx.ptr_to_int_value(far);
        let pending = chc_ctx.pending_far_observations.borrow();
        assert_eq!(pending.len(), 1, "one fail-closed observation: {pending:?}");
        assert_eq!(pending[0].0, Expr::bool_const(true), "the constant pointer is far");
        assert!(!pending[0].2, "a far observation is never certified");
    });
}

const FAR_PRECISION_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_slice_wrapping_step(data: [u8; 5], offset: usize) -> *const [u8] {
        let ptr = &data as *const [u8];
        ptr.wrapping_byte_add(offset)
    }

    pub fn probe_with_addr_tag(x: u64) -> *const u64 {
        let p = &x as *const u64;
        p.with_addr(p.addr() | 2)
    }

    pub fn probe_box_deref(b: &Box<u64>) -> &u64 {
        std::ops::Deref::deref(b)
    }

    pub fn probe_box_new_into_raw() -> *mut u64 {
        let b = Box::new(5u64);
        Box::into_raw(b)
    }

    pub fn probe_box_from_far_raw_into_raw(q: *mut u64, k: usize) -> *mut u64 {
        let b = unsafe { Box::from_raw(q.wrapping_byte_add(k)) };
        Box::into_raw(b)
    }

    const T: &str = "hello";

    pub fn probe_const_str_as_ptr_step() -> *const u8 {
        let p = T.as_ptr();
        p.wrapping_add(2)
    }

    pub fn probe_param_str_as_ptr_step(s: &str) -> *const u8 {
        let p = s.as_ptr();
        p.wrapping_add(2)
    }
"#;

/// The local of `body` whose debug name is `name`.
fn local_named(body: &rustc_public::mir::Body, name: &str) -> usize {
    body.var_debug_info
        .iter()
        .find_map(|info| match &info.value {
            rustc_public::mir::VarDebugInfoContents::Place(place)
                if info.name == name && place.projection.is_empty() =>
            {
                Some(place.local)
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("no local named {name}"))
}

fn copy_of(local: usize) -> rustc_public::mir::Operand {
    rustc_public::mir::Operand::Copy(rustc_public::mir::Place { local, projection: Vec::new() })
}

#[test]
fn test_a_wide_pointers_wrapping_step_knows_its_offset() {
    // `&data as *const [u8]` cannot be far, so the step from it knows the 64-bit
    // offset of its data word. Read off the wide value, the offset was unknown
    // and each step of a round trip drew a free far bit, which cost the bug twin
    // its Genuine label (slice_ptr_byte_add_deref_dual.rs
    // `bug_wrapping_roundtrip_len_is_not_fabricated`, Genuine on main).
    with_test_ay_ctx_for_source(FAR_PRECISION_SOURCE, |ctx| {
        let fn_name = "probe_slice_wrapping_step";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, mem_config());
        let ptr = local_named(&body, "ptr");
        let wide = Expr::var("ptr_value", Sort::bitvec(128));
        let t = chc_ctx.wrapping_operand_t64(&copy_of(ptr), &wide, &Default::default());
        let t = t.expect("the data word's 64-bit offset is known");
        assert_eq!(t.sort().bitvec_width(), Some(64));
    });
}

#[test]
fn test_a_tag_rebase_of_a_pointer_that_cannot_be_far_cannot_be_far() {
    // `p.with_addr(p.addr() | 2)` is `p`'s object at an address in `p`'s own
    // region: far exactly when `p` is, and `p` is a local's address. Taken as
    // any wrapping step, the tagged pointer drew a free far bit and every
    // observation of it a fail-closed split (`safe_low_tag_roundtrip_stack`,
    // proved on main, Unknown before).
    with_test_ay_ctx_for_source(FAR_PRECISION_SOURCE, |ctx| {
        let fn_name = "probe_with_addr_tag";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, mem_config());
        assert!(chc_ctx.operand_cannot_be_far(&copy_of(0)), "the tagged pointer is not far");
    });
}

#[test]
fn test_a_boxs_pointer_is_the_pointer_it_was_built_from() {
    // A `Box`'s data pointer is the pointer it was built from (round 9 of
    // fix/chc-false-certificates, `box_pointer_source`): `Box::new` allocates,
    // so `Box::into_raw` of it cannot be far; `Box::from_raw(p)` holds `p`
    // (undefined behavior Kani does not report when `p` is no box allocation),
    // so a pointer stepped by a wrapping step and round-tripped through a box
    // may be far. The walk used to take every box's pointer as a fresh
    // allocation, "whatever wrote the box": `Box::into_raw(Box::from_raw(q))
    // != p` with `q` stepped by `1 << 48` was a clean proof where Kani fails it
    // (`rv_far_obs.rs` `o11_box_from_raw_roundtrip`). A box this body did not
    // build (a reference parameter in `<Box as Deref>::deref`) may hold any
    // pointer, so its pointer may be far too.
    with_test_ay_ctx_for_source(FAR_PRECISION_SOURCE, |ctx| {
        for (fn_name, may_be_far) in
            [("probe_box_new_into_raw", false), ("probe_box_from_far_raw_into_raw", true)]
        {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, mem_config());
            assert_eq!(
                chc_ctx.operand_cannot_be_far(&copy_of(0)),
                !may_be_far,
                "{fn_name}: the returned pointer may be far: {may_be_far}"
            );
        }
        use rustc_public::mir::TerminatorKind;
        use rustc_public::mir::mono::Instance;
        use rustc_public::ty::{RigidTy, TyKind};
        let probe = find_instance_by_suffix(ctx.tcx, "probe_box_deref");
        let probe_body = probe.body().expect("function body");
        let instance = probe_body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, .. } => match func.ty(probe_body.locals()).ok()?.kind() {
                    TyKind::RigidTy(RigidTy::FnDef(def, args)) => Instance::resolve(def, &args).ok(),
                    _ => None,
                },
                _ => None,
            })
            .expect("the call to Box::deref");
        let body = instance.body().expect("Box::deref has a body");
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "deref", mem_config());
        assert!(
            !chc_ctx.operand_cannot_be_far(&copy_of(0)),
            "a box this body did not build may hold a far pointer"
        );
    });
}

#[test]
fn test_a_constant_strs_data_pointer_cannot_be_far() {
    // `str::as_ptr` is the reference's data pointer, no step: from a constant
    // `&str` it cannot be far, so a wrapping step from it draws no free far bit
    // (const_pointer_raw_from_ref_dual.rs `bug_substr_as_ptr`, Genuine on main,
    // OverApproximation on the merge of main f5dfb8d48 before this). From a
    // parameter it may still be far.
    with_test_ay_ctx_for_source(FAR_PRECISION_SOURCE, |ctx| {
        for (fn_name, may_be_far) in
            [("probe_const_str_as_ptr_step", false), ("probe_param_str_as_ptr_step", true)]
        {
            let instance = find_instance_by_suffix(ctx.tcx, fn_name);
            let body = instance.body().expect("function body");
            let chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, mem_config());
            let p = local_named(&body, "p");
            assert_eq!(!chc_ctx.operand_cannot_be_far(&copy_of(p)), may_be_far, "{fn_name}");
        }
    });
}
