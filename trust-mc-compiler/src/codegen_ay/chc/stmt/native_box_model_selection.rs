// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Physical Box dereferences require address-bearing memory semantics.

use crate::args::ChcTrackLevel;
use crate::codegen_ay::chc::ChcConfig;
use rustc_middle::ty::TyCtxt;
use rustc_public::mir::Body;

fn requires_memory(tcx: TyCtxt<'_>, body: &Body) -> bool {
    #[cfg(all(trust_toolchain, version("1.101")))]
    {
        use rustc_public::mir::{CastKind, Rvalue, StatementKind, TerminatorKind, mono::Instance};
        use rustc_public::ty::{RigidTy, TyKind};
        body.blocks.iter().any(|block| {
            if block.statements.iter().any(|statement| {
                matches!(
                    &statement.kind,
                    StatementKind::Assign(_, Rvalue::Cast(CastKind::BoxDerefTransmute, _, _))
                )
            }) {
                return true;
            }
            let TerminatorKind::Call { func, .. } = &block.terminator.kind else { return false };
            let Ok(ty) = func.ty(body.locals()) else { return false };
            let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { return false };
            Instance::resolve(def, &args).ok().is_some_and(|instance| {
                crate::codegen_ay::shared::native_box_raw::native_box_into_raw_identity(
                    tcx, &instance,
                )
                .is_some()
            })
        })
    }
    #[cfg(not(all(trust_toolchain, version("1.101"))))]
    {
        let _ = (tcx, body);
        false
    }
}

pub(super) fn config_for_body(tcx: TyCtxt<'_>, config: ChcConfig, body: &Body) -> ChcConfig {
    // This is the compiler's actual native dereference operation, not a type
    // name or guessed allocation. Its address cannot be used with Reg's
    // dropped pointee reads, and scalar int lifting cannot model its heap.
    // Select before creating the first context; validity, ownership and
    // initializedness still require their own ordinary checks.
    // A preserved ownership-release call carries the same checked pointer
    // operation even though its BoxDerefTransmute body was not inlined.
    if requires_memory(tcx, body) {
        ChcConfig { track_level: ChcTrackLevel::Mem, int_lift: false, ..config }
    } else {
        config
    }
}

#[cfg(all(test, feature = "compiler-corpus-tests", trust_toolchain, version("1.101")))]
mod tests {
    use super::*;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    const SOURCE: &str = r#"
        #![allow(dead_code, non_snake_case)]
        trait View { fn get(&self) -> u8; }
        impl View for u8 { fn get(&self) -> u8 { *self } }
        type Owner = Box<dyn View>;
        pub fn thin() -> u8 { *Box::new(7u8) }
        pub fn dynamic(value: u8) -> u8 {
            let owner: Owner = Box::new(value); owner.get()
        }
        pub fn borrowed(owner: &Box<u8>) -> u8 { **owner }
        struct BoxRaw { value: u8 }
        fn BoxDerefTransmute(value: BoxRaw) -> u8 { value.value }
        pub fn lookalike() -> u8 { BoxDerefTransmute(BoxRaw { value: 7 }) }
        pub fn stack(value: &u8) -> u8 { *value }
        pub fn allocation_only() { let _owner = Box::new(7u8); }
        pub fn native_release() -> *mut u8 { Box::into_raw(Box::new(7u8)) }
        struct Wrapper;
        impl Wrapper { fn into_raw(self) -> u8 { 7 } }
        pub fn release_lookalike() -> u8 { Wrapper.into_raw() }
    "#;

    #[test]
    fn actual_box_operation_selects_memory_before_reg_or_scalar_lifting() {
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            for (name, needed) in [
                ("thin", true),
                ("dynamic", true),
                ("borrowed", true),
                ("lookalike", false),
                ("stack", false),
                ("allocation_only", false),
                ("native_release", true),
                ("release_lookalike", false),
            ] {
                let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
                assert_eq!(requires_memory(ctx.tcx, &body), needed, "{name}");
                for track_level in [ChcTrackLevel::Reg, ChcTrackLevel::Ptr, ChcTrackLevel::Mem] {
                    for int_lift in [false, true] {
                        let original = ChcConfig { track_level, int_lift, ..ChcConfig::default() };
                        let selected = config_for_body(ctx.tcx, original, &body);
                        assert_eq!(
                            selected.track_level,
                            if needed { ChcTrackLevel::Mem } else { track_level },
                            "{name}"
                        );
                        assert_eq!(selected.int_lift, int_lift && !needed, "{name}");
                        assert_eq!(selected.memory_safety_checks, original.memory_safety_checks);
                        assert_eq!(selected.overflow_checks, original.overflow_checks);
                        assert_eq!(selected.uninit_checks, original.uninit_checks);
                    }
                }
            }
        });
    }
}
