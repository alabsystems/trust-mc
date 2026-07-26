// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::super::codegen_types_adt_sort::CodegenTypesAdtSort;
use super::*;

#[test]
fn test_translate_ty_custom_into_iter_uses_generic_adt_sort() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]

        pub struct LazyLeafRange {
            pub front: usize,
            pub back: usize,
        }

        pub struct IntoIter {
            pub range: LazyLeafRange,
            pub length: usize,
        }

        pub fn probe_custom_into_iter(iter: IntoIter) -> IntoIter {
            iter
        }
    "#;

    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "probe_custom_into_iter");
        let sort = ChcCtx::translate_ty(sig.inputs()[0]).unwrap();

        let dt = sort.datatype_sort().expect("custom IntoIter should translate to a datatype");
        assert_eq!(dt.name, "IntoIter");
        assert_eq!(dt.constructors.len(), 1);
        let fields = &dt.constructors[0].fields;
        assert_eq!(
            fields.len(),
            2,
            "custom IntoIter should keep its own fields, not array-iterator wrapper shape"
        );
        assert_eq!(fields[0].name, "fld_range");
        assert_eq!(fields[1].name, "fld_length");
        assert_eq!(
            fields[1].sort.bitvec_width(),
            Some(64),
            "usize length should remain pointer-width BV"
        );
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = sig.inputs()[0].kind() else {
            panic!("custom IntoIter should be an ADT type");
        };
        assert!(
            ChcCtx::translate_into_iter_sort(def, &args).is_none(),
            "user-defined IntoIter must not use the std::array::IntoIter special sort"
        );
    });
}
