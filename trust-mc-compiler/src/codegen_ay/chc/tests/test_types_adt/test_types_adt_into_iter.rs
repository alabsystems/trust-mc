// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_translate_into_iter_sort_array() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        pub fn probe_array_into_iter() {
            let mut iter = IntoIterator::into_iter([1u32, 2, 3]);
            let _ = iter.next();
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_into_iter");
        let body = instance.body().expect("function body");

        let (def, args) =
            find_into_iter_adt_in_locals(&body).expect("should find array IntoIter ADT in locals");
        let full_name = def.0.name();
        assert!(
            full_name.contains("array"),
            "array IntoIter should have an array path, got: {full_name}"
        );

        let sort = ChcCtx::translate_into_iter_sort(def, &args);
        assert!(sort.is_some(), "Array IntoIter should produce a sort");
        let sort = sort.unwrap();
        assert!(sort.is_datatype(), "Array IntoIter should be a datatype");
        let dt = sort.datatype_sort().expect("array IntoIter should be datatype-backed");
        let fields = &dt.constructors[0].fields;
        assert_eq!(fields.len(), 1, "array IntoIter should have one inner field");
        let inner =
            fields[0].sort.datatype_sort().expect("array IntoIter inner should be datatype");
        assert_eq!(
            inner.name, "PolymorphicIter",
            "array IntoIter sort should wrap PolymorphicIter"
        );
    });
}
