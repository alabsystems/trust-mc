// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Maps trust_vc `SortMeta` to ay `Sort`.

use ay_bindings::Sort;
use trust_vc_merge_contract::SortMeta;

/// Translate a trust_vc `SortMeta` to a ay `Sort`.
///
/// Mapping:
/// - `Bool` -> `Sort::bool()`
/// - `BitVector { width, .. }` -> `Sort::bitvec(width)` (signedness is in Expr ops, not Sort)
/// - `Seq { elem }` -> `Sort::seq(translate(elem))`
/// - `Set { elem }` -> `Sort::array(translate(elem), Sort::bool())` (SMT set encoding)
/// - `Map { key, value }` -> `Sort::array(translate(key), translate(value))`
/// - `Array { index, element }` -> `Sort::array(translate(index), translate(element))`
/// - `FloatingPoint { exponent_bits, significand_bits }` -> IEEE 754 FP sort
pub fn translate_sort(meta: &SortMeta) -> Result<Sort, String> {
    match meta {
        SortMeta::Bool => Ok(Sort::bool()),
        SortMeta::MathInt => Ok(Sort::int()),
        SortMeta::Real => Ok(Sort::real()),
        SortMeta::BitVector { width, signed: _ } => {
            if *width == 0 {
                return Err("BitVector width must be > 0".to_string());
            }
            Ok(Sort::bitvec(*width))
        }
        SortMeta::Opaque { name } => Ok(Sort::uninterpreted(name.clone())),
        SortMeta::Seq { elem } => {
            let elem_sort = translate_sort(elem)?;
            Ok(Sort::seq(elem_sort))
        }
        SortMeta::Set { elem } => {
            let elem_sort = translate_sort(elem)?;
            // SMT sets are modeled as Array(elem -> Bool)
            Ok(Sort::array(elem_sort, Sort::bool()))
        }
        SortMeta::Map { key, value } => {
            let key_sort = translate_sort(key)?;
            let val_sort = translate_sort(value)?;
            Ok(Sort::array(key_sort, val_sort))
        }
        SortMeta::FloatingPoint { exponent_bits, significand_bits } => {
            if *exponent_bits == 0 || *significand_bits == 0 {
                return Err(
                    "FloatingPoint exponent_bits and significand_bits must be > 0".to_string()
                );
            }
            Ok(Sort::fp(*exponent_bits, *significand_bits))
        }
        SortMeta::Array { index, element } => {
            let index_sort = translate_sort(index)?;
            let element_sort = translate_sort(element)?;
            Ok(Sort::array(index_sort, element_sort))
        }
        _ => Err(format!("unsupported SortMeta variant: {meta:?}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bool_maps_to_ay_bool() {
        let sort = translate_sort(&SortMeta::Bool).unwrap();
        assert!(sort.is_bool());
    }

    #[test]
    fn bv32_maps_to_ay_bitvec_32() {
        let sort = translate_sort(&SortMeta::BitVector { width: 32, signed: true }).unwrap();
        assert!(sort.is_bitvec());
        assert_eq!(sort.bitvec_width(), Some(32));
    }

    #[test]
    fn bv0_rejected() {
        let result = translate_sort(&SortMeta::BitVector { width: 0, signed: false });
        assert!(result.is_err());
    }

    #[test]
    fn seq_maps_to_ay_seq() {
        let sort = translate_sort(&SortMeta::Seq {
            elem: Box::new(SortMeta::BitVector { width: 64, signed: false }),
        })
        .unwrap();
        assert!(sort.seq_element().is_some());
    }

    #[test]
    fn set_maps_to_ay_array_bool() {
        let sort = translate_sort(&SortMeta::Set {
            elem: Box::new(SortMeta::BitVector { width: 8, signed: false }),
        })
        .unwrap();
        assert!(sort.is_array());
    }

    #[test]
    fn map_maps_to_ay_array() {
        let sort = translate_sort(&SortMeta::Map {
            key: Box::new(SortMeta::BitVector { width: 64, signed: false }),
            value: Box::new(SortMeta::Bool),
        })
        .unwrap();
        assert!(sort.is_array());
    }

    #[test]
    fn floating_point_maps_to_ay_fp() {
        let sort =
            translate_sort(&SortMeta::FloatingPoint { exponent_bits: 8, significand_bits: 24 })
                .unwrap();
        assert!(sort.is_floating_point());
        assert_eq!(sort.fp_exponent_bits(), Some(8));
        assert_eq!(sort.fp_significand_bits(), Some(24));
    }

    #[test]
    fn array_maps_to_ay_array() {
        let sort = translate_sort(&SortMeta::Array {
            index: Box::new(SortMeta::BitVector { width: 64, signed: false }),
            element: Box::new(SortMeta::BitVector { width: 32, signed: false }),
        })
        .unwrap();
        assert!(sort.is_array());
    }
}
