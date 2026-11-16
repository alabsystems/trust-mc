// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Complete input validity and modeled-type admission shared by the direct diagnostic BMC and CHC lanes.

use trust_ir::Module;
use trust_ir::value::FuncId;
use trust_mc_core::bmc::BmcVc;
use trust_mc_core::ident::PropertyId;
use trust_mc_core::violation::{PropertyKind, Violation};

use crate::translate::{TranslateOptions, query_for_options, translate_valid_function};

/// One complete canonical validation of one immutably borrowed module.
/// Neither the diagnostic nor the translated VCs grants proof authority.
pub(crate) struct ModuleInput<'module> {
    module: &'module Module,
    refusal: Option<String>,
}

impl<'module> ModuleInput<'module> {
    pub(crate) fn new(module: &'module Module) -> Self {
        let errors = trust_ir_build::validate_module(module);
        let refusal = (!errors.is_empty()).then(|| {
            let detail =
                errors.iter().take(8).map(ToString::to_string).collect::<Vec<_>>().join("; ");
            format!(
                "invalid trust_ir module `{}` ({} validation errors): {detail}",
                module.name,
                errors.len()
            )
        });
        // Allocation-only Storage is valid IR geometry, but this consumer's
        // Alloca model requires initialized array elements. Nominal FnItem
        // singletons likewise have no SMT carrier in either lane. Refuse the entire
        // module before any function, array or SSA symbol is translated. Scan
        // every declared type, including unused rows and pointer pointees;
        // unsupported input must not become a vacuous empty-success batch.
        let refusal = refusal.or_else(|| {
            value_sort_refusal(module).map(|reason| {
                format!("unsupported trust_ir module `{}`: {}", module.name, reason.message())
            })
        });
        // The tensor region (trust-ir v67-v70) has no SMT value carrier in
        // either lane (`crate::tensor_region`). Refuse the entire module,
        // naming every construct it stores, before any symbol is translated,
        // exactly as for Storage above: an unused tensor row, signature or blob
        // must not become a vacuous empty-success batch either.
        let refusal = refusal.or_else(|| {
            let constructs = crate::tensor_region::tensor_region_constructs(module);
            (!constructs.is_empty()).then(|| {
                format!(
                    "unsupported trust_ir module `{}`: {}",
                    module.name,
                    crate::tensor_region::tensor_region_refusal_message(&constructs)
                )
            })
        });
        Self { module, refusal }
    }

    pub(crate) fn module(&self) -> &'module Module {
        self.module
    }

    /// Module-level input invalidity, separate from instruction diagnostics.
    pub(crate) fn refusal_reason(&self) -> Option<&str> {
        self.refusal.as_deref()
    }

    /// Invalidity is charged independently of instruction reachability.
    /// There is no invented Function, FuncId, source symbol or location.
    fn refusal_vc(&self, options: &TranslateOptions) -> Option<BmcVc> {
        let reason = self.refusal.as_ref()?;
        let property = PropertyId::with_description(0, reason.clone());
        Some(BmcVc {
            decls: Vec::new(),
            constraints: Vec::new(),
            violations: vec![
                Violation::new(property, PropertyKind::Other, ay_bindings::Expr::true_())
                    .with_message(reason),
            ],
            query: query_for_options(options),
            model_queries: Vec::new(),
        })
    }

    pub(crate) fn all(&self, options: &TranslateOptions) -> Vec<BmcVc> {
        if let Some(refusal) = self.refusal_vc(options) {
            // An invalid empty module must not become an empty-success batch.
            // This is a MODULE input refusal, not a fictitious function VC.
            return vec![refusal];
        }
        self.module
            .functions
            .iter()
            .map(|function| translate_valid_function(function, self.module, options))
            .collect()
    }

    pub(crate) fn function(&self, id: FuncId, options: &TranslateOptions) -> Option<BmcVc> {
        // A missing selection remains None, which is a refusal to translate,
        // never evidence that the input or an absent function was verified.
        let function = self.module.function_by_id(id)?;
        Some(
            self.refusal_vc(options)
                .unwrap_or_else(|| translate_valid_function(function, self.module, options)),
        )
    }
}

/// Refuse types with no value carrier before allocating any SMT symbol.
pub(crate) fn value_sort_refusal(module: &Module) -> Option<crate::translate::UnsupportedSort> {
    let mut unsupported = None;
    module.visit_types(|ty| {
        if matches!(ty, trust_ir::Ty::Storage(_)) {
            unsupported = Some(crate::translate::UnsupportedSort::AddressableStorage);
        } else if unsupported.is_none() && matches!(ty, trust_ir::Ty::FnItem(_)) {
            unsupported = Some(crate::translate::UnsupportedSort::FunctionItem);
        }
    });
    unsupported
}
