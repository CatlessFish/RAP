pub mod contracts;
pub mod inter_record;
pub mod matcher;
pub mod visitor;

use crate::{
    analysis::unsafety_isolation::{
        hir_visitor::{ContainsUnsafe, RelatedFnCollector},
        UnsafetyIsolationCheck,
    },
    rap_info, rap_warn,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Operand, TerminatorKind};
use rustc_middle::ty;
use rustc_middle::ty::TyCtxt;
use std::collections::HashSet;
use visitor::CheckResult;
// use visitor::{BodyVisitor, CheckResult};

use super::unsafety_isolation::generate_dot::UigUnit;

pub struct SenryxCheck<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub threshhold: usize,
}

impl<'tcx> SenryxCheck<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, threshhold: usize) -> Self {
        Self { tcx, threshhold }
    }

    pub fn start(&self) {
        let related_items = RelatedFnCollector::collect(self.tcx); // find all func
        let hir_map = self.tcx.hir();
        for (_, &ref vec) in &related_items {
            for (body_id, _span) in vec {
                let (function_unsafe, block_unsafe) =
                    ContainsUnsafe::contains_unsafe(self.tcx, *body_id);
                let def_id = hir_map.body_owner_def_id(*body_id).to_def_id();
                if block_unsafe {
                    self.check_soundness(def_id);
                }
                if function_unsafe {
                    self.annotate_safety(def_id);
                }
            }
        }
    }

    pub fn check_soundness(&self, def_id: DefId) {
        let _check_results = self.body_visit_and_check(def_id);
        // if check_results.len() > 0 {
        //     Self::show_check_results(def_id, check_results);
        // }
    }

    pub fn annotate_safety(&self, def_id: DefId) {
        let annotation_results = self.get_annotation(def_id);
        if annotation_results.len() == 0 {
            return;
        }
        Self::show_annotate_results(self.tcx, def_id, annotation_results);
    }

    // pub fn body_visit_and_check(&self, def_id: DefId) -> Vec<CheckResult> {
    //     let mut uig_checker = UnsafetyIsolationCheck::new(self.tcx);
    //     let func_type = UnsafetyIsolationCheck::get_type(self.tcx,def_id);
    //     let mut body_visitor = BodyVisitor::new(self.tcx, def_id, 0);
    //     if func_type == 1 {
    //         let func_cons = uig_checker.search_constructor(def_id);
    //         for func_con in func_cons {
    //             let mut cons_body_visitor = BodyVisitor::new(self.tcx, func_con, 0);
    //             cons_body_visitor.path_forward_check();
    //             // TODO: cache fields' states
    //             // TODO: update method body's states
    //             // analyze body's states
    //             body_visitor.path_forward_check();
    //         }
    //     } else {
    //         body_visitor.path_forward_check();
    //     }
    //     return body_visitor.check_results;
    // }

    pub fn body_visit_and_check(&self, def_id: DefId) {
        let mut uig_checker = UnsafetyIsolationCheck::new(self.tcx);
        let func_type = UnsafetyIsolationCheck::get_type(self.tcx, def_id);
        if func_type == 1 && self.get_annotation(def_id).len() > 0 {
            let func_cons = uig_checker.search_constructor(def_id);
            for func_con in func_cons {
                if UnsafetyIsolationCheck::check_safety(self.tcx, func_con) {
                    Self::show_annotate_results(self.tcx, func_con, self.get_annotation(def_id));
                    // uphold safety to unsafe constructor
                }
            }
        }
    }

    pub fn get_annotation(&self, def_id: DefId) -> HashSet<String> {
        let mut results = HashSet::new();
        if !self.tcx.is_mir_available(def_id) {
            return results;
        }
        let body = self.tcx.optimized_mir(def_id);
        let basicblocks = &body.basic_blocks;
        for i in 0..basicblocks.len() {
            let iter = BasicBlock::from(i);
            let terminator = basicblocks[iter].terminator.clone().unwrap();
            match terminator.kind {
                TerminatorKind::Call {
                    ref func,
                    args: _,
                    destination: _,
                    target: _,
                    unwind: _,
                    call_source: _,
                    fn_span: _,
                } => match func {
                    Operand::Constant(c) => match c.ty().kind() {
                        ty::FnDef(id, ..) => {
                            if UigUnit::get_sp(self.tcx, *id).len() > 0 {
                                results.extend(UigUnit::get_sp(self.tcx, *id));
                            } else {
                                results.extend(self.get_annotation(*id));
                            }
                        }
                        _ => {}
                    },
                    _ => {}
                },
                _ => {}
            }
        }
        results
    }

    pub fn show_check_results(tcx: TyCtxt<'tcx>, def_id: DefId, check_results: Vec<CheckResult>) {
        rap_info!(
            "--------In safe function {:?}---------",
            UigUnit::get_cleaned_def_path_name(tcx, def_id)
        );
        for check_result in check_results {
            rap_info!(
                "  Unsafe api {:?}: {} passed, {} failed!",
                check_result.func_name,
                check_result.passed_contracts.len(),
                check_result.failed_contracts.len()
            );
            for failed_contract in check_result.failed_contracts {
                rap_warn!("      Contract failed: {:?}", failed_contract);
            }
        }
    }

    pub fn show_annotate_results(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        annotation_results: HashSet<String>,
    ) {
        rap_info!(
            "--------In unsafe function {:?}---------",
            UigUnit::get_cleaned_def_path_name(tcx, def_id)
        );
        rap_warn!("Lack safety annotations: {:?}.", annotation_results);
    }
}
