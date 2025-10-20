pub mod call_graph_helper;
pub mod call_graph_visitor;

use std::collections::HashSet;

use call_graph_helper::CallGraphInfo;
use call_graph_visitor::CallGraphVisitor;
use rustc_hir::def::DefKind;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::InstanceKind;

use crate::rap_info;
pub struct CallGraph<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub graph: CallGraphInfo,
    pub quiet: bool,
}

impl<'tcx> CallGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx: tcx,
            graph: CallGraphInfo::new(),
            quiet: false,
        }
    }

    pub fn set_quiet(&mut self, quiet: bool) {
        self.quiet = quiet;
    }

    pub fn start(&mut self) {
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                let def_kind = self.tcx.def_kind(def_id);
                let body: &Body = match def_kind {
                    DefKind::Fn | DefKind::AssocFn => &self.tcx.instance_mir(InstanceKind::Item(def_id)),
                    // using optimizied_mir() may cause ICE: do not use `optimized_mir` for constants
                    // see https://github.com/rust-lang/rust/issues/81918

                    // Fallbacks for const types
                    DefKind::Const 
                    | DefKind::Static { .. }
                    | DefKind::AssocConst
                    | DefKind::InlineConst
                    | DefKind::AnonConst => {
                        // Compile Time Function Evaluation
                        &self.tcx.mir_for_ctfe(def_id)
                    }

                    // Skip other type
                    _ => continue,
                };


                let mut call_graph_visitor =
                    CallGraphVisitor::new(self.tcx, def_id.into(), body, &mut self.graph);
                call_graph_visitor.visit();
            }
        }
        if !self.quiet {
            self.graph.print_call_graph();
        }

        // DEBUG
        for (func_name, index) in &self.graph.node_registry {
            rap_info!("{} | {}", index, func_name);
        }
        for (caller, callees) in &self.graph.function_calls {
           for callee in callees {
                rap_info!("{} -> {}", caller, callee);
           }
        }
    }

    pub fn get_callee_def_path(&self, def_path: String) -> Option<HashSet<String>> {
        self.graph.get_callees_path(&def_path)
    }
}
