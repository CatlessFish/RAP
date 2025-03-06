use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;


use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};
// use crate::utils::source::get_fn_name;


impl<'tcx> DeadlockDetection<'tcx> {
    pub fn collect_isr(&self) {

        // Gather function names; SHOULD INCLUDE IMPLs? (see DefKind)
        for local_def_id in self.tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            if let DefKind::Fn = self.tcx.def_kind(def_id) {
                // rap_debug!("[Fn] {}", self.tcx.def_path_str(def_id));
            }
        }

        // for local_def_id in self.tcx.iter_local_def_id() {
        //     let hir_map = self.tcx.hir();
        //     if hir_map.maybe_body_owned_by(local_def_id).is_some() {
        //         if let Some(fn_name) = get_fn_name(self.tcx, local_def_id.to_def_id()) {
        //             rap_debug!("{}", fn_name);
        //         }
        //     }
        // }

        // TODO: filter out possible ISR
        // Steps:
        // 1. Collect a set of ISRs

        // 2. Collect the enable / disable ISR APIs that we're interested in

        // 3. Build a mapping from ISR to API, to model that which API affects which ISRs
    }
}

