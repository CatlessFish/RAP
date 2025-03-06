pub mod collect_isr;
pub mod deadlock;
pub mod lockset_analysis;

use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;

use crate::analysis::core::alias::mop::MopAlias;
use crate::analysis::core::alias::FnMap;
use crate::analysis::core::heap_item::{AdtOwner, TypeAnalysis};
use crate::analysis::rcanary::rCanary;
use crate::{rap_info, rap_debug};
use crate::utils::source::get_fn_name;

pub struct DeadlockDetection<'tcx> {
    pub tcx: TyCtxt<'tcx>,
}

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
    pub fn start(&self) {
        rap_info!("Executing Deadlock Detection");

        // Steps:
        // 1. Identify ISRs
        self.collect_isr();

        // TODO: consider alias
        // 2. Analysis LockSet
        self.lockset_analysis();

        // 3. Analysis InterruptSet

        // 3. Construct Lock Graph
        // 4. Detect Cycles on Lock Graph
    }
}

