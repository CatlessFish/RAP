pub mod collect_isr;
pub mod lockset_analysis;
pub mod lockset_analysis_old;

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
    pub target_types: Vec<&'tcx str>,
    pub target_lock_apis: Vec<(&'tcx str, &'tcx str)>,
}

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            target_types: vec![
                "sync::mutex::Mutex",
                "sync::rwlock::RwLock",
                "sync::rwmutex::RwMutex",
                "sync::spin::SpinLock",
            ],
            target_lock_apis: vec![
                ("sync::spin::SpinLock::<T, G>::lock", "write"),
                ("sync::spin::SpinLock::<T, G>::lock_arc", "write"),
                ("sync::rwlock::RwLock::<T>::read", "read"),
                ("sync::rwlock::RwLock::<T>::read_arc", "read"),
                ("sync::rwlock::RwLock::<T>::write", "write"),
                ("sync::rwlock::RwLock::<T>::write_arc", "write"),
                ("sync::mutex::Mutex::<T>::lock", "write"),
                ("sync::mutex::Mutex::<T>::lock_arc", "write"),
                ("sync::rwmutex::RwMutex::<T>::read", "read"),
                ("sync::rwmutex::RwMutex::<T>::write", "write"),
                ("sync::rwmutex::RwMutex::<T>::upread", "upgradable_read"),
            ],
        }
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

