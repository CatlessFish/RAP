pub mod types;
pub mod isr_analysis;
// pub mod lockset_analysis;
pub mod lockset;
pub mod function_summary;
pub mod ilg_construction;
pub mod deadlock_detection;

use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};
use rustc_middle::mir::{BasicBlock, TerminatorKind};
use rustc_hir::def_id::DefId;
use crate::rap_info;
use crate::analysis::core::call_graph::CallGraph;
use crate::analysis::deadlock::types::*;
use crate::analysis::deadlock::lockset::LocksetAnalysis;
pub struct DeadlockDetection<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub call_graph: CallGraph<'tcx>,
    pub target_lock_types: Vec<&'tcx str>,
    pub target_lock_apis: Vec<&'tcx str>,
    pub target_isr_entries: Vec<&'tcx str>,
    pub target_interrupt_apis: Vec<(&'tcx str, InterruptApiType)>,
    pub enable_interrupt_apis: Vec<DefId>,
    pub disable_interrupt_apis: Vec<DefId>,

    program_lock_info: ProgramLockInfo,
    program_isr_info: ProgramIsrInfo,
    program_func_summary: ProgramFuncSummary,
    interrupt_lock_graph: ILG,
}


impl<'tcx> DeadlockDetection<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            call_graph: CallGraph::new(tcx),
            target_lock_types: vec![
                "sync::mutex::Mutex",
                "sync::rwlock::RwLock",
                "sync::rwmutex::RwMutex",
                "sync::spin::SpinLock",
            ],
            target_lock_apis: vec![
                "sync::spin::SpinLock::<T, G>::lock",
                "sync::spin::SpinLock::<T, G>::lock_arc",
                "sync::rwlock::RwLock::<T>::read",
                "sync::rwlock::RwLock::<T>::read_arc",
                "sync::rwlock::RwLock::<T>::write",
                "sync::rwlock::RwLock::<T>::write_arc",
                "sync::mutex::Mutex::<T>::lock",
                "sync::mutex::Mutex::<T>::lock_arc",
                "sync::rwmutex::RwMutex::<T>::read",
                "sync::rwmutex::RwMutex::<T>::write",
                "sync::rwmutex::RwMutex::<T>::upread",
            ],
            target_isr_entries: vec![
                "arch::x86::iommu::fault::iommu_page_fault_handler",
                "arch::x86::kernel::tsc::determine_tsc_freq_via_pit::pit_callback",
                "arch::x86::serial::handle_serial_input",
                "arch::x86::timer::apic::init_periodic_mode::pit_callback",
                "arch::x86::timer::timer_callback",
                "smp::do_inter_processor_call",
                "mm::tlb::do_remote_flush", // This is added manually
            ],
            target_interrupt_apis: vec![
                ("arch::x86::irq::enable_local", InterruptApiType::Enable),
                ("arch::x86::irq::disable_local", InterruptApiType::Disable),
            ],

            enable_interrupt_apis: Vec::new(),
            disable_interrupt_apis: Vec::new(),

            program_lock_info: ProgramLockInfo::new(),
            program_isr_info: ProgramIsrInfo::new(),
            program_func_summary: ProgramFuncSummary::new(),
            interrupt_lock_graph: ILG::new(),
        }
    }

    /// Start Interrupt-Aware Deadlock Detection
    /// Note: the detection is currently crate-local
    pub fn start(&mut self) {
        rap_info!("Executing Deadlock Detection");

        // Steps:
        // Dependencies
        self.call_graph.set_quiet(true);
        self.call_graph.start();

        // 1. Identify ISRs and Analysis InterruptSet
        self.isr_analysis();
        self.print_isr_analysis_result();

        // TODO: consider alias
        // 2. Analysis LockSet
        let mut lockset = LocksetAnalysis::new(
            self.tcx,
            // &self.target_lock_types,
            // &self.target_lock_apis,
        );
        lockset.run();

        // 3. Computes Function Summary
        // self.function_summary();
        // self.print_function_summary_result();

        // 4. Construct Lock Graph
        // self.construct_ilg();
        // self.print_ilg_result();

        // 5. Detect Cycles on Lock Graph
        // self.detect_deadlock();
    }
}

// TODO:
// 1. test? correctness?