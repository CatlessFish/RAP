pub mod types;
pub mod isr_analysis;
pub mod lockset_analysis;
pub mod function_summary;
pub mod ilg_construction;

use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};
use rustc_middle::mir::{BasicBlock, TerminatorKind};
use crate::{rap_info, rap_debug};
use crate::analysis::core::call_graph::CallGraph;
use crate::analysis::deadlock::types::*;
pub struct DeadlockDetection<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub call_graph: CallGraph<'tcx>,
    pub target_lock_types: Vec<&'tcx str>,
    pub target_lock_apis: Vec<(&'tcx str, &'tcx str)>,
    pub target_isr_entries: Vec<&'tcx str>,
    pub target_interrupt_apis: Vec<(&'tcx str, InterruptApiType)>,

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
            target_isr_entries: vec![
                "arch::x86::iommu::fault::iommu_page_fault_handler",
                "arch::x86::kernel::tsc::determine_tsc_freq_via_pit::pit_callback",
                "arch::x86::serial::handle_serial_input",
                "arch::x86::timer::apic::init_periodic_mode::pit_callback",
                "arch::x86::timer::timer_callback",
                "smp::do_inter_processor_call",
            ],
            target_interrupt_apis: vec![
                ("arch::x86::irq::enable_local", InterruptApiType::Enable),
                ("arch::x86::irq::disable_local", InterruptApiType::Disable),
            ],
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
        self.lockset_analysis();
        self.print_lockset_analysis_results();

        // 3. Computes Function Summary
        self.function_summary();
        self.print_function_summary_result();

        // 4. Construct Lock Graph
        self.construct_ilg();
        self.print_ilg_result();

        // 5. Detect Cycles on Lock Graph
    }
}

// TODO:
// 1. test? correctness?