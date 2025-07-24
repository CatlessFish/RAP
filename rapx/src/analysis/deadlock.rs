pub mod types;
pub mod isr_analyzer;
pub mod lock_collector;
pub mod lockset_analyzer;

use rustc_middle::ty::TyCtxt;
use crate::rap_info;
use crate::analysis::core::call_graph::CallGraph;
use crate::analysis::deadlock::types::{lock::*, interrupt::*};
use crate::analysis::deadlock::isr_analyzer::IsrAnalyzer;
use crate::analysis::deadlock::lock_collector::LockCollector;
use crate::analysis::deadlock::lockset_analyzer::LockSetAnalyzer;

pub struct DeadlockDetection<'tcx, 'a> {
    pub tcx: TyCtxt<'tcx>,
    pub callgraph: CallGraph<'tcx>,
    pub target_lock_types: Vec<&'a str>,
    pub target_lockguard_types: Vec<&'a str>,
    pub target_isr_entries: Vec<&'a str>,
    pub target_interrupt_apis: Vec<(&'a str, InterruptApiType)>,

    program_lock_info: ProgramLockInfo,
    program_lock_set: ProgramLockSet,
    program_isr_info: ProgramIsrInfo,
}


impl<'tcx, 'a> DeadlockDetection<'tcx, 'a> where 'tcx: 'a {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            callgraph: CallGraph::new(tcx),
            target_lock_types: vec![
                // "sync::mutex::Mutex",
                // "sync::rwlock::RwLock",
                // "sync::rwmutex::RwMutex",
                "sync::spin::SpinLock",
            ],
            target_lockguard_types: vec![
                "sync::spin::SpinLockGuard_",
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

            program_lock_info: ProgramLockInfo::new(),
            program_lock_set: ProgramLockSet::new(),
            program_isr_info: ProgramIsrInfo::new(),
        }
    }

    /// Start Interrupt-Aware Deadlock Detection
    /// Note: the detection is currently crate-local
    pub fn start (&'a mut self) {
        rap_info!("Executing Deadlock Detection");

        // Steps:
        // Dependencies
        self.callgraph.set_quiet(true);
        self.callgraph.start();

        // 1. Identify ISRs and Analysis InterruptSet
        let mut isr_analyzer = IsrAnalyzer::new(
            self.tcx, 
            &self.callgraph,
            &self.target_isr_entries,
            &self.target_interrupt_apis
        );
        self.program_isr_info = isr_analyzer.run();
        // self.isr_analysis();
        // self.print_isr_analysis_result();

        // TODO: consider alias
        // 2. Collect Locks and LockGuards
        let mut lock_collector = LockCollector::new(
            self.tcx,
            &self.target_lock_types,
            &self.target_lockguard_types,
        );
        self.program_lock_info = lock_collector.collect();

        // 3. Analysis LockSet
        let mut lockset_analyzer = LockSetAnalyzer::new(
            self.tcx,
            &self.callgraph,
            &self.program_lock_info.lockmap,
        );
        self.program_lock_set = lockset_analyzer.run();
        lockset_analyzer.print_result();
    }
}

// TODO:
// 1. test? correctness?