pub mod deadlock_reporter;
pub mod isr_analyzer;
pub mod ldg_constructor;
pub mod lock_collector;
pub mod lockset_analyzer;
pub mod types;

use crate::analysis::core::callgraph::default::{CallGraphAnalyzer, CallGraphInfo};
use crate::analysis::deadlock::deadlock_reporter::DeadlockReporter;
use crate::analysis::deadlock::isr_analyzer::IsrAnalyzer;
use crate::analysis::deadlock::ldg_constructor::LDGConstructor;
use crate::analysis::deadlock::lock_collector::LockCollector;
use crate::analysis::deadlock::lockset_analyzer::LockSetAnalyzer;
use crate::analysis::deadlock::types::{interrupt::*, lock::*, LockDependencyGraph};
use crate::rap_info;
use rustc_middle::ty::TyCtxt;

pub struct DeadlockDetector<'tcx, 'a> {
    pub tcx: TyCtxt<'tcx>,
    pub callgraph: CallGraphInfo<'tcx>,
    pub target_lock_types: Vec<&'a str>,
    pub target_lockguard_types: Vec<&'a str>,
    pub target_isr_entries: Vec<&'a str>,
    pub target_interrupt_apis: Vec<(&'a str, InterruptApiType)>,

    program_lock_info: ProgramLockInfo,
    program_lock_set: ProgramLockSet,
    program_isr_info: ProgramIsrInfo,
    lock_dependency_graph: LockDependencyGraph,
}

impl<'tcx, 'a> DeadlockDetector<'tcx, 'a>
where
    'tcx: 'a,
{
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            callgraph: CallGraphInfo::new(),
            target_lock_types: vec![
                "sync::spin::SpinLock",
                // "sync::mutex::Mutex",
                // "sync::rwlock::RwLock",
                // "sync::rwmutex::RwMutex",
            ],
            target_lockguard_types: vec![
                "sync::spin::SpinLockGuard_",
                // "sync::spin::MutexGuard_",
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
            lock_dependency_graph: LockDependencyGraph::new(),
        }
    }

    /// Start Interrupt-Aware Deadlock Detection
    /// Note: the detection is currently crate-local
    pub fn run(&'a mut self) {
        rap_info!("Executing Deadlock Detection");

        // Steps:
        // Dependencies
        let mut callgraph_analyzer = CallGraphAnalyzer::new(self.tcx);
        callgraph_analyzer.start();
        self.callgraph = callgraph_analyzer.graph;

        // 1. Identify ISRs and Analysis InterruptSet
        let mut isr_analyzer = IsrAnalyzer::new(
            self.tcx,
            &self.callgraph,
            &self.target_isr_entries,
            &self.target_interrupt_apis,
        );
        self.program_isr_info = isr_analyzer.run();
        // isr_analyzer.print_result();

        // 2. Collect Locks and LockGuards
        let mut lock_collector = LockCollector::new(
            self.tcx,
            &self.target_lock_types,
            &self.target_lockguard_types,
        );
        self.program_lock_info = lock_collector.collect();
        // lock_collector.print_result();

        // 3. Analysis LockSet
        let mut lockset_analyzer = LockSetAnalyzer::new(self.tcx, &self.program_lock_info.lockmap);
        self.program_lock_set = lockset_analyzer.run();
        // lockset_analyzer.print_result();

        // 4. Construct Lock Dependency Graph
        let mut ldg_constructor =
            LDGConstructor::new(self.tcx, &self.program_lock_set, &self.program_isr_info);
        ldg_constructor.run();
        ldg_constructor.print_result();
        self.lock_dependency_graph = ldg_constructor.into_graph();

        // 5. Detect cycles on LDG
        let mut lock_reporter = DeadlockReporter::new(self.tcx, &self.lock_dependency_graph);
        lock_reporter.run();
    }
}

// TODO:
// 1. test? correctness?
