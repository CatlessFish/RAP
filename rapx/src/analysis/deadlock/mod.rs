pub mod cycle_detector;
pub mod deadlock_reporter;
pub mod isr_analyzer;
pub mod ldg_constructor;
pub mod lock_collector;
pub mod lockset_analyzer;
pub mod tag_parser;
pub mod types;

use crate::analysis::callgraph::default::{CallGraph, CallGraphAnalyzer};
use crate::analysis::deadlock::deadlock_reporter::DeadlockReporter;
use crate::analysis::deadlock::isr_analyzer::IsrAnalyzer;
use crate::analysis::deadlock::ldg_constructor::LDGConstructor;
use crate::analysis::deadlock::lock_collector::LockCollector;
use crate::analysis::deadlock::lockset_analyzer::LockSetAnalyzer;
use crate::analysis::deadlock::tag_parser::{LockTagItem, TagParser};
use crate::analysis::deadlock::types::{LockDependencyGraph, interrupt::*, lock::*};
use rustc_middle::ty::TyCtxt;

pub struct DeadlockDetector<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub callgraph: CallGraph<'tcx>,
    // pub target_isr_entries: Vec<&'a str>,
    // pub target_interrupt_apis: Vec<(&'a str, InterruptApiType)>,
    parsed_tags: Vec<LockTagItem>,
    program_lock_info: ProgramLockInfo,
    program_lock_set: ProgramLockSet,
    program_isr_info: ProgramIsrInfo,
    lock_dependency_graph: LockDependencyGraph,
}

impl<'tcx> DeadlockDetector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            callgraph: CallGraph::new(tcx),
            // target_isr_entries: vec![
            //     "arch::x86::iommu::fault::iommu_page_fault_handler",
            //     "arch::x86::kernel::tsc::determine_tsc_freq_via_pit::pit_callback",
            //     "arch::x86::serial::handle_serial_input",
            //     "arch::x86::timer::apic::init_periodic_mode::pit_callback",
            //     "arch::x86::timer::timer_callback",
            //     "smp::do_inter_processor_call",
            //     "mm::tlb::do_remote_flush", // This is added manually
            // ],
            // target_interrupt_apis: vec![
            //     ("arch::x86::irq::enable_local", InterruptApiType::Enable),
            //     ("arch::x86::irq::disable_local", InterruptApiType::Disable),
            // ],
            parsed_tags: vec![],
            program_lock_info: ProgramLockInfo::new(),
            program_lock_set: ProgramLockSet::new(),
            program_isr_info: ProgramIsrInfo::new(),
            lock_dependency_graph: LockDependencyGraph::new(),
        }
    }

    /// Start Interrupt-Aware Deadlock Detection
    /// Note: the detection is currently crate-local
    pub fn run_with_tag_io(&mut self, save_tags: Option<&str>, load_tags: Option<&str>) {
        rap_info!("Executing Deadlock Detection");

        rap_info!("Deadlock phase: build callgraph");
        let mut callgraph_analyzer = CallGraphAnalyzer::new(self.tcx);
        callgraph_analyzer.start();
        self.callgraph = callgraph_analyzer.graph;

        rap_info!("Deadlock phase: parse tags");
        let tag_parser = TagParser::new(self.tcx);
        let tags = tag_parser.load_analyze_save(load_tags, save_tags);
        self.parsed_tags = tags;

        rap_info!("Deadlock phase: collect lock information");
        let mut lock_collector = LockCollector::new(self.tcx, &self.parsed_tags);
        self.program_lock_info = lock_collector.collect();
        lock_collector.print_result();
        if !self.program_lock_info.missing_lock_op_apis.is_empty() {
            rap_warn!(
                "Deadlock phase: {} guard-returning APIs are still analyzed via legacy fallback because they are missing LockOp tags",
                self.program_lock_info.missing_lock_op_apis.len()
            );
        }

        rap_info!("Deadlock phase: analyze locksets");
        let mut lockset_analyzer = LockSetAnalyzer::new(self.tcx, &self.program_lock_info.lockmap);
        self.program_lock_set = lockset_analyzer.run();
        // lockset_analyzer.print_result();

        rap_info!("Deadlock phase: analyze interrupt state");
        let mut isr_analyzer = IsrAnalyzer::new(
            self.tcx,
            &self.callgraph,
            &self.parsed_tags,
            &self.program_lock_info,
        );
        self.program_isr_info = isr_analyzer.run();
        // isr_analyzer.print_result();

        rap_info!("Deadlock phase: construct dependency graph");
        let mut ldg_constructor =
            LDGConstructor::new(self.tcx, &self.program_lock_set, &self.program_isr_info);
        ldg_constructor.run();
        // ldg_constructor.print_result();
        self.lock_dependency_graph = ldg_constructor.into_graph();

        rap_info!("Deadlock phase: report cycles");
        let mut lock_reporter = DeadlockReporter::new(self.tcx, &self.lock_dependency_graph);
        lock_reporter.run();
    }
}

// TODO:
// 1. test? correctness?
