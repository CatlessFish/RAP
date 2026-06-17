pub mod asterinas_patch;
pub mod atomic_mode_checker;
pub mod deadlock_reporter;
pub mod isr_analyzer;
pub mod ldg_constructor;
pub mod lock_collector;
pub mod lockset_analyzer;
pub mod tag_parser;
pub mod types;

use crate::analysis::core::callgraph::default::{CallGraph, CallGraphAnalyzer};
use crate::analysis::deadlock::deadlock_reporter::DeadlockReporter;
use crate::analysis::deadlock::isr_analyzer::IsrAnalyzer;
use crate::analysis::deadlock::ldg_constructor::LDGConstructor;
use crate::analysis::deadlock::lock_collector::LockCollector;
use crate::analysis::deadlock::lockset_analyzer::LockSetAnalyzer;
use crate::analysis::deadlock::tag_parser::{LockTagItem, TagParser};
use crate::analysis::deadlock::types::{LockDependencyGraph, interrupt::*, lock::*};
use rustc_middle::ty::TyCtxt;

pub struct LockAnalysisContext<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub callgraph: CallGraph<'tcx>,
    pub parsed_tags: Vec<LockTagItem>,
    pub program_lock_info: ProgramLockInfo,
    pub program_lock_set: ProgramLockSet,
    pub program_isr_info: ProgramIsrInfo,
}

pub fn run_lock_analysis_with_tag_io<'tcx>(
    tcx: TyCtxt<'tcx>,
    save_tags: Option<&str>,
    load_tags: Option<&str>,
    analysis_name: &str,
) -> LockAnalysisContext<'tcx> {
    rap_info!("Executing {} analysis", analysis_name);

    rap_info!("{} phase: build callgraph", analysis_name);
    let mut callgraph_analyzer = CallGraphAnalyzer::new(tcx);
    callgraph_analyzer.start();
    let callgraph = callgraph_analyzer.graph;

    rap_info!("{} phase: parse tags", analysis_name);
    let tag_parser = TagParser::new(tcx);
    let parsed_tags = tag_parser.load_analyze_save(load_tags, save_tags);

    rap_info!("{} phase: collect lock information", analysis_name);
    let mut lock_collector = LockCollector::new(tcx, &parsed_tags);
    let program_lock_info = lock_collector.collect();
    lock_collector.print_result();
    if !program_lock_info.missing_lock_op_apis.is_empty() {
        rap_warn!(
            "{} phase: {} guard-returning APIs are still analyzed via legacy fallback because they are missing LockOp tags",
            analysis_name,
            program_lock_info.missing_lock_op_apis.len()
        );
    }

    rap_info!("{} phase: analyze locksets", analysis_name);
    let mut lockset_analyzer = LockSetAnalyzer::new(tcx, &program_lock_info.lockmap);
    let program_lock_set = lockset_analyzer.run();

    rap_info!("{} phase: analyze interrupt state", analysis_name);
    let mut isr_analyzer = IsrAnalyzer::new(tcx, &callgraph, &parsed_tags, &program_lock_info);
    let program_isr_info = isr_analyzer.run();

    LockAnalysisContext {
        tcx,
        callgraph,
        parsed_tags,
        program_lock_info,
        program_lock_set,
        program_isr_info,
    }
}

pub struct DeadlockDetector<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    lock_dependency_graph: LockDependencyGraph,
}

impl<'tcx> DeadlockDetector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            lock_dependency_graph: LockDependencyGraph::new(),
        }
    }

    /// Start Interrupt-Aware Deadlock Detection
    /// Note: the detection is currently crate-local
    pub fn run_with_tag_io(&mut self, save_tags: Option<&str>, load_tags: Option<&str>) {
        let lock_analysis =
            run_lock_analysis_with_tag_io(self.tcx, save_tags, load_tags, "Deadlock");

        rap_info!("Deadlock phase: construct dependency graph");
        let mut ldg_constructor = LDGConstructor::new(
            self.tcx,
            &lock_analysis.program_lock_set,
            &lock_analysis.program_isr_info,
        );
        ldg_constructor.run();
        self.lock_dependency_graph = ldg_constructor.into_graph();

        rap_info!("Deadlock phase: report cycles");
        let mut lock_reporter = DeadlockReporter::new(self.tcx, &self.lock_dependency_graph);
        lock_reporter.run();
    }
}

// TODO:
// 1. test? correctness?
