use std::collections::{HashMap, HashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, BasicBlock, Location, Statement, Terminator, TerminatorEdges, TerminatorKind, CallReturnPlaces};
use rustc_middle::ty::TyCtxt;

extern crate rustc_mir_dataflow;
use rustc_mir_dataflow::{ Analysis, AnalysisDomain, JoinSemiLattice };

use crate::analysis::deadlock::types::interrupt::*;
use crate::analysis::core::call_graph::CallGraph;
use crate::{rap_info, rap_debug};

impl JoinSemiLattice for IrqState {
    fn join(&mut self, other: &Self) -> bool {
        let old = self.clone();
        *self = self.union(other);
        *self != old
    }
}

struct FuncIsrAnalyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,

    /// The `DefId`s of Enable-Interrupt Apis
    enable_interrupt_apis: Vec<DefId>,

    /// The `DefId`s of Disable-Interrupt Apis
    disable_interrupt_apis: Vec<DefId>,

    /// Ref of a global cache recording the result of analyzed functions
    analyzed_functions: &'a HashMap<DefId, FuncIrqInfo>,
}

impl<'tcx, 'a> FuncIsrAnalyzer<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        enable_interrupt_apis: Vec<DefId>,
        disable_interrupt_apis: Vec<DefId>,
        analyzed_functions: &'a HashMap<DefId, FuncIrqInfo>,
    ) -> Self {
        FuncIsrAnalyzer {
            tcx,
            enable_interrupt_apis: enable_interrupt_apis,
            disable_interrupt_apis: disable_interrupt_apis,
            analyzed_functions: analyzed_functions,
        }
    }
}

impl<'tcx, 'a> AnalysisDomain<'tcx> for FuncIsrAnalyzer<'tcx, 'a> {
    type Domain = IrqState;

    const NAME: &'static str = "ISRAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> <Self as AnalysisDomain<'tcx>>::Domain {
        IrqState::new()
    }

    fn initialize_start_block(
        &self, 
        _body: &Body<'tcx>, 
        state: &mut <Self as AnalysisDomain<'tcx>>::Domain
    ) {
        *state = IrqState::new()
    }
}

impl<'tcx, 'a> Analysis<'tcx> for FuncIsrAnalyzer<'tcx, 'a> {
    fn apply_statement_effect(
            &mut self,
            _state: &mut <Self as AnalysisDomain<'tcx>>::Domain,
            _statement: &Statement<'tcx>,
            _location: Location,
        ) {
        // We don't care about normal statements, since they don't affect Irq state.
    }

    fn apply_terminator_effect<'air>(
            &mut self,
            _state: &mut <Self as AnalysisDomain<'tcx>>::Domain,
            terminator: &'air Terminator<'tcx>,
            _location: Location,
        ) -> TerminatorEdges<'air, 'tcx> {
            if let TerminatorKind::Call { func, .. } = &terminator.kind {
                // Handle call return effects
                if let Some(callee_def_id) = func.const_fn_def() {
                    // Check if it's an interrupt API
                    let mut found_api = false;
                    if self.enable_interrupt_apis.contains(&callee_def_id.0) {
                        found_api = true;
                        // Update current state
                        *_state = IrqState::MayBeEnabled;
                    }

                    if self.disable_interrupt_apis.contains(&callee_def_id.0) {
                        found_api = true;
                        // Update current state
                        *_state = IrqState::MustBeDisabled;
                    }

                    // If not an interrupt API, check if it's a regular function call
                    if !found_api && self.tcx.is_mir_available(callee_def_id.0) {
                        // Merge the exit interrupt set of the called function
                        if let Some(callee_info) = self.analyzed_functions.get(&callee_def_id.0) {
                            _state.join(&callee_info.exit_irq_state);
                        }
                    }
                }
            }
            terminator.edges()
        }

    fn apply_call_return_effect(
            &mut self,
            _state: &mut <Self as AnalysisDomain<'tcx>>::Domain,
            _block: BasicBlock,
            _return_places: CallReturnPlaces<'_, 'tcx>,
        ) {
        // Do nothing
    }
}

pub struct IsrAnalyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    target_isr_entries: &'a Vec<&'a str>,
    target_interrupt_apis: &'a Vec<(&'a str, InterruptApiType)>,
    enable_interrupt_apis: Vec<DefId>,
    disable_interrupt_apis: Vec<DefId>,
    program_isr_info: ProgramIsrInfo,
}

impl<'tcx, 'a> IsrAnalyzer<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        callgraph: &'a CallGraph<'tcx>,
        target_isr_entries: &'a Vec<&'a str>,
        target_interrupt_apis: &'a Vec<(&'a str, InterruptApiType)>,
    ) -> Self {
        Self {
            tcx,
            callgraph,
            target_isr_entries,
            target_interrupt_apis,
            enable_interrupt_apis: vec![],
            disable_interrupt_apis: vec![],
            program_isr_info: ProgramIsrInfo::new(),
        }
    }

    pub fn run(&mut self) -> ProgramIsrInfo {
        // Steps:
        // 1. Collect a set of ISRs
        self.collect_isr();
        
        // 2. Collect a set of interrupt APIs
        self.collect_interrupt_apis();
        
        // 3. Calculate interrupt sets for each function
        // This step is inter-procedural
        self.analyze_interrupt_set();
        
        rap_info!("Collected {} ISRs", self.program_isr_info.isr_funcs.len());
        self.program_isr_info.clone()
    }

    /// Collect the `DefIds` of `target_isr_entries` and their (recursively) callees
    fn collect_isr(&mut self) {
        let mut isr_def_ids: HashMap<String, DefId> = HashMap::new();
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            let fn_name = self.tcx.def_path_str(def_id);
            if self.target_isr_entries.contains(&fn_name.as_str()) {
                isr_def_ids.insert(fn_name.clone(), def_id);
            }
        }

        self.program_isr_info.isr_entries = isr_def_ids.values().cloned().collect();

        // Start from self.target_isr_entries,
        // traverse self.call_graph.graph to find all possible callees
        // and mark them as ISRs
        let mut isr_funcs: HashSet<DefId> = HashSet::new();
        for &isr_entry in self.target_isr_entries.iter() {
            if let Some(isr_def_id) = isr_def_ids.get(isr_entry) {
                // first, mark isr entries themselves as called by themselves
                isr_funcs.insert(isr_def_id.clone());

                // then, find all possible callees
                if let Some(callees) = self.callgraph.graph.get_callees_defid_recursive(&isr_entry.to_string()) {
                    for callee in callees {
                        isr_funcs.insert(callee);
                    }
                }
            }
        }

        for isr_func in isr_funcs.iter() {
            rap_debug!("Function {} may be a ISR function", self.tcx.def_path_str(isr_func));
        }

        self.program_isr_info.isr_funcs = isr_funcs;
    }

    /// Collect target_interrupt_apis's `DefId`
    /// into `self.enable_interrupt_apis` and `self.disable_interrupt_apis`
    fn collect_interrupt_apis(&mut self) {
        // Iterate through all functions
        for local_def_id in self.tcx.hir().body_owners() {
            // filter const mir
            // FIXME: explain this
            if let Some(_other) = self.tcx.hir().body_const_context(local_def_id) {
                continue;
            }

            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                let func_name = self.tcx.def_path_str(def_id);
                for (api_name, api_type) in self.target_interrupt_apis.iter() {
                    if func_name.contains(api_name) {
                        if *api_type == InterruptApiType::Enable {
                            self.enable_interrupt_apis.push(def_id);
                        } else if *api_type == InterruptApiType::Disable {
                            self.disable_interrupt_apis.push(def_id);
                        }
                    }
                }
            }
        }
    }

    /// The outer iteration for inter-procedurely calculate `FuncIrqInfo` for each function
    fn analyze_interrupt_set(&mut self) {
        // Track the exit interrupt sets of already analyzed functions
        let mut analyzed_functions: HashMap<DefId, FuncIrqInfo> = HashMap::new();
        // Track the recursion stack to prevent cycles
        let mut recursion_stack: HashSet<DefId> = HashSet::new();

        // Iterate through all functions
        for local_def_id in self.tcx.hir().body_owners() {
            /* filter const mir */
            if let Some(_other) = self.tcx.hir().body_const_context(local_def_id) {
                continue;
            }

            // Make sure all functions are analyzed
            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                self.analyze_function_interrupt_set(
                    def_id,
                    &mut analyzed_functions,
                    &mut recursion_stack,
                );
            }
        }

        // Save the results to program_isr_info
        for (def_id, func_info) in analyzed_functions {
            self.program_isr_info
                .func_irq_infos
                .insert(def_id, func_info);
        }
    }

    /// The inner iteration for inter-procedurely calculate `FuncIrqInfo` for a function with `func_def_id`.\
    /// If any callee hasn't been analyzed yet, recursively analyze the callee first.
    /// Maintains a recursive stack to avoid cycle.\
    /// Use `FuncISRAnalyzer` to perform fix-point iteration on a functions's CFG.
    fn analyze_function_interrupt_set(
        &self,
        func_def_id: DefId,
        analyzed_functions: &mut HashMap<DefId, FuncIrqInfo>,
        recursion_stack: &mut HashSet<DefId>,
    ) {
        // If the function has already been analyzed, return
        if let Some(_) = analyzed_functions.get(&func_def_id) {
            return;
        }

        // If we are already in the recursion stack, return, avoid infinite recursion
        if recursion_stack.contains(&func_def_id) {
            return;
        }

        // If no MIR available, return
        if !self.tcx.is_mir_available(func_def_id) {
            return;
        }

        // Add current function to the recursion stack
        recursion_stack.insert(func_def_id);

        // First collect callees, and analyze them first
        if let Some(callees) = self
            .callgraph
            .graph
            .get_callees_defid(&self.tcx.def_path_str(func_def_id))
        {
            for callee in callees {
                self.analyze_function_interrupt_set(callee, analyzed_functions, recursion_stack);
            }
        }

        // TODO: collect isr api sites

        // Analyze the function
        let body: &Body = self.tcx.optimized_mir(func_def_id);
        let mut result_cursor = FuncIsrAnalyzer::new(
            self.tcx,
            self.enable_interrupt_apis.clone(),
            self.disable_interrupt_apis.clone(),
            &analyzed_functions,
        )
        .into_engine(self.tcx, body)
        .iterate_to_fixpoint()
        .into_results_cursor(body);

        let mut post_bb_irq_states = HashMap::new();
        let mut pre_bb_irq_states = HashMap::new();
        let mut exit_irq_state = IrqState::new();
        for (bb, _) in body.basic_blocks.iter_enumerated() {
            // 1. Record `IrqState` at the START of each BB in `bb_irq_states`
            result_cursor.seek_to_block_start(bb);
            pre_bb_irq_states.insert(bb, result_cursor.get().clone());

            // 2. Record `IrqState` at the END of each BB in `bb_irq_states`
            result_cursor.seek_to_block_end(bb);
            let current_state = result_cursor.get();
            post_bb_irq_states.insert(bb, current_state.clone());

            // 3. Maintain the `exit_irq_state`.
            // If the BB's terminator is `Return`, merge its state into `exit_irq_state`
            let loc = body.terminator_loc(bb);
            let terminator = body
                .stmt_at(loc) // Either<&Statement, &Terminator>
                .right() // Right should be Terminator
                .unwrap(); // This must be Some because the `loc` is this bb's terminator
            if let TerminatorKind::Return = terminator.kind {
                // update exit_irq_state
                exit_irq_state.join(current_state);
            }
        }

        // Update `analyzed_functions`
        analyzed_functions.insert(
            func_def_id,
            FuncIrqInfo {
                def_id: func_def_id,
                exit_irq_state,
                post_bb_irq_states,
                pre_bb_irq_states,
                interrupt_enable_sites: Vec::new(),
            },
        );

        // Remove current function from the recursion stack
        recursion_stack.remove(&func_def_id);
    }

    
    pub fn print_result(&self) {
        rap_info!("==== ISR Analysis Results ====");

        for isr_func in self.program_isr_info.isr_funcs.iter() {
            rap_info!("May be ISR func: {} ", self.tcx.def_path_str(isr_func));
        }

        let mut count = 0;
        for (def_id, func_info) in self.program_isr_info.func_irq_infos.iter() {
            if func_info.exit_irq_state == IrqState::Bottom {
                continue;
            }
            rap_info!("Func: {},\t IRQ {}", self.tcx.def_path_str(def_id), func_info);
            count += 1;
        }
        rap_info!("==== ISR Analysis Results End ({} ISR entries, {} non-trivial interrupt set functions) ====", self.program_isr_info.isr_entries.len(), count);
    }
}

// TODO:
// 1. Support nested disable_local()