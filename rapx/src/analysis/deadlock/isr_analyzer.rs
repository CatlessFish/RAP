use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Location, Statement, Terminator, TerminatorEdges, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};

extern crate rustc_mir_dataflow;
use rustc_mir_dataflow::{Analysis, JoinSemiLattice};

use crate::analysis::core::callgraph::default::CallGraph;
use crate::analysis::deadlock::tag_parser::LockTagItem;
use crate::analysis::deadlock::types::{interrupt::*, lock::*};

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

    /// LockGuardInstances
    lockguards: &'a HashSet<LockGuardInstance>,

    /// Ref of a global cache recording the result of analyzed functions
    analyzed_functions: &'a HashMap<DefId, FuncIrqInfo>,
}

impl<'tcx, 'a> FuncIsrAnalyzer<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        enable_interrupt_apis: Vec<DefId>,
        disable_interrupt_apis: Vec<DefId>,
        lockguards: &'a HashSet<LockGuardInstance>,
        analyzed_functions: &'a HashMap<DefId, FuncIrqInfo>,
    ) -> Self {
        FuncIsrAnalyzer {
            tcx,
            enable_interrupt_apis,
            disable_interrupt_apis,
            lockguards,
            analyzed_functions,
        }
    }
}

impl<'tcx, 'a> Analysis<'tcx> for FuncIsrAnalyzer<'tcx, 'a> {
    type Domain = IrqState;

    const NAME: &'static str = "ISRAnalysis";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        IrqState::new()
    }

    fn initialize_start_block(
        &self,
        _body: &rustc_middle::mir::Body<'tcx>,
        state: &mut Self::Domain,
    ) {
        *state = IrqState::new()
    }

    fn apply_primary_statement_effect(
        &self,
        _state: &mut Self::Domain,
        _statement: &Statement<'tcx>,
        _location: Location,
    ) {
        // We don't care about normal statements, since they don't affect Irq state.
    }

    fn apply_primary_terminator_effect<'air>(
        &self,
        state: &mut Self::Domain,
        terminator: &'air Terminator<'tcx>,
        _location: Location,
    ) -> TerminatorEdges<'air, 'tcx> {
        match &terminator.kind {
            TerminatorKind::Call {
                func, destination, ..
            } => {
                // Handle call return effects
                if let Some(callee_def_id) = func.const_fn_def() {
                    // Check if it's an interrupt API
                    let mut found_api = false;
                    if self.enable_interrupt_apis.contains(&callee_def_id.0) {
                        found_api = true;
                        // Update current state
                        *state = IrqState::MayBeEnabled;
                    }

                    if self.disable_interrupt_apis.contains(&callee_def_id.0) {
                        found_api = true;
                        // Update current state
                        *state = IrqState::MustBeDisabled;
                    }

                    // If not an interrupt API, check if it's a regular function call
                    if !found_api && self.tcx.is_mir_available(callee_def_id.0) {
                        // Check if this is some lock() api call
                        // by checking whether the return type is a LockGuard
                        if let Some(instance) = self
                            .lockguards
                            .iter()
                            .find(|&inst| inst.local == destination.local)
                        {
                            // If the LockGuard disables local irq, we should update the state
                            match instance.guard_type {
                                LockGuardType::SpinLockLocalDisabled => {
                                    *state = IrqState::MustBeDisabled;
                                }
                                _ => {}
                            }
                        }

                        // Merge the exit interrupt set of the called function
                        if let Some(callee_info) = self.analyzed_functions.get(&callee_def_id.0) {
                            state.join(&callee_info.exit_irq_state);
                        }
                    }
                }
            }
            TerminatorKind::Drop { place, .. } => {
                // If this is a lockguard drop, maybe we should modify its state
                if let Some(instance) = self
                    .lockguards
                    .iter()
                    .find(|&inst| inst.local == place.local)
                {
                    match instance.guard_type {
                        // Dropping a DisableLocalGuard
                        // FIXME: this is inaccurate since irq is not always enabled when dropping such a lockguard
                        LockGuardType::SpinLockLocalDisabled => {
                            *state = IrqState::MayBeEnabled;
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        terminator.edges()
    }
}

pub struct IsrAnalyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    parsed_tags: &'a Vec<LockTagItem>,
    program_lock_info: &'a ProgramLockInfo,
    enable_interrupt_apis: Vec<DefId>,
    disable_interrupt_apis: Vec<DefId>,
    program_isr_info: ProgramIsrInfo,
}

impl<'tcx, 'a> IsrAnalyzer<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        callgraph: &'a CallGraph<'tcx>,
        parsed_tags: &'a Vec<LockTagItem>,
        program_lock_info: &'a ProgramLockInfo,
    ) -> Self {
        Self {
            tcx,
            callgraph,
            parsed_tags,
            program_lock_info,
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
        let mut isr_def_ids = HashSet::new();
        self.parsed_tags.iter().for_each(|tag_item| {
            if let LockTagItem::IsrEntry(did, _) = tag_item {
                isr_def_ids.insert(did.clone());
            }
        });

        self.program_isr_info.isr_entries = isr_def_ids.clone();

        // Start from self.target_isr_entries,
        // traverse self.call_graph.graph to find all possible callees
        // and mark them as ISRs
        let mut isr_funcs: HashSet<DefId> = HashSet::new();
        for isr_entry_id in isr_def_ids.iter() {
            // first, mark isr entries themselves as called by themselves
            isr_funcs.insert(isr_entry_id.clone());

            // then, find all possible callees
            for callee in self.callgraph.get_callees_recursive(*isr_entry_id) {
                isr_funcs.insert(callee);
            }
        }

        for isr_func in isr_funcs.iter() {
            rap_debug!(
                "Function {} may be a ISR function",
                self.tcx.def_path_str(isr_func)
            );
        }

        self.program_isr_info.isr_funcs = isr_funcs;
    }

    /// Collect target_interrupt_apis's `DefId`
    /// into `self.enable_interrupt_apis` and `self.disable_interrupt_apis`
    fn collect_interrupt_apis(&mut self) {
        self.parsed_tags.iter().for_each(|tag_item| {
            if let LockTagItem::IntrApi(did, is_enable, _is_nested, _) = tag_item {
                if *is_enable {
                    self.enable_interrupt_apis.push(did.clone());
                } else {
                    self.disable_interrupt_apis.push(did.clone());
                }
            }
        });
    }

    /// The outer iteration for inter-procedurely calculate `FuncIrqInfo` for each function
    fn analyze_interrupt_set(&mut self) {
        // Track the exit interrupt sets of already analyzed functions
        let mut analyzed_functions: HashMap<DefId, FuncIrqInfo> = HashMap::new();
        // Track the recursion stack to prevent cycles
        let mut recursion_stack: HashSet<DefId> = HashSet::new();

        // Iterate through all functions
        for local_def_id in self.tcx.hir_body_owners() {
            /* filter const mir */
            if let Some(_other) = self.tcx.hir_body_const_context(local_def_id) {
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
        for callee in self.callgraph.get_callees(func_def_id) {
            self.analyze_function_interrupt_set(callee, analyzed_functions, recursion_stack);
        }

        // TODO: collect isr api sites

        // Analyze the function
        let body: &Body = self.tcx.optimized_mir(func_def_id);
        let lockguards = &self.program_lock_info.lockguard_instances;
        let mut result_cursor = FuncIsrAnalyzer::new(
            self.tcx,
            self.enable_interrupt_apis.clone(),
            self.disable_interrupt_apis.clone(),
            lockguards,
            &analyzed_functions,
        )
        .iterate_to_fixpoint(self.tcx, body, None)
        .into_results_cursor(body);

        let mut pre_bb_irq_states = HashMap::new();
        let mut exit_irq_state = IrqState::new();
        for (bb, _) in body.basic_blocks.iter_enumerated() {
            // 1. Record `IrqState` at the START of each BB in `bb_irq_states`
            result_cursor.seek_to_block_start(bb);
            pre_bb_irq_states.insert(bb, result_cursor.get().clone());

            // 2. Record `IrqState` at the END of each BB in `bb_irq_states`
            result_cursor.seek_to_block_end(bb);
            let current_state = result_cursor.get();

            // 3. Maintain the `exit_irq_state`.
            // If the BB's terminator is `Return`, merge its state into `exit_irq_state`
            // TODO: Refactor and put this into `visit_terminator`
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
            rap_info!(
                "Func: {},\t IRQ {}",
                self.tcx.def_path_str(def_id),
                func_info
            );
            count += 1;
        }
        rap_info!(
            "==== ISR Analysis Results End ({} ISR entries, {} non-trivial interrupt set functions) ====",
            self.program_isr_info.isr_entries.len(),
            count
        );
    }
}

// TODO:
// 1. Support nested disable_local()
