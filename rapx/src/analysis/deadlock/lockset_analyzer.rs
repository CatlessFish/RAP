use std::collections::{HashMap, VecDeque};
use rustc_hir::{BodyOwnerKind, def_id::DefId};
use rustc_middle::mir::{Body, BasicBlock, Location, TerminatorEdges, TerminatorKind, CallReturnPlaces};
use rustc_middle::ty::TyCtxt;

extern crate rustc_mir_dataflow;
use rustc_mir_dataflow::{ Analysis, AnalysisDomain, JoinSemiLattice };

use crate::analysis::deadlock::types::lock::*;
use crate::analysis::core::call_graph::CallGraph;
use crate::{rap_info};

impl JoinSemiLattice for LockSet {
    fn join(&mut self, other: &Self) -> bool {
        self.merge(other)
    }
}

pub struct FuncLockSetAnalyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,

    /// The `LocalLockMap` of current function
    lockmap: &'a LocalLockMap,

    /// The entry_lockset to start analysis with
    entry_lockset: LockSet,

    /// Ref of a global cache recording the result of analyzed functions
    analyzed_functions: &'a HashMap<DefId, FunctionLockSet>,

    /// The analysis result of current function
    func_lock_info: FunctionLockSet,

    /// The callsites in current function
    callsites: HashMap<Location, DefId>,

    /// The callees of current function whose entry_lockset may have changed during analysis
    influenced_callees: HashMap<DefId, LockSet>,
}

/// The auxilury struct that implements `Analysis` trait. The fields are all Refs of the outer FuncLockSetAnalyzer
pub struct FuncLockSetAnalyzerInner<'a> {
    lockmap: &'a LocalLockMap,
    entry_lockset: &'a LockSet,
    analyzed_functions: &'a HashMap<DefId, FunctionLockSet>,
    func_lock_info: &'a mut FunctionLockSet,
    callsites: &'a mut HashMap<Location, DefId>,
}

impl<'tcx, 'a> AnalysisDomain<'tcx> for FuncLockSetAnalyzerInner<'a> {
    type Domain = LockSet;

    const NAME: &'static str = "FuncLockSetAnalysis";

    fn initialize_start_block(
        &self,
        _body: &rustc_middle::mir::Body<'tcx>,
        state: &mut Self::Domain
    ) {
        *state = self.entry_lockset.clone();
    }

    fn bottom_value(&self, _body: &rustc_middle::mir::Body<'tcx>) -> Self::Domain {
        Self::Domain {
            lock_states: HashMap::new()
        }
    }
}

impl <'tcx, 'a> Analysis<'tcx> for FuncLockSetAnalyzerInner<'a> {
    fn apply_statement_effect(
            &mut self,
            _state: &mut Self::Domain,
            _statement: &rustc_middle::mir::Statement<'tcx>,
            _location: Location,
        ) {
        // Do nothing
    }

    fn apply_terminator_effect<'mir>(
            &mut self,
            state: &mut Self::Domain,
            terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
            location: Location,
        ) -> TerminatorEdges<'mir, 'tcx> {
        match &terminator.kind {
            // TODO: record operation site
            TerminatorKind::Call { func, destination, .. } => {
                if let Some((callee, _args)) = func.const_fn_def() {
                    // 1. Record callsite
                    self.callsites.insert(location, callee);

                    // 2. Check if destination is a LockGuard. If yes, we suppose it's a lock api call
                    // TODO: support non-lock function call with lockguard as return type
                    if let Some((_, lock)) = self.lockmap.iter().find(
                        |(&local, _)| local == destination.local
                    ) {
                        state.update_lock_state(lock.clone(), LockState::MayHold);
                    } else {
                        // Otherwise, it's some other function call
                        // 3. Merge the callee's exit_lockset
                        let callee_exit_lockset = match self.analyzed_functions.get(&callee) {
                            Some(callee_func_info) => &callee_func_info.exit_lockset,
                            None => &LockSet::new(),
                        };
                        state.merge(callee_exit_lockset);
                    }
                };
            },
            TerminatorKind::Drop { place, .. } => {
                // Dropping a lockguard releases the lock
                if let Some((_, lock)) = self.lockmap.iter().find(
                    |(&local, _)| local == place.local
                ) {
                    state.update_lock_state(lock.clone(), LockState::MustNotHold);
                }
            },
            TerminatorKind::Return => {
                // Update exit state
                self.func_lock_info.exit_lockset.merge(state);
            },
            _ => {},
        }
        terminator.edges()
    }

    fn apply_call_return_effect(
            &mut self,
            _state: &mut Self::Domain,
            _block: BasicBlock,
            _return_places: CallReturnPlaces<'_, 'tcx>,
        ) {
        // Do nothing
    }
}

impl <'tcx, 'a> FuncLockSetAnalyzer<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        lockmap: &'a LocalLockMap,
        entry_lockset: LockSet,
        analyzed_functions: &'a HashMap<DefId, FunctionLockSet>,
    ) -> Self {
        let func_lock_info = analyzed_functions
            .get(&func_def_id)
            .unwrap_or(&FunctionLockSet {
                func_def_id,
                entry_lockset: entry_lockset.clone(),
                exit_lockset: LockSet::new(),
                bb_locksets: HashMap::new(),
            })
            .clone();
        Self {
            tcx,
            func_def_id,
            lockmap,
            entry_lockset,
            analyzed_functions,
            func_lock_info,
            callsites: HashMap::new(),
            influenced_callees: HashMap::new(),
        }
    }

    /// Run inter-procedure analysis on current function.
    /// `Use` but not `Modify` other function's analysis result
    pub fn run(&mut self) {
        let body: &Body = self.tcx.optimized_mir(self.func_def_id);
        let result = FuncLockSetAnalyzerInner {
            lockmap: &self.lockmap,
            entry_lockset:  &self.entry_lockset,
            analyzed_functions: &self.analyzed_functions,
            func_lock_info: &mut self.func_lock_info,
            callsites: &mut self.callsites,
        }
            .into_engine(self.tcx, body)
            .iterate_to_fixpoint();

        // Clone callsites to avoid longer reference
        let callsites = result.analysis.callsites.clone();

        // The result has been stored in self.func_lock_info.
        // Now calculate influenced_callees.
        let mut cursor = result.into_results_cursor(body);
        for (loc, callee) in callsites.iter() {
            // Note that bb_locksets are lockset AFTER the bb's terminator (e.g. after function call),
            // For entry_lockset however, we need the lockset BEFORE the function call
            cursor.seek_to_block_start(loc.block);
            let new_entry_set = cursor.get();
            let old_entry_set = match self.analyzed_functions.get(&callee) {
                Some(callee_func_info) => &callee_func_info.exit_lockset,
                None => &LockSet::new(),
            };
            if new_entry_set != old_entry_set {
                self.influenced_callees.insert(*callee, new_entry_set.clone());
            }
        }
    }

    /// Is the `exit_lockset` of self.result() different from the original result in analyzed_functions.
    /// This suggests whether the `Callers` of current function are influenced
    pub fn exit_changed(&self) -> bool {
        match self.analyzed_functions.get(&self.func_def_id) {
            Some(old_result) => old_result.exit_lockset != self.func_lock_info.exit_lockset,
            None => true
        }
    }

    /// The analysis result of current function
    pub fn result(&self) -> FunctionLockSet {
        self.func_lock_info.clone()
    }

    /// Get the influenced callee of current function, i.e. those whose entry_lockset have changed.
    pub fn influenced_callees(&self) -> HashMap<DefId, LockSet> {
        self.influenced_callees.clone()
    }
}

pub struct LockSetAnalyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    callgraph: &'a CallGraph<'tcx>,
    global_lockmap: &'a GlobalLockMap,

    analyzed_functions: HashMap<DefId, FunctionLockSet>,
}

impl <'tcx, 'a> LockSetAnalyzer<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        callgraph: &'a CallGraph<'tcx>,
        global_lockmap: &'a GlobalLockMap,
    ) -> Self {
        Self {
            tcx,
            callgraph,
            global_lockmap,
            analyzed_functions: HashMap::new(),
        }
    }
    
    pub fn run(&mut self) -> ProgramLockSet {
        let mut worklist: VecDeque<(DefId, LockSet)> = VecDeque::new();
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = match self.tcx.hir().body_owner_kind(local_def_id) {
                BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };
            worklist.push_back((def_id, LockSet::new()));
        };

        let mut iteration_limit = 10 * worklist.len();
        while iteration_limit > 0 && !worklist.is_empty() {
            iteration_limit -= 1;
            let (func_def_id, entry_lockset) = worklist.pop_front().unwrap(); // this must be Some() since worklist is not empty
            let func_lockmap = match self.global_lockmap.get(&func_def_id) {
                Some(lockmap) => lockmap,
                None => continue,
            };

            let mut func_analyzer = FuncLockSetAnalyzer::new(
                self.tcx,
                func_def_id,
                func_lockmap,
                entry_lockset,
                &self.analyzed_functions,
            );
            func_analyzer.run();
            
            // Does callers need update?
            if func_analyzer.exit_changed() {
                if let Some(callers) = self.callgraph.graph.get_callers_defid(&self.tcx.def_path_str(func_def_id)) {
                    for caller in callers {
                        // Entry set remains the same as in analyzed_functions
                        let caller_entry_lockset = match self.analyzed_functions.get(&caller) {
                            Some(func_info) => func_info.entry_lockset.clone(),
                            None => LockSet::new(),
                        };
                        worklist.push_back((caller, caller_entry_lockset));
                    }
                }
            }
            
            // Does callees need update?
            for pending in func_analyzer.influenced_callees() {
                worklist.push_back(pending);
            }

            // Save the result
            self.analyzed_functions.insert(func_def_id, func_analyzer.result());
        }

        self.analyzed_functions.clone()
    }

    pub fn print_result(&self) {
        for func_info in self.analyzed_functions.values() {
            if func_info.exit_lockset.is_all_bottom() {
                continue;
            }
            rap_info!("{} : {:?}", self.tcx.def_path_str(func_info.func_def_id), func_info.exit_lockset.lock_states);
        }
    }
}