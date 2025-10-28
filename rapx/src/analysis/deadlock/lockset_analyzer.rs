use rustc_hir::{def_id::DefId, BodyOwnerKind};
use rustc_middle::mir::{
    BasicBlock, Body, CallReturnPlaces, Location, TerminatorEdges, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet, VecDeque};

extern crate rustc_mir_dataflow;
use rustc_mir_dataflow::{Analysis, JoinSemiLattice};

use crate::analysis::deadlock::types::{lock::*, *};
use crate::rap_info;

impl JoinSemiLattice for LockSet {
    fn join(&mut self, other: &Self) -> bool {
        self.merge(other)
    }
}

pub struct FuncLockSetAnalyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,

    /// The context of current function
    call_context: CallContext,

    /// The `LocalLockMap` of current function
    lockmap: &'a LocalLockMap,

    /// The entry_lockset to start analysis with
    entry_lockset: HashMap<CallContext, LockSet>,

    /// Ref of a global cache recording the result of analyzed functions
    analyzed_functions: &'a HashMap<DefId, FunctionLockSet>,

    /// The analysis result of current function
    func_lock_info: FunctionLockSet,

    /// The callsites in current function
    callsites: HashMap<Location, DefId>,

    /// The callees of current function whose entry_lockset may have changed during analysis
    influenced_callees: HashMap<DefId, (CallContext, LockSet)>,
}

/// The auxilury struct that implements `Analysis` trait. The fields are all Refs of the outer FuncLockSetAnalyzer
pub struct FuncLockSetAnalyzerInner<'a> {
    func_def_id: DefId,
    call_context: CallContext,
    lockmap: &'a LocalLockMap,
    entry_lockset: &'a HashMap<CallContext, LockSet>,
    analyzed_functions: &'a HashMap<DefId, FunctionLockSet>,
    func_lock_info: &'a mut FunctionLockSet,
    callsites: &'a mut HashMap<Location, DefId>,
}

impl<'tcx, 'a> Analysis<'tcx> for FuncLockSetAnalyzerInner<'a> {
    type Domain = LockSet;

    const NAME: &'static str = "FuncLockSetAnalysis";

    fn initialize_start_block(
        &self,
        _body: &rustc_middle::mir::Body<'tcx>,
        state: &mut Self::Domain,
    ) {
        *state = if let Some(entry_set) = self.entry_lockset.get(&self.call_context) {
            entry_set.clone()
        } else {
            LockSet::new()
        }
    }

    fn bottom_value(&self, _body: &rustc_middle::mir::Body<'tcx>) -> Self::Domain {
        Self::Domain::new()
    }

    fn apply_primary_statement_effect(
        &mut self,
        _state: &mut Self::Domain,
        _statement: &rustc_middle::mir::Statement<'tcx>,
        _location: Location,
    ) {
        // Do nothing
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir rustc_middle::mir::Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        match &terminator.kind {
            TerminatorKind::Call {
                func, destination, ..
            } => {
                if let Some((callee, _args)) = func.const_fn_def() {
                    // 1. Record callsite
                    self.callsites.insert(location, callee);

                    // 2. Check if destination is a LockGuard. If yes, we suppose it's a lock api call
                    // TODO: support non-lock function call with lockguard as return type
                    if let Some((_, lock)) = self
                        .lockmap
                        .iter()
                        .find(|(&local, _)| local == destination.local)
                    {
                        state.update_lock_state(lock.clone(), LockState::MayHold);
                        state.add_callsite(
                            lock.clone(),
                            CallSite {
                                location,
                                caller_def_id: self.func_def_id,
                            },
                        );

                        // Record lock operation
                        self.func_lock_info.lock_operations.insert(LockSite {
                            lock: lock.clone(),
                            site: CallSite {
                                caller_def_id: self.func_def_id,
                                location,
                            },
                        });
                    } else {
                        // Otherwise, it's some other function call
                        // 3. Merge the callee's exit_lockset
                        let callee_exit_lockset = match self.analyzed_functions.get(&callee) {
                            Some(callee_func_info) => {
                                // Find the corresponding exit_lockset to this function call site
                                let inner_context = CallContext::Place(CallSite {
                                    caller_def_id: self.func_def_id,
                                    location,
                                });
                                if let Some(exit_set) =
                                    callee_func_info.exit_lockset.get(&inner_context)
                                {
                                    exit_set
                                } else {
                                    &LockSet::new()
                                }
                            }
                            None => &LockSet::new(),
                        };
                        state.merge(callee_exit_lockset);
                    }
                };
            }
            TerminatorKind::Drop { place, .. } => {
                // Dropping a lockguard releases the lock
                if let Some((_, lock)) =
                    self.lockmap.iter().find(|(&local, _)| local == place.local)
                {
                    state.update_lock_state(lock.clone(), LockState::MustNotHold);
                    // Clear the lock_sites since the lock is released here
                    if let Some(callsites) = state.lock_sites.get_mut(lock) {
                        callsites.clear();
                    }
                }
            }
            TerminatorKind::Return => {
                // Update the corresponding exit state
                if let Some(target_set) =
                    self.func_lock_info.exit_lockset.get_mut(&self.call_context)
                {
                    target_set.merge(state);
                } else {
                    self.func_lock_info
                        .exit_lockset
                        .insert(self.call_context.clone(), state.clone());
                }
            }
            _ => {}
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

impl<'tcx, 'a> FuncLockSetAnalyzer<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        call_context: CallContext,
        lockmap: &'a LocalLockMap,
        entry_lockset: HashMap<CallContext, LockSet>,
        analyzed_functions: &'a HashMap<DefId, FunctionLockSet>,
    ) -> Self {
        let func_lock_info = analyzed_functions
            .get(&func_def_id)
            .unwrap_or(&FunctionLockSet {
                func_def_id,
                entry_lockset: entry_lockset.clone(),
                exit_lockset: HashMap::new(),
                pre_bb_locksets: HashMap::new(),
                lock_operations: HashSet::new(),
            })
            .clone();
        Self {
            tcx,
            func_def_id,
            call_context,
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
            func_def_id: self.func_def_id,
            call_context: self.call_context.clone(),
            lockmap: &self.lockmap,
            entry_lockset: &self.entry_lockset,
            analyzed_functions: &self.analyzed_functions,
            func_lock_info: &mut self.func_lock_info,
            callsites: &mut self.callsites,
        }
        .iterate_to_fixpoint(self.tcx, body, None);

        // Clone callsites to avoid longer reference
        let callsites = result.analysis.callsites.clone();

        // The result has been stored in self.func_lock_info, except pre_bb_locksets
        let mut cursor = result.into_results_cursor(body);

        // Now calculate influenced_callees.
        for (loc, callee) in callsites.iter() {
            // Note that bb_locksets are lockset AFTER the bb's terminator (e.g. after function call),
            // For entry_lockset however, we need the lockset BEFORE the function call
            cursor.seek_to_block_start(loc.block);
            let new_entry_set = cursor.get();
            let old_entry_set = match self.analyzed_functions.get(&callee) {
                Some(callee_func_info) => {
                    if let Some(entry_set) = callee_func_info.entry_lockset.get(&self.call_context)
                    {
                        entry_set
                    } else {
                        &LockSet::new()
                    }
                }
                None => &LockSet::new(),
            };
            if new_entry_set != old_entry_set {
                let inner_context = CallContext::Place(CallSite {
                    caller_def_id: self.func_def_id,
                    location: *loc,
                });
                self.influenced_callees
                    .insert(*callee, (inner_context, new_entry_set.clone()));
            }
        }

        // pre_bb_locksets is now available after the analysis is finished
        // Collect pre_bb_locksets
        let mut pre_bb_locksets = HashMap::new();
        for (bb_idx, _) in body.basic_blocks.iter_enumerated() {
            cursor.seek_to_block_start(bb_idx);
            pre_bb_locksets.insert(bb_idx, cursor.get().clone());
        }

        self.func_lock_info.pre_bb_locksets = pre_bb_locksets;
    }

    /// Is the `exit_lockset` of self.result() different from the original result in analyzed_functions.
    /// This suggests whether the `Callers` of current function are influenced
    pub fn exit_changed(&self) -> bool {
        match self.analyzed_functions.get(&self.func_def_id) {
            Some(old_result) => old_result.exit_lockset != self.func_lock_info.exit_lockset,
            None => true,
        }
    }

    /// The analysis result of current function
    pub fn result(&self) -> FunctionLockSet {
        self.func_lock_info.clone()
    }

    /// Get the influenced callee of current function, i.e. those whose entry_lockset have changed.
    pub fn influenced_callees(&self) -> HashMap<DefId, (CallContext, LockSet)> {
        self.influenced_callees.clone()
    }
}

pub struct LockSetAnalyzer<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    global_lockmap: &'a GlobalLockMap,
    analyzed_functions: HashMap<DefId, FunctionLockSet>,
}

impl<'tcx, 'a> LockSetAnalyzer<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, global_lockmap: &'a GlobalLockMap) -> Self {
        Self {
            tcx,
            global_lockmap,
            analyzed_functions: HashMap::new(),
        }
    }

    pub fn run(&mut self) -> ProgramLockSet {
        // TODO: What should worklist be like?
        // - VecDeque<DefId, CallContext, VecDeque>
        // How to propagate change to both caller and callees?
        // - caller: we know the current caller; for each possible context of the caller, push it into the worklist as is
        // - callees: push influenced_callees into worklist

        let mut worklist: VecDeque<(DefId, CallContext, LockSet)> = VecDeque::new();
        for local_def_id in self.tcx.hir_body_owners() {
            let def_id = match self.tcx.hir_body_owner_kind(local_def_id) {
                BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };
            // In the first iteration, we don't have call context info
            worklist.push_back((def_id, CallContext::Default, LockSet::new()));
        }

        let mut iteration_limit = 10 * worklist.len();
        while iteration_limit > 0 && !worklist.is_empty() {
            iteration_limit -= 1;
            // Work on function with `func_def_id`
            let (func_def_id, call_context, single_entry_lockset) = worklist.pop_front().unwrap(); // this must be Some() since worklist is not empty
            let func_lockmap = match self.global_lockmap.get(&func_def_id) {
                Some(lockmap) => lockmap,
                None => continue,
            };

            // Get the cached entry_set
            let current_entry_lockset =
                if let Some(func_lock_set) = self.analyzed_functions.get_mut(&func_def_id) {
                    &mut func_lock_set.entry_lockset
                } else {
                    &mut HashMap::new()
                };

            // Then update it with current worklist item
            if let Some(old_lockset) = current_entry_lockset.get_mut(&call_context) {
                old_lockset.merge(&single_entry_lockset);
            } else {
                current_entry_lockset.insert(call_context.clone(), LockSet::new());
            }

            let mut func_analyzer = FuncLockSetAnalyzer::new(
                self.tcx,
                func_def_id,
                call_context.clone(),
                func_lockmap,
                current_entry_lockset.clone(),
                &self.analyzed_functions,
            );
            func_analyzer.run();

            // Does caller need update?
            if func_analyzer.exit_changed() {
                if let CallContext::Place(callsite) = &call_context {
                    let caller_def_id = callsite.caller_def_id;
                    if let Some(caller_lock_info) = self.analyzed_functions.get(&caller_def_id) {
                        for (ctxt, lockset) in &caller_lock_info.entry_lockset {
                            worklist.push_back((caller_def_id, ctxt.clone(), lockset.clone()));
                        }
                    }
                }
            }

            // Does callees need update?
            for (callee_id, (inner_context, new_entry_lockset)) in
                func_analyzer.influenced_callees()
            {
                // Update the callee's entry_lockset
                // let mut callee_old_entry = match self.analyzed_functions.get(&callee_id) {
                //     Some(func_info) => {
                //         if let Some(old_entry) = func_info.entry_lockset.get(&inner_context) {
                //             old_entry
                //         } else {
                //             &LockSet::new()
                //         }
                //     },
                //     None => &LockSet::new(),
                // };
                // callee_old_entry.merge(&callee_new_entry);
                // NOTE: this is done in worklist

                // Then push it into worklist
                worklist.push_back((callee_id, inner_context, new_entry_lockset));
            }

            // Save the result
            self.analyzed_functions
                .insert(func_def_id, func_analyzer.result());
        }

        self.analyzed_functions.clone()
    }

    pub fn print_result(&self) {
        for func_info in self.analyzed_functions.values() {
            if func_info
                .exit_lockset
                .iter()
                .all(|(_ctxt, lockset)| lockset.is_all_bottom())
            {
                continue;
            }
            rap_info!(
                "{} : {:?}",
                self.tcx.def_path_str(func_info.func_def_id),
                func_info.exit_lockset
            );
            // rap_info!("{:?}", func_info);
        }
    }
}
