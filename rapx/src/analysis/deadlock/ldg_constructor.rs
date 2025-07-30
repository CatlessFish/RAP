use std::collections::{HashSet};
use petgraph::visit::{EdgeRef, IntoNodeReferences};
use rustc_hir::def_id::DefId;
use rustc_hir::{BodyOwnerKind};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::{TyCtxt};
use rustc_middle::mir::{Body, TerminatorKind};

use petgraph::dot::{Dot, Config};

use crate::analysis::deadlock::types::{*, lock::*, interrupt::*};
use crate::{rap_info};

fn extract_locksite_pairs(
    // The lockset BEFORE function call / interrupt
    callsite_lockset: &LockSet,
    // The lock_operations of callee / ISR
    callee_lock_operations: &HashSet<LockSite>,
) -> HashSet<(LockSite, LockSite)> {
    let mut result = HashSet::new();
    let caller_locksites: HashSet<LockSite> = callsite_lockset.lock_sites
        .iter()
        .filter(
            |(lock, _)|
            callsite_lockset.lock_states.get(lock).is_some_and(|state| *state == LockState::MayHold)
        )
        .flat_map(|(lock, callsites)| {
            callsites.iter().map(|callsite| LockSite {lock: lock.clone(), site: *callsite})
        })
        .collect();
    for callee_locksite in callee_lock_operations {
        for caller_locksite in caller_locksites.iter() {
            result.insert((callee_locksite.clone(), caller_locksite.clone()));
        }
    }
    result
}

/// Corresponding to an edge new_lock -- @CallSite --> old_lock
type LockSitePairsWithCallSite = HashSet<(LockSite, LockSite, CallSite)>;

struct NormalEdgeCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    program_lock_set: &'a ProgramLockSet,
    locksite_pairs: LockSitePairsWithCallSite,
}

impl<'tcx, 'a> NormalEdgeCollector<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        program_lock_set: &'a ProgramLockSet,
    ) -> Self {
        Self {
            tcx,
            caller_def_id: func_def_id,
            program_lock_set,
            locksite_pairs: HashSet::new(),
        }
    }

    /// Analyze function foo() and every callee bar() in foo()
    pub fn collect(mut self) -> LockSitePairsWithCallSite{
        // 1. handle function calls
        let body: &Body = self.tcx.optimized_mir(self.caller_def_id);
        self.visit_body(body);

        // 2. handle lock operations in this function
        if let Some(func_info) = self.program_lock_set.get(&self.caller_def_id) {
            for new_lock_site in func_info.lock_operations.iter() {
                if let Some(current_lockset) = func_info.pre_bb_locksets.get(&new_lock_site.site.location.block) {
                    let held_lock_sites: HashSet<LockSite> = current_lockset.lock_sites
                        .iter()
                        .filter(
                            |(lock, _)|
                            current_lockset.lock_states.get(lock).is_some_and(|state| *state == LockState::MayHold)
                        )
                        .flat_map(
                            |(lock, callsites)|
                            callsites.iter().map(|callsite| LockSite {lock: lock.clone(), site: *callsite})
                        )
                        .collect();
                    for held_lock_site in held_lock_sites {
                        self.locksite_pairs.insert((new_lock_site.clone(), held_lock_site, new_lock_site.site));
                    }
                }
            }
        }

        
        self.locksite_pairs
    }
}

impl<'tcx, 'a> Visitor<'tcx> for NormalEdgeCollector<'tcx, 'a> {
    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location:rustc_middle::mir::Location,
    ) {
        // The lockset at callsite
        let callsite_lockset = match self.program_lock_set.get(&self.caller_def_id) {
            Some(func_lockset) => {
                // This must be Some since we have analyzed that function
                func_lockset.pre_bb_locksets.get(&location.block).unwrap()
            },
            None => return
        };
        match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                if let Some((callee_def_id, _)) = func.const_fn_def() {
                    if let Some(callee_func_info) = self.program_lock_set.get(&callee_def_id) {
                        self.locksite_pairs.extend(
                            extract_locksite_pairs(callsite_lockset, &callee_func_info.lock_operations)
                                    .iter()
                                    .map(
                                        // Append CallSite information
                                        |pair| 
                                        (pair.0.clone(), pair.1.clone(), CallSite {caller_def_id: self.caller_def_id, location})
                                    )
                        );
                    }
                }
            },
            _ => {},
        }
    }
}

struct InterruptEdgeCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,
    program_lock_set: &'a ProgramLockSet,
    program_isr_info: &'a ProgramIsrInfo,
    locksite_pairs: LockSitePairsWithCallSite,
}

impl<'tcx, 'a> InterruptEdgeCollector<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        program_lock_set: &'a ProgramLockSet,
        program_isr_info: &'a ProgramIsrInfo,
    ) -> Self {
        Self {
            tcx,
            func_def_id,
            program_lock_set,
            program_isr_info,
            locksite_pairs: HashSet::new(),
        }
    }

    /// Analyze any ISR that may interrupt this function
    pub fn collect(mut self) ->LockSitePairsWithCallSite{
        let body: &Body = self.tcx.optimized_mir(self.func_def_id);
        self.visit_body(body);
        self.locksite_pairs
    }
}

impl<'tcx, 'a> Visitor<'tcx> for InterruptEdgeCollector<'tcx, 'a> {
    fn visit_terminator(
        &mut self,
        _terminator: &rustc_middle::mir::Terminator<'tcx>,
        location:rustc_middle::mir::Location,
    ) {
        // Simulates an interrupt at each terminator
        // 1. Check irq state
        let irq_state = match self.program_isr_info.func_irq_infos.get(&self.func_def_id) {
            Some(func_info) => {
                // This must be Some since we have analyzed that function
                func_info.pre_bb_irq_states.get(&location.block).unwrap()
            },
            None => return,
        };
        if *irq_state == IrqState::MustBeDisabled {
            return
        }

        // 2. Get the lockset of current position
        let callsite_lockset = match self.program_lock_set.get(&self.func_def_id) {
            Some(func_info) => {
                // This must be Some since we have analyzed that function
                func_info.pre_bb_locksets.get(&location.block).unwrap()
            },
            None => return,
        };

        // 3. Iterate through all isr functions
        for isr_def_id in self.program_isr_info.isr_funcs.iter() {
            let isr_lock_ops = match self.program_lock_set.get(isr_def_id) {
                Some(func_info) => &func_info.lock_operations,
                None => continue,
            };
            self.locksite_pairs.extend(
                extract_locksite_pairs(callsite_lockset, isr_lock_ops)
                    .iter()
                    .map(
                        // Append CallSite information
                        |pair|
                        (pair.0.clone(), pair.1.clone(), CallSite {caller_def_id: self.func_def_id, location})
                    )
            );
        }
    }
}

pub struct LDGConstructor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    program_lock_set: &'a ProgramLockSet,
    program_isr_info: &'a ProgramIsrInfo,

    graph: LockDependencyGraph,
}

impl<'tcx, 'a> LDGConstructor<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        program_lock_set: &'a ProgramLockSet,
        program_isr_info: &'a ProgramIsrInfo,
    ) -> Self {
        Self {
            tcx,
            program_isr_info,
            program_lock_set,
            graph: LockDependencyGraph::new(),
        }
    }

    pub fn run(&mut self) {
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = match self.tcx.hir().body_owner_kind(local_def_id) {
                BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };
            // Normal edge: foo() -> call -> bar()
            let normal_edges = NormalEdgeCollector::new(
                self.tcx,
                def_id,
                self.program_lock_set,
            ).collect();

            // Interrupt edge: foo() -> interrupt happens -> handler -> bar()
            let intr_edges = InterruptEdgeCollector::new(
                self.tcx,
                def_id,
                self.program_lock_set,
                self.program_isr_info
            ).collect();

            for (new, old, callsite) in normal_edges.iter() {
                self.graph.insert_normal_edge(new, old, callsite);
                // rap_info!("Normal | {} -> {}, Function call at: {:?}", new, old, callsite);
            }

            for  (new, old, callsite) in intr_edges.iter() {
                self.graph.insert_interrupt_edge(new, old, callsite);
                // rap_info!("Interrupt | {} -> {}, Interrupt happens at: {:?}", new, old, callsite);
            }
        }
    }

    pub fn print_result(&self) {
        let mut result = String::new();
        result.push_str("\n");
        for (idx, lock) in self.graph.graph.node_references() {
            result.push_str(format!("{} {}\n", idx.index(), lock).as_str());
        }
        for edge in self.graph.graph.edge_references() {
            result.push_str(format!("{} -> {} | {:?}\n", edge.source().index(), edge.target().index(), edge.weight().edge_type).as_str())
        }
        rap_info!("{}", result);
    }

    pub fn print_dot_graph(&self) {
        rap_info!("\n{:?}", Dot::with_config(&self.graph.graph, &[Config::GraphContentOnly]));
    }

    pub fn into_graph(self) -> LockDependencyGraph {
        self.graph
    }
}