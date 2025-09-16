use std::collections::{HashSet};
use petgraph::graph::{EdgeIndex, NodeIndex};
use petgraph::visit::{EdgeRef, IntoNodeReferences};
use petgraph::algo::tarjan_scc;
use rustc_hir::def_id::DefId;
use rustc_hir::{BodyOwnerKind};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::{TyCtxt};
use rustc_middle::mir::{Body, TerminatorKind};

use crate::analysis::deadlock::types::{*, lock::*, interrupt::*};
use crate::{rap_info};

pub struct DeadlockReporter<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    graph: &'a LockDependencyGraph,
}

impl <'tcx, 'a> DeadlockReporter<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        graph: &'a LockDependencyGraph, 
    ) -> Self {
        Self {
            tcx,
            graph,
        }
    }

    pub fn run(&mut self) {
        // let cycles = tarjan_scc(&self.graph.graph);
        // for cycle in cycles {
        //     rap_info!("Possible Deadlock Cycle: {:?}", cycle);

        //     // TODO: analyze all cycles
        // }
        let self_cycle_nodes = self_cycle_node(self.graph);
        rap_info!("Found {} self-cycle nodes", self_cycle_nodes.len());
        for (node, edge) in self_cycle_nodes {
            rap_info!("Possible Deadlock at: {:?}\n\tFirst acquired at {:?}\n\tthen aquired at {:?}\n\ttype {:?}",
                self.graph.graph[node].def_id,
                self.graph.graph[edge].old_lock_site.site,
                self.graph.graph[edge].new_lock_site.site,
                self.graph.graph[edge].edge_type,
            );
            // rap_info!("Possible Deadlock at {:?}", self.graph.graph[node]);
            // for edge in self.graph.graph.edges(node) {
            //     rap_info!("{}", edge.weight());
            // }
        }
    }

    pub fn print_result(&self) {

    }
}

fn self_cycle_node(graph: &LockDependencyGraph) -> HashSet<(NodeIndex, EdgeIndex)> {
    // FIXME: missing some nodes
    let mut result: HashSet<(NodeIndex, EdgeIndex)> = HashSet::new();
    for node_idx in graph.graph.node_indices() {
        let mut neighbors = graph.graph.neighbors(node_idx);
        if neighbors.any(|neighbor_idx| neighbor_idx == node_idx) {
            if let Some(edge_idx) = graph.graph.find_edge(node_idx, node_idx) {
                if let LockDependencyEdgeType::Interrupt(_) = graph.graph[edge_idx].edge_type {
                    result.insert((node_idx, edge_idx));
                }
            }
        }
    }
    result
}