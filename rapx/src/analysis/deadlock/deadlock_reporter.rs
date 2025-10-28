use petgraph::graph::{EdgeIndex, NodeIndex};
use rustc_middle::ty::TyCtxt;
use std::collections::HashSet;

use crate::analysis::deadlock::types::*;
use crate::rap_info;

pub struct DeadlockReporter<'tcx, 'a> {
    _tcx: TyCtxt<'tcx>,
    graph: &'a LockDependencyGraph,
}

impl<'tcx, 'a> DeadlockReporter<'tcx, 'a> {
    pub fn new(_tcx: TyCtxt<'tcx>, graph: &'a LockDependencyGraph) -> Self {
        Self { _tcx, graph }
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

    pub fn print_result(&self) {}
}

fn self_cycle_node(graph: &LockDependencyGraph) -> HashSet<(NodeIndex, EdgeIndex)> {
    let mut result: HashSet<(NodeIndex, EdgeIndex)> = HashSet::new();
    for edge_idx in graph.graph.edge_indices() {
        if let LockDependencyEdgeType::Call(_) = graph.graph[edge_idx].edge_type {
            // Temporarily only look for interrupt self cycle
            continue;
        }
        if let Some((start_node, end_node)) = graph.graph.edge_endpoints(edge_idx) {
            if start_node == end_node {
                result.insert((start_node, edge_idx));
            }
        }
    }
    result
}
