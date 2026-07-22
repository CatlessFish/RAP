use rustc_middle::ty::TyCtxt;

use crate::analysis::deadlock::cycle_detector::detect_cycles;
use crate::analysis::deadlock::types::*;

pub struct DeadlockReporter<'tcx, 'a> {
    _tcx: TyCtxt<'tcx>,
    graph: &'a LockDependencyGraph,
}

impl<'tcx, 'a> DeadlockReporter<'tcx, 'a> {
    pub fn new(_tcx: TyCtxt<'tcx>, graph: &'a LockDependencyGraph) -> Self {
        Self { _tcx, graph }
    }

    pub fn run(&mut self) {
        let limits = CycleDetectionLimits::default();
        let cycles = detect_cycles(&self.graph.graph, &limits);

        let node_count = self.graph.graph.node_count();
        let edge_count = self.graph.graph.edge_count();
        rap_info!(
            "LDG: {} lock(s), {} dependency edge(s)",
            node_count,
            edge_count
        );

        if cycles.is_empty() {
            rap_info!("No deadlock cycles detected.");
        } else {
            // Group cycles: self-cycles first, then multi-node cycles
            let (self_cycles, multi_cycles): (Vec<_>, Vec<_>) = cycles
                .iter()
                .partition(|c| c.nodes.len() == 1 && c.edges.len() == 1);

            let self_count = self_cycles.len();
            let multi_count = multi_cycles.len();

            rap_info!(
                "Found {} self-cycle(s) and {} multi-node cycle(s).",
                self_count,
                multi_count
            );

            // Report self-cycles
            for cycle in &self_cycles {
                let node = cycle.nodes[0];
                let edge = cycle.edges[0];
                let edge_weight = &self.graph.graph[edge];
                rap_info!(
                    "Self-cycle deadlock at: {}\n  first acquired: {:?}\n  then acquired: {:?}\n  type: {}",
                    self.graph.graph[node],
                    edge_weight.old_lock_site.site,
                    edge_weight.new_lock_site.site,
                    cycle.kind,
                );
            }

            // Report multi-node cycles
            for (idx, cycle) in multi_cycles.iter().enumerate() {
                report_multi_cycle(idx, cycle, self.graph);
            }

            // Summary
            let pure_call = cycles
                .iter()
                .filter(|c| c.kind == CycleKind::PureCall)
                .count();
            let pure_intr = cycles
                .iter()
                .filter(|c| c.kind == CycleKind::PureInterrupt)
                .count();
            let mixed = cycles.iter().filter(|c| c.kind == CycleKind::Mixed).count();
            rap_info!(
                "Deadlock summary: {} PureCall, {} PureInterrupt, {} Mixed",
                pure_call,
                pure_intr,
                mixed
            );
        }
    }

    pub fn print_result(&self) {}
}

fn report_multi_cycle(idx: usize, cycle: &DeadlockCycle, graph: &LockDependencyGraph) {
    let n = cycle.nodes.len();
    let mut names: Vec<String> = cycle
        .nodes
        .iter()
        .map(|&n| format!("{}", graph.graph[n]))
        .collect();

    // Rotate to start with lexicographically smallest name for canonical output
    if let Some(min_pos) = names
        .iter()
        .enumerate()
        .min_by_key(|(_, name)| name.as_str())
        .map(|(i, _)| i)
    {
        if min_pos != 0 {
            names.rotate_left(min_pos);
        }
    }

    rap_info!(
        "Multi-node cycle #{} ({}): [{}]",
        idx + 1,
        cycle.kind,
        names.join(" -> ")
    );

    for i in 0..n {
        let edge = &graph.graph[cycle.edges[i]];
        let from_node = &graph.graph[cycle.nodes[i]];
        let to_node = &graph.graph[cycle.nodes[(i + 1) % n]];
        let kind_str = match edge.edge_type {
            LockDependencyEdgeType::Call(ref site) => {
                format!("Call @ {:?}", site.caller_def_id)
            }
            LockDependencyEdgeType::Interrupt(ref site) => {
                format!("Interrupt @ {:?}", site.caller_def_id)
            }
        };
        rap_info!("  {} --[{}]--> {}", from_node, kind_str, to_node);
    }
}
