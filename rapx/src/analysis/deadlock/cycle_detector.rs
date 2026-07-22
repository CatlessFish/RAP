use petgraph::algo::tarjan_scc;
use petgraph::graph::{DiGraph, EdgeIndex, NodeIndex};
use petgraph::visit::EdgeRef;
use std::collections::{HashMap, HashSet};

use crate::analysis::deadlock::types::{
    CycleDetectionLimits, CycleKind, DeadlockCycle, LockDependencyEdge, LockDependencyEdgeType,
    LockDependencyNode,
};

/// Entry point: detect all deadlock cycles in the lock dependency graph.
pub fn detect_cycles(
    graph: &DiGraph<LockDependencyNode, LockDependencyEdge>,
    limits: &CycleDetectionLimits,
) -> Vec<DeadlockCycle> {
    let node_count = graph.node_count();

    if node_count == 0 {
        return vec![];
    }

    if node_count > limits.max_graph_nodes {
        rap_warn!(
            "LDG has {} nodes, exceeding limit {}. Skipping cycle enumeration.",
            node_count,
            limits.max_graph_nodes
        );
        return vec![];
    }

    let sccs = tarjan_scc(graph);
    let mut cycles: Vec<DeadlockCycle> = Vec::new();

    for scc in &sccs {
        if scc.is_empty() {
            continue;
        }

        if cycles.len() >= limits.max_total_cycles {
            rap_warn!(
                "Reached max cycle limit ({}), truncating.",
                limits.max_total_cycles
            );
            break;
        }

        if scc.len() == 1 {
            // Single-node SCC: check self-loops
            collect_self_cycles(graph, scc[0], &mut cycles, limits);
        } else if scc.len() <= limits.max_scc_size_for_enumeration {
            // Multi-node SCC: run Johnson's algorithm
            let remaining = limits.max_total_cycles - cycles.len();
            let scc_cycles = johnson_cycles_in_scc(graph, scc, remaining);
            cycles.extend(scc_cycles);
        } else {
            rap_warn!(
                "SCC of size {} exceeds enumeration limit {}. Reporting as complex region with {} locks.",
                scc.len(),
                limits.max_scc_size_for_enumeration,
                scc.len(),
            );
            let names: Vec<String> = scc.iter().map(|&n| format!("{}", graph[n])).collect();
            rap_info!("  Complex deadlock region: {:?}", names);
        }
    }

    cycles
}

/// Collect self-cycle (single-node cycle) edges for a node.
fn collect_self_cycles(
    graph: &DiGraph<LockDependencyNode, LockDependencyEdge>,
    node: NodeIndex,
    cycles: &mut Vec<DeadlockCycle>,
    limits: &CycleDetectionLimits,
) {
    for edge in graph.edges(node) {
        if edge.target() != node {
            continue;
        }
        if cycles.len() >= limits.max_total_cycles {
            break;
        }
        let kind = match graph[edge.id()].edge_type {
            LockDependencyEdgeType::Call(_) => CycleKind::PureCall,
            LockDependencyEdgeType::Interrupt(_) => CycleKind::PureInterrupt,
        };
        cycles.push(DeadlockCycle {
            kind,
            nodes: vec![node],
            edges: vec![edge.id()],
        });
    }
}

/// Run Johnson's algorithm on a single SCC to enumerate all elementary cycles.
fn johnson_cycles_in_scc(
    graph: &DiGraph<LockDependencyNode, LockDependencyEdge>,
    scc: &[NodeIndex],
    max_cycles: usize,
) -> Vec<DeadlockCycle> {
    let n = scc.len();
    if n < 2 {
        return vec![];
    }

    // Map global NodeIndex → local index within this SCC
    let mut global_to_local: HashMap<NodeIndex, usize> = HashMap::new();
    for (i, &node) in scc.iter().enumerate() {
        global_to_local.insert(node, i);
    }

    // Build adjacency list: adj[i] = Vec<(local_target, global_edge_id)>
    let mut adj: Vec<Vec<(usize, EdgeIndex)>> = vec![Vec::new(); n];
    for (i, &node) in scc.iter().enumerate() {
        for edge in graph.edges(node) {
            if let Some(&target_local) = global_to_local.get(&edge.target()) {
                adj[i].push((target_local, edge.id()));
            }
        }
    }

    let mut cycles: Vec<DeadlockCycle> = Vec::new();
    #[allow(non_snake_case)]
    let mut B: Vec<HashSet<usize>> = vec![HashSet::new(); n];
    let mut blocked = vec![false; n];
    let mut vert_stack: Vec<usize> = Vec::new();
    let mut edge_stack: Vec<EdgeIndex> = Vec::new();

    for start in 0..n {
        if cycles.len() >= max_cycles {
            break;
        }

        // Reset state for vertices >= start
        for i in start..n {
            blocked[i] = false;
            B[i].clear();
        }
        vert_stack.clear();
        edge_stack.clear();

        // The allowed set is vertices with index >= start
        let allowed: HashSet<usize> = (start..n).collect();

        circuit(
            start,
            start,
            &adj,
            &allowed,
            &mut blocked,
            &mut B,
            &mut vert_stack,
            &mut edge_stack,
            &mut cycles,
            scc,
            graph,
            max_cycles,
        );
    }

    cycles
}

/// Recursive CIRCUIT procedure from Johnson's algorithm (1975).
///
/// Searches for all elementary cycles starting from vertex `s`, currently at vertex `v`.
/// `vert_stack` contains the path from `s` to `v` (inclusive).
/// `edge_stack[i]` is the edge from `vert_stack[i]` to `vert_stack[i+1]`.
#[allow(non_snake_case)]
fn circuit(
    v: usize,
    s: usize,
    adj: &[Vec<(usize, EdgeIndex)>],
    allowed: &HashSet<usize>,
    blocked: &mut [bool],
    B: &mut [HashSet<usize>],
    vert_stack: &mut Vec<usize>,
    edge_stack: &mut Vec<EdgeIndex>,
    cycles: &mut Vec<DeadlockCycle>,
    scc: &[NodeIndex],
    graph: &DiGraph<LockDependencyNode, LockDependencyEdge>,
    max_cycles: usize,
) -> bool {
    let mut found_cycle = false;
    vert_stack.push(v);
    blocked[v] = true;

    for &(w, edge_id) in &adj[v] {
        if !allowed.contains(&w) {
            continue;
        }

        if w == s {
            // Found a cycle: s → ... → v → s
            found_cycle = true;
            let nodes: Vec<NodeIndex> = vert_stack.iter().map(|&i| scc[i]).collect();
            let mut edges: Vec<EdgeIndex> = edge_stack.clone();
            edges.push(edge_id); // edge from v → s closes the cycle
            let kind = classify_cycle_kind(&edges, graph);
            cycles.push(DeadlockCycle { kind, nodes, edges });

            if cycles.len() >= max_cycles {
                // Still need to clean up before returning
                blocked[v] = false;
                vert_stack.pop();
                return true;
            }
        } else if !blocked[w] {
            edge_stack.push(edge_id);
            if circuit(
                w, s, adj, allowed, blocked, B, vert_stack, edge_stack, cycles, scc, graph,
                max_cycles,
            ) {
                found_cycle = true;
            }
            edge_stack.pop();
        }
    }

    if found_cycle {
        unblock(v, blocked, B);
    } else {
        for &(w, _) in &adj[v] {
            if allowed.contains(&w) {
                B[w].insert(v);
            }
        }
    }

    vert_stack.pop();
    // Only unblock if we're returning through a non-start vertex.
    // For the start vertex (v == s), blocked[s] stays blocked so it won't be
    // used as a start vertex again.
    if v != s {
        blocked[v] = blocked[v]; // keep as-is (may have been unblocked already)
    }
    found_cycle
}

/// Unblock vertex u: mark it unblocked, then recursively unblock
/// any vertices that were blocked solely because of u.
#[allow(non_snake_case)]
fn unblock(u: usize, blocked: &mut [bool], B: &mut [HashSet<usize>]) {
    blocked[u] = false;
    let waiting: Vec<usize> = B[u].drain().collect();
    for w in waiting {
        if blocked[w] {
            unblock(w, blocked, B);
        }
    }
}

/// Classify a cycle by inspecting all its edges.
fn classify_cycle_kind(
    edges: &[EdgeIndex],
    graph: &DiGraph<LockDependencyNode, LockDependencyEdge>,
) -> CycleKind {
    let mut has_call = false;
    let mut has_interrupt = false;
    for &edge_idx in edges {
        match graph[edge_idx].edge_type {
            LockDependencyEdgeType::Call(_) => has_call = true,
            LockDependencyEdgeType::Interrupt(_) => has_interrupt = true,
        }
    }
    match (has_call, has_interrupt) {
        (true, false) => CycleKind::PureCall,
        (false, true) => CycleKind::PureInterrupt,
        _ => CycleKind::Mixed,
    }
}
