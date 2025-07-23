// use std::collections::{HashSet};

// use crate::analysis::deadlock::*;
// use crate::rap_info;

// impl<'tcx> DeadlockDetection<'tcx> {
//     pub fn detect_deadlock(&self) {
//         rap_info!("Detecting deadlock...");

//         // Detect cycles on self.interrupt_lock_graph
//         // ILG edges are interrupt edges and regular edges
//         // ILG vertices are lock object DefIds

//         let mut visited = HashSet::<OperationSite>::new();
//         let mut stack = Vec::<OperationSite>::new();

//         fn dfs(
//             node: &OperationSite,
//             edges: &Vec<ILGEdge>,
//             visited: &mut HashSet<OperationSite>,
//             stack: &mut Vec<OperationSite>,
//             tcx: &TyCtxt,
//         ) {
//             visited.insert(node.clone());
//             stack.push(node.clone());
    
//             // NOTE: a -> a pattern
//             // TODO: Optimize time complexity
//             for edge in edges.iter() {
//                 if edge.source == *node {
//                     let neighbor = edge.target;
                    
//                     // If the lock object is already in the stack, there is a deadlock
//                     if stack.iter().any(|stack_node| stack_node.object_def_id == neighbor.object_def_id) {
//                         // Deadlock path is the node in stack between neighbor and current node
//                         let mut deadlock_path = Vec::<OperationSite>::new();
//                         let mut flag = false;
//                         for stack_node in stack.iter() {
//                             if stack_node.object_def_id == neighbor.object_def_id {
//                                 flag = true;
//                             }
//                             if flag {
//                                 deadlock_path.push(stack_node.clone());
//                             }
//                             if stack_node == node {
//                                 break;
//                             }
//                         }
//                         rap_info!("Deadlock detected: {}", deadlock_path.iter().map(|node| node.to_string(tcx)).collect::<Vec<String>>().join(" -> "));
//                     }
//                     if !visited.contains(&neighbor) {
//                         dfs(&neighbor, edges, visited, stack, tcx);
//                     }
//                 }
//             }
//             stack.pop();
//         }

//         for node in self.interrupt_lock_graph.edges.iter() {
//             if !visited.contains(&node.source) {
//                 dfs(&node.source, &self.interrupt_lock_graph.edges, &mut visited, &mut stack, &self.tcx);
//             }
//         }
//     }

//     pub fn print_deadlock_result(&self) {
//         rap_info!("==== Deadlock Result ====");
//         rap_info!("==== End of Deadlock Result ====");
//     }
// }