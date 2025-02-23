mod dep_edge;
mod dep_node;

use crate::utils::fs::rap_create_file;
pub use dep_edge::DepEdge;
pub use dep_node::{desc_str, desc_ty_str, DepNode};
use petgraph::dot::{Config, Dot};
use petgraph::graph::NodeIndex;
use petgraph::Graph;
use rustc_hir::def_id::DefId;
use rustc_middle::query::IntoQueryParam;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Symbol;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::hash::Hash;
use std::io::Write;
use std::path::Path;

type InnerGraph<'tcx> = Graph<DepNode<'tcx>, DepEdge>;
pub struct ApiDepGraph<'tcx> {
    graph: InnerGraph<'tcx>,
    node_indices: HashMap<DepNode<'tcx>, NodeIndex>,
    // node_indices: HashMap<String, NodeIndex>,
    // lifetime_binding: HashMap<DepNode<'tcx>, DepNode<'tcx>> // whether the type has an lifetime binding. Type -> Lifetime
}

impl<'tcx> ApiDepGraph<'tcx> {
    pub fn new() -> ApiDepGraph<'tcx> {
        ApiDepGraph {
            graph: Graph::new(),
            node_indices: HashMap::new(),
        }
    }

    pub fn inner_graph(&self) -> &InnerGraph<'tcx> {
        &self.graph
    }

    pub fn get_node(&mut self, node: DepNode<'tcx>) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node);
            self.node_indices.insert(node, node_index);
            node_index
        }
    }

    pub fn add_edge(&mut self, src: NodeIndex, dst: NodeIndex, edge: DepEdge) {
        self.graph.add_edge(src, dst, edge);
    }

    pub fn dump_to_dot<P: AsRef<Path>>(&self, path: P, tcx: TyCtxt<'tcx>) {
        let get_edge_attr =
            |graph: &Graph<DepNode<'tcx>, DepEdge>,
             edge_ref: petgraph::graph::EdgeReference<DepEdge>| {
                let color = match edge_ref.weight() {
                    DepEdge::Arg(_) | DepEdge::Ret => "black",
                    DepEdge::Fn2Lifetime => "grey",
                };
                format!("label=\"{}\", color = {}", edge_ref.weight(), color)
            };
        let get_node_attr = |graph: &Graph<DepNode<'tcx>, DepEdge>,
                             node_ref: (NodeIndex, &DepNode<'tcx>)| {
            format!("label={:?}, ", desc_str(*node_ref.1, tcx))
                + match node_ref.1 {
                    DepNode::Api(_) => "color = blue",
                    DepNode::Ty(_) => "color = red",
                    DepNode::GenericParamDef(..) => "color = green",
                }
                + ", shape=box"
        };

        let dot = Dot::with_attr_getters(
            &self.graph,
            &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );
        let mut file = rap_create_file(path, "can not create dot file");
        write!(&mut file, "{:?}", dot).expect("fail when writing data to dot file");
        // println!("{:?}", dot);
    }
}
