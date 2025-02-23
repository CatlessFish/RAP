use std::io::Write;

use super::graph::ApiDepGraph;
use super::graph::{DepEdge, DepNode};
use crate::rap_debug;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{self, FnKind, Visitor},
    BodyId, FnDecl,
};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Span;

pub struct FnVisitor<'tcx, 'a> {
    fn_cnt: usize,
    tcx: TyCtxt<'tcx>,
    funcs: Vec<DefId>,
    graph: &'a mut ApiDepGraph<'tcx>,
}

impl<'tcx, 'a> FnVisitor<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, graph: &'a mut ApiDepGraph<'tcx>) -> FnVisitor<'tcx, 'a> {
        let fn_cnt = 0;
        let funcs = Vec::new();
        FnVisitor {
            fn_cnt,
            tcx,
            graph,
            funcs,
        }
    }
    pub fn fn_cnt(&self) -> usize {
        self.fn_cnt
    }
    pub fn write_funcs<T: Write>(&self, F: &mut T) {
        for id in &self.funcs {
            write!(F, "{}\n", self.tcx.def_path_str(id)).expect("fail when write funcs");
        }
    }

    // pub fn bind_lifetime(&mut self, ty: Ty<'tcx>, no: usize, src_node: NodeIndex) {
    //     let kind = ty.kind();
    //     match kind {
    //         ty::TyKind::Ref(region, inner_ty, _) => {
    //             rap_debug!(
    //                 "Region, Ref: {:?}, {:?}",
    //                 get_region_kind_variant(*region),
    //                 inner_ty
    //             );
    //             let node_index = self.graph.get_node(DepNode::region(ty, no));
    //             self.graph.add_edge(src_node, node_index);
    //             self.bind_lifetime(*inner_ty, no + 1, src_node);
    //         }
    //         ty::TyKind::Adt(adt_def, generic_args) => {
    //             for region in generic_args.regions() {
    //                 rap_debug!("Region: {}", get_region_kind_variant(region));
    //                 let node_index = self.graph.get_node(DepNode::region(ty, no));
    //                 self.graph.add_edge(src_node, node_index);
    //             }
    //             // TODO: handle adt_def
    //         }
    //         ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => {
    //             self.bind_lifetime(*ty, no + 1, src_node);
    //         }
    //         _ => {}
    //     }
    // }
}

impl<'tcx, 'a> Visitor<'tcx> for FnVisitor<'tcx, 'a> {
    fn visit_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        let fn_def_id = id.to_def_id();
        self.fn_cnt += 1;
        self.funcs.push(fn_def_id);
        let api_node = self.graph.get_node(DepNode::api(id));

        let early_fn_sig = self.tcx.fn_sig(fn_def_id);
        rap_debug!("fn_sig: {:?}", early_fn_sig);
        let binder_fn_sig = early_fn_sig.instantiate_identity();
        let fn_sig = self
            .tcx
            .liberate_late_bound_regions(fn_def_id, binder_fn_sig);

        // add generic param def to graph
        let generics = self.tcx.generics_of(fn_def_id);
        let generic_param_count = generics.count();
        for i in 0..generic_param_count {
            let generic_param_def = generics.param_at(i, self.tcx);
            let node_index = self.graph.get_node(DepNode::generic_param_def(
                i,
                generic_param_def.name,
                !generic_param_def.kind.is_ty_or_const(),
            ));
            self.graph
                .add_edge(api_node, node_index, DepEdge::fn2lifetime());
        }

        // add inputs/output to graph
        for (no, input_ty) in fn_sig.inputs().iter().enumerate() {
            let input_node = self.graph.get_node(DepNode::ty(*input_ty));
            // self.bind_lifetime(*input_ty, 0, input_node);
            self.graph.add_edge(input_node, api_node, DepEdge::arg(no));
        }

        let output_ty = fn_sig.output();
        let output_node = self.graph.get_node(DepNode::ty(output_ty));
        // self.bind_lifetime(output_ty, 0, output_node);
        self.graph.add_edge(api_node, output_node, DepEdge::ret());
    }
}
