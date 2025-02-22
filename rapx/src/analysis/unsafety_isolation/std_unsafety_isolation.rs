use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_hir::def_id::CRATE_DEF_INDEX;
use rustc_middle::ty::Visibility;
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty,
    ty::TyCtxt,
};
use std::collections::HashSet;
// use crate::analysis::unsafety_isolation::draw_dot::render_dot_graphs;

use super::{
    generate_dot::{NodeType, UigUnit},
    UnsafetyIsolationCheck,
};

impl<'tcx> UnsafetyIsolationCheck<'tcx> {
    pub fn handle_std_unsafe(&mut self) {
        self.get_all_std_unsafe_def_id_by_treat_std_as_local_crate(self.tcx);
        let mut dot_strs = Vec::new();
        for uig in &self.uigs {
            let dot_str = uig.generate_dot_str();
            // uig.compare_labels(self.tcx);
            dot_strs.push(dot_str);
        }
        for uig in &self.single {
            let dot_str = uig.generate_dot_str();
            // uig.compare_labels();
            dot_strs.push(dot_str);
        }
        // println!("single {:?}",self.single.len());
        // render_dot_graphs(dot_strs);
    }

    pub fn get_all_std_unsafe_def_id_by_rustc_extern_crates(
        &mut self,
        tcx: TyCtxt<'tcx>,
    ) -> HashSet<DefId> {
        let mut visited = HashSet::new();
        let mut unsafe_fn = HashSet::new();
        for &crate_num in tcx.crates(()).iter() {
            let crate_name = tcx.crate_name(crate_num).to_string();
            // if crate_name == "std" || crate_name == "core" || crate_name == "alloc" {
            if crate_name == "core" {
                let crate_root = DefId {
                    krate: crate_num,
                    index: CRATE_DEF_INDEX,
                };
                self.process_def_id(tcx, crate_root, &mut visited, &mut unsafe_fn);
                println!(
                    "{:?} has {:?} MIR instances totally, with {:?} unsafe fns.",
                    crate_name,
                    visited.len(),
                    unsafe_fn.len()
                );
            }
        }
        // Self::print_hashset(&unsafe_fn);
        unsafe_fn
    }

    pub fn get_all_std_unsafe_def_id_by_treat_std_as_local_crate(
        &mut self,
        tcx: TyCtxt<'tcx>,
    ) -> HashSet<DefId> {
        let mut unsafe_fn = HashSet::new();
        let def_id_sets = tcx.mir_keys(());
        for local_def_id in def_id_sets {
            let def_id = local_def_id.to_def_id();
            if Self::filter_mir(def_id) {
                continue;
            }
            if tcx.def_kind(def_id) == DefKind::Fn || tcx.def_kind(def_id) == DefKind::AssocFn {
                if Self::check_safety(tcx, def_id)
                    && self.tcx.visibility(def_id) == Visibility::Public
                {
                    // if UigUnit::get_sp(tcx, def_id).len() == 0 {
                    //     println!("name : {:?}", UigUnit::get_cleaned_def_path_name(tcx, def_id));
                    // }
                    unsafe_fn.insert(def_id);
                    self.insert_uig(
                        def_id,
                        self.get_callees(def_id),
                        Self::get_cons(tcx, def_id),
                    );
                }
            }
        }
        unsafe_fn
    }

    pub fn process_def_id(
        &mut self,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        visited: &mut HashSet<DefId>,
        unsafe_fn: &mut HashSet<DefId>,
    ) {
        if !visited.insert(def_id) || Self::filter_mir(def_id) {
            return;
        }
        match tcx.def_kind(def_id) {
            DefKind::Fn | DefKind::AssocFn => {
                if Self::check_safety(tcx, def_id)
                    && self.tcx.visibility(def_id) == Visibility::Public
                {
                    unsafe_fn.insert(def_id);
                    self.insert_uig(
                        def_id,
                        self.get_callees(def_id),
                        Self::get_cons(tcx, def_id),
                    );
                }
            }
            DefKind::Mod => {
                for child in tcx.module_children(def_id) {
                    if let Some(child_def_id) = child.res.opt_def_id() {
                        self.process_def_id(tcx, child_def_id, visited, unsafe_fn);
                    }
                }
            }
            DefKind::Impl { of_trait: _ } => {
                for item in tcx.associated_item_def_ids(def_id) {
                    self.process_def_id(tcx, *item, visited, unsafe_fn);
                }
            }
            DefKind::Struct => {
                let impls = tcx.inherent_impls(def_id);
                for impl_def_id in impls {
                    self.process_def_id(tcx, *impl_def_id, visited, unsafe_fn);
                }
            }
            DefKind::Ctor(_of, _kind) => {
                if tcx.is_mir_available(def_id) {
                    let _mir = tcx.optimized_mir(def_id);
                }
            }
            _ => {
                // println!("{:?}",tcx.def_kind(def_id));
            }
        }
    }

    pub fn filter_mir(def_id: DefId) -> bool {
        let def_id_fmt = format!("{:?}", def_id);
        def_id_fmt.contains("core_arch")
            || def_id_fmt.contains("::__")
            || def_id_fmt.contains("backtrace_rs")
            || def_id_fmt.contains("stack_overflow")
            || def_id_fmt.contains("thread_local")
            || def_id_fmt.contains("raw_vec")
            || def_id_fmt.contains("sys_common")
            || def_id_fmt.contains("adapters")
            || def_id_fmt.contains("sys::sync")
            || def_id_fmt.contains("personality")
            || def_id_fmt.contains("collections::btree::borrow")
            || def_id_fmt.contains("num::int_sqrt")
            || def_id_fmt.contains("collections::btree::node")
            || def_id_fmt.contains("collections::btree::navigate")
            || def_id_fmt.contains("core_simd")
            || def_id_fmt.contains("unique")
    }

    pub fn insert_uig(
        &mut self,
        caller: DefId,
        callee_set: HashSet<DefId>,
        caller_cons: Vec<NodeType>,
    ) {
        let mut pairs = HashSet::new();
        for callee in &callee_set {
            let callee_cons = Self::get_cons(self.tcx, *callee);
            pairs.insert((Self::generate_node_ty(self.tcx, *callee), callee_cons));
        }
        let uig =
            UigUnit::new_by_pair(Self::generate_node_ty(self.tcx, caller), caller_cons, pairs);
        if callee_set.len() > 0 {
            self.uigs.push(uig);
        } else {
            self.single.push(uig);
        }
    }

    pub fn get_cons(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<NodeType> {
        let mut cons = Vec::new();
        if tcx.def_kind(def_id) == DefKind::Fn || Self::get_type(tcx, def_id) == 0 {
            return cons;
        }
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                // get struct ty
                let ty = tcx.type_of(impl_id).skip_binder();
                if let Some(adt_def) = ty.ty_adt_def() {
                    let adt_def_id = adt_def.did();
                    let impls = tcx.inherent_impls(adt_def_id);
                    for impl_def_id in impls {
                        for item in tcx.associated_item_def_ids(impl_def_id) {
                            if (tcx.def_kind(item) == DefKind::Fn
                                || tcx.def_kind(item) == DefKind::AssocFn)
                                && Self::get_type(tcx, *item) == 0
                            {
                                cons.push(Self::generate_node_ty(tcx, *item));
                            }
                        }
                    }
                }
            }
        }
        cons
    }

    pub fn get_callees(&self, def_id: DefId) -> HashSet<DefId> {
        let mut callees = HashSet::new();
        let tcx = self.tcx;
        if tcx.is_mir_available(def_id) {
            let body = tcx.optimized_mir(def_id);
            for bb in body.basic_blocks.iter() {
                match &bb.terminator().kind {
                    TerminatorKind::Call { func, .. } => {
                        if let Operand::Constant(func_constant) = func {
                            if let ty::FnDef(ref callee_def_id, _) =
                                func_constant.const_.ty().kind()
                            {
                                if Self::check_safety(self.tcx, *callee_def_id) {
                                    callees.insert(*callee_def_id);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        return callees;
    }

    pub fn generate_node_ty(tcx: TyCtxt<'tcx>, def_id: DefId) -> NodeType {
        (
            def_id,
            Self::check_safety(tcx, def_id),
            Self::get_type(tcx, def_id),
        )
    }

    pub fn print_hashset<T: std::fmt::Debug>(set: &HashSet<T>) {
        for item in set {
            println!("{:?}", item);
        }
        println!("---------------");
    }
}
