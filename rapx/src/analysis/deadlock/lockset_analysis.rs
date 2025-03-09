use std::collections::HashMap;
use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::hir::ModuleItems;
use rustc_middle::ty::{Interner, Ty, TyCtxt, TyKind};
use rustc_middle::mir::{Body, TerminatorKind};
use rustc_span::def_id::LocalDefId;
use rustc_span::Symbol;
use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};


impl<'tcx> DeadlockDetection<'tcx> {
    pub fn lockset_analysis(&self) {
        // Steps:
        // 1. Collect all locks that we're interested in
        // Filter by type
        let target_types = [
            vec!["sync::mutex::Mutex"],
            vec!["sync::rwlock::RwLock"],
            vec!["sync::rwmutex::RwMutex"],
            vec!["sync::spin::SpinLock"],
        ];


        for var_def_id in self.tcx.hir().body_owners() {
            let def_id = var_def_id.to_def_id();

            // Filter the (const/static ?) Lock Objects
            let var_ty = self.tcx.type_of(def_id).instantiate_identity();
            for target_type in target_types.iter() {
                if match_target_type(var_ty, target_type, self.tcx) {
                    rap_debug!("Lock Object {} of type {} | {:?}", self.tcx.def_path_str(def_id), var_ty.to_string(), self.tcx.def_span(def_id));
                }
            }

            // rap_info!("{:?}", self.tcx.def_path_str(def_id)); // eg. "<sync::rwlock::RwLockUpgradeableGuard_<T, R> as core::ops::Drop>::drop"
            // rap_info!("DefId {:?} | Path {:?} | Type {:?}", def_id, self.tcx.hir().def_path(var_def_id).to_string_no_crate_verbose(), self.tcx.type_of(def_id).instantiate_identity()); // eg. "::sync::rwlock::{impl#22}::drop"
        }

        // Find Lock Struct definitions
        for local_def_id in self.tcx.hir_crate_items(()).definitions() {
            // rap_debug!("{:?}", local_def_id);
            let def_id: DefId =  local_def_id.to_def_id();
            if let DefKind::Struct = self.tcx.def_kind(def_id) {
                let struct_name = self.tcx.def_path_str(def_id);
                if target_types.contains(&vec![struct_name.as_str()]) {
                    rap_debug!("{:?} | {:?}", struct_name, self.tcx.def_span(def_id));
                }
            }
        }

        // Filter the usage (local decl) in each function body
        for var_def_id in self.tcx.hir().body_owners() {
            let def_id = var_def_id.to_def_id(); // The function body def_id

            /* filter const mir */
            if let Some(_other) = self.tcx.hir().body_const_context(def_id.expect_local()) {
                continue;
            }

            if self.tcx.is_mir_available(def_id) {
                let body: Body = self.tcx.optimized_mir(def_id).clone();
                for local in body.local_decls {
                    let local_ty = local.ty;
                    for target_type in target_types.iter() {
                        if match_target_type(local_ty, target_type, self.tcx) {
                            rap_debug!("Local Variable of type {} in function {} | {:?}", local_ty.to_string(), self.tcx.def_path_str(def_id), local.source_info.span);
                            // Mark these functions for future analysis
                        }
                    }
                }
            }
        }


        // 2. Collect all the Lock / Unlock APIs that we're interested in
        let target_lock_apis = ["sync::spin::SpinLock::<T, G>::lock"];
        let mut lock_apis: HashMap<DefId, String> = HashMap::new();

        // Find lock / unlock api definitions
        for var_def_id in self.tcx.hir().body_owners() {
            let def_id = var_def_id.to_def_id(); // The function body def_id
            match self.tcx.def_kind(def_id) {
                DefKind::AssocFn => {
                    let fn_name = self.tcx.def_path_str(def_id);
                    // if is_lock_unlock_api
                    if target_lock_apis.contains(&fn_name.as_str()) {
                        rap_info!("Lock API {:?}", fn_name);
                        lock_apis.insert(def_id, fn_name);
                    }
                }
                _ => {}
            }
        }

        for var_def_id in self.tcx.hir().body_owners() {
            let def_id = var_def_id.to_def_id(); // The function body def_id

            /* filter const mir */
            if let Some(_other) = self.tcx.hir().body_const_context(def_id.expect_local()) {
                continue;
            }

            if self.tcx.is_mir_available(def_id) {
                let body: Body = self.tcx.optimized_mir(def_id).clone();
                for bb in body.basic_blocks.iter() {
                    let terminator = bb.terminator();
                    match terminator.kind {
                        TerminatorKind::Call {
                            ref func,
                            ref args,
                            destination: _,
                            target: _,
                            unwind: _,
                            call_source: _,
                            ref fn_span,
                        } => {
                            if let Some((callee_def_id, _)) = func.const_fn_def() {
                                rap_debug!("Calling function {:?} | {:?}", self.tcx.def_path_str(callee_def_id), terminator.source_info.span);
                                if lock_apis.contains_key(&callee_def_id) {
                                    rap_info!("Calling lock API {:?} in function {:?} | {:?}", self.tcx.def_path_str(callee_def_id), self.tcx.def_path_str(def_id), terminator.source_info.span);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }

        // 3. Conduct Intra-procedure analysis, calculate lockset for each function

    }
}

/// Compare a Type ty and a target_type foo::bar
/// Return true if target_type is EXACTLY the outermost layers of ty
///
/// Examples:
///
/// (foo<bar>, \["foo", "bar"]) => true
///
/// (foo<bar<xyz>>, \["foo", "bar"]) => true
///
/// (foo, \["foo", "bar"]) => false
fn is_target_type(ty: Ty, target_type: &Vec<&str>, tcx: TyCtxt) -> bool {
    // target is empty, meaning that all types are matched
    if target_type.is_empty() {
        return true;
    }

    // get the current outer layer type
    let current_target = target_type[0];

    match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            // check if current layer matches
            if tcx.def_path_str(adt_def.did()) == current_target {
                // recursively check next layer
                let inner_ty = substs.type_at(0);
                return is_target_type(inner_ty, &target_type[1..].to_vec(), tcx);
            }
        }
        // Maybe need to support other types, such as TyKind::FnDef / TyKind::Slice
        _ => (),
    }

    false
}

/// Compare a Type ty and a target_type foo::bar
/// Return true if ty INCLUDES target_type at SOME layers
///
/// Examples:
///
/// (foo<bar>, \["bar"]) => true
///
/// (foo<bar<xyz>>, \["bar", "xyz"]) => true
///
/// (foo, \["foo", "bar"]) => false
fn match_target_type(ty: Ty, target_type: &Vec<&str>, tcx: TyCtxt) -> bool {
    // target is empty, meaning that all types are matched
    if target_type.is_empty() {
        return true;
    }

    // get the current outer layer type
    let current_target = target_type[0];

    match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            // check if current layer matches
            if tcx.def_path_str(adt_def.did()) == current_target {
                // recursively check next layer, STRICTLY (with is_target_type)
                let inner_ty = substs.type_at(0);
                if is_target_type(inner_ty, &target_type[1..].to_vec(), tcx) {
                    return true;
                }
            }
            // if current layer doesn't match, check inner types
            for args in substs.iter() {
                // GenericArg can be Type, Const or Lifetime, only go deeper if it is a Type
                if let Some(inner_ty) = args.as_type() {
                    if match_target_type(inner_ty, target_type, tcx) {
                        return true;
                    }
                }
            }
        }
        _ => (),
    }

    false
}