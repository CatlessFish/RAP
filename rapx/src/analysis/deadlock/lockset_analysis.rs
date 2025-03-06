use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{Interner, Ty, TyCtxt, TyKind};

use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};
// use crate::utils::source::get_fn_name;


impl<'tcx> DeadlockDetection<'tcx> {
    pub fn lockset_analysis(&self) {

        // Filter Static
        for local_def_id in self.tcx.iter_local_def_id() {
            let def_id = local_def_id.to_def_id();
            if let DefKind::Static { safety: _, nested: _, mutability: _ } = self.tcx.def_kind(def_id) {
                // rap_debug!("[Static] {}", self.tcx.def_path_str(def_id));
            }
        }

        // Filter any certain type
        let target_types = [
            vec!["sync::mutex::Mutex"],
            vec!["sync::rwlock::RwLock"],
            vec!["sync::rwmutex::RwMutex"],
            vec!["sync::spin::SpinLock"],
        ];
        for var_def_id in self.tcx.hir().body_owners() {
            let var_ty = self.tcx.type_of(var_def_id.to_def_id()).instantiate_identity();
            for target_type in target_types.iter() {
                if match_target_type(var_ty, target_type, self.tcx) {
                    rap_info!("Found {} type {}", var_ty.to_string(), self.tcx.def_path_str(var_def_id.to_def_id()))
                }
            }
        }

        // Steps:
        // 1. Collect all locks that we're interested in

        // 2. Collect all the Lock / Unlock APIs that we're interested in

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