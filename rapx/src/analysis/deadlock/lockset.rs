use std::collections::{HashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::{AdtKind, Ty, TyCtxt, TyKind};
use rustc_middle::mir::{Local, LocalDecl};

use crate::analysis::deadlock::*;
use crate::{rap_info};

struct LockGuardInstanceCollector<'tcx>{
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,
    lockguard_type_str: Vec<&'tcx str>,
    lockguard_instances: HashSet<Local>,
}

impl<'tcx> LockGuardInstanceCollector<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        lockguard_type_str: Vec<&'tcx str>,
    ) -> Self {
        Self {
            tcx,
            func_def_id,
            lockguard_type_str,
            lockguard_instances: HashSet::new(),
        }
    }

    fn run(&mut self) {
        // let fn_name = self.tcx.def_path_str(self.func_def_id);
        // rap_info!("Function {}", fn_name);
        let body = self.tcx.optimized_mir(self.func_def_id);
        self.visit_body(body);
    }

    // TODO: return LockGuardType
    fn lockguard_type_from(&self, local_type: Ty<'tcx>) -> Option<()> {
        // Only look for Adt(struct), as we suppose lockguard types are all struct
        if let TyKind::Adt(adt_def, ..) = local_type.kind() {
            if !adt_def.is_struct() {
                return None
            }
            // Match name
            // FIXME: match DefId maybe?
            let struct_name = format!("{:?}", adt_def);

            for &type_str in &self.lockguard_type_str {
                if type_str == struct_name {
                    return Some(())
                }
            }
        }
        None
    }

    pub fn collect(&mut self) -> HashSet<LockGuardInstance> {
        self.run();
        self.lockguard_instances.iter().map(|local| 
            LockGuardInstance {
                func_def_id: self.func_def_id,
                local: *local,
        }).collect()
    }
}

impl<'tcx> Visitor<'tcx> for LockGuardInstanceCollector<'tcx> {
    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        if self.lockguard_type_from(local_decl.ty).is_some() {
            self.lockguard_instances.insert(local);
        }
        self.super_local_decl(local, local_decl);
    }
}

pub struct LocksetAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    // _target_lock_types: &'tcx Vec<&'tcx str>,
    // _target_lock_apis: &'tcx Vec<&'tcx str>,
    program_lock_info: ProgramLockInfo,
}

impl<'tcx> LocksetAnalysis<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        // target_lock_types: &'tcx Vec<&'tcx str>,
        // target_lock_apis: &'tcx Vec<&'tcx str>,
    ) -> Self {
        Self { 
            tcx,
            // _target_lock_types: target_lock_types,
            // _target_lock_apis: target_lock_apis,
            program_lock_info: ProgramLockInfo::new(),
        }
    }

    pub fn run(&mut self) -> &ProgramLockInfo {
        // 1. Collect LockGuard Instances
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = match self.tcx.hir().body_owner_kind(local_def_id) {
                rustc_hir::BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };

            let mut lockguard_collector = LockGuardInstanceCollector::new(
                self.tcx,
                def_id,
                vec!["sync::spin::SpinLockGuard_"],
            );
            let func_lockguard_instances = lockguard_collector.collect();

            // DEBUG
            rap_info!("{} | {:?}", self.tcx.def_path_str(def_id), func_lockguard_instances);
        }

        // 2. Collect Lock Instances
        // 3. Build LockMap: LockGuardInstance -> LockInstance
        // 4. Calculate LockSet

        &self.program_lock_info
    }
}