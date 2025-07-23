use std::collections::{HashSet};
use rustc_hir::def_id::DefId;
use rustc_hir::{BodyOwnerKind, ItemKind};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
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

struct LockTypeCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    lock_type_str: Vec<&'tcx str>,
    lock_types: HashSet<AdtDef<'tcx>>,
}

impl<'tcx> LockTypeCollector<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        lock_type_str: Vec<&'tcx str>,
    ) -> Self {
        Self { 
            tcx,
            lock_type_str,
            lock_types: HashSet::new()
        }
    }

    fn run(&mut self) {
        // Collect all AdtDef that matches given name
        // We suppose lock types are all structs, thus we use AdtDef to represent the lock type

        // iterate through struct def
        for item_id in self.tcx.hir().items() {
            let item = self.tcx.hir().item(item_id);
            let def_id = match item.kind {
                ItemKind::Struct(..) => item.owner_id.def_id.to_def_id(),
                _ => continue,
            };
            let adt_def = self.tcx.adt_def(def_id);

            // Match name
            // FIXME: use a more stable approach?
            let struct_name = format!("{:?}", adt_def);
            for candidate in &self.lock_type_str {
                if struct_name == *candidate {
                    self.lock_types.insert(adt_def);
                    // rap_info!("Locktype: {:?}", struct_name);
                }
            }
        }
    }

    pub fn collect(&mut self) -> HashSet<AdtDef<'tcx>> {
        self.run();
        self.lock_types.clone()
    }
}

struct LockInstanceCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    lock_types: HashSet<AdtDef<'tcx>>,
    lock_instances: HashSet<LockInstance>,
}

impl<'tcx> LockInstanceCollector<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        lock_types: HashSet<AdtDef<'tcx>>,
    ) -> Self {
        Self { 
            tcx,
            lock_types,
            lock_instances: HashSet::new()
        }
    }

    fn run(&mut self) {
        // Collect `static` item whose type is an `ADT` containing `lock_type`
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = match self.tcx.hir().body_owner_kind(local_def_id) {
                BodyOwnerKind::Static(..) => local_def_id.to_def_id(),
                _ => continue,
            };
            // rap_info!("{}", self.tcx.def_path_str(def_id));
            
            let body = self.tcx.hir().body_owned_by(local_def_id);
            let expr = body.value;
            let typeck = self.tcx.typeck_body(body.id());
            let value_ty = typeck.expr_ty_adjusted(expr);
            // rap_info!("{:?}", value_ty);

            if let Some(_lock_type) = self.lock_type_from(value_ty) {
                // We found a static variable of lock type
                self.lock_instances.insert(LockInstance { 
                    def_id: def_id.clone(),
                    span: self.tcx.hir().span(self.tcx.local_def_id_to_hir_id(local_def_id)),
                });
            }
        }
    }

    fn lock_type_from(&self, local_type: Ty<'tcx>) -> Option<Ty<'tcx>> {
        // Only look for Adt(struct), as we suppose lockguard types are all struct
        if let TyKind::Adt(adt_def, generic_args) = local_type.kind() {
            if !adt_def.is_struct() {
                return None
            }

            // If local_type exactly matches some lock_type
            if self.lock_types.contains(adt_def) {
                return Some(local_type)
            }

            // Or, if any fields of local_type matches some lock_type
            // Temporarily we don't look deeper
            for field in adt_def.all_fields() {
                let field_ty = field.ty(self.tcx, generic_args);
                if let TyKind::Adt(field_adt_def, ..) = field_ty.kind() {
                    if self.lock_types.contains(field_adt_def) {
                        return Some(local_type)
                    }
                }
            }
        }
        None
    }

    pub fn collect(&mut self) -> HashSet<LockInstance> {
        self.run();
        self.lock_instances.clone()
    }
}

pub struct LocksetAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
    // _target_lock_types: &'tcx Vec<&'tcx str>,
    // _target_lock_apis: &'tcx Vec<&'tcx str>,
    lock_types: HashSet<AdtDef<'tcx>>,
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
            lock_types: HashSet::new(),
            program_lock_info: ProgramLockInfo::new(),
        }
    }

    pub fn run(&mut self) -> &ProgramLockInfo {
        // 1. Collect LockGuard Instances
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = match self.tcx.hir().body_owner_kind(local_def_id) {
                BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };

            let mut lockguard_collector = LockGuardInstanceCollector::new(
                self.tcx,
                def_id,
                vec!["sync::spin::SpinLockGuard_"],
            );
            let _func_lockguard_instances = lockguard_collector.collect();

            // DEBUG
            // if !_func_lockguard_instances.is_empty() {
            //     rap_info!("{} | {:?}", self.tcx.def_path_str(def_id), _func_lockguard_instances);
            // }
        }

        // 2. Collect Lock Types
        let mut locktype_collector = LockTypeCollector::new(
            self.tcx,
            vec!["sync::spin::SpinLock"],
        );
        self.lock_types = locktype_collector.collect();

        // DEBUG
        for ty in &self.lock_types {
            rap_info!("Lock Type | {:?}", ty);
        }

        // 3. Collect Lock Instances
        let mut lock_collector = LockInstanceCollector::new(
            self.tcx,
            self.lock_types.clone(),
        );
        let lock_instances = lock_collector.collect();

        // DEBUG
        for lock in lock_instances {
            rap_info!("Lock Instance | {:?}", lock);
        }

        // 4. Build LockMap: LockGuardInstance -> LockInstance
        // 5. Calculate LockSet

        &self.program_lock_info
    }
}