use rustc_hir::def_id::DefId;
use rustc_hir::{BodyOwnerKind, ItemKind};
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Body, Local, LocalDecl, Operand, Rvalue, TerminatorKind};
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use std::collections::{HashMap, HashSet};

use crate::analysis::deadlock::types::lock::*;
use crate::rap_info;

struct LockGuardInstanceCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,
    lockguard_type_str: &'a Vec<&'a str>,
    lockguard_instances: HashSet<Local>,
}

impl<'tcx, 'a> LockGuardInstanceCollector<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        lockguard_type_str: &'a Vec<&'a str>,
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
                return None;
            }
            // Match name
            // FIXME: match DefId maybe?
            let struct_name = format!("{:?}", adt_def);

            for &type_str in self.lockguard_type_str {
                if type_str == struct_name {
                    return Some(());
                }
            }
        }
        None
    }

    pub fn collect(&mut self) -> HashSet<LockGuardInstance> {
        self.run();
        self.lockguard_instances
            .iter()
            .map(|local| LockGuardInstance {
                func_def_id: self.func_def_id,
                local: *local,
            })
            .collect()
    }
}

impl<'tcx, 'a> Visitor<'tcx> for LockGuardInstanceCollector<'tcx, 'a> {
    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        if self.lockguard_type_from(local_decl.ty).is_some() {
            self.lockguard_instances.insert(local);
        }
        self.super_local_decl(local, local_decl);
    }
}

struct LockTypeCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    lock_type_str: &'a Vec<&'a str>,
    lock_types: HashSet<AdtDef<'tcx>>,
}

impl<'tcx, 'a> LockTypeCollector<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, lock_type_str: &'a Vec<&'a str>) -> Self {
        Self {
            tcx,
            lock_type_str,
            lock_types: HashSet::new(),
        }
    }

    fn run(&mut self) {
        // Collect all AdtDef that matches given name
        // We suppose lock types are all structs, thus we use AdtDef to represent the lock type

        // iterate through struct def
        for item_id in self.tcx.hir_free_items() {
            let item = self.tcx.hir_item(item_id);
            let def_id = match item.kind {
                ItemKind::Struct(..) => item.owner_id.def_id.to_def_id(),
                _ => continue,
            };
            let adt_def = self.tcx.adt_def(def_id);

            // Match name
            // FIXME: use a more stable approach?
            let struct_name = format!("{:?}", adt_def);
            for candidate in self.lock_type_str {
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
    pub fn new(tcx: TyCtxt<'tcx>, lock_types: HashSet<AdtDef<'tcx>>) -> Self {
        Self {
            tcx,
            lock_types,
            lock_instances: HashSet::new(),
        }
    }

    fn run(&mut self) {
        // Collect `static` item whose type is an `ADT` containing `lock_type`
        for local_def_id in self.tcx.hir_body_owners() {
            let def_id = match self.tcx.hir_body_owner_kind(local_def_id) {
                BodyOwnerKind::Static(..) => local_def_id.to_def_id(),
                _ => continue,
            };

            let body = self.tcx.hir_body_owned_by(local_def_id);
            let expr = body.value;
            let typeck = self.tcx.typeck_body(body.id());
            let value_ty = typeck.expr_ty_adjusted(expr);
            // rap_info!("{:?}", value_ty);

            if let Some(_lock_type) = self.lock_type_from(value_ty) {
                // We found a static variable of lock type
                self.lock_instances.insert(LockInstance {
                    def_id: def_id.clone(),
                    span: self
                        .tcx
                        .hir_span(self.tcx.local_def_id_to_hir_id(local_def_id)),
                });
            }
        }
    }

    // FIXME: fail to support nested locktype, e.g. Vec<SpinLock>
    fn lock_type_from(&self, local_type: Ty<'tcx>) -> Option<Ty<'tcx>> {
        // Only look for Adt(struct), as we suppose lockguard types are all struct
        if let TyKind::Adt(adt_def, ..) = local_type.kind() {
            if !adt_def.is_struct() {
                return None;
            }

            // If local_type exactly matches some lock_type
            if self.lock_types.contains(adt_def) {
                return Some(local_type);
            }

            // Or, if any generic param of the struct is some lock_type
            // TODO: record more detail for field-sensitive
            for generic in local_type.walk() {
                if let Some(gen_type) = generic.as_type() {
                    if let TyKind::Adt(sub_adt, ..) = gen_type.kind() {
                        if self.lock_types.contains(sub_adt) {
                            return Some(local_type);
                        }
                    }
                }
            }

            // TODO: support struct field
        }
        None
    }

    pub fn collect(&mut self) -> HashSet<LockInstance> {
        self.run();
        self.lock_instances.clone()
    }
}

/// Build LocalLockMap for a function
struct LockMapBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,
    lock_instances: HashSet<LockInstance>,
    lockguard_instances: HashSet<LockGuardInstance>,

    /// Map from Local to Local.\
    /// e.g. _1 = lock(move _2), then we have _1 -> _2
    local_dataflow_map: HashMap<Local, Local>,

    /// The LocalLockMap of the function
    lockmap: LocalLockMap,
}

impl<'tcx> LockMapBuilder<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        lockguard_instances: HashSet<LockGuardInstance>,
        lock_instances: HashSet<LockInstance>,
    ) -> Self {
        Self {
            tcx,
            func_def_id,
            lock_instances,
            lockguard_instances,

            local_dataflow_map: HashMap::new(),
            lockmap: LocalLockMap::new(),
        }
    }

    fn run(&mut self) {
        let body: &Body = self.tcx.optimized_mir(self.func_def_id);
        // By visit_terminator and visit_assign, we constructed:
        // 1. Local -> Local (both lock_guard and lock_instance) dataflow map
        // 2. Local (lock_instance) -> LockInstance lockmap
        self.visit_body(body);

        // Skip if the function contains no lock
        if self.lockmap.is_empty() {
            return;
        }

        // DEBUG
        // for guard in self.lockguard_instances.iter().filter(|guard| guard.func_def_id == self.func_def_id) {
        //     rap_info!("Guard | {:?}", guard.local);
        // }
        // rap_info!("Dataflow | {:?}", self.local_dataflow_map);
        // rap_info!("Lockmap | {:?}", self.lockmap);

        // Now we squash these two maps to build
        // Local (only lock_guard) -> LockInstance lockmap
        for local in self.local_dataflow_map.keys() {
            if self.lockmap.get(local).is_some() {
                continue;
            }
            let mut current = local;
            if let Some(lock_instance) = loop {
                // Follow the dataflow
                if let Some(lock) = self.lockmap.get(current) {
                    break Some(lock);
                }
                if let Some(upstream) = self.local_dataflow_map.get(current) {
                    current = upstream;
                } else {
                    break None;
                }
            } {
                self.lockmap.insert(*local, lock_instance.clone());
            }
        }

        // Filter out Locals that are not lockguard
        self.lockmap.retain(|&local, _| {
            self.lockguard_instances
                .iter()
                .any(|guard| guard.func_def_id == self.func_def_id && guard.local == local)
        });
    }

    pub fn collect(&mut self) -> LocalLockMap {
        self.run();
        self.lockmap.clone()
    }
}

impl<'tcx> Visitor<'tcx> for LockMapBuilder<'tcx> {
    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        // Track the assignment of LockGuards to find out which LockInstance they correspond to
        // We suppose the assignments are terminators like `_2 = spin::SpinLock::<u32>::lock(move _3) -> [return: bb2, unwind continue];`
        match &terminator.kind {
            TerminatorKind::Call {
                args, destination, ..
            } => {
                // TODO: if some non-lock function returns a lockguard?

                // 1. Match return place
                if let Some(lockguard) = self.lockguard_instances.iter().find(|&guard| {
                    guard.func_def_id == self.func_def_id && guard.local == destination.local
                }) {
                    // 2. Record `self` param
                    // We suppose `self` to be the LockInstance
                    let self_arg = args[0].node.clone();
                    match self_arg {
                        Operand::Copy(place) | Operand::Move(place) => {
                            // TODO: Is it possible that a lockguard local being assigned twice?
                            self.local_dataflow_map.insert(lockguard.local, place.local);
                        }
                        Operand::Constant(..) => {}
                    };
                } else {
                    // FIXME: support dataflow through fn call, e.g. get_on_cpu
                    // TODO: field-sensitive
                    // for now, just consider the first arg
                    if args.len() >= 1 {
                        let self_arg = args[0].node.clone();
                        match self_arg {
                            Operand::Copy(place) | Operand::Move(place) => {
                                self.local_dataflow_map
                                    .insert(destination.local, place.local);
                            }
                            Operand::Constant(..) => {}
                        };
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_assign(
        &mut self,
        place: &rustc_middle::mir::Place<'tcx>,
        rvalue: &rustc_middle::mir::Rvalue<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        // Track dataflow of a function to find which `Local` represents a `LockInstance`
        match rvalue {
            Rvalue::Ref(_, _, ref_place) => {
                self.local_dataflow_map.insert(place.local, ref_place.local);
            }
            Rvalue::Use(operand) => {
                match operand {
                    Operand::Copy(use_place) | Operand::Move(use_place) => {
                        self.local_dataflow_map.insert(place.local, use_place.local);
                    }
                    Operand::Constant(const_op) => {
                        // We suppose all `LockInstance`s are `static`
                        if let Some(const_def_id) = const_op.check_static_ptr(self.tcx) {
                            // Check if the referenced const is a LockInstance
                            if let Some(lock_instance) = self
                                .lock_instances
                                .iter()
                                .find(|lock| lock.def_id == const_def_id)
                            {
                                self.lockmap.insert(place.local, lock_instance.clone());
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

pub struct LockCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    _target_lock_types: &'a Vec<&'a str>,
    _target_lockguard_types: &'a Vec<&'a str>,
    lock_types: HashSet<AdtDef<'tcx>>,
    lock_instances: HashSet<LockInstance>,
    lockguard_instances: HashSet<LockGuardInstance>,
    global_lockmap: GlobalLockMap,
}

impl<'tcx, 'a> LockCollector<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        _target_lock_types: &'a Vec<&'a str>,
        _target_lockguard_types: &'a Vec<&'a str>,
    ) -> Self {
        Self {
            tcx,
            _target_lock_types,
            _target_lockguard_types,
            lock_types: HashSet::new(),
            lock_instances: HashSet::new(),
            lockguard_instances: HashSet::new(),
            global_lockmap: GlobalLockMap::new(),
        }
    }

    fn run(&mut self) {
        // 1. Collect LockGuard Instances
        for local_def_id in self.tcx.hir_body_owners() {
            let def_id = match self.tcx.hir_body_owner_kind(local_def_id) {
                BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };

            let mut lockguard_collector =
                LockGuardInstanceCollector::new(self.tcx, def_id, self._target_lockguard_types);
            let func_lockguard_instances = lockguard_collector.collect();

            // DEBUG
            // if !func_lockguard_instances.is_empty() {
            //     rap_info!("{} | {:?}", self.tcx.def_path_str(def_id), func_lockguard_instances);
            // }

            self.lockguard_instances.extend(func_lockguard_instances);
        }

        // 2. Collect Lock Types
        let mut locktype_collector = LockTypeCollector::new(self.tcx, self._target_lock_types);
        self.lock_types = locktype_collector.collect();

        // 3. Collect Lock Instances
        let mut lock_collector = LockInstanceCollector::new(self.tcx, self.lock_types.clone());
        self.lock_instances = lock_collector.collect();

        // 4. Build LockMap: LockGuardInstance -> LockInstance
        for local_def_id in self.tcx.hir_body_owners() {
            let def_id = match self.tcx.hir_body_owner_kind(local_def_id) {
                BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };

            let mut lockmap_builder = LockMapBuilder::new(
                self.tcx,
                def_id,
                self.lockguard_instances.clone(),
                self.lock_instances.clone(),
            );
            let func_lockmap = lockmap_builder.collect();

            self.global_lockmap.insert(def_id, func_lockmap);
        }
    }

    pub fn collect(&mut self) -> ProgramLockInfo {
        self.run();
        ProgramLockInfo {
            lock_instances: self.lock_instances.clone(),
            lockguard_instances: self.lockguard_instances.clone(),
            lockmap: self.global_lockmap.clone(),
        }
    }

    pub fn print_result(&self) {
        for ty in &self.lock_types {
            rap_info!("Lock Type | {:?}", ty);
        }
        for lock in &self.lock_instances {
            rap_info!("Lock Instance | {}", self.tcx.def_path_str(lock.def_id));
        }
        for (def_id, func_lockmap) in self.global_lockmap.iter() {
            for (local, lock) in func_lockmap.iter() {
                rap_info!(
                    "LockGuard | {} # {:?} -> {}",
                    self.tcx.def_path_str(def_id),
                    local,
                    self.tcx.def_path_str(lock.def_id)
                );
            }
        }
    }
}
