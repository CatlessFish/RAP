use rustc_hir::BodyOwnerKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    Body, Local, LocalDecl, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, Terminator,
    TerminatorKind,
};
use rustc_middle::ty::{AdtDef, GenericArgsRef, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};

use crate::analysis::deadlock::tag_parser::LockTagItem;
use crate::analysis::deadlock::types::lock::*;

const MAX_LOCK_FIELD_DEPTH: usize = 6;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TrackedPlace {
    root: LockRoot,
    field_path: Vec<FieldPathElem>,
}

impl TrackedPlace {
    fn to_lock_instance(&self, span: Span) -> LockInstance {
        LockInstance {
            root: self.root.clone(),
            field_path: self.field_path.clone(),
            span,
        }
    }
}

type LocalTrackedPlaceMap = HashMap<Local, HashSet<TrackedPlace>>;
type ReturnSummaryMap = HashMap<DefId, HashSet<TrackedPlace>>;

struct LockGuardInstanceCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,
    parsed_tags: &'a [LockTagItem],
    lockguard_instances: HashSet<(Local, LockGuardType)>,
}

impl<'tcx, 'a> LockGuardInstanceCollector<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, func_def_id: DefId, parsed_tags: &'a [LockTagItem]) -> Self {
        Self {
            tcx,
            func_def_id,
            parsed_tags,
            lockguard_instances: HashSet::new(),
        }
    }

    fn run(&mut self) {
        let body = self.tcx.optimized_mir(self.func_def_id);
        self.visit_body(body);
    }

    fn lockguard_type_from(&self, local_type: Ty<'tcx>) -> Option<LockGuardType> {
        if let TyKind::Adt(adt_def, _generics) = local_type.kind() {
            if !adt_def.is_struct() {
                return None;
            }
            for tag in self.parsed_tags.iter() {
                if let LockTagItem::LockGuardType(def_id, _name, _) = tag {
                    if adt_def.did() == *def_id {
                        return Some(LockGuardType::Default);
                    }
                }
            }
        }
        None
    }

    pub fn collect(&mut self) -> HashSet<LockGuardInstance> {
        self.run();
        self.lockguard_instances
            .iter()
            .map(|(local, ty)| LockGuardInstance {
                func_def_id: self.func_def_id,
                local: *local,
                guard_type: ty.clone(),
            })
            .collect()
    }
}

impl<'tcx, 'a> Visitor<'tcx> for LockGuardInstanceCollector<'tcx, 'a> {
    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        if let Some(guard_type) = self.lockguard_type_from(local_decl.ty) {
            self.lockguard_instances.insert((local, guard_type));
        }
        self.super_local_decl(local, local_decl);
    }
}

struct LockTypeCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    parsed_tags: &'a [LockTagItem],
    lock_types: HashSet<AdtDef<'tcx>>,
}

impl<'tcx, 'a> LockTypeCollector<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, parsed_tags: &'a [LockTagItem]) -> Self {
        Self {
            tcx,
            parsed_tags,
            lock_types: HashSet::new(),
        }
    }

    fn run(&mut self) {
        for tag in self.parsed_tags {
            if let LockTagItem::LockType(did, _name, _) = tag {
                self.lock_types.insert(self.tcx.adt_def(*did));
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

    fn first_type_arg(args: GenericArgsRef<'tcx>) -> Option<Ty<'tcx>> {
        args.iter().find_map(|arg| arg.as_type())
    }

    fn wrapper_inner_ty(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            TyKind::Ref(_, inner_ty, _) => Some(*inner_ty),
            TyKind::Adt(adt_def, args) => match self.tcx.item_name(adt_def.did()).as_str() {
                "Arc" | "Box" | "Pin" | "Once" | "MaybeUninit" | "UnsafeCell"
                | "SyncUnsafeCell" | "ManuallyDrop" | "Option" | "Result" => {
                    Self::first_type_arg(*args)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn field_name(&self, current_ty: Ty<'tcx>, field_idx: usize) -> String {
        if let TyKind::Adt(adt_def, _) = current_ty.kind() {
            if let Some(field) = adt_def.all_fields().nth(field_idx) {
                return field.name.as_str().to_string();
            }
        }
        format!("field{field_idx}")
    }

    fn collect_lock_instances_from_ty(
        &mut self,
        root: &LockRoot,
        ty: Ty<'tcx>,
        field_path: Vec<FieldPathElem>,
        span: Span,
        field_depth: usize,
        path_stack: &mut HashSet<Ty<'tcx>>,
    ) {
        if field_depth > MAX_LOCK_FIELD_DEPTH || !path_stack.insert(ty) {
            return;
        }

        if let Some(inner_ty) = self.wrapper_inner_ty(ty) {
            self.collect_lock_instances_from_ty(
                root,
                inner_ty,
                field_path,
                span,
                field_depth,
                path_stack,
            );
            path_stack.remove(&ty);
            return;
        }

        let TyKind::Adt(adt_def, args) = ty.kind() else {
            path_stack.remove(&ty);
            return;
        };

        if self.lock_types.contains(adt_def) {
            self.lock_instances.insert(LockInstance {
                root: root.clone(),
                field_path,
                span,
            });
            path_stack.remove(&ty);
            return;
        }

        for (field_idx, field) in adt_def.all_fields().enumerate() {
            let mut nested_path = field_path.clone();
            nested_path.push(FieldPathElem {
                index: field_idx,
                name: self.field_name(ty, field_idx),
            });
            self.collect_lock_instances_from_ty(
                root,
                field.ty(self.tcx, args),
                nested_path,
                span,
                field_depth + 1,
                path_stack,
            );
        }

        path_stack.remove(&ty);
    }

    fn run(&mut self) {
        for local_def_id in self.tcx.hir_body_owners() {
            let def_id = match self.tcx.hir_body_owner_kind(local_def_id) {
                BodyOwnerKind::Static(..) => local_def_id.to_def_id(),
                _ => continue,
            };

            let body = self.tcx.hir_body_owned_by(local_def_id);
            let expr = body.value;
            let typeck = self.tcx.typeck_body(body.id());
            let value_ty = typeck.expr_ty_adjusted(expr);
            let span = self
                .tcx
                .hir_span(self.tcx.local_def_id_to_hir_id(local_def_id));
            let root = LockRoot::Static {
                def_id,
                name: self.tcx.def_path_str(def_id),
            };
            let mut path_stack = HashSet::new();
            self.collect_lock_instances_from_ty(
                &root,
                value_ty,
                Vec::new(),
                span,
                0,
                &mut path_stack,
            );
        }
    }

    pub fn collect(&mut self) -> HashSet<LockInstance> {
        self.run();
        self.lock_instances.clone()
    }
}

struct LockMapBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    func_def_id: DefId,
    lock_types: HashSet<AdtDef<'tcx>>,
    lockguard_instances: HashSet<LockGuardInstance>,
    callee_return_summaries: ReturnSummaryMap,
    body: &'tcx Body<'tcx>,
    local_tracked_places: LocalTrackedPlaceMap,
    lockmap: LocalLockMap,
}

impl<'tcx> LockMapBuilder<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        lockguard_instances: HashSet<LockGuardInstance>,
        lock_types: HashSet<AdtDef<'tcx>>,
        callee_return_summaries: ReturnSummaryMap,
    ) -> Self {
        let body = tcx.optimized_mir(func_def_id);
        Self {
            tcx,
            func_def_id,
            lock_types,
            lockguard_instances,
            callee_return_summaries,
            body,
            local_tracked_places: HashMap::new(),
            lockmap: LocalLockMap::new(),
        }
    }

    fn first_type_arg(args: GenericArgsRef<'tcx>) -> Option<Ty<'tcx>> {
        args.iter().find_map(|arg| arg.as_type())
    }

    fn wrapper_inner_ty(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            TyKind::Ref(_, inner_ty, _) => Some(*inner_ty),
            TyKind::Adt(adt_def, args) => match self.tcx.item_name(adt_def.did()).as_str() {
                "Arc" | "Box" | "Pin" | "Once" | "MaybeUninit" | "UnsafeCell"
                | "SyncUnsafeCell" | "ManuallyDrop" | "Option" | "Result" => {
                    Self::first_type_arg(*args)
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn ty_may_reach_lock(
        &self,
        ty: Ty<'tcx>,
        field_depth: usize,
        path_stack: &mut HashSet<Ty<'tcx>>,
    ) -> bool {
        if field_depth > MAX_LOCK_FIELD_DEPTH || !path_stack.insert(ty) {
            return false;
        }

        if let Some(inner_ty) = self.wrapper_inner_ty(ty) {
            let result = self.ty_may_reach_lock(inner_ty, field_depth, path_stack);
            path_stack.remove(&ty);
            return result;
        }

        let TyKind::Adt(adt_def, args) = ty.kind() else {
            path_stack.remove(&ty);
            return false;
        };

        if self.lock_types.contains(adt_def) {
            path_stack.remove(&ty);
            return true;
        }

        let result = adt_def.all_fields().any(|field| {
            self.ty_may_reach_lock(field.ty(self.tcx, args), field_depth + 1, path_stack)
        });
        path_stack.remove(&ty);
        result
    }

    fn field_name(&self, current_ty: Ty<'tcx>, field_idx: usize) -> String {
        if let TyKind::Adt(adt_def, _) = current_ty.kind() {
            if let Some(field) = adt_def.all_fields().nth(field_idx) {
                return field.name.as_str().to_string();
            }
        }
        format!("field{field_idx}")
    }

    fn resolve_place(&self, place: &Place<'tcx>) -> HashSet<TrackedPlace> {
        let mut tracked = self
            .local_tracked_places
            .get(&place.local)
            .cloned()
            .unwrap_or_default();
        if tracked.is_empty() {
            return tracked;
        }

        let mut current_ty = self.body.local_decls[place.local].ty;
        for projection in place.projection.iter() {
            match projection {
                ProjectionElem::Deref => {
                    if let Some(next_ty) = self.wrapper_inner_ty(current_ty) {
                        current_ty = next_ty;
                    }
                }
                ProjectionElem::Field(field, field_ty) => {
                    let field_idx = field.as_usize();
                    let field_elem = FieldPathElem {
                        index: field_idx,
                        name: self.field_name(current_ty, field_idx),
                    };
                    tracked = tracked
                        .into_iter()
                        .map(|mut tracked_place| {
                            tracked_place.field_path.push(field_elem.clone());
                            tracked_place
                        })
                        .collect();
                    current_ty = field_ty;
                }
                _ => {}
            }
        }

        tracked
    }

    fn resolve_operand(&self, operand: &Operand<'tcx>) -> HashSet<TrackedPlace> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => self.resolve_place(place),
            Operand::Constant(const_op) => {
                let Some(def_id) = const_op.check_static_ptr(self.tcx) else {
                    return HashSet::new();
                };
                let mut roots = HashSet::new();
                roots.insert(TrackedPlace {
                    root: LockRoot::Static {
                        def_id,
                        name: self.tcx.def_path_str(def_id),
                    },
                    field_path: Vec::new(),
                });
                roots
            }
        }
    }

    fn resolve_lock_instances_from_place(
        &self,
        place: &Place<'tcx>,
        span: Span,
    ) -> HashSet<LockInstance> {
        let mut path_stack = HashSet::new();
        if !self.ty_may_reach_lock(place.ty(self.body, self.tcx).ty, 0, &mut path_stack) {
            return HashSet::new();
        }
        self.resolve_place(place)
            .into_iter()
            .map(|tracked_place| tracked_place.to_lock_instance(span))
            .collect()
    }

    fn insert_local_roots(&mut self, local: Local, roots: HashSet<TrackedPlace>) {
        if roots.is_empty() {
            return;
        }
        self.local_tracked_places
            .entry(local)
            .or_default()
            .extend(roots);
    }

    fn record_guard_locks(&mut self, local: Local, locks: HashSet<LockInstance>) {
        if locks.is_empty() {
            return;
        }
        self.lockmap.entry(local).or_default().extend(locks);
    }

    fn run(&mut self) {
        self.visit_body(self.body);
        self.lockmap.retain(|&local, _| {
            self.lockguard_instances
                .iter()
                .any(|guard| guard.func_def_id == self.func_def_id && guard.local == local)
        });
    }

    pub fn collect(&mut self) -> (LocalLockMap, HashSet<TrackedPlace>) {
        self.run();
        (
            self.lockmap.clone(),
            self.local_tracked_places
                .get(&RETURN_PLACE)
                .cloned()
                .unwrap_or_default(),
        )
    }
}

impl<'tcx> Visitor<'tcx> for LockMapBuilder<'tcx> {
    fn visit_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            let Some((callee, _)) = func.const_fn_def() else {
                return;
            };

            if self.lockguard_instances.iter().any(|guard| {
                guard.func_def_id == self.func_def_id && guard.local == destination.local
            }) {
                if let Some(receiver) = args.first() {
                    match &receiver.node {
                        Operand::Copy(place) | Operand::Move(place) => {
                            let locks = self.resolve_lock_instances_from_place(
                                place,
                                terminator.source_info.span,
                            );
                            self.record_guard_locks(destination.local, locks);
                        }
                        Operand::Constant(..) => {}
                    }
                }
                return;
            }

            let mut roots = self
                .callee_return_summaries
                .get(&callee)
                .cloned()
                .unwrap_or_default();

            if roots.is_empty() {
                let mut path_stack = HashSet::new();
                if self.ty_may_reach_lock(
                    self.body.local_decls[destination.local].ty,
                    0,
                    &mut path_stack,
                ) {
                    if let Some(receiver) = args.first() {
                        roots.extend(self.resolve_operand(&receiver.node));
                    }
                }
            }

            self.insert_local_roots(destination.local, roots);
        }
    }

    fn visit_assign(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        match rvalue {
            Rvalue::Ref(_, _, ref_place) => {
                self.insert_local_roots(place.local, self.resolve_place(ref_place));
            }
            Rvalue::Use(operand) => {
                self.insert_local_roots(place.local, self.resolve_operand(operand));
            }
            _ => {}
        }
    }
}

pub struct LockCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    parsed_tags: &'a [LockTagItem],
    lock_types: HashSet<AdtDef<'tcx>>,
    lock_instances: HashSet<LockInstance>,
    lockguard_instances: HashSet<LockGuardInstance>,
    global_lockmap: GlobalLockMap,
}

impl<'tcx, 'a> LockCollector<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, parsed_tags: &'a [LockTagItem]) -> Self {
        Self {
            tcx,
            parsed_tags,
            lock_types: HashSet::new(),
            lock_instances: HashSet::new(),
            lockguard_instances: HashSet::new(),
            global_lockmap: GlobalLockMap::new(),
        }
    }

    fn run(&mut self) {
        for local_def_id in self.tcx.hir_body_owners() {
            let def_id = match self.tcx.hir_body_owner_kind(local_def_id) {
                BodyOwnerKind::Fn => local_def_id.to_def_id(),
                _ => continue,
            };

            let mut lockguard_collector =
                LockGuardInstanceCollector::new(self.tcx, def_id, self.parsed_tags);
            self.lockguard_instances
                .extend(lockguard_collector.collect());
        }

        let mut locktype_collector = LockTypeCollector::new(self.tcx, self.parsed_tags);
        self.lock_types = locktype_collector.collect();

        let mut lock_instance_collector =
            LockInstanceCollector::new(self.tcx, self.lock_types.clone());
        self.lock_instances = lock_instance_collector.collect();

        let function_ids: Vec<_> = self
            .tcx
            .hir_body_owners()
            .filter_map(
                |local_def_id| match self.tcx.hir_body_owner_kind(local_def_id) {
                    BodyOwnerKind::Fn => Some(local_def_id.to_def_id()),
                    _ => None,
                },
            )
            .collect();

        let mut return_summaries: ReturnSummaryMap = HashMap::new();
        let mut iteration_limit = 4 * function_ids.len().max(1);
        while iteration_limit > 0 {
            iteration_limit -= 1;
            let mut changed = false;

            for def_id in &function_ids {
                let mut lockmap_builder = LockMapBuilder::new(
                    self.tcx,
                    *def_id,
                    self.lockguard_instances.clone(),
                    self.lock_types.clone(),
                    return_summaries.clone(),
                );
                let (func_lockmap, return_summary) = lockmap_builder.collect();

                if self.global_lockmap.get(def_id) != Some(&func_lockmap) {
                    self.global_lockmap.insert(*def_id, func_lockmap);
                    changed = true;
                }
                if return_summaries.get(def_id) != Some(&return_summary) {
                    return_summaries.insert(*def_id, return_summary);
                    changed = true;
                }
            }

            if !changed {
                break;
            }
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
        rap_info!(
            "{} Lock Types, {} Lock Instances, {} LockGuard Instances",
            self.lock_types.len(),
            self.lock_instances.len(),
            self.lockguard_instances.len(),
        )
    }
}
