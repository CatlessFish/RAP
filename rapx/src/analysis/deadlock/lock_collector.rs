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

use crate::analysis::deadlock::asterinas_patch::{
    infer_asterinas_guard_irq_semantics_for_call, infer_asterinas_lockguard_type,
};
use crate::analysis::deadlock::tag_parser::LockTagItem;
use crate::analysis::deadlock::types::lock::*;

// Keep recursive field expansion bounded so nested container types do not
// dominate the deadlock analysis runtime.
const MAX_LOCK_FIELD_DEPTH: usize = 6;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct TrackedPlace {
    // The abstract root object currently carried by a MIR local.
    root: LockRoot,

    // The field-sensitive projection from the root to the current subobject.
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

// Summaries only keep roots that can be reconstructed by the caller, so phase 1/2
// stay lightweight without a full points-to analysis.
type ReturnSummaryMap = HashMap<DefId, HashSet<TrackedPlace>>;

#[derive(Debug, Clone)]
struct LockOpSemantics {
    lock_arg: usize,
    irq_semantics: GuardIrqSemantics,
}

type LockOpSemanticsMap = HashMap<DefId, LockOpSemantics>;

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
                        return infer_asterinas_lockguard_type(self.tcx, local_type)
                            .or(Some(LockGuardType::Default));
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
        // Use a path-local stack instead of a global visited set so sibling fields
        // with the same type are still explored.
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
    lock_ops: LockOpSemanticsMap,
    callee_return_summaries: ReturnSummaryMap,
    body: &'tcx Body<'tcx>,
    local_tracked_places: LocalTrackedPlaceMap,
    lockmap: LocalLockMap,

    // Tracks newly discovered non-static abstract instances for global reporting.
    discovered_lock_instances: HashSet<LockInstance>,
    missing_lock_op_apis: HashSet<DefId>,
}

impl<'tcx> LockMapBuilder<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        func_def_id: DefId,
        lockguard_instances: HashSet<LockGuardInstance>,
        lock_types: HashSet<AdtDef<'tcx>>,
        lock_ops: LockOpSemanticsMap,
        callee_return_summaries: ReturnSummaryMap,
    ) -> Self {
        let body = tcx.optimized_mir(func_def_id);
        Self {
            tcx,
            func_def_id,
            lock_types,
            lockguard_instances,
            lock_ops,
            callee_return_summaries,
            body,
            local_tracked_places: HashMap::new(),
            lockmap: LocalLockMap::new(),
            discovered_lock_instances: HashSet::new(),
            missing_lock_op_apis: HashSet::new(),
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

    fn type_bucket_name(&self, ty: Ty<'tcx>) -> String {
        format!("{ty}")
    }

    fn collect_type_bucket_lock_instances_from_ty(
        &self,
        ty: Ty<'tcx>,
        span: Span,
        field_depth: usize,
        path_stack: &mut HashSet<Ty<'tcx>>,
        instances: &mut HashSet<LockInstance>,
    ) {
        // Type buckets are intentionally coarse: once we lose a precise static root,
        // all values of the same lock-containing type collapse to one abstract root.
        if field_depth > MAX_LOCK_FIELD_DEPTH || !path_stack.insert(ty) {
            return;
        }

        if let Some(inner_ty) = self.wrapper_inner_ty(ty) {
            self.collect_type_bucket_lock_instances_from_ty(
                inner_ty,
                span,
                field_depth,
                path_stack,
                instances,
            );
            path_stack.remove(&ty);
            return;
        }

        let TyKind::Adt(adt_def, args) = ty.kind() else {
            path_stack.remove(&ty);
            return;
        };

        if self.lock_types.contains(adt_def) {
            instances.insert(LockInstance {
                root: LockRoot::TypeBucket {
                    type_name: self.type_bucket_name(ty),
                },
                field_path: Vec::new(),
                span,
            });
            path_stack.remove(&ty);
            return;
        }

        for field in adt_def.all_fields() {
            self.collect_type_bucket_lock_instances_from_ty(
                field.ty(self.tcx, args),
                span,
                field_depth + 1,
                path_stack,
                instances,
            );
        }

        path_stack.remove(&ty);
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
        &mut self,
        place: &Place<'tcx>,
        span: Span,
    ) -> HashSet<LockInstance> {
        let place_ty = place.ty(self.body, self.tcx).ty;
        let mut path_stack = HashSet::new();
        if !self.ty_may_reach_lock(place_ty, 0, &mut path_stack) {
            return HashSet::new();
        }

        // Prefer precise static-root recovery whenever the MIR value still carries it.
        let static_instances: HashSet<_> = self
            .resolve_place(place)
            .into_iter()
            .map(|tracked_place| tracked_place.to_lock_instance(span))
            .collect();
        if !static_instances.is_empty() {
            return static_instances;
        }

        let mut path_stack = HashSet::new();
        let mut type_bucket_instances = HashSet::new();
        // Fall back to the coarse type bucket only when no precise static root survives.
        self.collect_type_bucket_lock_instances_from_ty(
            place_ty,
            span,
            0,
            &mut path_stack,
            &mut type_bucket_instances,
        );
        type_bucket_instances
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

    fn record_guard_locks(
        &mut self,
        local: Local,
        locks: HashSet<LockInstance>,
        irq_semantics: GuardIrqSemantics,
    ) {
        if locks.is_empty() {
            return;
        }
        self.discovered_lock_instances.extend(locks.clone());
        self.lockmap
            .entry(local)
            .or_default()
            .extend(locks.into_iter().map(|lock| GuardAcquireInfo {
                lock,
                irq_semantics: irq_semantics.clone(),
            }));
    }

    fn infer_guard_irq_semantics(
        &self,
        receiver_place: &Place<'tcx>,
        destination_local: Local,
        fallback: GuardIrqSemantics,
    ) -> GuardIrqSemantics {
        infer_asterinas_guard_irq_semantics_for_call(
            self.tcx,
            self.body,
            receiver_place,
            destination_local,
        )
        .unwrap_or(fallback)
    }

    fn run(&mut self) {
        self.visit_body(self.body);
        self.lockmap.retain(|&local, _| {
            self.lockguard_instances
                .iter()
                .any(|guard| guard.func_def_id == self.func_def_id && guard.local == local)
        });
    }

    pub fn collect(
        &mut self,
    ) -> (
        LocalLockMap,
        HashSet<LockInstance>,
        HashSet<TrackedPlace>,
        HashSet<DefId>,
    ) {
        self.run();
        (
            self.lockmap.clone(),
            self.discovered_lock_instances.clone(),
            self.local_tracked_places
                .get(&RETURN_PLACE)
                .cloned()
                .unwrap_or_default(),
            self.missing_lock_op_apis.clone(),
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
                if let Some(lock_op) = self.lock_ops.get(&callee).cloned() {
                    if let Some(lock_arg) = args.get(lock_op.lock_arg) {
                        if let Operand::Copy(place) | Operand::Move(place) = &lock_arg.node {
                            let fallback_irq_semantics = lock_op.irq_semantics.clone();
                            let irq_semantics = self.infer_guard_irq_semantics(
                                place,
                                destination.local,
                                fallback_irq_semantics.clone(),
                            );
                            let locks = self.resolve_lock_instances_from_place(
                                place,
                                terminator.source_info.span,
                            );
                            self.record_guard_locks(destination.local, locks, irq_semantics);
                        }
                    } else {
                        rap_warn!(
                            "LockOp argument {} out of range for callee {:?}",
                            lock_op.lock_arg,
                            callee
                        );
                    }
                } else if let Some(receiver) = args.first() {
                    self.missing_lock_op_apis.insert(callee);
                    match &receiver.node {
                        Operand::Copy(place) | Operand::Move(place) => {
                            let irq_semantics = self.infer_guard_irq_semantics(
                                place,
                                destination.local,
                                GuardIrqSemantics::Unchanged,
                            );
                            let locks = self.resolve_lock_instances_from_place(
                                place,
                                terminator.source_info.span,
                            );
                            self.record_guard_locks(destination.local, locks, irq_semantics);
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
    lock_ops: LockOpSemanticsMap,
    lock_instances: HashSet<LockInstance>,
    lockguard_instances: HashSet<LockGuardInstance>,
    global_lockmap: GlobalLockMap,
    missing_lock_op_apis: HashSet<DefId>,
}

impl<'tcx, 'a> LockCollector<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, parsed_tags: &'a [LockTagItem]) -> Self {
        Self {
            tcx,
            parsed_tags,
            lock_types: HashSet::new(),
            lock_ops: HashMap::new(),
            lock_instances: HashSet::new(),
            lockguard_instances: HashSet::new(),
            global_lockmap: GlobalLockMap::new(),
            missing_lock_op_apis: HashSet::new(),
        }
    }

    fn run(&mut self) {
        self.lock_ops = self
            .parsed_tags
            .iter()
            .filter_map(|tag| match tag {
                LockTagItem::LockOp(def_id, lock_arg, guard_irq_disabled, _) => Some((
                    *def_id,
                    LockOpSemantics {
                        lock_arg: *lock_arg,
                        irq_semantics: if *guard_irq_disabled {
                            GuardIrqSemantics::DisabledWhileHeld
                        } else {
                            GuardIrqSemantics::Unchanged
                        },
                    },
                )),
                _ => None,
            })
            .collect();

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
        rap_debug!(
            "Deadlock lock collector: identified {} lockguard locals",
            self.lockguard_instances.len()
        );

        let mut locktype_collector = LockTypeCollector::new(self.tcx, self.parsed_tags);
        self.lock_types = locktype_collector.collect();
        rap_debug!(
            "Deadlock lock collector: identified {} tagged lock types",
            self.lock_types.len()
        );

        let mut lock_instance_collector =
            LockInstanceCollector::new(self.tcx, self.lock_types.clone());
        self.lock_instances = lock_instance_collector.collect();
        let initial_static_instances = self.lock_instances.len();
        rap_debug!(
            "Deadlock lock collector: collected {} static-root lock instances before lockmap propagation",
            initial_static_instances
        );

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
        let mut iteration_count = 0;
        while iteration_limit > 0 {
            iteration_limit -= 1;
            iteration_count += 1;
            let mut changed = false;
            let mut updated_lockmaps = 0;
            let mut updated_summaries = 0;
            let mut discovered_this_round = 0;

            for def_id in &function_ids {
                let mut lockmap_builder = LockMapBuilder::new(
                    self.tcx,
                    *def_id,
                    self.lockguard_instances.clone(),
                    self.lock_types.clone(),
                    self.lock_ops.clone(),
                    return_summaries.clone(),
                );
                let (func_lockmap, discovered_locks, return_summary, missing_lock_ops) =
                    lockmap_builder.collect();

                if self.global_lockmap.get(def_id) != Some(&func_lockmap) {
                    self.global_lockmap.insert(*def_id, func_lockmap);
                    changed = true;
                    updated_lockmaps += 1;
                }
                if return_summaries.get(def_id) != Some(&return_summary) {
                    return_summaries.insert(*def_id, return_summary);
                    changed = true;
                    updated_summaries += 1;
                }
                let new_instance_count = discovered_locks
                    .iter()
                    .filter(|lock| !self.lock_instances.contains(lock))
                    .count();
                if new_instance_count > 0 {
                    self.lock_instances.extend(discovered_locks);
                    changed = true;
                    discovered_this_round += new_instance_count;
                }
                self.missing_lock_op_apis.extend(missing_lock_ops);
            }

            rap_debug!(
                "Deadlock lock collector iteration {}: updated_lockmaps={}, updated_return_summaries={}, new_instances={}, total_instances={}",
                iteration_count,
                updated_lockmaps,
                updated_summaries,
                discovered_this_round,
                self.lock_instances.len()
            );

            if !changed {
                break;
            }
        }

        let static_root_instances = self
            .lock_instances
            .iter()
            .filter(|lock| matches!(lock.root, LockRoot::Static { .. }))
            .count();
        let type_bucket_instances = self
            .lock_instances
            .iter()
            .filter(|lock| matches!(lock.root, LockRoot::TypeBucket { .. }))
            .count();
        let mapped_guards = self
            .global_lockmap
            .values()
            .map(|lockmap| lockmap.len())
            .sum::<usize>();
        let candidate_mappings = self
            .global_lockmap
            .values()
            .flat_map(|lockmap| lockmap.values())
            .map(|locks| locks.len())
            .sum::<usize>();
        let avg_candidates = if mapped_guards == 0 {
            0.0
        } else {
            candidate_mappings as f64 / mapped_guards as f64
        };
        rap_debug!(
            "Deadlock lock collector summary: iterations={}, static_instances={}, type_bucket_instances={}, mapped_guards={}, avg_candidates_per_guard={:.2}",
            iteration_count,
            static_root_instances,
            type_bucket_instances,
            mapped_guards,
            avg_candidates
        );
    }

    pub fn collect(&mut self) -> ProgramLockInfo {
        self.run();
        ProgramLockInfo {
            lock_instances: self.lock_instances.clone(),
            lockguard_instances: self.lockguard_instances.clone(),
            lockmap: self.global_lockmap.clone(),
            missing_lock_op_apis: self.missing_lock_op_apis.clone(),
        }
    }

    pub fn print_result(&self) {
        rap_info!(
            "{} Lock Types, {} LockOps, {} Lock Instances, {} LockGuard Instances",
            self.lock_types.len(),
            self.lock_ops.len(),
            self.lock_instances.len(),
            self.lockguard_instances.len(),
        );
        if !self.missing_lock_op_apis.is_empty() {
            rap_warn!(
                "{} guard-returning APIs still rely on legacy fallback because they are missing LockOp tags",
                self.missing_lock_op_apis.len()
            );
        }
    }
}
