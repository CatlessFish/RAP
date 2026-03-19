use rustc_middle::mir::{Body, Local, Place};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use std::collections::HashSet;

use crate::analysis::deadlock::types::lock::{GuardIrqSemantics, LockGuardType};

const ASTERINAS_GUARD_IRQ_PATCH_ENV: &str = "RAP_ASTERINAS_GUARD_IRQ_PATCH";
const SPIN_LOCK_PATHS: &[&str] = &["ostd::sync::SpinLock", "ostd::sync::spin::SpinLock"];
const SPIN_LOCK_GUARD_PATHS: &[&str] = &[
    "ostd::sync::SpinLockGuard",
    "ostd::sync::spin::SpinLockGuard",
];
const LOCAL_IRQ_DISABLED_PATHS: &[&str] = &[
    "ostd::sync::LocalIrqDisabled",
    "ostd::sync::guard::LocalIrqDisabled",
];
const PREEMPT_DISABLED_PATHS: &[&str] = &[
    "ostd::sync::PreemptDisabled",
    "ostd::sync::guard::PreemptDisabled",
];

pub fn asterinas_guard_irq_patch_enabled() -> bool {
    std::env::var(ASTERINAS_GUARD_IRQ_PATCH_ENV)
        .map(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
        .unwrap_or(false)
}

pub fn infer_asterinas_lockguard_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    guard_ty: Ty<'tcx>,
) -> Option<LockGuardType> {
    if !asterinas_guard_irq_patch_enabled() {
        return None;
    }

    guard_type_from_ty(tcx, guard_ty)
}

pub fn infer_asterinas_guard_irq_semantics_for_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    receiver_place: &Place<'tcx>,
    destination_local: Local,
) -> Option<GuardIrqSemantics> {
    if !asterinas_guard_irq_patch_enabled() {
        return None;
    }

    let receiver_ty = receiver_place.ty(body, tcx).ty;
    let destination_ty = body.local_decls[destination_local].ty;
    guard_irq_semantics_from_ty(tcx, receiver_ty)
        .or_else(|| guard_irq_semantics_from_ty(tcx, destination_ty))
}

fn guard_type_from_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<LockGuardType> {
    let mut visited = HashSet::new();
    guard_type_from_ty_recursive(tcx, ty, &mut visited)
}

fn guard_irq_semantics_from_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<GuardIrqSemantics> {
    let mut visited = HashSet::new();
    guard_irq_semantics_from_ty_recursive(tcx, ty, &mut visited)
}

fn guard_type_from_ty_recursive<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    visited: &mut HashSet<Ty<'tcx>>,
) -> Option<LockGuardType> {
    let ty = peel_refs(ty);
    if !visited.insert(ty) {
        return None;
    }
    let TyKind::Adt(adt_def, args) = ty.kind() else {
        return None;
    };

    let adt_path = tcx.def_path_str(adt_def.did());
    let type_args: Vec<_> = args.types().collect();
    if matches_any_path(&adt_path, SPIN_LOCK_GUARD_PATHS) {
        if has_any_type_arg_path(tcx, &type_args, LOCAL_IRQ_DISABLED_PATHS) {
            return Some(LockGuardType::SpinLockLocalDisabled);
        }
        if has_any_type_arg_path(tcx, &type_args, PREEMPT_DISABLED_PATHS) {
            return Some(LockGuardType::SpinLockPreemptDisabled);
        }
    }

    for field in adt_def.all_fields() {
        if let Some(guard_type) = guard_type_from_ty_recursive(tcx, field.ty(tcx, args), visited) {
            return Some(guard_type);
        }
    }

    None
}

fn guard_irq_semantics_from_ty_recursive<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    visited: &mut HashSet<Ty<'tcx>>,
) -> Option<GuardIrqSemantics> {
    let ty = peel_refs(ty);
    if !visited.insert(ty) {
        return None;
    }
    let TyKind::Adt(adt_def, args) = ty.kind() else {
        return None;
    };

    let adt_path = tcx.def_path_str(adt_def.did());
    let type_args: Vec<_> = args.types().collect();
    if matches_any_path(&adt_path, SPIN_LOCK_PATHS)
        || matches_any_path(&adt_path, SPIN_LOCK_GUARD_PATHS)
    {
        if has_any_type_arg_path(tcx, &type_args, LOCAL_IRQ_DISABLED_PATHS) {
            return Some(GuardIrqSemantics::DisabledWhileHeld);
        }
        if has_any_type_arg_path(tcx, &type_args, PREEMPT_DISABLED_PATHS) {
            return Some(GuardIrqSemantics::Unchanged);
        }
    }

    for field in adt_def.all_fields() {
        if let Some(semantics) =
            guard_irq_semantics_from_ty_recursive(tcx, field.ty(tcx, args), visited)
        {
            return Some(semantics);
        }
    }

    if has_any_type_arg_path(tcx, &type_args, LOCAL_IRQ_DISABLED_PATHS) {
        Some(GuardIrqSemantics::DisabledWhileHeld)
    } else if has_any_type_arg_path(tcx, &type_args, PREEMPT_DISABLED_PATHS) {
        Some(GuardIrqSemantics::Unchanged)
    } else {
        None
    }
}

fn peel_refs<'tcx>(mut ty: Ty<'tcx>) -> Ty<'tcx> {
    while let TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    ty
}

fn has_type_arg_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut tys: impl Iterator<Item = Ty<'tcx>>,
    wanted_path: &str,
) -> bool {
    tys.any(|ty| type_contains_path(tcx, ty, wanted_path))
}

fn has_any_type_arg_path<'tcx>(tcx: TyCtxt<'tcx>, tys: &[Ty<'tcx>], wanted_paths: &[&str]) -> bool {
    wanted_paths
        .iter()
        .any(|wanted_path| has_type_arg_path(tcx, tys.iter().copied(), wanted_path))
}

fn type_contains_path<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, wanted_path: &str) -> bool {
    let ty = peel_refs(ty);
    let TyKind::Adt(adt_def, args) = ty.kind() else {
        return false;
    };

    if tcx.def_path_str(adt_def.did()) == wanted_path {
        return true;
    }

    args.types()
        .any(|nested_ty| type_contains_path(tcx, nested_ty, wanted_path))
}

fn matches_any_path(actual_path: &str, wanted_paths: &[&str]) -> bool {
    wanted_paths.iter().any(|wanted| actual_path == *wanted)
}
