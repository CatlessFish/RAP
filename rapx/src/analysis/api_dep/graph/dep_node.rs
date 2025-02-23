use std::hash::Hash;

use rustc_middle::{
    query::IntoQueryParam,
    ty::{self, Ty, TyCtxt},
};
use rustc_span::Symbol;

use rustc_hir::def_id::DefId;

#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
enum IntrinsicKind {
    Borrow,
}

#[derive(Clone, Copy, Debug)]
pub enum DepNode<'tcx> {
    Api(DefId),
    Ty(Ty<'tcx>),
    GenericParamDef(usize, Symbol, bool), // (index, symbol, is_lifetime_param)
}

fn eq_ty<'tcx>(lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> bool {
    match (lhs.kind(), rhs.kind()) {
        (ty::TyKind::Adt(adt_def1, generic_arg1), ty::TyKind::Adt(adt_def2, generic_arg2)) => {
            if adt_def1.did() != adt_def2.did() {
                return false;
            }
            for (arg1, arg2) in generic_arg1.iter().zip(generic_arg2.iter()) {
                match (arg1.unpack(), arg2.unpack()) {
                    (ty::GenericArgKind::Lifetime(_), ty::GenericArgKind::Lifetime(_)) => continue,
                    (ty::GenericArgKind::Type(ty1), ty::GenericArgKind::Type(ty2)) => {
                        if !eq_ty(ty1, ty2) {
                            return false;
                        }
                    }
                    (ty::GenericArgKind::Const(ct1), ty::GenericArgKind::Const(ct2)) => {
                        if ct1 != ct2 {
                            return false;
                        }
                    }
                    _ => return false,
                }
            }
            true
        }
        (
            ty::TyKind::RawPtr(inner_ty1, mutability1),
            ty::TyKind::RawPtr(inner_ty2, mutability2),
        )
        | (
            ty::TyKind::Ref(_, inner_ty1, mutability1),
            ty::TyKind::Ref(_, inner_ty2, mutability2),
        ) => mutability1 == mutability2 && eq_ty(*inner_ty1, *inner_ty2),
        (ty::TyKind::Array(inner_ty1, _), ty::TyKind::Array(inner_ty2, _))
        | (ty::TyKind::Pat(inner_ty1, _), ty::TyKind::Pat(inner_ty2, _))
        | (ty::TyKind::Slice(inner_ty1), ty::TyKind::Slice(inner_ty2)) => {
            eq_ty(*inner_ty1, *inner_ty2)
        }
        (ty::TyKind::Tuple(tys1), ty::TyKind::Tuple(tys2)) => {
            if tys1.len() != tys2.len() {
                return false;
            }
            tys1.iter()
                .zip(tys2.iter())
                .all(|(ty1, ty2)| eq_ty(ty1, ty2))
        }
        _ => lhs == rhs,
    }
}

// hashing Ty<'tcx>, but ignore the difference of lifetimes
fn hash_ty<'tcx, H: std::hash::Hasher>(ty: Ty<'tcx>, state: &mut H, no: &mut usize) {
    // hash the variant
    match ty.kind() {
        ty::TyKind::Adt(..) => 0,
        ty::TyKind::RawPtr(..) => 1,
        ty::TyKind::Ref(..) => 2,
        ty::TyKind::Array(..) => 3,
        ty::TyKind::Pat(..) => 4,
        ty::TyKind::Slice(..) => 5,
        ty::TyKind::Tuple(..) => 6,
        _ => {
            ty.hash(state);
            return;
        }
    }
    .hash(state);

    // hash the content
    match ty.kind() {
        ty::TyKind::Adt(adt_def, generic_arg) => {
            adt_def.did().hash(state);
            for arg in generic_arg.iter() {
                match arg.unpack() {
                    ty::GenericArgKind::Lifetime(lt) => {
                        *no = *no + 1;
                        no.hash(state);
                    }
                    ty::GenericArgKind::Type(ty) => {
                        hash_ty(ty, state, no);
                    }
                    ty::GenericArgKind::Const(ct) => {
                        ct.hash(state);
                    }
                }
            }
        }

        ty::TyKind::RawPtr(inner_ty, mutability) | ty::TyKind::Ref(_, inner_ty, mutability) => {
            mutability.hash(state);
            *no = *no + 1;
            no.hash(state);
            hash_ty(*inner_ty, state, no);
        }
        ty::TyKind::Array(inner_ty, _)
        | ty::TyKind::Pat(inner_ty, _)
        | ty::TyKind::Slice(inner_ty) => {
            hash_ty(*inner_ty, state, no);
        }
        ty::TyKind::Tuple(tys) => {
            for inner_ty in tys.iter() {
                hash_ty(inner_ty, state, no);
            }
        }
        _ => {
            unreachable!("unexpected ty kind");
        }
    }
}

pub fn desc_str<'tcx>(node: DepNode<'tcx>, tcx: TyCtxt<'tcx>) -> String {
    match node {
        DepNode::Api(def_id) => tcx.def_path_str(def_id),
        DepNode::Ty(ty) => desc_ty_str(ty, &mut 0, tcx),
        DepNode::GenericParamDef(idx, sym, is_lifetime) => {
            format!("{}/{}", sym, idx)
        }
    }
}

pub fn desc_ty_str<'tcx>(ty: Ty<'tcx>, no: &mut usize, tcx: TyCtxt<'tcx>) -> String {
    match ty.kind() {
        ty::TyKind::Adt(adt_def, generic_arg) => {
            let mut ty_str = tcx.def_path_str(adt_def.did());
            if (!generic_arg.is_empty()) {
                ty_str += "<";
                ty_str += &generic_arg
                    .iter()
                    .map(|arg| match arg.unpack() {
                        ty::GenericArgKind::Lifetime(lt) => {
                            let current_no = *no;
                            *no = *no + 1;
                            format!("'#{:?}", current_no)
                        }
                        ty::GenericArgKind::Type(ty) => desc_ty_str(ty, no, tcx),
                        ty::GenericArgKind::Const(ct) => format!("{:?}", ct),
                    })
                    .collect::<Vec<String>>()
                    .join(", ");
                ty_str += ">";
            }
            ty_str
        }

        ty::TyKind::RawPtr(inner_ty, mutability) => {
            let mut_str = {
                match mutability {
                    ty::Mutability::Mut => "mut",
                    ty::Mutability::Not => "const",
                }
            };
            format!("*{} {}", mut_str, desc_ty_str(*inner_ty, no, tcx))
        }
        ty::TyKind::Ref(_, inner_ty, mutability) => {
            let mut_str = {
                match mutability {
                    ty::Mutability::Mut => "mut",
                    ty::Mutability::Not => "",
                }
            };
            let current_no = *no;
            *no = *no + 1;
            format!(
                "&'#{}{} {}",
                current_no,
                mut_str,
                desc_ty_str(*inner_ty, no, tcx)
            )
        }
        ty::TyKind::Array(inner_ty, _)
        | ty::TyKind::Pat(inner_ty, _)
        | ty::TyKind::Slice(inner_ty) => desc_ty_str(*inner_ty, no, tcx),
        ty::TyKind::Tuple(tys) => format!(
            "({})",
            tys.iter()
                .map(|ty| desc_ty_str(ty, no, tcx,))
                .collect::<Vec<String>>()
                .join(", "),
        ),
        _ => format!("{:?}", ty),
    }
}

impl PartialEq for DepNode<'_> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (DepNode::Api(def_id1), DepNode::Api(def_id2)) => def_id1 == def_id2,
            (DepNode::Ty(ty1), DepNode::Ty(ty2)) => eq_ty(*ty1, *ty2),
            (
                DepNode::GenericParamDef(idx1, sym1, lf1),
                DepNode::GenericParamDef(idx2, sym2, lf2),
            ) => idx1 == idx2 && sym1 == sym2 && lf1 == lf2,
            _ => false,
        }
    }
}

impl Eq for DepNode<'_> {}

impl<'tcx> std::hash::Hash for DepNode<'tcx> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            DepNode::Api(def_id) => def_id.hash(state),
            DepNode::Ty(ty) => {
                hash_ty(*ty, state, &mut 0);
            }
            DepNode::GenericParamDef(idx, sym, lf) => {
                idx.hash(state);
                sym.hash(state);
                lf.hash(state);
            }
        }
    }
}

impl<'tcx> DepNode<'tcx> {
    pub fn api(id: impl IntoQueryParam<DefId>) -> DepNode<'tcx> {
        DepNode::Api(id.into_query_param())
    }
    pub fn ty(ty: Ty<'tcx>) -> DepNode<'tcx> {
        DepNode::Ty(ty)
    }
    pub fn generic_param_def(index: usize, symbol: Symbol, is_lifetime: bool) -> DepNode<'tcx> {
        DepNode::GenericParamDef(index, symbol, is_lifetime)
    }
}
