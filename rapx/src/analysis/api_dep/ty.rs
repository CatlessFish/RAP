use rustc_middle::ty::{AdtDef, FloatTy, GenericArg, IntTy, Mutability, UintTy};

// pub enum Ty {
//     Bool,
//     Char,
//     Int(IntTy),
//     Uint(UintTy),
//     Float(FloatTy),
//     Struct(&[(String, Ty)]),
//     Tuple()
//     Str,
//     Array(I::Ty, I::Const),
//     Pat(I::Ty, I::Pat),
//     Slice(I::Ty),
//     RawPtr(I::Ty, Mutability),
//     Ref(u32, I::Ty, Mutability), // 使用整数存储 lifetime
//     FnDef(I::DefId, I::GenericArgs),
//     FnPtr(ty::Binder<I, FnSigTys<I>>, FnHeader<I>),
//     Dynamic(I::BoundExistentialPredicates, u32, DynKind), // 使用整数存储 lifetime
//     Closure(I::DefId, I::GenericArgs),
//     CoroutineClosure(I::DefId, I::GenericArgs),
//     Coroutine(I::DefId, I::GenericArgs),
//     CoroutineWitness(I::DefId, I::GenericArgs),
//     Never,
//     Tuple(I::Tys),
//     Alias(AliasTyKind, AliasTy<I>),
//     Param(I::ParamTy),
//     Bound(DebruijnIndex, I::BoundTy),
//     Placeholder(I::PlaceholderTy),
//     Infer(InferTy),
//     Error(I::ErrorGuaranteed),
// }
