use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt};
use std::fmt::{self, Formatter, Display};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use rustc_middle::mir::{BasicBlock, BasicBlockData, Local};

extern crate rustc_mir_dataflow;
use rustc_mir_dataflow::fmt::DebugWithContext;

pub mod lock {
    use super::*;
    use rustc_mir_dataflow::JoinSemiLattice;

    /// A `LockInstance` is a `static` variable, with Lock type
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct LockInstance {
        /// The def_id of the static item
        pub def_id: DefId,
        
        /// Source span
        pub span: Span,

        // TODO: lock_type
    }

    impl Display for LockInstance {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{:?}", self.def_id)
        }
    }

    /// A `LockGuardInstance` is a `Local` inside a function, with LockGuard type
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub struct LockGuardInstance {
        pub func_def_id: DefId,
        pub local: Local,
    }

    /// Map from `Local` LockGuard to LockInstance of a function
    pub type LocalLockMap = HashMap<Local, LockInstance>;

    /// Each function's `LocalLockMap`
    pub type GlobalLockMap = HashMap<DefId, LocalLockMap>;

    /// `LockState` indicates the status of a `LockInstance`.\
    /// This is a semi-lattice.
    //      MayHold
    // MustHold, MustNotHold
    //      Bottom
    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
    pub enum LockState {
        Bottom,
        MustHold,
        MustNotHold,
        MayHold,
    }

    impl JoinSemiLattice for LockState {
        fn join(&mut self, other: &Self) -> bool {
            let old = self.clone();
            *self = match (&self, other) {
                // Bottom U any = any
                (Self::Bottom, _) => other.clone(),
                (_, Self::Bottom) => self.clone(),

                // MayHold U any = MayHold
                (Self::MayHold, _) => Self::MayHold,
                (_, Self::MayHold) => Self::MayHold,

                // MustHold U MustHold = MustHold
                (Self::MustHold, Self::MustHold) => Self::MustHold,

                // MustNotHold U MustNotHold = MustNotHold
                (Self::MustNotHold, Self::MustNotHold) => Self::MustNotHold,

                // MustHold U MustNotHold = MayHold
                (Self::MustHold, Self::MustNotHold) => Self::MayHold,
                (Self::MustNotHold, Self::MustHold) => Self::MayHold,
            };
            *self != old
        }
    }

    /// 表示一个函数中的锁集
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct LockSet {
        pub lock_states: HashMap<DefId, LockState>, // 锁的状态
    }

    impl LockSet {
        pub fn new() -> Self {
            LockSet {
                lock_states: HashMap::new(),
            }
        }
        
        // 合并两个锁集（用于分支汇合点）
        // Usage: next_bb_lockstate.merge(&current_bb_lockstate)
        pub fn merge(&mut self, other: &LockSet) {
            for (lock_id, other_state) in other.lock_states.iter() {
                if let Some(old_state) = self.lock_states.get_mut(lock_id) {
                    old_state.join(other_state);
                } else {
                    self.lock_states.insert(lock_id.clone(), other_state.clone());
                }
            }
        }

        // 更新单个锁的state
        pub fn update_lock_state(&mut self, lock_id: DefId, state: LockState) {
            self.lock_states.insert(lock_id, state);
        }

        // 获取must_hold的锁列表
        pub fn get_must_hold_locks(&self) -> Vec<DefId> {
            self.lock_states.iter().filter(|(_, state)| **state == LockState::MustHold).map(|(lock_id, _)| *lock_id).collect()
        }

        // 获取may_hold的锁列表
        pub fn get_may_hold_locks(&self) -> Vec<DefId> {
            self.lock_states.iter().filter(|(_, state)| **state == LockState::MayHold).map(|(lock_id, _)| *lock_id).collect()
        }
        
        // 获取must_not_hold的锁列表
        pub fn get_must_not_hold_locks(&self) -> Vec<DefId> {
            self.lock_states.iter().filter(|(_, state)| **state == LockState::MustNotHold).map(|(lock_id, _)| *lock_id).collect()
        }

        // 判断是否所有锁都是Bottom
        pub fn is_all_bottom(&self) -> bool {
            self.lock_states.iter().all(|(_, state)| *state == LockState::Bottom)
        }
    }

    impl Display for LockSet {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "MustHold: {:?}, MustNotHold: {:?}, MayHold: {:?}", self.get_must_hold_locks(), self.get_must_not_hold_locks(), self.get_may_hold_locks())
        }
    }


    // 函数的锁集信息
    #[derive(Debug, Clone)]
    pub struct FunctionLockSet {
        pub func_def_id: DefId,                                // 函数ID
        pub entry_lockset: LockSet,                       // 入口锁集
        pub exit_lockset: LockSet,                        // 出口锁集
        pub bb_locksets: HashMap<BasicBlock, LockSet>,    // 每个基本块的锁集
        pub call_sites: Vec<(BasicBlock, DefId)>,      // 调用点信息
        pub lock_sites: Vec<OperationSite>,                    // 锁点信息
    }

    impl PartialEq for FunctionLockSet {
        fn eq(&self, other: &Self) -> bool {
            self.func_def_id == other.func_def_id &&
            self.entry_lockset == other.entry_lockset &&
            self.exit_lockset == other.exit_lockset &&
            self.bb_locksets == other.bb_locksets &&
            self.lock_sites == other.lock_sites
        }
    }

    /// ProgramLockInfo contains `LockGuardInstance`, `LockInstance` and Map from `LockGuardInstance` to `LockInstance`
    #[derive(Debug)]
    pub struct ProgramLockInfo {
        /// `static` lock definitions
        pub lock_instances: HashSet<LockInstance>,

        /// `Local`s with LockGuard type
        pub lockguard_instances: HashSet<LockGuardInstance>,

        /// Map from LockGuard Locals to LockInstance
        pub lockmap: GlobalLockMap,
    }

    impl ProgramLockInfo {
        pub fn new() -> Self {
            ProgramLockInfo {
                lock_instances: HashSet::new(),
                lockguard_instances: HashSet::new(),
                lockmap: GlobalLockMap::new(),
            }
        }
    }
}

pub mod interrupt {
    use super::*;
    /// 表示某个Program Point处的中断开关状态
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum IrqState {
        Bottom,
        MustBeDisabled, // Must
        MayBeEnabled, // May
    }

    impl IrqState {
        pub fn new() -> Self {
            Self::Bottom
        }

        /// Return a new IrqState of self U other
        pub fn union(&self, other: &IrqState) -> IrqState {
            match (self, other) {
                (IrqState::Bottom, _) => other.clone(),
                (_, IrqState::Bottom) => self.clone(),
                (IrqState::MustBeDisabled, IrqState::MustBeDisabled) => IrqState::MustBeDisabled,
                _ => IrqState::MayBeEnabled,
            }
        }
    }

    impl Display for IrqState {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "{:?}", self)
        }
    }

    impl<C> DebugWithContext<C> for IrqState {}

    /// 表示某个函数中各个位置的中断开关状态
    #[derive(Debug, Clone)]
    pub struct FuncIrqInfo {
        /// 函数的defId
        pub def_id: DefId,

        /// 函数出口处的中断开关状态
        pub exit_irq_state: IrqState,

        /// 每个Basic Block结束位置的中断开关状态
        pub bb_irq_states: HashMap<BasicBlock, IrqState>,

        /// 开启中断的位置
        pub interrupt_enable_sites: Vec<OperationSite>,
    }

    impl PartialEq for FuncIrqInfo {
        fn eq(&self, other: &Self) -> bool {
            self.def_id == other.def_id &&
            self.exit_irq_state == other.exit_irq_state &&
            self.bb_irq_states == other.bb_irq_states &&
            self.interrupt_enable_sites == other.interrupt_enable_sites
        }
    }

    impl Display for FuncIrqInfo {
        fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
            write!(f, "Exit state: {}", self.exit_irq_state)
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum InterruptApiType {
        Disable,
        Enable,
    }

    /// The interrupt info of the whole program
    #[derive(Debug, Clone)]
    pub struct ProgramIsrInfo {
        /// The `DefId`s of all the identified ISR ENTRY functions.
        /// Corresponds to `DeadlockDetection.target_isr_entries`.
        pub isr_entries: HashSet<DefId>, 

        /// All possible callee (and recursively their callee)
        /// of a ISR ENTRY function should be considered as a ISR function.
        pub isr_funcs: HashSet<DefId>, 

        /// The `FuncIrqInfo` of each function
        pub func_irq_infos: HashMap<DefId, FuncIrqInfo>, 
    }

    impl ProgramIsrInfo {
        pub fn new() -> Self {
            ProgramIsrInfo {
                isr_entries: HashSet::new(),
                isr_funcs: HashSet::new(),
                func_irq_infos: HashMap::new(),
            }
        }
    }
}

// === Function Summary ===

// LockSite / InterrupteEnableSite
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OperationSite {
    pub object_def_id: DefId,
    pub func_def_id: Option<DefId>, // Should only be None for regular lock edge nodes, because we may not know where the lock is acquired
    pub bb_index: Option<BasicBlock>, // As above
}

impl OperationSite {
    pub fn to_span(&self, tcx: &TyCtxt) -> Option<Span> {
        if self.func_def_id.is_none() || self.bb_index.is_none() {
            return None;
        }
        if !tcx.is_mir_available(self.func_def_id.unwrap()) {
            return None;
        }
        let body = tcx.optimized_mir(self.func_def_id.unwrap());
        let bb: &BasicBlockData = &body.basic_blocks[self.bb_index.unwrap()];
        let terminator = bb.terminator();
        Some(terminator.source_info.span)
    }

    pub fn to_string(&self, tcx: &TyCtxt) -> String {
        let span = self.to_span(tcx);
        if let Some(span) = span {
            format!("{:?} at {:?}", self.object_def_id, span)
        } else {
            format!("{:?}", self.object_def_id)
        }
    }
}

impl Display for OperationSite {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.func_def_id.is_none() || self.bb_index.is_none() {
            write!(f, "{:?}", self.object_def_id)
        } else {
            write!(f, "{:?} in {:?}", self.object_def_id, self.func_def_id.unwrap())
        }
    }
}