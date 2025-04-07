use rustc_hir::def_id::DefId;

use std::fmt::{self, Formatter, Display};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use rustc_middle::mir::BasicBlock;

// 表示一个锁对象
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LockObject {
    pub def_id: DefId,          // 锁变量的DefId
    pub lock_type: String,      // 锁的类型（Mutex/RwLock等）
    pub is_static: bool,        // 是否是静态锁
    pub span: Span,             // 源码位置
}

// 表示锁的类型
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LockType {
    ReadLocked,             // 读锁状态
    WriteLocked,            // 写锁状态
    UpgradeableReadLocked,  // 可升级读锁状态（RwLock特有）
}

// 表示锁的状态
// MayHold
// MustHold, MustNotHold
// Bottom
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LockState {
    Bottom,
    MustHold,
    MustNotHold,
    MayHold,
}

impl LockState {
    pub fn union(&self, other: &LockState) -> LockState {
        match (self, other) {
            // Bottom U any = any
            (LockState::Bottom, _) => other.clone(),
            (_, LockState::Bottom) => self.clone(),
            // MayHold U any = MayHold
            (LockState::MayHold, _) => LockState::MayHold,
            (_, LockState::MayHold) => LockState::MayHold,
            // MustHold U MustHold = MustHold
            (LockState::MustHold, LockState::MustHold) => LockState::MustHold,
            // MustNotHold U MustNotHold = MustNotHold
            (LockState::MustNotHold, LockState::MustNotHold) => LockState::MustNotHold,
            // MustHold U MustNotHold = MayHold
            (LockState::MustHold, LockState::MustNotHold) => LockState::MayHold,
            (LockState::MustNotHold, LockState::MustHold) => LockState::MayHold,
        }
    }

    pub fn intersect(&self, other: &LockState) -> LockState {
        match (self, other) {
            // Bottom ∩ any = Bottom
            (LockState::Bottom, _) => LockState::Bottom,
            (_, LockState::Bottom) => LockState::Bottom,
            // MayHold ∩ any = any
            (LockState::MayHold, _) => other.clone(),
            (_, LockState::MayHold) => self.clone(),
            // MustHold ∩ MustHold = MustHold
            (LockState::MustHold, LockState::MustHold) => LockState::MustHold,
            // MustNotHold ∩ MustNotHold = MustNotHold
            (LockState::MustNotHold, LockState::MustNotHold) => LockState::MustNotHold,
            // MustHold ∩ MustNotHold = Bottom
            (LockState::MustHold, LockState::MustNotHold) => LockState::Bottom,
            (LockState::MustNotHold, LockState::MustHold) => LockState::Bottom,
        }
    }
}
// 表示一个函数中的锁集
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockSet {
    pub lock_states: HashMap<DefId, LockState>, // 锁的状态
}

// 为LockSet实现默认构造函数
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
                *old_state = old_state.union(other_state);
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
pub struct FunctionLockInfo {
    pub def_id: DefId,                                // 函数ID
    pub entry_lockset: LockSet,                       // 入口锁集
    pub exit_lockset: LockSet,                        // 出口锁集
    pub bb_locksets: HashMap<BasicBlock, LockSet>,    // 每个基本块的锁集
    pub call_sites: Vec<(BasicBlock, DefId)>,      // 调用点信息
    pub lock_sites: Vec<OperationSite>,                    // 锁点信息
}

// 为FunctionLockInfo实现PartialEq
impl PartialEq for FunctionLockInfo {
    fn eq(&self, other: &Self) -> bool {
        self.def_id == other.def_id &&
        self.entry_lockset == other.entry_lockset &&
        self.exit_lockset == other.exit_lockset &&
        self.bb_locksets == other.bb_locksets &&
        self.lock_sites == other.lock_sites
        // 忽略call_sites比较，因为它主要用于过程内分析
    }
}

// 程序全局锁信息
#[derive(Debug)]
pub struct ProgramLockInfo {
    pub lock_objects: HashMap<DefId, LockObject>,      // 所有锁对象
    pub lock_apis: HashMap<DefId, (String, LockType)>, // 所有锁API及其对锁状态的影响
    pub function_lock_infos: HashMap<DefId, FunctionLockInfo>, // 每个函数的锁集信息
}

impl ProgramLockInfo {
    pub fn new() -> Self {
        ProgramLockInfo {
            lock_objects: HashMap::new(),
            lock_apis: HashMap::new(),
            function_lock_infos: HashMap::new(),
        }
    }
}

// ===== ISR =====
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IsrState {
    Bottom,
    Disabled, // Must
    Enabled, // May
}

impl IsrState {
    pub fn union(&self, other: &IsrState) -> IsrState {
        match (self, other) {
            (IsrState::Bottom, _) => other.clone(),
            (_, IsrState::Bottom) => self.clone(),
            (IsrState::Disabled, IsrState::Disabled) => IsrState::Disabled,
            _ => IsrState::Enabled,
        }
    }
}

// 表示一个中断集
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterruptSet{
    pub interrupt_states: HashMap<DefId, IsrState>,
}

impl InterruptSet {
    pub fn new() -> Self {
        InterruptSet { interrupt_states: HashMap::new() }
    }

    pub fn merge(&mut self, other: &InterruptSet) {
        for (isr_id, other_state) in other.interrupt_states.iter() {
            if let Some(old_state) = self.interrupt_states.get_mut(isr_id) {
                *old_state = old_state.union(other_state);
            } else {
                self.interrupt_states.insert(isr_id.clone(), other_state.clone());
            }
        }
    }

    pub fn update_single_isr_state(&mut self, isr_id: DefId, state: IsrState) {
        self.interrupt_states.insert(isr_id, state);
    }

    pub fn get_disabled_isrs(&self) -> Vec<DefId> {
        self.interrupt_states.iter().filter(|(_, state)| **state == IsrState::Disabled).map(|(isr_id, _)| *isr_id).collect()
    }

    pub fn get_enabled_isrs(&self) -> Vec<DefId> {
        self.interrupt_states.iter().filter(|(_, state)| **state == IsrState::Enabled).map(|(isr_id, _)| *isr_id).collect()
    }
    
    pub fn is_all_bottom(&self) -> bool {
        self.interrupt_states.iter().all(|(_, state)| *state == IsrState::Bottom)
    }
}

impl Display for InterruptSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "Disabled: {:?}, Enabled: {:?}", self.get_disabled_isrs(), self.get_enabled_isrs())
    }
}

// 函数的ISR信息
#[derive(Debug, Clone)]
pub struct FunctionInterruptInfo {
    pub def_id: DefId,
    pub exit_interruptset: InterruptSet,
    pub bb_interruptsets: HashMap<BasicBlock, InterruptSet>,
    pub interrupt_enable_sites: Vec<OperationSite>,
}

impl PartialEq for FunctionInterruptInfo {
    fn eq(&self, other: &Self) -> bool {
        self.def_id == other.def_id &&
        self.exit_interruptset == other.exit_interruptset &&
        self.bb_interruptsets == other.bb_interruptsets &&
        self.interrupt_enable_sites == other.interrupt_enable_sites
    }
}

impl Display for FunctionInterruptInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} BBs in total, Exit: {}", self.bb_interruptsets.len(), self.exit_interruptset)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptApiType {
    Disable,
    Enable,
}

#[derive(Debug)]
pub struct ProgramIsrInfo {
    pub isr_entries: HashSet<DefId>, // 所有ISR入口函数(对应target_isr_entries)
    pub isr_funcs: HashMap<DefId, Vec<DefId>>, // 所有ISR及其可能的调用者
    pub function_interrupt_infos: HashMap<DefId, FunctionInterruptInfo>, // 每个函数的ISR信息
}

impl ProgramIsrInfo {
    pub fn new() -> Self {
        ProgramIsrInfo {
            isr_entries: HashSet::new(),
            isr_funcs: HashMap::new(),
            function_interrupt_infos: HashMap::new(),
        }
    }
}

// === Function Summary ===

// LockSite / InterrupteEnableSite
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OperationSite {
    pub object_def_id: DefId,
    pub func_def_id: DefId,
    pub bb_index: BasicBlock,
}

// M1: Map<LockSite, InterruptSet>
type PreemptSummary = HashMap<OperationSite, InterruptSet>;

// M2: Map<LockSite, LockSet>
type LockingSummary = HashMap<OperationSite, LockSet>;

#[derive(Debug, Clone)]
pub struct FunctionSummary {
    pub preempt_summary: PreemptSummary,
    pub locking_summary: LockingSummary,
}

impl FunctionSummary {
    pub fn new() -> Self {
        FunctionSummary {
            preempt_summary: PreemptSummary::new(),
            locking_summary: LockingSummary::new(),
        }
    }
}

impl Display for FunctionSummary {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "MayBePreempted: {:?}, MustHaveUnlocked: {:?}", self.preempt_summary, self.locking_summary)
    }
}

#[derive(Debug)]
pub struct ProgramFuncSummary {
    pub function_summaries: HashMap<DefId, FunctionSummary>,
}

impl ProgramFuncSummary {
    pub fn new() -> Self {
        ProgramFuncSummary {
            function_summaries: HashMap::new(),
        }
    }
}

// === ILG ===

#[derive(Debug, Clone)]
pub struct ILG {
    pub interrupt_edges: HashMap<OperationSite, OperationSite>,
    pub regular_edges: HashMap<DefId, DefId>,
}

impl ILG {
    pub fn new() -> Self {
        ILG { interrupt_edges: HashMap::new(), regular_edges: HashMap::new() }
    }
}