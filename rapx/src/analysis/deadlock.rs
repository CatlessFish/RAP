pub mod isr_analysis;
pub mod lockset_analysis;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use std::fmt::{self, Formatter, Display};
use rustc_span::{Span, Symbol};
use std::collections::{HashMap, HashSet};
use rustc_middle::mir::{BasicBlock, TerminatorKind};
use crate::{rap_info, rap_debug};
use crate::utils::source::get_fn_name;


// 表示一个锁对象
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LockObject {
    def_id: DefId,          // 锁变量的DefId
    lock_type: String,      // 锁的类型（Mutex/RwLock等）
    is_static: bool,        // 是否是静态锁
    span: Span,             // 源码位置
}

// 表示锁的类型
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LockType {
    ReadLocked,             // 读锁状态
    WriteLocked,            // 写锁状态
    UpgradeableReadLocked,  // 可升级读锁状态（RwLock特有）
}

// 表示锁的状态
// MayHold
// MustHold, MustNotHold
// Bottom
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LockState {
    Bottom,
    MustHold,
    MustNotHold,
    MayHold,
}

impl LockState {
    fn union(&self, other: &LockState) -> LockState {
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

    fn intersect(&self, other: &LockState) -> LockState {
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
struct LockSet {
    lock_states: HashMap<DefId, LockState>, // 锁的状态
}

// 为LockSet实现默认构造函数
impl LockSet {
    fn new() -> Self {
        LockSet {
            lock_states: HashMap::new(),
        }
    }
    
    // 合并两个锁集（用于分支汇合点）
    // Usage: next_bb_lockstate.merge(&current_bb_lockstate)
    fn merge(&mut self, other: &LockSet) {
        for (lock_id, other_state) in other.lock_states.iter() {
            if let Some(old_state) = self.lock_states.get_mut(lock_id) {
                *old_state = old_state.union(other_state);
            } else {
                self.lock_states.insert(lock_id.clone(), other_state.clone());
            }
        }
    }

    // 更新单个锁的state
    fn update_lock_state(&mut self, lock_id: DefId, state: LockState) {
        self.lock_states.insert(lock_id, state);
    }

    // 获取must_hold的锁列表
    fn get_must_hold_locks(&self) -> Vec<DefId> {
        self.lock_states.iter().filter(|(_, state)| **state == LockState::MustHold).map(|(lock_id, _)| *lock_id).collect()
    }

    // 获取may_hold的锁列表
    fn get_may_hold_locks(&self) -> Vec<DefId> {
        self.lock_states.iter().filter(|(_, state)| **state == LockState::MayHold).map(|(lock_id, _)| *lock_id).collect()
    }
    
    // 获取must_not_hold的锁列表
    fn get_must_not_hold_locks(&self) -> Vec<DefId> {
        self.lock_states.iter().filter(|(_, state)| **state == LockState::MustNotHold).map(|(lock_id, _)| *lock_id).collect()
    }

    // 判断是否所有锁都是Bottom
    fn is_all_bottom(&self) -> bool {
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
struct FunctionLockInfo {
    def_id: DefId,                                // 函数ID
    entry_lockset: LockSet,                       // 入口锁集
    exit_lockset: LockSet,                        // 出口锁集
    bb_locksets: HashMap<BasicBlock, LockSet>,    // 每个基本块的锁集
    call_sites: Vec<(DefId, Span, LockSet)>,      // 调用点信息
}

// 为FunctionLockInfo实现PartialEq
impl PartialEq for FunctionLockInfo {
    fn eq(&self, other: &Self) -> bool {
        self.def_id == other.def_id &&
        self.entry_lockset == other.entry_lockset &&
        self.exit_lockset == other.exit_lockset &&
        self.bb_locksets == other.bb_locksets
        // 忽略call_sites比较，因为它主要用于过程内分析
    }
}

// 程序全局锁信息
#[derive(Debug)]
struct ProgramLockInfo {
    lock_objects: HashMap<DefId, LockObject>,      // 所有锁对象
    lock_apis: HashMap<DefId, (String, LockType)>, // 所有锁API及其对锁状态的影响
    function_infos: HashMap<DefId, FunctionLockInfo>, // 每个函数的锁集信息
}

pub struct DeadlockDetection<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub target_types: Vec<&'tcx str>,
    pub target_lock_apis: Vec<(&'tcx str, &'tcx str)>,
}

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            target_types: vec![
                "sync::mutex::Mutex",
                "sync::rwlock::RwLock",
                "sync::rwmutex::RwMutex",
                "sync::spin::SpinLock",
            ],
            target_lock_apis: vec![
                ("sync::spin::SpinLock::<T, G>::lock", "write"),
                ("sync::spin::SpinLock::<T, G>::lock_arc", "write"),
                ("sync::rwlock::RwLock::<T>::read", "read"),
                ("sync::rwlock::RwLock::<T>::read_arc", "read"),
                ("sync::rwlock::RwLock::<T>::write", "write"),
                ("sync::rwlock::RwLock::<T>::write_arc", "write"),
                ("sync::mutex::Mutex::<T>::lock", "write"),
                ("sync::mutex::Mutex::<T>::lock_arc", "write"),
                ("sync::rwmutex::RwMutex::<T>::read", "read"),
                ("sync::rwmutex::RwMutex::<T>::write", "write"),
                ("sync::rwmutex::RwMutex::<T>::upread", "upgradable_read"),
            ],
        }
    }
    pub fn start(&self) {
        rap_info!("Executing Deadlock Detection");

        // Steps:
        // 1. Identify ISRs and Analysis InterruptSet
        self.collect_isr();

        // TODO: consider alias
        // 2. Analysis LockSet
        self.lockset_analysis();

        // 3. Computes Function Summary

        // 4. Construct Lock Graph

        // 5. Detect Cycles on Lock Graph
    }
}

