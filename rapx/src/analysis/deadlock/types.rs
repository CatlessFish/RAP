use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, BasicBlockData};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LockObject {
    pub def_id: DefId,     // The DefId of the lock variable
    pub lock_type: String, // The type of lock (Mutex/RwLock etc.)
    pub is_static: bool,   // Whether it's a static lock
    pub span: Span,        // Source code location
}

// Represents the type of lock
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LockType {
    ReadLocked,            // Read lock state
    WriteLocked,           // Write lock state
    UpgradeableReadLocked, // Upgradeable read lock state (specific to RwLock)
}

// Represents the state of a lock
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
// Represents the lockset within a function
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockSet {
    pub lock_states: HashMap<DefId, LockState>, // States of locks
}

// Implementing the default constructor for LockSet
impl LockSet {
    pub fn new() -> Self {
        LockSet {
            lock_states: HashMap::new(),
        }
    }

    // Merges two locksets (used at branch join points)
    // Usage: next_bb_lockstate.merge(&current_bb_lockstate)
    pub fn merge(&mut self, other: &LockSet) {
        for (lock_id, other_state) in other.lock_states.iter() {
            if let Some(old_state) = self.lock_states.get_mut(lock_id) {
                *old_state = old_state.union(other_state);
            } else {
                self.lock_states
                    .insert(lock_id.clone(), other_state.clone());
            }
        }
    }

    // Updates the state of a single lock
    pub fn update_lock_state(&mut self, lock_id: DefId, state: LockState) {
        self.lock_states.insert(lock_id, state);
    }

    // Gets the list of locks in must_hold state
    pub fn get_must_hold_locks(&self) -> Vec<DefId> {
        self.lock_states
            .iter()
            .filter(|(_, state)| **state == LockState::MustHold)
            .map(|(lock_id, _)| *lock_id)
            .collect()
    }

    // Gets the list of locks in may_hold state
    pub fn get_may_hold_locks(&self) -> Vec<DefId> {
        self.lock_states
            .iter()
            .filter(|(_, state)| **state == LockState::MayHold)
            .map(|(lock_id, _)| *lock_id)
            .collect()
    }

    // Gets the list of locks in must_not_hold state
    pub fn get_must_not_hold_locks(&self) -> Vec<DefId> {
        self.lock_states
            .iter()
            .filter(|(_, state)| **state == LockState::MustNotHold)
            .map(|(lock_id, _)| *lock_id)
            .collect()
    }

    // Checks if all locks are in Bottom state
    pub fn is_all_bottom(&self) -> bool {
        self.lock_states
            .iter()
            .all(|(_, state)| *state == LockState::Bottom)
    }
}

impl Display for LockSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MustHold: {:?}, MustNotHold: {:?}, MayHold: {:?}",
            self.get_must_hold_locks(),
            self.get_must_not_hold_locks(),
            self.get_may_hold_locks()
        )
    }
}

// Function's lockset information
#[derive(Debug, Clone)]
pub struct FunctionLockInfo {
    pub def_id: DefId,                             // Function ID
    pub entry_lockset: LockSet,                    // Entry point lockset
    pub exit_lockset: LockSet,                     // Exit point lockset
    pub bb_locksets: HashMap<BasicBlock, LockSet>, // Lockset for each basic block
    pub call_sites: Vec<(BasicBlock, DefId)>,      // Call site information
    pub lock_sites: Vec<OperationSite>,            // Lock site information
}

// Implementing PartialEq for FunctionLockInfo
impl PartialEq for FunctionLockInfo {
    fn eq(&self, other: &Self) -> bool {
        self.def_id == other.def_id
            && self.entry_lockset == other.entry_lockset
            && self.exit_lockset == other.exit_lockset
            && self.bb_locksets == other.bb_locksets
            && self.lock_sites == other.lock_sites
        // Ignoring comparison of call_sites as it's mainly used for intra-procedural analysis
    }
}

// Program-wide lock information
#[derive(Debug)]
pub struct ProgramLockInfo {
    pub lock_objects: HashMap<DefId, LockObject>, // All lock objects
    pub lock_apis: HashMap<DefId, (String, LockType)>, // All lock APIs and their impact on lock states
    pub function_lock_infos: HashMap<DefId, FunctionLockInfo>, // Lockset information for each function
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
    Enabled,  // May
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

// Represents an interrupt set
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterruptSet {
    pub interrupt_states: HashMap<DefId, IsrState>,
}

impl InterruptSet {
    pub fn new() -> Self {
        InterruptSet {
            interrupt_states: HashMap::new(),
        }
    }

    pub fn merge(&mut self, other: &InterruptSet) {
        for (isr_id, other_state) in other.interrupt_states.iter() {
            if let Some(old_state) = self.interrupt_states.get_mut(isr_id) {
                *old_state = old_state.union(other_state);
            } else {
                self.interrupt_states
                    .insert(isr_id.clone(), other_state.clone());
            }
        }
    }

    pub fn update_single_isr_state(&mut self, isr_id: DefId, state: IsrState) {
        self.interrupt_states.insert(isr_id, state);
    }

    pub fn get_disabled_isrs(&self) -> Vec<DefId> {
        self.interrupt_states
            .iter()
            .filter(|(_, state)| **state == IsrState::Disabled)
            .map(|(isr_id, _)| *isr_id)
            .collect()
    }

    pub fn get_enabled_isrs(&self) -> Vec<DefId> {
        self.interrupt_states
            .iter()
            .filter(|(_, state)| **state == IsrState::Enabled)
            .map(|(isr_id, _)| *isr_id)
            .collect()
    }

    pub fn is_all_bottom(&self) -> bool {
        self.interrupt_states
            .iter()
            .all(|(_, state)| *state == IsrState::Bottom)
    }
}

impl Display for InterruptSet {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Disabled: {:?}, Enabled: {:?}",
            self.get_disabled_isrs(),
            self.get_enabled_isrs()
        )
    }
}

// Function's ISR information
#[derive(Debug, Clone)]
pub struct FunctionInterruptInfo {
    pub def_id: DefId,
    pub exit_interruptset: InterruptSet,
    pub bb_interruptsets: HashMap<BasicBlock, InterruptSet>,
    pub interrupt_enable_sites: Vec<OperationSite>,
}

impl PartialEq for FunctionInterruptInfo {
    fn eq(&self, other: &Self) -> bool {
        self.def_id == other.def_id
            && self.exit_interruptset == other.exit_interruptset
            && self.bb_interruptsets == other.bb_interruptsets
            && self.interrupt_enable_sites == other.interrupt_enable_sites
    }
}

impl Display for FunctionInterruptInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} BBs in total, Exit: {}",
            self.bb_interruptsets.len(),
            self.exit_interruptset
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InterruptApiType {
    Disable,
    Enable,
}

#[derive(Debug)]
pub struct ProgramIsrInfo {
    pub isr_entries: HashSet<DefId>, // All ISR entry functions (corresponding to target_isr_entries)
    pub isr_funcs: HashMap<DefId, Vec<DefId>>, // All ISRs and their possible callers
    pub function_interrupt_infos: HashMap<DefId, FunctionInterruptInfo>, // ISR information for each function
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
            write!(
                f,
                "{:?} in {:?}",
                self.object_def_id,
                self.func_def_id.unwrap()
            )
        }
    }
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
        write!(
            f,
            "MayBePreempted: {:?}, MustHaveUnlocked: {:?}",
            self.preempt_summary, self.locking_summary
        )
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EdgeType {
    Interrupt,
    Regular,
}

#[derive(Debug, Clone)]
pub struct ILGEdge {
    pub source: OperationSite,
    pub target: OperationSite,
    pub edge_type: EdgeType,
}

impl Display for ILGEdge {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} --{:?}--> {}",
            self.source, self.edge_type, self.target
        )
    }
}

#[derive(Debug, Clone)]
pub struct ILG {
    pub edges: Vec<ILGEdge>,
}

impl ILG {
    pub fn new() -> Self {
        ILG { edges: Vec::new() }
    }
}
