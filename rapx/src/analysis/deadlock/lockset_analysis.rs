use std::collections::{HashMap, HashSet};
use std::fmt::{self, Formatter, Display};
use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::hir::ModuleItems;
use rustc_middle::ty::{Interner, Ty, TyCtxt, TyKind};
use rustc_middle::mir::{Body, TerminatorKind, BasicBlock, Operand, Place, Local, Statement, StatementKind, Rvalue, LocalDecl};
use rustc_span::def_id::LocalDefId;
use rustc_span::{Span, Symbol};
use rustc_span::source_map::Spanned;
use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};

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
//
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
        for (lock_id, state) in other.lock_states.iter() {
            self.update_lock_state(*lock_id, state.clone());
        }
    }

    // 更新单个锁的state
    fn update_lock_state(&mut self, lock_id: DefId, state: LockState) {
        if let Some(old_state) = self.lock_states.get_mut(&lock_id) {
            *old_state = old_state.intersect(&state);
        } else {
            self.lock_states.insert(lock_id, state);
        }
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
    alias_map: HashMap<Local, DefId>,              // 局部变量与锁对象的别名关系
    guard_map: HashMap<Local, DefId>,              // 局部变量与lockguard的别名关系
}

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn lockset_analysis(&self) {
        rap_debug!("开始进行锁集分析...");
        
        // 初始化程序锁集信息
        let mut program_lock_info = ProgramLockInfo {
            lock_objects: HashMap::new(),
            lock_apis: HashMap::new(),
            function_infos: HashMap::new(),
            alias_map: HashMap::new(),
            guard_map: HashMap::new(),
        };
        
        // 1. 收集锁对象
        self.collect_lock_objects(&mut program_lock_info);
        rap_debug!("收集到 {} 个锁对象", program_lock_info.lock_objects.len());
        
        // 2. 收集锁API
        self.collect_lock_apis(&mut program_lock_info);
        rap_debug!("收集到 {} 个锁相关API", program_lock_info.lock_apis.len());
        
        // 3. 分析每个函数的锁集
        let mut analyzed_count = 0;
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                self.analyze_function_lockset(def_id, &mut program_lock_info);
                analyzed_count += 1;
            }
        }
        rap_debug!("完成对 {} 个函数的锁集分析", analyzed_count);
        
        // // 4. 进行过程间分析
        // self.interprocedural_analysis(&mut program_lock_info);
        // rap_debug!("完成过程间锁集分析");
        
        // 输出分析结果
        self.output_analysis_results(&program_lock_info);
    }
    
    // 收集程序中的锁对象
    fn collect_lock_objects(&self, program_lock_info: &mut ProgramLockInfo) {
        // 从静态变量中查找锁对象
        rap_debug!("开始收集锁对象...");
        
        // 扫描所有模块项 - 注意使用正确的API
        let module_items = self.tcx.hir_crate_items(());
        
        // 这里需要根据具体rustc版本选择合适的方法遍历所有项
        // 以下是一个通用方法的示例
        for item_id in self.tcx.hir().items() {
            let def_id = item_id.owner_id.to_def_id();
            let def_kind = self.tcx.def_kind(def_id);
            
            // 检查是否是static
            if let DefKind::Static{safety:_, mutability:_, nested:_} = def_kind {
                let item_ty = self.tcx.type_of(def_id).instantiate_identity();
                if self.is_target_lock_type(item_ty) {
                    let lock_obj = LockObject {
                        def_id,
                        lock_type: item_ty.to_string(),
                        is_static: true,
                        span: self.tcx.def_span(def_id),
                    };
                    
                    program_lock_info.lock_objects.insert(def_id, lock_obj);
                    rap_debug!("发现静态锁对象: {:?} 类型: {}", self.tcx.def_path_str(def_id), item_ty);
                }
            }
        }
        
        // 也可以扫描全局函数中的局部锁对象，但优先关注static锁
        // ...
    }
    
    // 检查类型是否是目标锁类型
    fn is_target_lock_type(&self, ty: Ty<'tcx>) -> bool {
        let type_str = ty.to_string();
        // rap_debug!("检查类型: {}", type_str);
        for target_type in &self.target_types {
            if type_str.contains(target_type) {
                return true;
            }
        }
        false
    }
    
    // 收集锁相关的API
    fn collect_lock_apis(&self, program_lock_info: &mut ProgramLockInfo) {
        rap_debug!("开始收集锁API...");
        
        // 遍历所有函数
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            let fn_name = self.tcx.def_path_str(def_id);
            
            // 检查是否是目标锁API
            for &(api_name, lock_state_str) in &self.target_lock_apis {
                if fn_name.contains(api_name) {
                    // 确定锁状态
                    let lock_state = match lock_state_str {
                        "read" => LockType::ReadLocked,
                        "write" => LockType::WriteLocked,
                        "upgradable_read" => LockType::UpgradeableReadLocked,
                        _ => LockType::WriteLocked, // 默认为写锁
                    };
                    
                    program_lock_info.lock_apis.insert(def_id, (fn_name.clone(), lock_state.clone()));
                    rap_debug!("发现锁API: {:?}, 锁状态: {:?}", fn_name, lock_state);
                    
                    // 找到匹配后不需要继续检查其他API
                    break;
                }
            }
        }
    }
    
    // 分析函数的锁集
    fn analyze_function_lockset(&self, func_def_id: DefId, program_lock_info: &mut ProgramLockInfo) {
        /* filter const mir */
        if let Some(_other) = self.tcx.hir().body_const_context(func_def_id) {
            return;
        }
        
        let func_name = self.tcx.def_path_str(func_def_id);
        rap_debug!("分析函数锁集: {}", func_name);
        
        let body = self.tcx.optimized_mir(func_def_id);
        
        // 初始化函数锁集信息
        let mut func_info = FunctionLockInfo {
            def_id: func_def_id,
            entry_lockset: LockSet::new(),
            exit_lockset: LockSet::new(),
            bb_locksets: HashMap::new(),
            call_sites: Vec::new(),
        };

        fn print_bb_locksets(bb_locksets: &HashMap<BasicBlock, LockSet>) {
            let mut sorted_bb_locksets = bb_locksets.iter().collect::<Vec<_>>();
            sorted_bb_locksets.sort_by_key(|(bb_idx, _)| bb_idx.index());
            for (bb_idx, lockset) in sorted_bb_locksets {
                rap_info!("基本块 {} 锁集: {}", bb_idx.index(), lockset);
            }
        }
        
        // 初始化每个基本块的锁集
        for (bb_idx, _) in body.basic_blocks.iter_enumerated() {
            func_info.bb_locksets.insert(bb_idx, LockSet::new());
        }
        
        // 创建局部变量别名映射
        let mut local_alias_map = HashMap::new(); // QUESTION: alias_map and local_alias_map?
        let mut local_guard_map: HashMap<Local, DefId> = HashMap::new();

        // 创建依赖关系映射，跟踪嵌套在其他类型中的锁
        // a-> [b, c] 表示a依赖b和c
        let mut dependency_map: HashMap<Local, HashSet<Local>> = HashMap::new();
        
        // 固定点迭代计算锁集
        let mut changed = true;
        let mut iteration = 0;
        let max_iterations = 10; // 防止无限循环
        
        while changed && iteration < max_iterations {
            changed = false;
            iteration += 1;
            
            rap_debug!("函数 {} 锁集分析迭代 #{}", func_name, iteration);
            
            for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
                let mut current_lockset = if bb_idx.index() == 0 {
                    // 起始基本块使用函数入口锁集
                    func_info.entry_lockset.clone()
                } else {
                    // 其他基本块使用当前状态
                    func_info.bb_locksets[&bb_idx].clone()
                };
                
                // 分析基本块中的每条语句
                for stmt in &bb.statements {
                    match &stmt.kind {
                        StatementKind::Assign(box(place, rvalue)) => {
                            // 处理赋值语句，检查是否是锁相关操作
                            self.handle_assignment(&mut current_lockset, place, rvalue, &mut local_alias_map, &mut local_guard_map, &mut dependency_map, program_lock_info);
                        }
                        // 可以处理其他类型的语句...
                        _ => {}
                    }
                }
                
                // 处理基本块的终结语句
                if let Some(terminator) = &bb.terminator {
                    match &terminator.kind {
                        TerminatorKind::Call { func, args, destination, target, .. } => {
                            // 处理函数调用
                            if let Some(func_def_id) = self.resolve_function_call(func) {
                                // 更新dependency_map
                                let l_place = destination.local;
                                for arg in args {
                                    let arg_operand = &arg.node;
                                    if let Operand::Copy(r_place) | Operand::Move(r_place) = arg_operand {
                                        dependency_map.entry(l_place).or_insert(HashSet::new()).insert(r_place.local);
                                    }
                                }

                                // 检查是否是锁API
                                if let Some((api_name, lock_state)) = program_lock_info.lock_apis.get(&func_def_id) {
                                    rap_info!("函数 {} 中发现锁API调用: {}", func_name, api_name);
                                    
                                    // 尝试确定操作的锁对象
                                    if let Some(lock_def_id) = self.resolve_lock_object_from_args(&args, &local_alias_map, &dependency_map, program_lock_info) {
                                        rap_info!("  锁API作用于锁对象: {:?}", self.tcx.def_path_str(lock_def_id));
                                        current_lockset.update_lock_state(lock_def_id, LockState::MustHold);

                                        // 处理锁API调用结果的别名关系
                                        // destination指向返回的lockguard
                                        local_guard_map.insert(l_place, lock_def_id);
                                    }
                                }
                                
                                // 记录调用点
                                func_info.call_sites.push((
                                    func_def_id,
                                    terminator.source_info.span,
                                    current_lockset.clone()
                                ));

                            }

                            // 传递lockset到下一个bb
                            if let Some(next_bb_idx) = target {
                                let target_lockset = func_info.bb_locksets.get_mut(&next_bb_idx).unwrap();
                                let old_target = target_lockset.clone();
                                target_lockset.merge(&current_lockset);
                                if &old_target != target_lockset {
                                    changed = true;
                                }
                            }

                            // TODO: Unwind
                        }
                        TerminatorKind::Drop { place,target, .. } => {
                            // 处理变量销毁，可能会释放锁
                            if let Some(lock_def_id) = self.resolve_place_to_lockguard(&place, &local_guard_map, &dependency_map) {
                                // Drop lockguard 操作会释放对应的锁
                                rap_debug!("在函数 {} 中检测到锁 {:?} 被释放", func_name, self.tcx.def_path_str(lock_def_id));
                                current_lockset.update_lock_state(lock_def_id, LockState::MustNotHold);
                            }
                            let target_lockset = func_info.bb_locksets.get_mut(target).unwrap();
                            let old_target = target_lockset.clone();
                            target_lockset.merge(&current_lockset);
                            if &old_target != target_lockset {
                                changed = true;
                            }
                        }
                        TerminatorKind::Goto { target } => {
                            // 处理无条件跳转
                            let target_lockset = func_info.bb_locksets.get_mut(target).unwrap();
                            let old_target = target_lockset.clone();
                            target_lockset.merge(&current_lockset);
                            if &old_target != target_lockset {
                                changed = true;
                            }
                        }
                        TerminatorKind::SwitchInt { targets, .. } => {
                            // 处理条件分支
                            for target in targets.all_targets() {
                                let target_lockset = func_info.bb_locksets.get_mut(target).unwrap();
                                let old_target = target_lockset.clone();
                                target_lockset.merge(&current_lockset);
                                if &old_target != target_lockset {
                                    changed = true;
                                }
                            }
                        }
                        TerminatorKind::Return => {
                            // 处理函数返回
                            let old_exit = func_info.exit_lockset.clone();
                            func_info.exit_lockset.merge(&current_lockset);
                            if old_exit != func_info.exit_lockset {
                                changed = true;
                            }
                        }
                        // 处理其他终结语句...
                        _ => {}
                    }
                }
                
                // 更新基本块的锁集
                if current_lockset != func_info.bb_locksets[&bb_idx] {
                    func_info.bb_locksets.insert(bb_idx, current_lockset);
                    changed = true;
                }
            }
        }
        
        // 合并局部别名映射到全局别名映射
        for (local, lock_def_id) in local_alias_map.clone() {
            program_lock_info.alias_map.insert(local.clone(), lock_def_id.clone());
        }
        
        program_lock_info.function_infos.insert(func_def_id, func_info.clone());
        rap_debug!("函数 {} 锁集分析完成别名结果: {:?}，依赖关系: {:?}", func_name, local_alias_map, dependency_map);
        rap_info!("函数 {} 锁集分析完成", func_name);
        print_bb_locksets(&func_info.bb_locksets);
    }
    
    // 处理赋值语句
    fn handle_assignment(&self, 
                        lockset: &mut LockSet, 
                        place: &Place<'tcx>, 
                        rvalue: &Rvalue<'tcx>, 
                        alias_map: &mut HashMap<Local, DefId>,
                        guard_map: &mut HashMap<Local, DefId>,
                        dependency_map: &mut HashMap<Local, HashSet<Local>>,
                        program_lock_info: &ProgramLockInfo) {
        match rvalue {
            Rvalue::Use(operand) => {
                // 处理简单赋值，传递别名关系
                if let Some(lock_def_id) = self.resolve_operand_to_lock_object(operand, alias_map, dependency_map, program_lock_info) {
                    alias_map.insert(place.local, lock_def_id);
                }
                // 更新数据依赖图，追踪嵌套在其他类型中的锁
                match operand {
                    Operand::Copy(r_place) | Operand::Move(r_place) => {
                        // 左边place依赖右边r_place
                        dependency_map.entry(place.local).or_insert(HashSet::new()).insert(r_place.local);
                    }
                    _ => {}
                }
            }
            Rvalue::Ref(_, _, borrowed_place) => {
                // 处理引用，传递别名关系
                if let Some(lock_def_id) = self.resolve_place_to_lock_object(borrowed_place, alias_map, dependency_map) {
                    alias_map.insert(place.local, lock_def_id);
                }
            }
            // 处理其他类型的右值...
            _ => {}
        }
    }
    
    // 从函数调用中解析出函数DefId
    fn resolve_function_call(&self, func: &Operand<'tcx>) -> Option<DefId> {
        // 尝试从操作数中解析出函数
        if let Some(callee) = func.const_fn_def() {
            // rap_debug!("解析出函数: {}", self.tcx.def_path_str(callee.0));
            return Some(callee.0);
        }
        None
    }
    
    // 从参数中解析出锁对象
    fn resolve_lock_object_from_args(&self, 
                                    args: &Box<[Spanned<Operand<'tcx>>]>, 
                                    alias_map: &HashMap<Local, DefId>,
                                    dependency_map: &HashMap<Local, HashSet<Local>>,
                                    program_lock_info: &ProgramLockInfo) -> Option<DefId> {
        // 通常第一个参数是self引用，即锁对象
        if !args.is_empty() {
            return self.resolve_operand_to_lock_object(&args[0].node, alias_map, dependency_map, program_lock_info);
        }
        None
    }
    
    // 从操作数解析出锁对象
    fn resolve_operand_to_lock_object(&self, 
                                     operand: &Operand<'tcx>, 
                                     alias_map: &HashMap<Local, DefId>,
                                     dependency_map: &HashMap<Local, HashSet<Local>>,
                                     program_lock_info: &ProgramLockInfo) -> Option<DefId> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.resolve_place_to_lock_object(place, alias_map, dependency_map)
            }
            Operand::Constant(constant) => {
                // 是否Static变量会走这里？
                if let Some(def_id) = constant.check_static_ptr(self.tcx) {
                    Some(def_id)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    
    // 从Place解析出可能引用的锁对象
    fn resolve_place_to_lock_object(&self, 
                                   place: &Place<'tcx>, 
                                   alias_map: &HashMap<Local, DefId>,
                                   dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        // 检查是否有别名映射
        if let Some(&lock_def_id) = alias_map.get(&place.local) {
            return Some(lock_def_id);
        }

        // 检查是否是嵌套的锁
        // 在dependency_map上dfs，匹配已知的锁
        let mut visited = HashSet::new();
        let mut stack = vec![place.local];
        while let Some(current) = stack.pop() {
            if visited.insert(current) {
                if let Some(dependencies) = dependency_map.get(&current) {
                    for dependency in dependencies {
                        if let Some(&lock_def_id) = alias_map.get(dependency) {
                            return Some(lock_def_id);
                        }
                        stack.push(*dependency);
                    }
                }
            }
        }
        
        // 是否直接使用static变量
        
        
        None
    }
    
    // 从Place解析出可能引用的lockguard
    fn resolve_place_to_lockguard(&self, 
                                 place: &Place<'tcx>, 
                                 local_guard_map: &HashMap<Local, DefId>,
                                 dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        // 检查是否有别名映射
        if let Some(&lock_def_id) = local_guard_map.get(&place.local) {
            return Some(lock_def_id);
        }

        // 追踪依赖关系
        let mut visited = HashSet::new();
        let mut stack = vec![place.local];
        while let Some(current) = stack.pop() {
            if visited.insert(current) {
                if let Some(dependencies) = dependency_map.get(&current) {
                    for dependency in dependencies {
                        if let Some(&lock_def_id) = local_guard_map.get(dependency) {
                            return Some(lock_def_id);
                        }
                        stack.push(*dependency);
                    }
                }
            }
        }
        
        None
    }
    
    // 过程间分析
    fn interprocedural_analysis(&self, program_lock_info: &mut ProgramLockInfo) {
        rap_debug!("开始进行过程间锁集分析...");
        
        let mut worklist: Vec<DefId> = program_lock_info.function_infos.keys().cloned().collect();
        let mut changed = true;
        let mut iteration = 0;
        let max_iterations = 5; // 限制迭代次数
        
        while changed && iteration < max_iterations {
            changed = false;
            iteration += 1;
            rap_debug!("过程间分析迭代 #{}", iteration);
            
            let current_worklist = worklist.clone();
            worklist.clear();
            
            for caller_def_id in current_worklist {
                let mut caller_info = program_lock_info.function_infos[&caller_def_id].clone();
                let caller_name = self.tcx.def_path_str(caller_def_id);
                let mut caller_changed = false;
                
                // 对每个调用点进行分析
                for (callee_id, span, call_lockset) in &caller_info.call_sites {
                    if let Some(callee_info) = program_lock_info.function_infos.get(callee_id) {
                        let callee_name = self.tcx.def_path_str(*callee_id);
                        rap_debug!("分析函数 {} 调用 {}", caller_name, callee_name);
                        
                        // 从调用点锁集和被调用函数的出口锁集推导调用后的锁集
                        let mut post_call_lockset = call_lockset.clone();
                        
                        // 合并被调用函数的出口锁集
                        post_call_lockset.merge(&callee_info.exit_lockset);
                        
                        // 更新调用者函数的基本块锁集
                        // 这里简化处理，实际上需要找到调用点所在的基本块和后继基本块
                        for (bb_idx, bb_lockset) in &mut caller_info.bb_locksets {
                            let old_lockset = bb_lockset.clone();
                            bb_lockset.merge(&post_call_lockset);
                            if old_lockset != *bb_lockset {
                                caller_changed = true;
                            }
                        }
                    }
                }
                
                // 如果有变化，更新函数信息并加入工作列表
                if caller_changed {
                    program_lock_info.function_infos.insert(caller_def_id, caller_info);
                    worklist.push(caller_def_id);
                    changed = true;
                }
            }
        }
        
        rap_debug!("过程间分析完成，共进行 {} 次迭代", iteration);
    }
    
    // 输出分析结果
    fn output_analysis_results(&self, program_lock_info: &ProgramLockInfo) {
        rap_info!("==== 锁集分析结果 ====");
        rap_info!("发现 {} 个锁对象", program_lock_info.lock_objects.len());
        
        // 输出所有锁对象
        // for (def_id, lock_obj) in &program_lock_info.lock_objects {
        //     rap_info!("锁对象: {:?}, 类型: {}, 是否静态: {}", 
        //              self.tcx.def_path_str(*def_id), 
        //              lock_obj.lock_type, 
        //              lock_obj.is_static);
        // }
        
        // 输出每个函数的锁集
        // for (func_def_id, func_info) in &program_lock_info.function_infos {
        //     let func_name = self.tcx.def_path_str(*func_def_id);
        //     rap_info!("\n函数: {}", func_name);
            
        //     // 输出出口锁集
        //     rap_info!("  出口锁集:");
        //     rap_info!("    必然持有: {}", self.format_lockset(&func_info.exit_lockset.must_hold));
        //     rap_info!("    可能持有: {}", self.format_lockset(&func_info.exit_lockset.may_hold));
            
        //     // 输出调用点
        //     for (callee_id, _, _) in &func_info.call_sites {
        //         rap_info!("  调用: {}", self.tcx.def_path_str(*callee_id));
        //     }
        // }
    }
    
    // 格式化锁集用于输出
    fn format_lockset(&self, lockset: &HashMap<DefId, LockType>) -> String {
        if lockset.is_empty() {
            return "无".to_string();
        }
        
        let mut result = Vec::new();
        for (lock_id, state) in lockset {
            let state_str = match state {
                LockType::ReadLocked => "读锁",
                LockType::WriteLocked => "写锁",
                LockType::UpgradeableReadLocked => "可升级读锁",
            };
            result.push(format!("{}({})", self.tcx.def_path_str(*lock_id), state_str));
        }
        
        result.join(", ")
    }
}

// TODO: 
// 1. 拆分代码为数个模块
// 2. 写一个测试库

// 3. 追踪lockguard
// 4. 追踪类似于Once<SpinLock>的情况，比如b = a.get()，a是Once<SpinLock>，b是SpinLock, 思路：data_dependency + type match
// 5. 追踪从参数中传进的锁，例如enable_dma_remapping()