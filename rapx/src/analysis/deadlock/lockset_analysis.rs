use std::collections::{HashMap, HashSet};
use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::ty::{Interner, Ty, TyCtxt, TyKind};
use rustc_middle::mir::{Body, TerminatorKind, BasicBlock, Operand, Place, Local, Statement, StatementKind, Rvalue, LocalDecl};
use rustc_span::def_id::LocalDefId;
use rustc_span::source_map::Spanned;

use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn lockset_analysis(&mut self) {
        rap_info!("Starting Lockset Analysis...");
        
        // 初始化程序锁集信息
        let mut program_lock_info = ProgramLockInfo {
            lock_objects: HashMap::new(),
            lock_apis: HashMap::new(),
            function_lock_infos: HashMap::new(),
        };
        
        // 1. 收集锁对象
        self.collect_lock_objects(&mut program_lock_info);
        rap_info!("Collected {} lock objects", program_lock_info.lock_objects.len());
        
        // 2. 收集锁API
        self.collect_lock_apis(&mut program_lock_info);
        rap_info!("Collected {} lock APIs", program_lock_info.lock_apis.len());
        
        // 3. 分析每个函数的锁集
        let mut analyzed_count = 0;
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                self.analyze_function_lockset(def_id, &mut program_lock_info);
                analyzed_count += 1;
            }
        }
        rap_info!("Completed Lockset Analysis for {} functions", analyzed_count);

        self.program_lock_info = program_lock_info;
    }
    
    // 收集程序中的锁对象
    fn collect_lock_objects(&self, program_lock_info: &mut ProgramLockInfo) {
        // 从静态变量中查找锁对象
        rap_debug!("Collecting lock objects...");
        
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
                    rap_debug!("Found static lock object: {:?} type: {}", self.tcx.def_path_str(def_id), item_ty);
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
        for target_type in &self.target_lock_types {
            if type_str.contains(target_type) {
                return true;
            }
        }
        false
    }
    
    // 收集锁相关的API
    fn collect_lock_apis(&self, program_lock_info: &mut ProgramLockInfo) {
        rap_debug!("Collecting lock APIs...");
        
        // 遍历所有函数
        // NOTE: THIS IS CRATE LOCAL
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
                    rap_debug!("Found lock API: {:?}, lock state: {:?}", fn_name, lock_state);
                    
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
        rap_debug!("Analyzing function lockset: {}", func_name);
        
        let body = self.tcx.optimized_mir(func_def_id);
        
        // 初始化函数锁集信息
        let mut func_info = FunctionLockInfo {
            def_id: func_def_id,
            entry_lockset: LockSet::new(),
            exit_lockset: LockSet::new(),
            bb_locksets: HashMap::new(),
            call_sites: Vec::new(),
            lock_sites: Vec::new(),
            // TODO: 缓存alias_map和guard_map以供context_sensitive分析使用
        };
        
        // 初始化每个基本块的锁集
        for (bb_idx, _) in body.basic_blocks.iter_enumerated() {
            func_info.bb_locksets.insert(bb_idx, LockSet::new());
        }
        
        // 创建局部变量别名映射
        let mut local_lock_map: HashMap<Local, DefId> = HashMap::new();
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
            
            rap_debug!("Function {} Lockset Analysis Iteration #{}", func_name, iteration);
            
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
                            self.handle_assignment(place, rvalue, &mut local_lock_map, &mut local_guard_map, &mut dependency_map);
                        }
                        // 可以处理其他类型的语句...
                        _ => {}
                    }
                }
                
                // 处理基本块的终结语句
                if let Some(terminator) = &bb.terminator {
                    match &terminator.kind {
                        TerminatorKind::Call { func, args, destination, .. } => {
                            // TODO: 处理手动调用drop()的情况
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
                                if let Some((api_name, ..)) = program_lock_info.lock_apis.get(&func_def_id) {
                                    rap_debug!("Found lock API: {} in function {}", api_name, func_name);
                                    
                                    // 尝试确定操作的锁对象
                                    if let Some(lock_def_id) = self.resolve_lock_object_from_args(&args, &local_lock_map, &dependency_map) {
                                        rap_debug!("Lock API {} acts on lock object: {}", api_name, self.tcx.def_path_str(lock_def_id));
                                        current_lockset.update_lock_state(lock_def_id, LockState::MustHold);
                                        func_info.lock_sites.push(OperationSite {
                                            object_def_id: lock_def_id,
                                            func_def_id,
                                            bb_index: bb_idx,
                                        });

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
                        }
                        TerminatorKind::Drop { place, .. } => {
                            // 处理变量销毁，可能会释放锁
                            // TODO: 通过类型判断drop的是否真的是lockguard
                            if let Some(lock_def_id) = self.resolve_place_to_lockguard(&place, &local_guard_map, &dependency_map) {
                                // Drop lockguard 操作会释放对应的锁
                                rap_debug!("Detected lock {:?} released in function {}", self.tcx.def_path_str(lock_def_id), func_name);
                                current_lockset.update_lock_state(lock_def_id, LockState::MustNotHold);
                            }
                        }
                        TerminatorKind::Return { .. } => {
                            func_info.exit_lockset = current_lockset.clone();
                        }
                        _ => {}
                    }

                    // Propagate lockset to successors
                    for succ_bb in terminator.successors() {
                        let succ_set = func_info.bb_locksets.get_mut(&succ_bb).unwrap();
                        let old_set = succ_set.clone();
                        succ_set.merge(&current_lockset);
                        if &old_set != succ_set {
                            changed = true;
                        }
                    }
                }
                
                // 更新基本块的锁集
                if current_lockset != func_info.bb_locksets[&bb_idx] {
                    func_info.bb_locksets.insert(bb_idx, current_lockset);
                    changed = true;
                }
            }
        }
        
        program_lock_info.function_lock_infos.insert(func_def_id, func_info.clone());

        rap_debug!("Lockset Analysis for Function {} Completed", func_name);
        rap_debug!("DependencyMap: {:?}", dependency_map);
        rap_debug!("LockMap: {:?}", local_lock_map);
        rap_debug!("GuardMap: {:?}", local_guard_map);

        fn _print_bb_locksets(bb_locksets: &HashMap<BasicBlock, LockSet>) {
            let mut sorted_bb_locksets = bb_locksets.iter().collect::<Vec<_>>();
            sorted_bb_locksets.sort_by_key(|(bb_idx, _)| bb_idx.index());
            for (bb_idx, lockset) in sorted_bb_locksets {
                rap_info!("BasicBlock {} Lockset: {}", bb_idx.index(), lockset);
            }
        }
        // _print_bb_locksets(&func_info.bb_locksets);
    }
    
    // 处理赋值语句
    fn handle_assignment(&self,
                        place: &Place<'tcx>, 
                        rvalue: &Rvalue<'tcx>, 
                        lock_map: &mut HashMap<Local, DefId>,
                        guard_map: &mut HashMap<Local, DefId>,
                        dependency_map: &mut HashMap<Local, HashSet<Local>>) {
        match rvalue {
            Rvalue::Use(operand) => {
                // 处理简单赋值
                if let Some(lock_def_id) = self.resolve_operand_to_lock_object(operand, lock_map, dependency_map) {
                    lock_map.insert(place.local, lock_def_id);
                }
                if let Some(guard_def_id) = self.resolv_operand_to_lockguard(operand, guard_map, dependency_map) {
                    guard_map.insert(place.local, guard_def_id);
                }
                // 更新数据依赖图
                match operand {
                    Operand::Copy(r_place) | Operand::Move(r_place) => {
                        // 左边place依赖右边r_place
                        dependency_map.entry(place.local).or_insert(HashSet::new()).insert(r_place.local);
                    }
                    _ => {}
                }
            }
            Rvalue::Ref(_, _, borrowed_place) => {
                // 处理引用
                if let Some(lock_def_id) = self.resolve_place_to_lock_object(borrowed_place, lock_map, dependency_map) {
                    lock_map.insert(place.local, lock_def_id);
                }
                if let Some(guard_def_id) = self.resolve_place_to_lockguard(borrowed_place, guard_map, dependency_map) {
                    guard_map.insert(place.local, guard_def_id);
                }
                // 更新数据依赖图
                dependency_map.entry(place.local).or_insert(HashSet::new()).insert(borrowed_place.local);
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
                                    lock_map: &HashMap<Local, DefId>,
                                    dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        // 通常第一个参数是self引用，即锁对象
        if !args.is_empty() {
            return self.resolve_operand_to_lock_object(&args[0].node, lock_map, dependency_map);
        }
        None
    }
    
    // 从操作数解析出锁对象
    fn resolve_operand_to_lock_object(&self, 
                                     operand: &Operand<'tcx>, 
                                     lock_map: &HashMap<Local, DefId>,
                                     dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.resolve_place_to_lock_object(place, lock_map, dependency_map)
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

    fn resolv_operand_to_lockguard(&self, 
                                 operand: &Operand<'tcx>, 
                                 guard_map: &HashMap<Local, DefId>,
                                 dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.resolve_place_to_lockguard(place, guard_map, dependency_map)
            }
            _ => None,
        }
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
    
    // 输出分析结果
    pub fn print_lockset_analysis_results(&self) {
        let program_lock_info = &self.program_lock_info;
        rap_info!("==== Lockset Analysis Results ====");
        rap_info!("Found {} lock objects", program_lock_info.lock_objects.len());
        
        // 输出所有锁对象
        for (def_id, lock_obj) in &program_lock_info.lock_objects {
            rap_info!("Lock Object: {:?}, Type: {}, Is Static: {}", 
                     self.tcx.def_path_str(*def_id), 
                     lock_obj.lock_type, 
                     lock_obj.is_static);
        }
        
        // 输出每个函数的锁集
        for (func_def_id, func_info) in &program_lock_info.function_lock_infos {
            if func_info.exit_lockset.is_all_bottom() {
                // rap_info!("Function {} has no lock operations", self.tcx.def_path_str(*func_def_id));
                continue;
            }
            let func_name = self.tcx.def_path_str(*func_def_id);
            rap_info!("Function: {}", func_name);
            rap_info!("  Exit Lockset: {}", func_info.exit_lockset);
            
            // // 输出调用点
            // for (callee_id, _, _) in &func_info.call_sites {
            //     rap_info!("  Callsites: {}", self.tcx.def_path_str(*callee_id));
            // }
        }

        rap_info!("==== Lockset Analysis Results End ====");
    }
}

// TODO: 
// 1. 拆分代码为数个模块
// 2. 写一个测试库
// 3. dependency更精确的别名关系
// 4. 追踪从参数中传进的锁，例如enable_dma_remapping()

// 5. 结合CFG,构建临界区，计算M2