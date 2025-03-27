use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;


use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};
// use crate::utils::source::get_fn_name;


impl<'tcx> DeadlockDetection<'tcx> {
    pub fn isr_analysis(&mut self) {
        // Steps:
        // 1. Collect a set of ISRs
        self.collect_isr();
        rap_info!("Collected {} ISRs", self.program_isr_info.isr_funcs.len());

        // 2. Calculate interrupt sets for each function
        // This step is inter-procedural
        self.calculate_function_interrupt_sets();

        // 3. Print interrupt sets for each function
        self.print_function_interrupt_sets();
    }

    fn collect_isr(&mut self) {
        // collect def_id of target_isr_entries
        let mut isr_def_ids: HashMap<String, DefId> = HashMap::new();
        // NOTE: THIS IS CRATE LOCAL
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            let fn_name = self.tcx.def_path_str(def_id);
            if self.target_isr_entries.contains(&fn_name.as_str()) {
                isr_def_ids.insert(fn_name.clone(), def_id);
            }
        }

        self.program_isr_info.isr_entries = isr_def_ids.values().cloned().collect();

        // Start from self.target_isr_entries,
        // traverse self.call_graph.graph to find all possible callees
        // and mark them as ISRs

        // callee -> possible callers
        let mut isr_info: HashMap<DefId, Vec<DefId>> = HashMap::new();
        for &isr_entry in self.target_isr_entries.iter() {
            if let Some(isr_def_id) = isr_def_ids.get(isr_entry) {
                if let Some(callees) = self.call_graph.graph.get_callees_defid_recursive(&isr_entry.to_string()) {
                    for callee in callees {
                        isr_info.entry(callee).or_insert(Vec::new()).push(isr_def_id.clone());
                    }
                }
            }
        }

        for (callee, callers) in isr_info.iter() {
            rap_debug!("Function {} may be called by ISRs: {:?}", self.tcx.def_path_str(callee), callers);
        }

        self.program_isr_info.isr_funcs = isr_info;
    }

    fn calculate_function_interrupt_sets(&mut self) {
        rap_info!("Calculating function interrupt sets...");
        
        // 记录已分析的函数的出口中断集
        let mut analyzed_functions: HashMap<DefId, FunctionInterruptInfo> = HashMap::new();
        // 记录递归栈，防止循环
        let mut recursion_stack: HashSet<DefId> = HashSet::new();
        
        // 遍历所有函数
        for local_def_id in self.tcx.hir().body_owners() {
            /* filter const mir */
            if let Some(_other) = self.tcx.hir().body_const_context(local_def_id) {
                continue;
            }

            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                self.analyze_function_interrupt_set(
                    def_id,
                    &mut analyzed_functions,
                    &mut recursion_stack
                );
            }
        }
        
        // 将结果保存到program_isr_info中
        for (def_id, func_info) in analyzed_functions {
            self.program_isr_info.function_interrupt_infos.insert(def_id, func_info);
        }
    }

    fn analyze_function_interrupt_set(
        &self,
        func_def_id: DefId,
        analyzed_functions: &mut HashMap<DefId, FunctionInterruptInfo>,
        recursion_stack: &mut HashSet<DefId>
    ) -> FunctionInterruptInfo {
        // 如果函数已经分析过，直接返回结果
        if let Some(exit_set) = analyzed_functions.get(&func_def_id) {
            return exit_set.clone();
        }
        
        let body: &Body = self.tcx.optimized_mir(func_def_id);
        let mut bb_interrupt_sets: HashMap<BasicBlock, InterruptSet> = HashMap::new();
        
        // 初始化每个基本块的中断集
        for (bb_idx, _) in body.basic_blocks.iter_enumerated() {
            bb_interrupt_sets.insert(bb_idx, InterruptSet::new());
        }
        
        // 检查是否在递归栈中
        if recursion_stack.contains(&func_def_id) {
            rap_debug!("Detected recursion for function {}, returning empty set", 
                self.tcx.def_path_str(func_def_id));
            return FunctionInterruptInfo {
                def_id: func_def_id,
                exit_interruptset: InterruptSet::new(),
                bb_interruptsets: bb_interrupt_sets,
            };
        }
        
        // 将当前函数加入递归栈
        recursion_stack.insert(func_def_id);
        
        // 固定点迭代
        let mut changed = true;
        let mut iteration = 0;
        let max_iterations = 10;
        
        while changed && iteration < max_iterations {
            changed = false;
            iteration += 1;
            
            for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
                let mut current_set = if bb_idx.index() == 0 {
                    InterruptSet::new()
                } else {
                    bb_interrupt_sets[&bb_idx].clone()
                };
                
                // 处理基本块的终结语句
                if let Some(terminator) = &bb.terminator {
                    if let TerminatorKind::Call { func, target, .. } = &terminator.kind {
                        if let Some(callee_def_id) = func.const_fn_def() {
                            let callee_name = self.tcx.def_path_str(callee_def_id.0);
                            
                            // 检查是否是中断API
                            let mut found_api = false;
                            for &(api_name, api_type) in &self.target_interrupt_apis {
                                if callee_name.contains(api_name) {
                                    found_api = true;
                                    // 更新所有ISR的状态
                                    for &isr_def_id in &self.program_isr_info.isr_entries {
                                        match api_type {
                                            InterruptApiType::Enable => {
                                                current_set.update_single_isr_state(isr_def_id, IsrState::Enabled);
                                            }
                                            InterruptApiType::Disable => {
                                                current_set.update_single_isr_state(isr_def_id, IsrState::Disabled);
                                            }
                                        }
                                    }
                                    break;
                                }
                            }
                            
                            // 如果不是中断API，检查是否是普通函数调用
                            if !found_api && self.tcx.is_mir_available(callee_def_id.0) {
                                // 递归分析被调用函数
                                let callee_func_info = self.analyze_function_interrupt_set(
                                    callee_def_id.0,
                                    analyzed_functions,
                                    recursion_stack
                                );
                                // 合并被调用函数的出口中断集
                                current_set.merge(&callee_func_info.exit_interruptset);
                            }

                            if found_api {
                                rap_debug!("Function {} {:?} calls an interrupt API, current set: {}", 
                                    self.tcx.def_path_str(func_def_id), bb_idx, current_set);
                            }
                        }
                        
                        // 更新后继基本块的中断集
                        if let Some(next_bb) = target {
                            let target_set = bb_interrupt_sets.get_mut(next_bb).unwrap();
                            let old_set = target_set.clone();
                            target_set.merge(&current_set);
                            if &old_set != target_set {
                                changed = true;
                            }
                        }
                    }

                    // 更新后继基本块的中断集
                    for succ_bb in terminator.successors() {
                        let succ_set = bb_interrupt_sets.get_mut(&succ_bb).unwrap();
                        let old_set = succ_set.clone();
                        succ_set.merge(&current_set);
                        if &old_set != succ_set {
                            changed = true;
                        }
                    }
                }
                
                // 更新当前基本块的中断集
                let old_set = bb_interrupt_sets[&bb_idx].clone();
                bb_interrupt_sets.insert(bb_idx, current_set);
                if old_set != bb_interrupt_sets[&bb_idx] {
                    changed = true;
                }
            }
        }
        
        // 计算函数的出口中断集
        let mut exit_set = InterruptSet::new();
        for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
            if let Some(terminator) = &bb.terminator {
                if let TerminatorKind::Return = terminator.kind {
                    // 找到返回语句，合并该基本块的中断集到出口集
                    exit_set.merge(&bb_interrupt_sets[&bb_idx]);
                }
            }
        }
        
        // 从递归栈中移除当前函数
        recursion_stack.remove(&func_def_id);
        
        // 保存并返回结果
        let result = FunctionInterruptInfo {
            def_id: func_def_id,
            exit_interruptset: exit_set.clone(),
            bb_interruptsets: bb_interrupt_sets,
        };
        analyzed_functions.insert(func_def_id, result.clone());
        result
    }
    
    fn print_function_interrupt_sets(&self) {
        for (def_id, func_info) in self.program_isr_info.function_interrupt_infos.iter() {
            rap_info!("Function {} interrupt set: {}", self.tcx.def_path_str(def_id), func_info);
        }
    }
}

// TODO:
// 1. Support nested disable_local()