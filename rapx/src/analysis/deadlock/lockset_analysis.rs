use std::collections::{HashMap, HashSet};
use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::ty::Ty;
use rustc_middle::mir::{TerminatorKind, BasicBlock, Operand, Place, Local, StatementKind, Rvalue};
use rustc_span::source_map::Spanned;

use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn lockset_analysis(&mut self) {
        rap_info!("Starting Lockset Analysis...");
        
        // Initialize program lockset information
        let mut program_lock_info = ProgramLockInfo {
            lock_objects: HashMap::new(),
            lock_apis: HashMap::new(),
            function_lock_infos: HashMap::new(),
        };
        
        // 1. Collect lock objects
        self.collect_lock_objects(&mut program_lock_info);
        rap_info!("Collected {} lock objects", program_lock_info.lock_objects.len());
        
        // 2. Collect lock APIs
        self.collect_lock_apis(&mut program_lock_info);
        rap_info!("Collected {} lock APIs", program_lock_info.lock_apis.len());
        
        // 3. Analyze lockset for each function
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
    
    // Collect lock objects in the program
    fn collect_lock_objects(&self, program_lock_info: &mut ProgramLockInfo) {
        // Find lock objects from static variables
        rap_debug!("Collecting lock objects...");
        
        // Need to choose an appropriate method to iterate through all items based on specific rustc version
        // Here is an example of a general method
        for item_id in self.tcx.hir().items() {
            let def_id = item_id.owner_id.to_def_id();
            let def_kind = self.tcx.def_kind(def_id);
            
            // Check if it's a static
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
        
        // We can also scan local lock objects in global functions, but prioritize static locks
        // ...
    }
    
    // Check if the type is a target lock type
    fn is_target_lock_type(&self, ty: Ty<'tcx>) -> bool {
        let type_str = ty.to_string();
        // rap_debug!("Checking type: {}", type_str);
        for target_type in &self.target_lock_types {
            if type_str.contains(target_type) {
                return true;
            }
        }
        false
    }
    
    // Collect lock-related APIs
    fn collect_lock_apis(&self, program_lock_info: &mut ProgramLockInfo) {
        rap_debug!("Collecting lock APIs...");
        
        // Iterate through all functions
        // NOTE: THIS IS CRATE LOCAL
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            let fn_name = self.tcx.def_path_str(def_id);
            
            // Check if it's a target lock API
            for &(api_name, lock_state_str) in &self.target_lock_apis {
                if fn_name.contains(api_name) {
                    // Determine lock state
                    let lock_state = match lock_state_str {
                        "read" => LockType::ReadLocked,
                        "write" => LockType::WriteLocked,
                        "upgradable_read" => LockType::UpgradeableReadLocked,
                        _ => LockType::WriteLocked, // Default to write lock
                    };
                    
                    program_lock_info.lock_apis.insert(def_id, (fn_name.clone(), lock_state.clone()));
                    rap_debug!("Found lock API: {:?}, lock state: {:?}", fn_name, lock_state);
                    
                    // No need to check other APIs after finding a match
                    break;
                }
            }
        }
    }
    
    // Analyze the lockset of a function
    fn analyze_function_lockset(&self, func_def_id: DefId, program_lock_info: &mut ProgramLockInfo) {
        /* filter const mir */
        if let Some(_other) = self.tcx.hir().body_const_context(func_def_id) {
            return;
        }
        
        let func_name = self.tcx.def_path_str(func_def_id);
        rap_debug!("Analyzing function lockset: {}", func_name);
        
        let body = self.tcx.optimized_mir(func_def_id);
        
        // Initialize function lockset information
        let mut func_info = FunctionLockInfo {
            def_id: func_def_id,
            entry_lockset: LockSet::new(),
            exit_lockset: LockSet::new(),
            bb_locksets: HashMap::new(),
            call_sites: Vec::new(),
            lock_sites: Vec::new(),
            // TODO: Cache alias_map and guard_map for context_sensitive analysis
        };
        
        // Initialize lockset for each basic block
        for (bb_idx, _) in body.basic_blocks.iter_enumerated() {
            func_info.bb_locksets.insert(bb_idx, LockSet::new());
        }
        
        // Create local variable alias mappings
        let mut local_lock_map: HashMap<Local, DefId> = HashMap::new();
        let mut local_guard_map: HashMap<Local, DefId> = HashMap::new();

        // Create dependency relationship mapping, tracking locks nested in other types
        // a-> [b, c] means a depends on b and c
        let mut dependency_map: HashMap<Local, HashSet<Local>> = HashMap::new();
        
        // Fixed-point iteration to calculate lockset
        let mut changed = true;
        let mut iteration = 0;
        let max_iterations = 10; // Prevent infinite loops
        
        while changed && iteration < max_iterations {
            changed = false;
            iteration += 1;
            
            rap_debug!("Function {} Lockset Analysis Iteration #{}", func_name, iteration);
            
            for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
                let mut current_lockset = if bb_idx.index() == 0 {
                    // Start basic block uses function entry lockset
                    func_info.entry_lockset.clone()
                } else {
                    // Other basic blocks use current state
                    func_info.bb_locksets[&bb_idx].clone()
                };
                
                // Analyze each statement in the basic block
                for stmt in &bb.statements {
                    match &stmt.kind {
                        StatementKind::Assign(box(place, rvalue)) => {
                            // Handle assignment statements, check if it's a lock-related operation
                            self.handle_assignment(place, rvalue, &mut local_lock_map, &mut local_guard_map, &mut dependency_map);
                        }
                        // Can handle other types of statements...
                        _ => {}
                    }
                }
                
                // Handle the terminator statement of the basic block
                if let Some(terminator) = &bb.terminator {
                    match &terminator.kind {
                        TerminatorKind::Call { func, args, destination, .. } => {
                            // TODO: Handle manual calls to drop()
                            // Handle function calls
                            if let Some(callee_func_def_id) = self.resolve_function_call(func) {
                                // Update dependency_map
                                let l_place = destination.local;
                                for arg in args {
                                    let arg_operand = &arg.node;
                                    if let Operand::Copy(r_place) | Operand::Move(r_place) = arg_operand {
                                        dependency_map.entry(l_place).or_insert(HashSet::new()).insert(r_place.local);
                                    }
                                }

                                // Check if it's a lock API
                                if let Some((api_name, ..)) = program_lock_info.lock_apis.get(&callee_func_def_id) {
                                    rap_debug!("Found lock API: {} in function {}", api_name, func_name);
                                    
                                    // Try to determine the lock object being operated on
                                    if let Some(lock_def_id) = self.resolve_lock_object_from_args(&args, &local_lock_map, &dependency_map) {
                                        rap_debug!("Lock API {} acts on lock object: {}", api_name, self.tcx.def_path_str(lock_def_id));
                                        current_lockset.update_lock_state(lock_def_id, LockState::MustHold);
                                        func_info.lock_sites.push(OperationSite {
                                            object_def_id: lock_def_id,
                                            func_def_id: Some(func_def_id),
                                            bb_index: Some(bb_idx),
                                        });

                                        // Handle alias relationship of lock API call result
                                        // destination points to the returned lockguard
                                        local_guard_map.insert(l_place, lock_def_id);
                                    }
                                }
                                
                                // Record call site
                                func_info.call_sites.push((
                                    bb_idx,
                                    callee_func_def_id,
                                ));

                            }
                        }
                        TerminatorKind::Drop { place, .. } => {
                            // Handle variable destruction, which may release locks
                            // TODO: Determine if the dropped object is actually a lockguard through type
                            if let Some(lock_def_id) = self.resolve_place_to_lockguard(&place, &local_guard_map, &dependency_map) {
                                // Dropping lockguard releases the corresponding lock
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
                
                // Update the lockset of the basic block
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
    
    // Handle assignment statements
    fn handle_assignment(&self,
                        place: &Place<'tcx>, 
                        rvalue: &Rvalue<'tcx>, 
                        lock_map: &mut HashMap<Local, DefId>,
                        guard_map: &mut HashMap<Local, DefId>,
                        dependency_map: &mut HashMap<Local, HashSet<Local>>) {
        match rvalue {
            Rvalue::Use(operand) => {
                // Handle simple assignment
                if let Some(lock_def_id) = self.resolve_operand_to_lock_object(operand, lock_map, dependency_map) {
                    lock_map.insert(place.local, lock_def_id);
                }
                if let Some(guard_def_id) = self.resolv_operand_to_lockguard(operand, guard_map, dependency_map) {
                    guard_map.insert(place.local, guard_def_id);
                }
                // Update data dependency graph
                match operand {
                    Operand::Copy(r_place) | Operand::Move(r_place) => {
                        // Left side place depends on right side r_place
                        dependency_map.entry(place.local).or_insert(HashSet::new()).insert(r_place.local);
                    }
                    _ => {}
                }
            }
            Rvalue::Ref(_, _, borrowed_place) => {
                // Handle references
                if let Some(lock_def_id) = self.resolve_place_to_lock_object(borrowed_place, lock_map, dependency_map) {
                    lock_map.insert(place.local, lock_def_id);
                }
                if let Some(guard_def_id) = self.resolve_place_to_lockguard(borrowed_place, guard_map, dependency_map) {
                    guard_map.insert(place.local, guard_def_id);
                }
                // Update data dependency graph
                dependency_map.entry(place.local).or_insert(HashSet::new()).insert(borrowed_place.local);
            }
            // Handle other types of right values...
            _ => {}
        }
    }
    
    // Resolve function DefId from function call
    fn resolve_function_call(&self, func: &Operand<'tcx>) -> Option<DefId> {
        // Try to resolve the function from the operand
        if let Some(callee) = func.const_fn_def() {
            // rap_debug!("Resolved function: {}", self.tcx.def_path_str(callee.0));
            return Some(callee.0);
        }
        None
    }
    
    // Resolve lock object from arguments
    fn resolve_lock_object_from_args(&self, 
                                    args: &Box<[Spanned<Operand<'tcx>>]>, 
                                    lock_map: &HashMap<Local, DefId>,
                                    dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        // Usually the first argument is the self reference, i.e., the lock object
        if !args.is_empty() {
            return self.resolve_operand_to_lock_object(&args[0].node, lock_map, dependency_map);
        }
        None
    }
    
    // Resolve lock object from operand
    fn resolve_operand_to_lock_object(&self, 
                                     operand: &Operand<'tcx>, 
                                     lock_map: &HashMap<Local, DefId>,
                                     dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.resolve_place_to_lock_object(place, lock_map, dependency_map)
            }
            Operand::Constant(constant) => {
                // Would static variables go through here?
                if let Some(def_id) = constant.check_static_ptr(self.tcx) {
                    Some(def_id)
                } else {
                    None
                }
            }
        }
    }
    
    // Resolve possible lock object references from Place
    fn resolve_place_to_lock_object(&self, 
                                   place: &Place<'tcx>, 
                                   alias_map: &HashMap<Local, DefId>,
                                   dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        // Check if there's an alias mapping
        if let Some(&lock_def_id) = alias_map.get(&place.local) {
            return Some(lock_def_id);
        }

        // Check if it's a nested lock
        // DFS on dependency_map to match known locks
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
        
        // Check if directly using static variable
        
        
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
    
    // Resolve possible lockguard references from Place
    fn resolve_place_to_lockguard(&self, 
                                 place: &Place<'tcx>, 
                                 local_guard_map: &HashMap<Local, DefId>,
                                 dependency_map: &HashMap<Local, HashSet<Local>>) -> Option<DefId> {
        // Check if there's an alias mapping
        if let Some(&lock_def_id) = local_guard_map.get(&place.local) {
            return Some(lock_def_id);
        }

        // Track dependency relationships
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
    
    // Output analysis results
    pub fn print_lockset_analysis_results(&self) {
        let program_lock_info = &self.program_lock_info;
        rap_info!("==== Lockset Analysis Results ====");
        rap_info!("Found {} lock objects", program_lock_info.lock_objects.len());
        
        // Output all lock objects
        for (def_id, lock_obj) in &program_lock_info.lock_objects {
            rap_info!("Lock Object: {:?}, Type: {}, Is Static: {}", 
                     self.tcx.def_path_str(*def_id), 
                     lock_obj.lock_type, 
                     lock_obj.is_static);
        }
        
        // Output lockset for each function
        let mut lock_count = 0;
        for (func_def_id, func_info) in &program_lock_info.function_lock_infos {
            if func_info.exit_lockset.is_all_bottom() {
                // rap_info!("Function {} has no lock operations", self.tcx.def_path_str(*func_def_id));
                continue;
            }
            let func_name = self.tcx.def_path_str(*func_def_id);
            rap_info!("Function: {}", func_name);
            rap_info!("  Exit Lockset: {}", func_info.exit_lockset);
            
            // // Output call sites
            // for (callee_id, _, _) in &func_info.call_sites {
            //     rap_info!("  Callsites: {}", self.tcx.def_path_str(*callee_id));
            // }
            lock_count += 1;
        }
        rap_info!("==== Lockset Analysis Results End ({} non-trivial functions) ====", lock_count);
    }
}

// TODO: 
// 1. More precise alias relationship in dependency
// 2. Track locks passed from parameters, such as enable_dma_remapping()
// 3. Track mem::drop