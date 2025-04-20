use rustc_middle::mir::{BasicBlock, TerminatorKind};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;

use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug, rap_error};

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn function_summary(&mut self) {
        rap_info!("Starting Function Summary...");

        let mut program_func_summary = ProgramFuncSummary::new();

        // 遍历所有函数
        let mut analyzed_count = 0;
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                self.construct_single_function_summary(def_id, &mut program_func_summary);
                analyzed_count += 1;
            }
        }
        rap_info!("Completed Function Summary for {} functions", analyzed_count);

        // worklist+不动点迭代，将callsite的summary合并到caller函数的summary
        self.construct_function_summary(&mut program_func_summary);

        self.program_func_summary = program_func_summary;
    }

    fn construct_function_summary(&self, program_func_summary: &mut ProgramFuncSummary) {
        let mut worklist = Vec::new();
        for (func_def_id, func_info) in &program_func_summary.function_summaries {
            worklist.push(func_def_id.clone());
        }

        while !worklist.is_empty() {    
            let func_def_id = worklist.pop().unwrap();
            let _func_lock_info = self.program_lock_info.function_lock_infos.get(&func_def_id);
            if _func_lock_info.is_none() {
                continue;
            }
            let func_lock_info = _func_lock_info.unwrap();

            let _func_summary = program_func_summary.function_summaries.get(&func_def_id);
            if _func_summary.is_none() {
                continue;
            }
            let func_summary = _func_summary.unwrap();

            for (call_site_bb, callee_def_id) in func_lock_info.call_sites.iter() {
                // Inline call site summary ( M1 and M2 )
                // let callee_summary = program_func_summary.function_summaries.get(callee_def_id).unwrap();
            }

            //TODO
        }
    }

    fn construct_single_function_summary(&self, func_def_id: DefId, program_func_summary: &mut ProgramFuncSummary) {
        /* filter const mir */
        if let Some(_other) = self.tcx.hir().body_const_context(func_def_id) {
            return;
        }

        let func_name = self.tcx.def_path_str(func_def_id);
        rap_debug!("Constructing function summary for {}", func_name);

        let mut function_summary = FunctionSummary::new();

        let func_lock_info = self.program_lock_info.function_lock_infos.get(&func_def_id).unwrap();
        let func_isr_info = self.program_isr_info.function_interrupt_infos.get(&func_def_id).unwrap();
        for lock_site in func_lock_info.lock_sites.iter() {
            if lock_site.bb_index.is_none() {
                rap_error!("lock_site.bb_index is none {:?}", lock_site);
                continue;
            }

            // NOTE: lock_site is the last operation in this bb, however, the lock_set is computed at the end of this bb, so the lockset is affected by the lock operation.
            // For a temporary solution, when using the lockset, we should manually subtract the current lock from the lockset
            // This is based on the assumption that the lock should not be held before the lock operation. (otherwise there is an obvious deadlock)
            // IE, we ignore the possibility of regular edge caused deadlock.

            // FIXME
            let lock_set = func_lock_info.bb_locksets.get(&lock_site.bb_index.unwrap()).unwrap();
            let interrupt_set = func_isr_info.bb_interruptsets.get(&lock_site.bb_index.unwrap()).unwrap();

            function_summary.preempt_summary.insert(lock_site.clone(), interrupt_set.clone());
            function_summary.locking_summary.insert(lock_site.clone(), lock_set.clone());
        }

        for interrupt_enable_site in func_isr_info.interrupt_enable_sites.iter() {
            if interrupt_enable_site.bb_index.is_none() {
                rap_error!("interrupt_enable_site.bb_index is none {:?}", interrupt_enable_site);
                continue;
            }
            let lock_set = func_lock_info.bb_locksets.get(&interrupt_enable_site.bb_index.unwrap()).unwrap();
            for lock_def_id in lock_set.get_must_hold_locks() {
                // TODO:
                // this lock is acquired at some locksite (o, s')
                // modify function_summary.preempt_summary[locksite] to mark the current isr as enabled
            }
        }

        // Update program_func_summary
        program_func_summary.function_summaries.insert(func_def_id, function_summary);
    }

    pub fn print_function_summary_result(&self) {
        rap_info!("==== Function Summary Results ====");
        let mut summary_count = 0;
        for (def_id, func_info) in self.program_func_summary.function_summaries.iter() {
            if func_info.preempt_summary.is_empty() && func_info.locking_summary.is_empty() {
                continue;
            }

            rap_info!("Function {} summary:", self.tcx.def_path_str(def_id));

            rap_info!(" MustNotBePreemptedBy:");
            for (lock_site, interrupt_set) in &func_info.preempt_summary {
                rap_info!("  LockSite: {:?}, ISRs: {:?}", lock_site.bb_index, interrupt_set.get_disabled_isrs());
            }

            rap_info!(" MustHaveUnlocked:");
            for (lock_site, lock_set) in &func_info.locking_summary {
                rap_info!("  LockSite: {:?}, Locks: {:?}", lock_site.bb_index, lock_set.get_must_not_hold_locks());
            }
            summary_count += 1;
        }
        rap_info!("==== Function Summary Results End ({} non-trivial functions) ====", summary_count);
    }
}