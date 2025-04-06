use rustc_middle::mir::{BasicBlock, TerminatorKind};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;

use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn function_summary(&mut self) {
        rap_info!("Starting Function Summary...");

        let mut program_func_summary = ProgramFuncSummary::new();

        // 遍历所有函数
        let mut analyzed_count = 0;
        for local_def_id in self.tcx.hir().body_owners() {
            let def_id = local_def_id.to_def_id();
            if self.tcx.is_mir_available(def_id) {
                self.construct_function_summary(def_id, &mut program_func_summary);
                analyzed_count += 1;
            }
        }
        rap_info!("Completed Function Summary for {} functions", analyzed_count);

        self.program_func_summary = program_func_summary;
    }

    fn construct_function_summary(&self, func_def_id: DefId, program_func_summary: &mut ProgramFuncSummary) {
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
            let lock_set = func_lock_info.bb_locksets.get(&lock_site.bb_index).unwrap();
            let interrupt_set = func_isr_info.bb_interruptsets.get(&lock_site.bb_index).unwrap();

            function_summary.preempt_summary.insert(lock_site.clone(), interrupt_set.clone());
            function_summary.locking_summary.insert(lock_site.clone(), lock_set.clone());
        }

        for interrupt_enable_site in func_isr_info.interrupt_enable_sites.iter() {
            let lock_set = func_lock_info.bb_locksets.get(&interrupt_enable_site.bb_index).unwrap();
            for lock_def_id in lock_set.get_must_hold_locks() {
                // TODO:
                // this lock is acquired at some locksite (o, s')
                // modify function_summary.preempt_summary[locksite] to mark the current isr as enabled
            }
            
        }
    }

    pub fn print_function_summary_result(&self) {
        rap_info!("==== Function Summary Results ====");
        for (def_id, func_info) in self.program_func_summary.function_summaries.iter() {
            rap_info!("Function {} summary: {}", self.tcx.def_path_str(def_id), func_info);
        }
        rap_info!("==== Function Summary Results End ====");
    }
}