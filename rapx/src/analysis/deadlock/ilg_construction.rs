use crate::analysis::deadlock::*;
use crate::{rap_info, rap_debug};

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn construct_ilg(&mut self) {
        rap_info!("Constructing ILG...");

        // Interrupt edges
        let all_funcs = self.program_func_summary.function_summaries.keys().collect::<Vec<_>>();
        let isr_funcs = self.program_isr_info.isr_funcs.keys().collect::<Vec<_>>();

        for func in all_funcs.iter() {
            for isr in isr_funcs.iter() {
                // TODO:
                // if isr has higher priority than func
                let func_summary = self.program_func_summary.function_summaries.get(func);
                if func_summary.is_none() {
                    continue;
                }
                let func_summary = func_summary.unwrap();
                
                for (func_lock_site, interrupt_set) in func_summary.preempt_summary.iter() {
                    if interrupt_set.get_disabled_isrs().contains(isr) {
                        continue;
                    }

                    let isr_func_summary = self.program_func_summary.function_summaries.get(isr);
                    if isr_func_summary.is_none() {
                        continue;
                    }
                    let isr_func_summary = isr_func_summary.unwrap();

                    for (isr_lock_site, _) in isr_func_summary.locking_summary.iter() {
                        self.interrupt_lock_graph.interrupt_edges.insert(func_lock_site.clone(), isr_lock_site.clone());
                    }
                    
                }
            }
        }

        // Regular edges
        for func in all_funcs.iter() {
            let func_summary = self.program_func_summary.function_summaries.get(func);
            if func_summary.is_none() {
                continue;
            }
            let func_summary = func_summary.unwrap();

            // lock operations
            for (lock_site, lock_set) in func_summary.locking_summary.iter() {
                for held_lock in lock_set.get_must_hold_locks() {
                    self.interrupt_lock_graph.regular_edges.insert(held_lock.clone(), lock_site.object_def_id.clone());
                }
            }

            // function calls
            let func_lock_info = self.program_lock_info.function_lock_infos.get(func);
            if func_lock_info.is_none() {
                continue;
            }
            let func_lock_info = func_lock_info.unwrap();

            for (call_site_bb, callee_func) in func_lock_info.call_sites.iter() {
                let callee_func_summary = self.program_func_summary.function_summaries.get(callee_func);
                if callee_func_summary.is_none() {
                    continue;
                }
                let callee_func_summary = callee_func_summary.unwrap();

                for acquired_lock in func_lock_info.bb_locksets.get(call_site_bb).unwrap().get_must_hold_locks() {
                    for (incoming_lock_site, incoming_lock_set) in callee_func_summary.locking_summary.iter() {
                        if incoming_lock_set.get_must_not_hold_locks().contains(&acquired_lock) {
                            continue;
                        }

                        self.interrupt_lock_graph.regular_edges.insert(acquired_lock.clone(), incoming_lock_site.object_def_id.clone());
                    }
                }
            }
        }
    }

    pub fn print_ilg_result(&self) {
        rap_info!("==== ILG Result ====");
        rap_info!("{} interrupt edges", self.interrupt_lock_graph.interrupt_edges.len());
        rap_info!("{} regular edges", self.interrupt_lock_graph.regular_edges.len());
        rap_info!("==== End of ILG Result ====");
    }
}