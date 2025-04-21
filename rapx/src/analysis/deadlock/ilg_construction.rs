use crate::analysis::deadlock::*;
use crate::{rap_debug, rap_info};

impl<'tcx> DeadlockDetection<'tcx> {
    pub fn construct_ilg(&mut self) {
        rap_info!("Constructing ILG...");

        // Interrupt edges
        let all_funcs = self
            .program_func_summary
            .function_summaries
            .keys()
            .collect::<Vec<_>>();
        let isr_funcs = self.program_isr_info.isr_funcs.keys().collect::<Vec<_>>();

        for func in all_funcs.iter() {
            for isr in isr_funcs.iter() {
                rap_debug!("func: {:?}, isr: {:?}", func, isr);
                // TODO:
                // if isr has higher priority than func
                let func_summary = self.program_func_summary.function_summaries.get(func);
                if func_summary.is_none() {
                    rap_debug!("  continue: func_summary of {:?} is None", func);
                    continue;
                }
                let func_summary = func_summary.unwrap();

                if func_summary.preempt_summary.is_empty() {
                    rap_debug!("  continue: func {:?} has no preempt summary", func);
                    continue;
                }
                for (func_lock_site, interrupt_set) in func_summary.preempt_summary.iter() {
                    if interrupt_set.get_disabled_isrs().contains(isr) {
                        rap_debug!("  continue: isr {:?} is disabled in func {:?}", isr, func);
                        continue;
                    }
                    rap_debug!("func_lock_site: {:?}", func_lock_site);

                    let isr_func_summary = self.program_func_summary.function_summaries.get(isr);
                    if isr_func_summary.is_none() {
                        rap_debug!("  continue: isr_func_summary of {:?} is None", isr);
                        continue;
                    }
                    let isr_func_summary = isr_func_summary.unwrap();

                    if isr_func_summary.locking_summary.is_empty() {
                        rap_debug!("  continue: isr_func {:?} has no locking summary", isr);
                        continue;
                    }
                    for (isr_lock_site, _) in isr_func_summary.locking_summary.iter() {
                        rap_debug!(
                            "Adding interrupt edge to isr_lock_site: {:?}",
                            isr_lock_site
                        );
                        self.interrupt_lock_graph.edges.push(ILGEdge {
                            source: func_lock_site.clone(),
                            target: isr_lock_site.clone(),
                            edge_type: EdgeType::Interrupt,
                        });
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
                // Fixme: should use previous bb's lockset
                for held_lock in lock_set.get_must_hold_locks() {
                    if held_lock == lock_site.object_def_id {
                        rap_debug!(
                            "  continue: held_lock == lock_site.object_def_id {:?}",
                            lock_site
                        );
                        continue;
                    }
                    rap_info!(
                        "Adding regular edge from {:?} to {:?}",
                        lock_site,
                        held_lock
                    );
                    self.interrupt_lock_graph.edges.push(ILGEdge {
                        source: lock_site.clone(),
                        // TODO: try to get locksite
                        target: OperationSite {
                            object_def_id: held_lock.clone(),
                            func_def_id: None,
                            bb_index: None,
                        },
                        edge_type: EdgeType::Regular,
                    });
                }
            }

            // function calls
            let func_lock_info = self.program_lock_info.function_lock_infos.get(func);
            if func_lock_info.is_none() {
                continue;
            }
            let func_lock_info = func_lock_info.unwrap();

            for (call_site_bb, callee_func) in func_lock_info.call_sites.iter() {
                let callee_func_summary = self
                    .program_func_summary
                    .function_summaries
                    .get(callee_func);
                if callee_func_summary.is_none() {
                    continue;
                }
                let callee_func_summary = callee_func_summary.unwrap();

                for acquired_lock in func_lock_info
                    .bb_locksets
                    .get(call_site_bb)
                    .unwrap()
                    .get_must_hold_locks()
                {
                    for (incoming_lock_site, incoming_lock_set) in
                        callee_func_summary.locking_summary.iter()
                    {
                        if incoming_lock_set
                            .get_must_not_hold_locks()
                            .contains(&acquired_lock)
                        {
                            continue;
                        }

                        rap_info!(
                            "Adding regular edge from {:?} to {:?}",
                            acquired_lock,
                            incoming_lock_site
                        );
                        self.interrupt_lock_graph.edges.push(ILGEdge {
                            // TODO: try to get locksite
                            source: OperationSite {
                                object_def_id: acquired_lock.clone(),
                                func_def_id: None,
                                bb_index: None,
                            },
                            target: incoming_lock_site.clone(),
                            edge_type: EdgeType::Regular,
                        });
                    }
                }
            }
        }
    }

    pub fn print_ilg_result(&self) {
        rap_info!("==== ILG Result ====");
        rap_info!(
            "{} interrupt edges",
            self.interrupt_lock_graph
                .edges
                .iter()
                .filter(|edge| edge.edge_type == EdgeType::Interrupt)
                .count()
        );
        rap_info!(
            "{} regular edges",
            self.interrupt_lock_graph
                .edges
                .iter()
                .filter(|edge| edge.edge_type == EdgeType::Regular)
                .count()
        );
        for edge in self.interrupt_lock_graph.edges.iter() {
            rap_info!("{}", edge);
        }
        rap_info!("==== End of ILG Result ====");
    }
}
