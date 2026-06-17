use rustc_hir::def_id::DefId;
use rustc_middle::mir::Location;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use std::collections::HashSet;

use crate::analysis::deadlock::types::{CallSite, LockSite, interrupt::ProgramIsrInfo, lock::*};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum AtomicModeViolationType {
    SpinHeldSleepAcquire,
    IsrSleepAcquire,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum AtomicContext {
    HeldSpinLock(LockSite),
    IsrContext(DefId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AtomicModeViolation {
    violation_type: AtomicModeViolationType,
    sleeping_lock_site: LockSite,
    atomic_context: AtomicContext,
}

pub struct AtomicModeViolationChecker<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    program_lock_info: &'a ProgramLockInfo,
    program_lock_set: &'a ProgramLockSet,
    program_isr_info: &'a ProgramIsrInfo,
    violations: HashSet<AtomicModeViolation>,
}

impl<'tcx, 'a> AtomicModeViolationChecker<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        program_lock_info: &'a ProgramLockInfo,
        program_lock_set: &'a ProgramLockSet,
        program_isr_info: &'a ProgramIsrInfo,
    ) -> Self {
        Self {
            tcx,
            program_lock_info,
            program_lock_set,
            program_isr_info,
            violations: HashSet::new(),
        }
    }

    pub fn run(&mut self) {
        self.collect_spin_held_sleep_acquire();
        self.collect_isr_sleep_acquire();
        self.report();
    }

    fn collect_spin_held_sleep_acquire(&mut self) {
        let sleeping_lock_instances = &self.program_lock_info.sleeping_lock_instances;

        for func_lockset in self.program_lock_set.values() {
            for sleeping_lock_site in func_lockset.lock_operations.iter() {
                if !sleeping_lock_instances.contains(&sleeping_lock_site.lock) {
                    continue;
                }

                let Some(pre_lockset) = func_lockset
                    .pre_bb_locksets
                    .get(&sleeping_lock_site.site.location.block)
                else {
                    continue;
                };

                for (held_lock, state) in &pre_lockset.lock_states {
                    if *state != LockState::MayHold || sleeping_lock_instances.contains(held_lock) {
                        continue;
                    }

                    let Some(held_sites) = pre_lockset.lock_sites.get(held_lock) else {
                        continue;
                    };

                    for held_site in held_sites {
                        self.violations.insert(AtomicModeViolation {
                            violation_type: AtomicModeViolationType::SpinHeldSleepAcquire,
                            sleeping_lock_site: sleeping_lock_site.clone(),
                            atomic_context: AtomicContext::HeldSpinLock(LockSite {
                                lock: held_lock.clone(),
                                site: *held_site,
                            }),
                        });
                    }
                }
            }
        }
    }

    fn collect_isr_sleep_acquire(&mut self) {
        let sleeping_lock_instances = &self.program_lock_info.sleeping_lock_instances;

        for isr_func in &self.program_isr_info.isr_funcs {
            let Some(func_lockset) = self.program_lock_set.get(isr_func) else {
                continue;
            };

            for sleeping_lock_site in func_lockset.lock_operations.iter() {
                if !sleeping_lock_instances.contains(&sleeping_lock_site.lock) {
                    continue;
                }

                self.violations.insert(AtomicModeViolation {
                    violation_type: AtomicModeViolationType::IsrSleepAcquire,
                    sleeping_lock_site: sleeping_lock_site.clone(),
                    atomic_context: AtomicContext::IsrContext(*isr_func),
                });
            }
        }
    }

    fn report(&self) {
        let mut violations: Vec<_> = self.violations.iter().collect();
        violations.sort_by_key(|violation| {
            (
                violation.violation_type as u8,
                self.callsite_desc(&violation.sleeping_lock_site.site),
                self.atomic_context_desc(&violation.atomic_context),
            )
        });

        rap_info!("Found {} atomic mode violation(s)", violations.len());
        if violations.is_empty() {
            return;
        }

        let mut interrupt_context_violations = Vec::new();
        let mut held_lock_violations = Vec::new();
        for violation in violations {
            match &violation.atomic_context {
                AtomicContext::IsrContext(_) => interrupt_context_violations.push(violation),
                AtomicContext::HeldSpinLock(_) => held_lock_violations.push(violation),
            }
        }

        rap_info!(
            "Atomic mode diagnostics summary: interrupt+mutex = {}, spinlock+mutex = {}",
            interrupt_context_violations.len(),
            held_lock_violations.len()
        );

        if !interrupt_context_violations.is_empty() {
            rap_info!("[Atomic Mode][Interrupt + Mutex]");
            for violation in interrupt_context_violations {
                rap_info!(
                    "mutex {} acquired at {}; this site may run in interrupt context",
                    violation.sleeping_lock_site.lock,
                    self.callsite_desc(&violation.sleeping_lock_site.site),
                );
            }
        }

        if !held_lock_violations.is_empty() {
            rap_info!("[Atomic Mode][SpinLock + Mutex]");
            for violation in held_lock_violations {
                let AtomicContext::HeldSpinLock(first_lock_site) = &violation.atomic_context else {
                    continue;
                };
                rap_info!(
                    "first lock {} acquired at {}; second lock {} acquired at {}",
                    first_lock_site.lock,
                    self.callsite_desc(&first_lock_site.site),
                    violation.sleeping_lock_site.lock,
                    self.callsite_desc(&violation.sleeping_lock_site.site),
                );
            }
        }
    }

    fn atomic_context_desc(&self, atomic_context: &AtomicContext) -> String {
        match atomic_context {
            AtomicContext::HeldSpinLock(lock_site) => {
                format!(
                    "held lock {} at {}",
                    lock_site.lock,
                    self.callsite_desc(&lock_site.site)
                )
            }
            AtomicContext::IsrContext(def_id) => {
                format!(
                    "call reachable from ISR function {}",
                    self.tcx.def_path_str(*def_id)
                )
            }
        }
    }

    fn callsite_desc(&self, callsite: &CallSite) -> String {
        let span = self.callsite_span(callsite);
        if span.is_dummy() {
            format!(
                "{}::{:?}[{}]",
                self.tcx.def_path_str(callsite.caller_def_id),
                callsite.location.block,
                callsite.location.statement_index,
            )
        } else {
            format!(
                "{} in {}",
                self.span_suffix(span),
                self.tcx.def_path_str(callsite.caller_def_id),
            )
        }
    }

    fn callsite_span(&self, callsite: &CallSite) -> Span {
        let body = self.tcx.optimized_mir(callsite.caller_def_id);
        self.location_span(body, callsite.location)
    }

    fn location_span(&self, body: &rustc_middle::mir::Body<'tcx>, location: Location) -> Span {
        let block = &body.basic_blocks[location.block];
        if location.statement_index < block.statements.len() {
            block.statements[location.statement_index].source_info.span
        } else if let Some(terminator) = &block.terminator {
            terminator.source_info.span
        } else {
            body.span
        }
    }

    fn span_suffix(&self, span: Span) -> String {
        if span.is_dummy() {
            String::new()
        } else {
            self.tcx.sess.source_map().span_to_diagnostic_string(span)
        }
    }
}
