use crate::analysis::deadlock::atomic_mode_checker::AtomicModeViolationChecker;
use crate::analysis::deadlock::run_lock_analysis_with_tag_io;
use rustc_middle::ty::TyCtxt;

pub struct AtomicModeDetector<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> AtomicModeDetector<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    pub fn run_with_tag_io(&mut self, save_tags: Option<&str>, load_tags: Option<&str>) {
        let lock_analysis =
            run_lock_analysis_with_tag_io(self.tcx, save_tags, load_tags, "Atomic mode");

        rap_info!("Atomic mode phase: report diagnostics");
        let mut atomic_mode_checker = AtomicModeViolationChecker::new(
            self.tcx,
            &lock_analysis.program_lock_info,
            &lock_analysis.program_lock_set,
            &lock_analysis.program_isr_info,
        );
        atomic_mode_checker.run();
    }
}
