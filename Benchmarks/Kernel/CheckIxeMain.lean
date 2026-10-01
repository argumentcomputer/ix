import Benchmarks.Kernel.CheckIxe
import Benchmarks.Kernel.CheckIxeFold
import Benchmarks.Kernel.CheckIxeGuarded
import Benchmarks.Kernel.CheckIxeReport
import Benchmarks.Kernel.CheckIxePaired

/-! Entry point of `kernel-check-ixe`, the certified checker's environment check:
the verified checker through the Ixon reader; see `Benchmarks.Kernel.CheckIxe`. A first
flag selects another mode:

* `--fold`: the batch fold over the records the environment check accepts
  (`Benchmarks.Kernel.CheckIxeFold`);
* `--guarded`: the check rerun past watchdog runaways, optionally under a
  cgroup memory cap (`Benchmarks.Kernel.CheckIxeGuarded`);
* `--report`, `--summary`: summaries of a run's rows
  (`Benchmarks.Kernel.CheckIxeReport`);
* `--compare`, `--paired`: two row files compared, and paired runs of two
  binaries (`Benchmarks.Kernel.CheckIxePaired`). -/

def main : List String → IO UInt32
  | "--fold" :: args => Benchmarks.Kernel.CheckIxeFold.run args
  | "--guarded" :: args => Benchmarks.Kernel.CheckIxeGuarded.run args
  | "--report" :: args => Benchmarks.Kernel.CheckIxeReport.runReport args
  | "--summary" :: args => Benchmarks.Kernel.CheckIxeReport.runSummary args
  | "--compare" :: args => Benchmarks.Kernel.CheckIxePaired.runCompare args
  | "--paired" :: args => Benchmarks.Kernel.CheckIxePaired.runPaired args
  | args => Benchmarks.Kernel.CheckIxe.run args
