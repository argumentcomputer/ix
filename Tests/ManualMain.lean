import Tests.Ix.Compile.ClosureBinding
import Tests.Ix.Kernel.BuildPrimitives
import Tests.Ix.Kernel.CheckCompPoly
import Tests.Ix.Kernel.CheckPrimeGaps
import Tests.Ix.Kernel.CheckTauCeti
import Tests.Ix.Kernel.CheckTauCetiReduction
import Tests.Ix.Kernel.PrimAddrs
import Tests.Ix.IxVM.InductiveDeclBench
import Tests.Ix.IxVM.Differential
import Tests.Ix.IxVM.BinderAnnotators
import Tests.Ix.IxVM.MustReject
import Tests.Ix.IxVM.IndVariations
import Tests.AggrBindingReuse
import Tests.AggrToolchains
import Tests.Ix.TableAdmissionCli
import Tests.Ix.TruthMines
import Tests.Registry
import Ix.Meta

/-!
  Manual-only benchmark, corpus, and differential test runner (`IxManualTests`).
  Kept separate from `IxTests` and `IxVMTests` so PR CI builds do not compile
  or link manual-only corpus drivers, while `lake lint` continues to typecheck
  every module.
-/

open Tests.Registry in
def registry : List Entry := [
  -- Must-reject gate: compact hand-built inputs the program has to refuse, with
  -- controls exercising the Rust executor and circuit-verdict deferred assertions.
  .env "ixvm-must-reject" (.manual "hand-built must-reject fixtures and their controls, checked against Lean's kernel") Tests.Ix.IxVM.MustReject.run,
  .env "ixvm-ind-variations" (.manual "inductive variations through Lean, the certified kernel and IxVM; IX_IV_ONLY") Tests.Ix.IxVM.IndVariations.run,
  .runner "binder-data-annotators" (.manual "the compiler's inline annotator against IxC's pass on a compiled artifact, byte for byte; IX_BD_IXE") Tests.Ix.IxVM.BinderAnnotators.run,
  .runner "prim-addrs-artifact" (.manual "every Ix.PrimAddrs address is the record a compiled artifact publishes under its Lean name; IX_PRIM_IXE") Tests.Ix.Kernel.PrimAddrs.artifact,
  -- IxVM against Lean's kernel on a compiled corpus (circuit verdict).
  .env "ixvm-differential" (.manual "a compiled corpus through IxVM and Lean's kernel; IX_DIFF_MODULES, IX_DIFF_LIMIT") Tests.Ix.IxVM.Differential.run,
  .env "ixvm-differential-shards" (.manual "a sharded corpus: an ix check report against Lean's kernel, failing parts run again by halving; IX_DIFF_IXE, IX_DIFF_IXES, IX_DIFF_REPORT, IX_DIFF_OUT") Tests.Ix.IxVM.Differential.runShards,
  -- Declaration-checker measurements: declaration costs, a Std shard, the
  -- inductive census and the in-process modeller's records. Not a gate.
  .env "ixvm-ind-decl-bench" (.manual "declaration-checker cost measurements; needs IX_TEST_OUTPUT_DIR") Tests.Ix.IxVM.InductiveDeclBench.bench,
  .env "ixvm-ind-decl-census" (.manual "inductive census and modeller records") Tests.Ix.IxVM.InductiveDeclBench.census,
  .env "ixvm-ind-decl-model" (.manual "the modeled-route prototype; needs IX_TEST_OUTPUT_DIR") Tests.Ix.IxVM.InductiveDeclBench.modelProbe,
  .suite "truthmines" (.manual "builds the whole TruthMines corpus (network, Mathlib, FLT)") Tests.Ix.TruthMines.buildSuite,
  .suite "truthmines-check" (.manual "checks the whole TruthMines corpus built by `truthmines`") Tests.Ix.TruthMines.checkSuite,
  .suite "truthmines-mini" (.manual "builds the small TruthMines tier (network, Mathlib, FLT)") Tests.Ix.TruthMines.miniSuite,
  .suite "kernel-check-comppoly" (.manual "needs comppoly.ixe at the repository root") Tests.Ix.Kernel.CheckCompPoly.suite,
  .suite "kernel-check-primegaps" (.manual "self-contained, but in no gate yet") Tests.Ix.Kernel.CheckPrimeGaps.suite,
  .suite "kernel-check-tauceti" (.manual "needs tauceti.ixe") Tests.Ix.Kernel.CheckTauCeti.suite,
  .suite "kernel-check-tauceti-reduction" (.manual "self-contained, but in no gate yet") Tests.Ix.Kernel.CheckTauCetiReduction.suite,
  .suite "rust-kernel-build-primitives" (.manual "dumps the primitive content-address table for PrimAddrs::new") Tests.Ix.Kernel.BuildPrimitives.suite,
  .runner "aggregate-binding-reuse" (.manual "one binding proof file discharges two aggregates, end to end through the `ix` binary; minutes of recursion and about 190 GB, needs `lake build ix`; `binding-proof-cli` runs it without the aggregates") Tests.Aggr.BindingReuse.run,
  .runner "aggregate-toolchains" (.manual "libraries from four Lean toolchains proven with one IxVM key and joined into one catalog root, end to end through the `ix` binary; tens of minutes of proving, needs `lake build ix` and `zstd`; IX_TOOLCHAINS_MAX_RAM sets the aggregate RAM budget in GiB (default 140)") Tests.Aggr.Toolchains.run,
  .runner "table-admission-cli" (.manual "ix verify on a claim under a generated artifact's role table, refused and admitted by the kernel's admission, through the `ix` binary; needs `lake build ix`") Tests.Ix.TableAdmissionCli.cli,
  .runner "table-admission-fixtures" (.manual "the kernel's admission of the role table of every .ixe under IX_TABLE_FIXTURES, over the artifact's own records, timed") Tests.Ix.TableAdmissionCli.fixtures,
  .runner "closure-binding-diagnosis" (.manual "the role binding a closure's artifact is read under: three compiles of three closures with the certified checker's verdicts; needs `lake build kernel-check-ixe`") Tests.Ix.Compile.ClosureBinding.run
]

def main (args : List String) : IO UInt32 :=
  Tests.Registry.runManual registry get_env! args
