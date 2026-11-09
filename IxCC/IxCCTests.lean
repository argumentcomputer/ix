import IxCCTests.Proofs
import IxCCTests.Lir.Run
import IxCCTests.Xv.Run
import IxCCTests.Xv.Alloc.Run
import IxCCTests.Backend.Run
import IxCCTests.Src.Run
import IxCCTests.Src.Relevance.Run
import IxCCTests.Lam.Run
import IxCCTests.Lam.KernelK1
import IxCCTests.Anf.Run
import IxCCTests.Fir.Run
import IxCCTests.Rt.Run
import IxCCTests.Pipeline.Run
import IxCCTests.Corpus.Run
import IxCCTests.Corpus.Build
import IxCCTests.Corpus.KernelGen
import IxCCTests.Own.Suite
import IxCCTests.Own.Plain.Suite
import IxCCTests.Pipeline.ShrinkSuite
import IxCCTests.Recheck.Run
import IxCCTests.Recheck.KernelSlow
import IxCCTests.Ring0

/-! Test and proof collection. The complete proof/fence target is registered
separately as `IxCCTests.Proofs`; runtime suites are compiled and run
through their executables (`check-lir` for `IxCCTests.Lir`,
`check-xv-select` for `IxCCTests.Xv`, `check-regalloc` for
`IxCCTests.Xv.Alloc`, `check-backend` for `IxCCTests.Backend`,
`tests-src` and `tests-src-slow` for `IxCCTests.Src`, `tests-relevance`
for its relevance suite, `tests-lam` for `IxCCTests.Lam`, `tests-anf`
for `IxCCTests.Anf`, `tests-fir` for `IxCCTests.Fir`, `tests-rt`
for `IxCCTests.Rt`, `tests-pipeline` for `IxCCTests.Pipeline`, `corpus` and `tests-corpus` for
`IxCCTests.Corpus` (whose kernel sample, `IxCCTests.Corpus.KernelSample`,
is a manual target), `tests-own` for `IxCCTests.Own`, `tests-shrink` for the
generators' shrinking and first-divergence ladders,
`tests-recheck` for `IxCCTests.Recheck`). -/
