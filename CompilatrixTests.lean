import CompilatrixTests.Proofs
import CompilatrixTests.Lir.Run
import CompilatrixTests.Xv.Run
import CompilatrixTests.Xv.Alloc.Run
import CompilatrixTests.Backend.Run
import CompilatrixTests.Src.Run
import CompilatrixTests.Src.Relevance.Run
import CompilatrixTests.Lam.Run
import CompilatrixTests.Lam.KernelK1
import CompilatrixTests.Anf.Run
import CompilatrixTests.Fir.Run
import CompilatrixTests.Rt.Run
import CompilatrixTests.Pipeline.Run
import CompilatrixTests.Corpus.Run
import CompilatrixTests.Corpus.Build
import CompilatrixTests.Corpus.KernelGen
import CompilatrixTests.Own.Suite
import CompilatrixTests.Pipeline.ShrinkSuite
import CompilatrixTests.Recheck.Run
import CompilatrixTests.Recheck.KernelSlow

/-! Test and proof collection. The complete proof/fence target is registered
separately as `CompilatrixTests.Proofs`; runtime suites are compiled and run
through their executables (`check-lir` for `CompilatrixTests.Lir`,
`check-xv-select` for `CompilatrixTests.Xv`, `check-regalloc` for
`CompilatrixTests.Xv.Alloc`, `check-backend` for `CompilatrixTests.Backend`,
`tests-src` and `tests-src-slow` for `CompilatrixTests.Src`, `tests-relevance`
for its relevance suite, `tests-lam` for `CompilatrixTests.Lam`, `tests-anf`
for `CompilatrixTests.Anf`, `tests-fir` for `CompilatrixTests.Fir`, `tests-rt`
for `CompilatrixTests.Rt`, `tests-pipeline` for `CompilatrixTests.Pipeline`, `corpus` and `tests-corpus` for
`CompilatrixTests.Corpus` (whose kernel sample, `CompilatrixTests.Corpus.KernelSample`,
is a manual target), `tests-own` for `CompilatrixTests.Own`, `tests-shrink` for the
generators' shrinking and first-divergence ladders,
`tests-recheck` for `CompilatrixTests.Recheck`). -/
