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
for `CompilatrixTests.Rt`, `tests-pipeline` for `CompilatrixTests.Pipeline`,
`tests-recheck` for `CompilatrixTests.Recheck`). -/
