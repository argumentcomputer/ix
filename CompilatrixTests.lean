import CompilatrixTests.Proofs
import CompilatrixTests.Lir.Run
import CompilatrixTests.Xv.Run

/-! Test and proof collection. The complete proof/fence target is registered
separately as `CompilatrixTests.Proofs`; runtime suites are compiled and run
through their executables (`check-lir` for `CompilatrixTests.Lir`,
`check-xv-select` for `CompilatrixTests.Xv`). -/
