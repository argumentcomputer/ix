import Lake
open Lake DSL

/-! The mode lane's tests, kernel package only (see README.md): the differential
tester `difftest` (engineer MT's, with MU's recognisers), built against this
tree's `IxC` package. The driver `Main.lean` and `Findings.lean` are run
interpreted and are not targets of this package. -/

package «mode-repair-tests»

require «ix-kernel» from "../IxC"

lean_lib DiffTest where
  roots := #[`DiffTest.Hyp, `DiffTest.Gen]

@[default_target]
lean_exe difftest where
  root := `DiffTest.Main
