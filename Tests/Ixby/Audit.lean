import Ix.Ixby.Audit

/-! Negative regression checks for the trust gate. These use existing theorems
and Lean's existing sorry axiom; no test axiom or proof hole is introduced. -/

open Ix.Tc.Verify.Audit

/-- error: axiom-audit root does not exist: Ix.Ixby.Audit.missingRoot -/
#guard_msgs in
run_cmd check #[{ root := `Ix.Ixby.Audit.missingRoot }]

/-- error: duplicate axiom-audit root: Ix.Ixby.Goldilocks.reduce_val -/
#guard_msgs in
run_cmd check #[
  { root := ``Ix.Ixby.Goldilocks.reduce_val },
  { root := ``Ix.Ixby.Goldilocks.reduce_val }]

/--
error: axiom allowlist mismatch for Ix.Ixby.Goldilocks.reduce_canonical
expected but absent: []
actual but unlisted: ["propext"]
-/
#guard_msgs in
run_cmd check #[{ root := ``Ix.Ixby.Goldilocks.reduce_canonical }]

/--
error: axiom allowlist mismatch for Ix.Ixby.Goldilocks.reduce_val
expected but absent: ["propext"]
actual but unlisted: []
-/
#guard_msgs in
run_cmd check #[
  { root := ``Ix.Ixby.Goldilocks.reduce_val,
    standardAxioms := #[``propext] }]

/-- error: Ix.Ixby.Goldilocks.reduce_val: sorryAx is not a permitted standard Lean axiom -/
#guard_msgs in
run_cmd check #[
  { root := ``Ix.Ixby.Goldilocks.reduce_val,
    standardAxioms := #[``sorryAx] }]

/--
error: axiom allowlist mismatch for sorryAx
expected but absent: []
actual but unlisted: ["sorryAx"]
-/
#guard_msgs in
run_cmd check #[{ root := ``sorryAx }]

/-- error: Ix.Ixby.Goldilocks.reduce_val: forbidden transitive dependency Ix.Ixby.Goldilocks.reduce -/
#guard_msgs in
run_cmd check #[
  { root := ``Ix.Ixby.Goldilocks.reduce_val,
    forbiddenDependencies := #[``Ix.Ixby.Goldilocks.reduce] }]
