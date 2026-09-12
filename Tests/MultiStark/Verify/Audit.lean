import Ix.MultiStark.Verify.Audit

open Ix.Tc.Verify.Audit

/-- error: axiom-audit root does not exist: MultiStark.Verify.Audit.missingRoot -/
#guard_msgs in
run_cmd check #[{ root := `MultiStark.Verify.Audit.missingRoot }]

/--
error: axiom allowlist mismatch for MultiStark.Verify.Transcript.sampleField_sound
expected but absent: []
actual but unlisted: ["propext", "Quot.sound"]
-/
#guard_msgs in
run_cmd check #[{ root := ``MultiStark.Verify.Transcript.sampleField_sound }]

/--
error: axiom allowlist mismatch for MultiStark.Verify.Transcript.sampleField_complete
expected but absent: ["Classical.choice"]
actual but unlisted: []
-/
#guard_msgs in
run_cmd check #[
  { root := ``MultiStark.Verify.Transcript.sampleField_complete,
    standardAxioms := #[``propext, ``Classical.choice, ``Quot.sound] }]
