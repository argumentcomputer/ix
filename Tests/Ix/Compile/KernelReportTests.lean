/-
  compiler-reports: the strict readers of the checkers' reports
  (`Tests.Ix.Compile.KernelReport`), which the `pass3` kernel legs and the
  closure suites use. The certified checker's JSONL rows: coverage by owning
  record address, every verdict kept for the caller's policy, an incomplete
  process or a malformed, truncated, duplicate or unknown row refused.
  `check-rs`'s fail-out rows and summary: messages per label, header and
  trailer comments skipped, anonymous labels resolved to their address.

  Ported from a9cf3607 (`Tests/Ix/Compile/KernelReportTests.lean`). The migrated
  IxC `check-lean` protocol has its separate strict controls in LeanReportTests.
-/
import LSpec
import Tests.Ix.Compile.KernelReport

namespace Tests.Ix.Compile.KernelReportTests

open Lean LSpec Tests.Ix.Compile.KernelReport

private def addressA : String := String.ofList (List.replicate 64 'a')
private def addressB : String := String.ofList (List.replicate 64 'b')

private def row (address outcome reason : String) : String :=
  (Lean.Json.mkObj [
    ("address", toJson address), ("names", toJson (#["Displayed"] : Array String)),
    ("outcome", toJson outcome), ("reason", toJson reason)]).compress

private def accepted : String := row addressA "accept" ""

private def failsWith (result : Except String α) (fragment : String) : Bool :=
  match result with
  | .error e => (e.splitOn fragment).length > 1
  | .ok _ => false

/-- A `check-rs --fail-out` file: header, two records under one message, one
under another, trailer. -/
private def failOut : String :=
  "# ix check-rs failures\n# env: out.ixe\n# seeds: names.txt\n" ++
  "# AppTypeMismatch: expected Nat\nA.f\nA.g\n#\n" ++
  "# declaration type mismatch\n#" ++ addressA ++ " (A.h)\n" ++
  "# total failures: 3\n"

def suite : List TestSeq := [
  test "certified report covers every alias through its owning address"
    ((do
      let report ← parse accepted
      checkCoverage report #[("Alias1", addressA), ("Alias2", addressA)]).isOk)
  ++ test "a rejected record remains rejected for an unlisted alias"
    ((do
      let report ← parse (row addressA "reject" "type mismatch")
      checkCoverage report #[("AliasNotDisplayed", addressA)]
      pure (report[addressA]?.map fun (v : Verdict) => (v.outcome, v.reason))).toOption ==
        some (some ("reject", "type mismatch")))
  ++ test "declines retain their reason for the caller's coverage policy"
    ((do
      let report ← parse (row addressA "decline" "reader: unsafe axiom")
      pure (report[addressA]?.map Verdict.reason)).toOption == some (some "reader: unsafe axiom"))
  ++ test "blocked dependency results are preserved"
    ((do
      let report ← parse (row addressA "blocked" addressB)
      pure (report[addressA]?.map Verdict.outcome)).toOption == some (some "blocked"))
  ++ test "an incomplete process fails despite complete-looking rows"
    (failsWith (parse accepted 3) "exited with code 3")
  ++ test "empty successful output fails"
    (failsWith (parse " \n") "wrote no rows")
  ++ test "a truncated trailing row invalidates the report"
    (failsWith (parse (accepted ++ "\n{\"address\":")) "certified row 2")
  ++ test "missing typed verdict fields fail"
    (failsWith (parse "{}") "certified row 1")
  ++ test "unknown verdicts fail"
    (failsWith (parse (row addressA "success" "")) "unknown outcome")
  ++ test "invalid record addresses fail"
    (failsWith (parse (row "bad-address" "accept" "")) "invalid record address")
  ++ test "duplicate records cannot replace earlier failures"
    (failsWith (parse (row addressA "reject" "bad" ++ "\n" ++ accepted)) "duplicate record")
  ++ test "a missing requested record fails even when other rows pass"
    (failsWith (do
      let report ← parse accepted
      checkCoverage report #[("Missing", addressB)]) "omitted 1 requested name")
  ++ test "anonymous diagnostic labels resolve to the address"
    (anonymousAddress? ("#" ++ addressA ++ " (Displayed)") == some addressA)
  ++ test "a bare address label resolves to itself"
    (anonymousAddress? addressA == some addressA)
  ++ test "a source name is no anonymous label"
    (anonymousAddress? "A.f" == none)
  ++ test "fail-out rows carry their message; header, separator and trailer are skipped"
    (failOutRows failOut == #[("A.f", "AppTypeMismatch: expected Nat"),
      ("A.g", "AppTypeMismatch: expected Nat"),
      ("#" ++ addressA ++ " (A.h)", "declaration type mismatch")])
  ++ test "check-rs's summary gives the checked count"
    (rsChecked "[check] seeded 7\n[check] 5/7 passed\n" == some 7)
  ++ test "no summary, no checked count"
    (rsChecked "[check] seeded 7\n" == none)
]

end Tests.Ix.Compile.KernelReportTests
