import LSpec
import Tests.Ix.Compile.KernelReport

namespace Tests.Ix.Compile.KernelReportTests

open Lean LSpec KernelReport

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
  ++ test "anonymous failure rows survive hash-comment filtering"
    (leanFailureLabels ("# ix check-lean failures\n#" ++ addressA ++ "\n# total failures: 1\n") true
      == #[addressA])
  ++ test "anonymous diagnostic labels resolve to the address"
    (anonymousAddress? ("#" ++ addressA ++ " (Displayed)") == some addressA)
  ++ test "zero-target success is not checker evidence"
    (failsWith (checkedLeanTargets "##check-lean## 0 0 0 0\n") "checked zero targets")
  ++ test "successful work has an explicit nonzero target count"
    ((checkedLeanTargets "##check-lean## 10 7 0 7\n").toOption == some 7)
  ++ test "reported work accounts for every checked target exactly once"
    (failsWith (checkedLeanTargets "##check-lean## 10 1 0 2\n") "inconsistent"
      && failsWith (checkedLeanTargets "##check-lean## 10 2 1 2\n") "inconsistent")
  ++ test "mixed passing and failing targets retain complete coverage"
    ((checkedLeanTargets "##check-lean## 10 2 1 3\n").toOption == some 3)
  ++ test "partial unmatched selections are preserved as failures"
    (leanUnmatched "[check-lean] warning: --consts name matched nothing: Missing\n##check-lean## 10 1 0 1\n"
      == #["Missing"])
]

end Tests.Ix.Compile.KernelReportTests
