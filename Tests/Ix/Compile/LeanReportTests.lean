import LSpec
import Tests.Ix.Compile.LeanReport

namespace Tests.Ix.Compile.LeanReportTests

open LSpec Tests.Ix.Compile.LeanReport

private def check : IO Nat := do
  let names := #["A", "A.alias", "A.«x: y»", "D", "B"]
  let summary := "##check-lean## 7 2 3 5\n"
  let lines := #["[check-lean] A: accept  (0ms)", "[check-lean] A.alias: typed unsafe (0ms)",
    "[check-lean] A.«x: y»: reject type mismatch (1ms)",
    "[check-lean] D: decline reader: nested (1ms)", "[check-lean] B: blocked dependency (1ms)"]
  let stderr := String.intercalate "\n" lines.toList ++ "\n[check-lean] support #abc: decline unsupported (1ms)\n"
  let failures := "# ix check-lean failures\n# env: fixture.ixe\n" ++
    "# reject: type mismatch\nA.«x: y»\n# decline: reader: nested | detail\nD\n" ++
    "# blocked: dependency\nB\n# total failures: 3\n"
  let result ← IO.ofExcept (parse names summary stderr failures 3)
  unless result.map (·.label) == names && result.map (·.outcome) ==
      #["accept", "typed", "reject", "decline", "blocked"] &&
      (result[3]?.map (·.reason)) == some "decline: reader: nested | detail" do
    throw (IO.userError "five outcomes, aliases, quoted label or refusal reasons changed")
  let successful ← IO.ofExcept (parse #["A", "A.alias"] "##check-lean## 0 2 0 2\n"
    (String.intercalate "\n" (lines.extract 0 2).toList) "# total failures: 0\n" 0)
  unless successful.map (·.outcome) == #["accept", "typed"] do
    throw (IO.userError "typed-only result was hidden as acceptance")
  let changed := fun (i : Nat) (s : String) => String.intercalate "\n" (lines.set! i s).toList
  let cases : List (String × Except String (Array Row) × String) := [
    ("empty request", parse #[] "##check-lean## 0 0 0 0\n" "" "" 0, "nonempty"),
    ("duplicate request", parse (names.push "A") summary stderr failures 3, "unique"),
    ("invocation failure", parse names summary stderr failures 1, "invocation exited 1"),
    ("usage failure", parse names summary stderr failures 2, "invocation exited 2"),
    ("missing summary", parse names "" stderr failures 3, "machine summary"),
    ("duplicate summary", parse names (summary ++ summary) stderr failures 3, "machine summary"),
    ("malformed summary", parse names "##check-lean## bad 2 3 5\n" stderr failures 3, "non-numeric"),
    ("short coverage", parse names "##check-lean## 0 2 2 4\n" stderr failures 3, "exact requested"),
    ("bad total", parse names "##check-lean## 0 2 2 5\n" stderr failures 3, "exact requested"),
    ("missing subject", parse names summary (String.intercalate "\n" (lines.extract 1 5).toList) failures 3, "missing requested"),
    ("duplicate subject", parse names summary (stderr ++ lines[0]!) failures 3, "duplicate subject"),
    ("unknown subject", parse names summary (stderr ++ "[check-lean] X: reject bad\n") failures 3, "unexpected subject"),
    ("unknown outcome", parse names summary (changed 0 "[check-lean] A: success (0ms)") failures 3, "unknown outcome"),
    ("wrong outcome counts", parse names "##check-lean## 0 3 2 5\n" stderr failures 3, "outcome counts"),
    ("false successful exit", parse names summary stderr failures 0, "exit disagree"),
    ("missing fail-out", parse names summary stderr "" 3, "incomplete fail-out"),
    ("duplicate fail-out", parse names summary stderr (failures ++ "# blocked: dependency\nB\n") 3, "duplicate fail-out"),
    ("unknown fail-out", parse names summary stderr (failures ++ "# reject: bad\nX\n") 3, "unexpected fail-out"),
    ("successful fail-out", parse names summary stderr (failures ++ "# reject: bad\nA\n") 3, "outcome disagrees"),
    ("wrong refusal kind", parse names summary stderr (failures.replace "# decline:" "# reject:") 3, "outcome disagrees")]
  for (label, result, message) in cases do
    match result with
    | .error e => unless e.contains message do throw (IO.userError s!"{label}: wrong refusal: {e}")
    | .ok _ => throw (IO.userError s!"{label}: malformed/incomplete evidence was accepted")
  unless cases.length == 20 do throw (IO.userError "protocol controls did not all execute")
  IO.println "check-lean protocol: 2 complete reports with all 5 outcomes; 20 invocation/coverage/protocol refusals"
  return cases.length + 2

def suite : List TestSeq := [
  .individualIO "IxC CLI reports require exact labels and coherent outcome evidence" none (do
    let n ← check
    return (true, n, 0, none)) .done]

end Tests.Ix.Compile.LeanReportTests
