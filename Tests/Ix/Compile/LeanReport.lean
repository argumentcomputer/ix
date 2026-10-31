module

public import Tests.Ix.Compile.KernelReport

public section

namespace Tests.Ix.Compile.LeanReport

structure Row where
  label : String
  outcome : String
  reason : String := ""
  deriving BEq, Repr

def Row.toJson (r : Row) : Lean.Json :=
  Lean.Json.mkObj [("label", Lean.toJson r.label), ("outcome", Lean.toJson r.outcome),
    ("reason", Lean.toJson r.reason)]

def success (outcome : String) : Bool := outcome == "accept" || outcome == "typed"

/-- Read the actual verbose IxC CLI protocol. Every requested label has one
outcome; machine counts, fail-out labels/reasons and exit status must agree.
Invocation/protocol failures cannot become known logical refusals. -/
def parse (expected : Array String) (stdout stderr failOut : String) (exitCode : UInt32) :
    Except String (Array Row) := do
  unless !expected.isEmpty && expected.toList.eraseDups.length == expected.size do
    throw "check-lean: expected labels must be nonempty and unique"
  unless exitCode == 0 || exitCode == 3 do
    throw s!"check-lean: invocation exited {exitCode}"
  let [line] := (stdout.splitOn "\n").filter (·.startsWith "##check-lean## ")
    | throw "check-lean: missing or duplicate machine summary"
  let ["##check-lean##", elapsed, passed, failed, covered] := line.splitOn " "
    | throw "check-lean: malformed machine summary"
  let some [_, passed, failed, covered] := [elapsed, passed, failed, covered].mapM String.toNat?
    | throw "check-lean: non-numeric machine summary"
  unless covered == expected.size && passed + failed == covered do
    throw "check-lean: machine summary does not cover the exact requested labels"
  let mut outcomes : Std.HashMap String String := {}
  for line in stderr.splitOn "\n" do
    if let some label := expected.find? (fun n => line.startsWith s!"[check-lean] {n}: ") then
      if outcomes.contains label then throw s!"check-lean: duplicate subject {label}"
      let rest := (line.drop (s!"[check-lean] {label}: ").length).toString
      let outcome := (rest.splitOn " ").headD ""
      unless #["accept", "typed", "reject", "decline", "blocked"].contains outcome do
        throw s!"check-lean: unknown outcome for {label}: {outcome}"
      outcomes := outcomes.insert label outcome
    else if line.startsWith "[check-lean] " && line.contains ": " &&
        !line.startsWith "[check-lean] support #" then
      throw s!"check-lean: unexpected subject row: {line}"
  unless outcomes.size == expected.size && expected.all outcomes.contains do
    throw "check-lean: missing requested subject outcomes"
  let successes := expected.filter fun n => success (outcomes.getD n "")
  unless successes.size == passed && exitCode == (if failed == 0 then 0 else 3) do
    throw "check-lean: outcome counts or exit disagree with summary"
  let mut reasons : Std.HashMap String String := {}
  for (label, reason) in KernelReport.failOutRows failOut do
    let some outcome := outcomes[label]? | throw s!"check-lean: unexpected fail-out label {label}"
    if reasons.contains label then throw s!"check-lean: duplicate fail-out label {label}"
    unless !success outcome && reason.startsWith (outcome ++ ":") do
      throw s!"check-lean: fail-out outcome disagrees for {label}"
    reasons := reasons.insert label reason
  unless reasons.size == failed && expected.all (fun n => success (outcomes.getD n "") || reasons.contains n) do
    throw "check-lean: incomplete fail-out coverage"
  return expected.map fun label => { label, outcome := outcomes.getD label "", reason := reasons.getD label "" }

end Tests.Ix.Compile.LeanReport
