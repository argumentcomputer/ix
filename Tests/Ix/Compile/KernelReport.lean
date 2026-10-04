import Lean.Data.Json
import Std.Data.HashMap

/-! Strict reading of the certified checker's JSONL evidence. Display names
are capped by the checker; coverage is determined by owning record address. -/

namespace Tests.Ix.Compile.KernelReport

structure Verdict where
  names : Array String
  outcome : String
  reason : String
  deriving BEq, Repr

abbrev Report := Std.HashMap String Verdict

def isAddress (address : String) : Bool :=
  address.length == 64 && address.toList.all (fun c => "0123456789abcdef".contains c)

/-- Reject failed processes, malformed or incomplete rows, duplicate records,
and empty output. A valid report can contain declines, rejects and blocked
records; those verdicts remain available for the caller's explicit policy. -/
def parse (content : String) (exitCode : UInt32 := 0) : Except String Report := do
  unless exitCode == 0 do
    throw s!"certified checker exited with code {exitCode}"
  let mut report : Report := {}
  let mut lineNo := 0
  for raw in content.splitOn "\n" do
    lineNo := lineNo + 1
    let line := raw.trimAscii.toString
    if line.isEmpty then continue
    let read : Except String (String × Verdict) := do
      let j ← Lean.Json.parse line
      let address ← j.getObjValAs? String "address"
      unless isAddress address do
        throw "invalid record address"
      let names ← j.getObjValAs? (Array String) "names"
      let outcome ← j.getObjValAs? String "outcome"
      let reason ← j.getObjValAs? String "reason"
      unless #["accept", "decline", "reject", "blocked"].contains outcome do
        throw s!"unknown outcome {outcome}"
      return (address, { names, outcome, reason })
    let (address, verdict) ← read.mapError (fun e => s!"certified row {lineNo}: {e}")
    if report.contains address then
      throw s!"certified row {lineNo}: duplicate record {address}"
    report := report.insert address verdict
  if report.isEmpty then throw "certified checker wrote no rows"
  return report

/-- Each requested name must have a verdict for its owning record. Multiple
aliases may share a record, including aliases absent from its display names.
The expected mapping must come from the compiled environment, not the report. -/
def checkCoverage (report : Report) (expected : Array (String × String)) : Except String Unit := do
  let missing := expected.filter fun (_, address) => !report.contains address
  unless missing.isEmpty do
    throw s!"certified checker omitted {missing.size} requested name(s): \
      {String.intercalate ", " (missing.toList.map fun (n, a) => s!"{n}@{a}")}"

/-- Anonymous Lean failure labels are `#hex`, optionally followed by a
display name. Ordinary `#` comments must not hide these failure rows. -/
def anonymousAddress? (label : String) : Option String := do
  let token ← (label.trimAscii.toString.splitOn " ").head?
  let address := if token.startsWith "#" then (token.drop 1).toString else token
  if isAddress address then some address else none

def leanFailureLabels (content : String) (anon : Bool) : Array String :=
  (content.splitOn "\n").toArray.filterMap fun line =>
    let label := line.trimAscii.toString
    if anon then anonymousAddress? label
    else if label.isEmpty || label.startsWith "#" then none else some label

def leanUnmatched (content : String) : Array String :=
  let tag := "[check-lean] warning: --consts name matched nothing: "
  (content.splitOn "\n").toArray.filterMap fun line =>
    if line.startsWith tag then some ((line.drop tag.length).toString.trimAscii.toString)
    else none

/-- A successful process must report actual work. The stable summary has
elapsed milliseconds, passed count, failed count and total targets. -/
def checkedLeanTargets (content : String) : Except String Nat := do
  let tag := "##check-lean## "
  let summaries := (content.splitOn "\n").filter (·.startsWith tag)
  let [line] := summaries | throw "check-lean did not emit exactly one work summary"
  let fields := ((line.drop tag.length).toString.splitOn " ").filter (!·.isEmpty)
  let [elapsed, passed, failed, targets] := fields
    | throw "malformed check-lean work summary"
  let (some _, some p, some f, some total) :=
      (elapsed.toNat?, passed.toNat?, failed.toNat?, targets.toNat?)
    | throw "nonnumeric check-lean work summary"
  if total == 0 then throw "check-lean checked zero targets"
  if p > total || f > total then throw "inconsistent check-lean work summary"
  return total

end Tests.Ix.Compile.KernelReport
