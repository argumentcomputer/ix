module

public import Lean.Data.Json
public import Std.Data.HashMap

/-! Strict reading of the certified checker's JSONL evidence
(`kernel-check-ixe`, rows of `Benchmarks.Kernel.CheckIxeStep.Row`). Display
names are capped by the checker; coverage is determined by owning record
address. -/

public section

namespace Tests.Ix.Compile.KernelReport

/-- One row's verdict: the record's display names (at most three), its
outcome (`accept`, `decline`, `reject` or `blocked`) and its reason (a
blocked row's reason is its root record's address). -/
structure Verdict where
  names : Array String
  outcome : String
  reason : String
  deriving BEq, Repr

/-- Verdicts by owning record address (64 hex). -/
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

end Tests.Ix.Compile.KernelReport
