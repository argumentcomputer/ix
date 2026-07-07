/-
  The benchmark-results row contract, Lean side.

  Every measured tool reports results as one JSON object per benchmark name
  in a single file:

    { "<name>": { "status": "ok" | "rejected" | "oom",
                  "<metric>": <number>, ... } }

  Rows are flushed after every name, so a killed process still leaves a
  complete file of the rows measured so far. Tools write `ok` or `rejected`;
  `oom` is merged in by the orchestrator (`ix bench run`) after an abnormal
  exit — a tool never observes its own OOM kill.

  Exit codes are the failure channel (no stdout markers, no log grepping):
  0 = every row ok; `exitUsage` = bad invocation; `exitRejected` = the
  kernel rejected at least one constant (its row is on disk). Any other
  exit is an infrastructure failure. The Rust mirror of this contract is
  `crates/bench` (`ix-bench`); the constants must stay in lockstep.
-/
module
public import Lean.Data.Json

public section

namespace Ix.Benchmark.Results

/-- Bad invocation (unknown name, missing input, conflicting flags). -/
def exitUsage : UInt32 := 2

/-- The kernel rejected at least one constant; its row is on disk. -/
def exitRejected : UInt32 := 3

/-- A `Json` number with at most `d` decimal places, rendered decimally.
    `Float`'s own `ToJson` prints the full binary representation
    (`0.02602000000000000146…`), so build the `JsonNumber` (mantissa ·
    10⁻ᵈ) directly from the rounded value instead. -/
def jsonRound (d : Nat) (f : Float) : Lean.Json :=
  let scale := (10.0 : Float) ^ d.toFloat
  let scaled := f * scale
  let m : Int :=
    if scaled < 0 then -Int.ofNat (-scaled).round.toUInt64.toNat
    else Int.ofNat scaled.round.toUInt64.toNat
  Lean.Json.num ⟨m, d⟩

/-- Read the results object at `path`, tolerating a missing file or
    unparseable content (both yield `{}` — a fresh accumulator). -/
def readRows (path : String) : IO Lean.Json := do
  if ← System.FilePath.pathExists path then
    let s ← IO.FS.readFile path
    match Lean.Json.parse s with
    | .ok j@(.obj _) => return j
    | _ => return Lean.Json.mkObj []
  else
    return Lean.Json.mkObj []

/-- Write the row `{ "<name>": { "status": <status>, <fields> } }` into the
    results file at `path`, merging into any existing object (overwriting on
    collision) so a multi-name run accumulates one map with a row per name. -/
def writeRow (path : String) (name : String) (status : String)
    (fields : List (String × Lean.Json)) : IO Unit := do
  let existing ← readRows path
  let row := Lean.Json.mkObj (("status", Lean.Json.str status) :: fields)
  IO.FS.writeFile path ((existing.setObjVal! name row).compress)

end Ix.Benchmark.Results
