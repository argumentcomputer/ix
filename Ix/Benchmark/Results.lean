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

/-- Write a prebuilt row object into the results file at `path`, merging
    into any existing object (overwriting on collision) — the shape every
    tool uses, so per-constant processes can safely share one file.

    The write is ATOMIC (temp file + rename): the accumulator is shared by
    N sequential processes and their orchestrator, and a watchdog KILL
    landing mid-write would otherwise truncate it — which the tolerant
    `readRows` would then silently reset to `{}`, losing every prior
    constant's row. -/
def writeEntry (path : String) (name : String) (row : Lean.Json) : IO Unit := do
  let existing ← readRows path
  let tmp := path ++ ".tmp"
  IO.FS.writeFile tmp ((existing.setObjVal! name row).compress)
  IO.FS.rename tmp path

/-- Write the row `{ "<name>": { "status": <status>, <fields> } }` into the
    results file at `path`. -/
def writeRow (path : String) (name : String) (status : String)
    (fields : List (String × Lean.Json)) : IO Unit :=
  writeEntry path name (Lean.Json.mkObj (("status", Lean.Json.str status) :: fields))

end Ix.Benchmark.Results
