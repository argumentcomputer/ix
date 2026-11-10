import IxCCTests.Support.Shrink
import IxCC.Sem.Result

/-!
# First diverging level and replayable failure records

**The first diverging level**. A generated
program is run on one input at every level a generator's *ladder* lists,
from its reference level (the generator's source level) down the
pipeline; each level gives an observation (`ok` and the value read back,
or the failure). The first level whose observation differs from the
reference's is the failure's signature: the pass that produced that level
is the first one that broke the program. An input on which the reference
level does not finish (`timeout`, or `stuck`, which a generated source
imposes nothing on) is inconclusive.

**Failure records**, format `ixcc/repro/1`: a failing generated
program has no Lean source, so it is written out as the generator's name,
the seed it was found at, the shrunk choice sequences that regenerate it
(`RngM.replay`), the input, the planted bug if any, the level and the two
observations, the sizes before and after shrinking, and the program as
text. `lake exe tests-shrink replay FILE` regenerates the program from the
sequences and runs the ladder again. (The sequences, not the seed,
reproduce the program.) -/

namespace IxCCTests.Support.Repro

open Lean

/-- One level's observation on one input. -/
structure Obs where
  level : String
  obs : String
  deriving BEq, Inhabited, Repr

/-- Observations that leave the reference with nothing to compare. -/
def inconclusive (obs : String) : Bool := obs == "timeout" || obs == "stuck"

/-- The first level of a ladder (reference first) that differs from the
reference: `(level, reference, observed)`. -/
def firstDivergence : List Obs → Option (String × String × String)
  | [] => none
  | ref :: rest =>
    if inconclusive ref.obs then none
    else (rest.find? (·.obs != ref.obs)).map fun o => (o.level, ref.obs, o.obs)

/-- A failure: the input and its first divergence. -/
structure Failure where
  input : List Nat
  level : String
  expected : String
  got : String
  deriving BEq, Inhabited, Repr

def Failure.render (f : Failure) : String :=
  s!"input {f.input}: first divergence at {f.level}: expected {f.expected}, got {f.got}"

def format : String := "ixcc/repro/1"

structure Record where
  generator : String
  planted : Option String := none
  /-- The seed the failure was found at (it no longer regenerates the
  program once the generator changes; the sequences do). -/
  seed : Nat
  /-- Extra seeds the ladder uses (a memory image's), not shrunk. -/
  aux : List Nat := []
  seqs : Shrink.Seqs
  failure : Failure
  originalChoices : Nat
  shrunkChoices : Nat
  originalSize : Nat
  shrunkSize : Nat
  program : String
  deriving Inhabited

def rerun (file : String) : String := s!"lake exe tests-shrink replay {file}"

def Record.toJson (r : Record) (file : String) : Json :=
  Json.mkObj [("format", format), ("generator", r.generator),
    ("planted", match r.planted with | some p => Json.str p | none => Json.null),
    ("seed", r.seed), ("aux", Lean.toJson r.aux),
    ("choices", Lean.toJson (r.seqs.map (·.toList)).toList),
    ("input", Lean.toJson r.failure.input), ("level", r.failure.level),
    ("expected", r.failure.expected), ("observed", r.failure.got),
    ("size", Json.mkObj [("choices", Json.mkObj [("original", r.originalChoices), ("shrunk", r.shrunkChoices)]),
      ("program", Json.mkObj [("original", r.originalSize), ("shrunk", r.shrunkSize)])]),
    ("rerun", rerun file), ("program", r.program)]

def Record.ofJson (j : Json) : Except String Record := do
  let f ← j.getObjValAs? String "format"
  unless f == format do throw s!"not a {format} record"
  let seqs : List (List Nat) ← j.getObjValAs? (List (List Nat)) "choices"
  let size ← j.getObjVal? "size"
  let ch ← size.getObjVal? "choices"
  let pr ← size.getObjVal? "program"
  return { generator := ← j.getObjValAs? String "generator"
           planted := (j.getObjValAs? String "planted").toOption
           seed := ← j.getObjValAs? Nat "seed", aux := (j.getObjValAs? (List Nat) "aux").toOption.getD []
           seqs := (seqs.map List.toArray).toArray
           failure := { input := ← j.getObjValAs? (List Nat) "input", level := ← j.getObjValAs? String "level"
                        expected := ← j.getObjValAs? String "expected", got := ← j.getObjValAs? String "observed" }
           originalChoices := ← ch.getObjValAs? Nat "original", shrunkChoices := ← ch.getObjValAs? Nat "shrunk"
           originalSize := ← pr.getObjValAs? Nat "original", shrunkSize := ← pr.getObjValAs? Nat "shrunk"
           program := ← j.getObjValAs? String "program" }

/-! ## Ladders -/

/-- A replayed case: its normalised sequences, its first failure on the
ladder's inputs, its size (characters of its rendering) and the rendering. -/
structure Outcome where
  seqs : Shrink.Seqs
  failure : Option Failure := none
  size : Nat := 0
  text : String := ""
  deriving Inhabited

/-- A generator with its ladder of levels. -/
structure Ladder where
  generator : String
  /-- The test-side bug `check true` plants, and the level that must be
  named first when it fires. -/
  planted : String
  plantedLevel : String
  /-- Seeds the ladder needs besides the sequences (kept, not shrunk). -/
  aux : Nat → List Nat := fun _ => []
  /-- The sequences a seed draws. -/
  record : Nat → Shrink.Seqs
  /-- Replay the sequences, run the ladder (with the planted bug when the
  flag is set), and report. -/
  check : Bool → List Nat → Shrink.Seqs → IO Outcome
  /-- The seed's case as the generator makes it without a tape, rendered
  (for checking that recording changes nothing). -/
  ofSeed : Nat → String

/-- The ladder's observation of a `Sem.Result`-like outcome: `ok` with the
value read back, or the failure. -/
def obsOf {α : Type} (r : IxCC.Sem.Result α) (read : α → String) : String :=
  match r with
  | .ok v => s!"ok {(read v).replace "IxCC.Sem.Obs." ""}"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource r => s!"resource {reprStr r}"

def Record.write (r : Record) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path ((r.toJson path.toString).pretty ++ "\n")

def Record.read (path : System.FilePath) : IO Record := do
  match Json.parse (← IO.FS.readFile path) >>= Record.ofJson with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"{path}: {e}")

end IxCCTests.Support.Repro
