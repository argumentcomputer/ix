/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Admission
import Ix.CompileDriver
import Ix.Meta
import Benchmarks.Kernel.ConLecheStep
import Tests.Ix.Kernel.EntryCaseDefs

/-! # Host-compiled cases of the certified entry (`kernel-entry-cases`)

Each case names Lean declarations of `Tests.Ix.Kernel.EntryCaseDefs`. The
harness loads that module's environment, takes the dependency closure of
the seeds (with the recursors of every inductive in it, which the reader
requires), compiles it with Ix's compiler (`Ix.CompileM.compileLeanConsts`),
loads the serialized environment with the host codec, orders the primary
records as the census does (`Benchmarks.Kernel.ConLecheStep`: dependencies,
`Nat`-operation grounds and literal edges first; projections last), and
submits canonical record bytes, the literal blobs and the compiler's
reducibility hints to the certified entry `Ix.Ixon.Admission.checkBytes`.
Some cases first alter the input (bytes, keys, a recursor header).

Every case has an exact expected verdict: accepted with each seed installed
under its reader name, or the entry's error at a named stage with the
classification of `Ix.Ixon.Admission.outcome`. The compiler, loader, order
and hints are untrusted producers of the input; only the verdict of
`checkBytes` is under test. One JSON row per case goes to stdout. -/

open Ix.Kernel.ConLecheReader
open Benchmarks.Kernel.ConLecheStep (RecordStore Hints setup)

namespace Tests.Ix.Kernel.EntryCases

/-! ## The closure of a case's seeds -/

/-- The constants a declaration names, including an inductive's
constructors, block and recursors (every recursor of the block, the
auxiliary ones of a nested block included) and a recursor's block and rule
right-hand sides. -/
def references (env : Lean.Environment) (ci : Lean.ConstantInfo) : Array Lean.Name := Id.run do
  let mut out : Array Lean.Name := ci.type.getUsedConstants
  match ci with
  | .defnInfo v => out := out ++ v.value.getUsedConstants
  | .thmInfo v => out := out ++ v.value.getUsedConstants
  | .opaqueInfo v => out := out ++ v.value.getUsedConstants
  | .inductInfo v =>
    out := out ++ v.ctors.toArray ++ v.all.toArray
    for t in v.all do out := out.push (t ++ `rec)
    if let some first := v.all.head? then
      for i in [1:v.numNested + 1] do
        out := out.push (first.str s!"rec_{i}")
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for rule in v.rules do out := out ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return out.filter (env.contains ·)

/-- The seeds and everything they reach. -/
def closure (env : Lean.Environment) (seeds : List Lean.Name) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  let mut seen : Lean.NameSet := {}
  let mut todo := seeds.toArray
  let mut out : Array (Lean.Name × Lean.ConstantInfo) := #[]
  while h : todo.size > 0 do
    let n := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw s!"missing declaration {n}"
    out := out.push (n, ci)
    todo := todo ++ references env ci
  return out.toList

/-! ## The input -/

structure Input where
  constants : List (Address × Ixon.Constant)
  blobs : List (Address × ByteArray)
  hints : Hints
  /-- the reader's context over the compiled records and the prelude (for
  the names of installed seeds) -/
  cx : Ctx
  /-- the seeds' addresses -/
  seeds : List (Lean.Name × Address)
  /-- every compiled name's address -/
  named : Lean.Name → Option Address
  /-- the census's view of the same records (store, reader context, order) -/
  census : Benchmarks.Kernel.ConLecheStep.Setup

def owner (address : Address) (source : Ixon.Constant) : Address :=
  Benchmarks.Kernel.ConLecheStep.owner address source

/-- Compile the seeds' closure and order its records: primaries in the
census order (without the prelude's own records, which the entry supplies),
then projections by address. -/
def prepare (leanEnv : Lean.Environment) (seeds : List Lean.Name) : IO Input := do
  let closed ← IO.ofExcept (closure leanEnv seeds)
  let compiled ← match ← Ix.CompileM.compileLeanConsts closed (numWorkers := 1) with
    | .ok out => pure out
    | .error e => throw (IO.userError s!"compilation failed: {e}")
  unless compiled.ungroundedCount == 0 do
    throw (IO.userError s!"{compiled.ungroundedCount} constants are ungrounded")
  let env ← IO.ofExcept (Ixon.deEnv compiled.bytes)
  let mut store : RecordStore := {}
  for (address, lazy) in env.consts.toList do
    store := store.insert address (← IO.ofExcept lazy.get)
  let pins ← IO.ofExcept defaultPins
  let pre ← IO.ofExcept builtinPrelude
  let hints := Hints.ofStore store env.anonHints
  let s := setup store (env.blobs[·]?) pins pre hints.lookup
  let primaries := s.ordered.filterMap fun a => (store[a]?).map (a, ·)
  let projections := (store.toArray.filter fun (a, c) => owner a c != a).qsort
    fun x y => x.1.cmpBytes y.1 == .lt
  let named (n : Lean.Name) : Option Address := (env.named[Ix.Name.fromLeanName n]?).map (·.addr)
  let seedAddrs ← seeds.mapM fun n => do
    let some a := named n | throw (IO.userError s!"seed {n} was not compiled")
    pure (n, a)
  let blobs := (env.blobs.toArray.qsort fun x y => x.1.cmpBytes y.1 == .lt).toList
  return { constants := (primaries ++ projections).toList, blobs, hints, cx := s.cx,
           seeds := seedAddrs, named, census := s }

/-! ## Cases -/

inductive Expected where
  | accept
  /-- the classification, the stage, and what the error must be -/
  | fail (outcome : Ix.Ixon.Admission.Outcome) (stage : String)
      (check : Input → Ix.Ixon.ConLecheAdmission.Error → Bool)

def Expected.label : Expected → String
  | .accept => "accept"
  | .fail .rejected stage _ => s!"reject ({stage})"
  | .fail .declined stage _ => s!"decline ({stage})"

/-- The records and blobs submitted, after a case's alteration. -/
structure Submission where
  records : Ix.Ixon.Admission.Records
  blobs : List (Address × ByteArray)

def encode (input : Input) : Submission :=
  { records := input.constants.map fun (a, c) => (a, Ixon.serConstant c), blobs := input.blobs }

structure Case where
  label : String
  seeds : List Lean.Name
  expected : Expected
  alter : Input → Except String Submission := fun input => pure (encode input)

def seed (n : String) : Lean.Name := `Tests.Ix.Kernel.EntryCaseDefs ++ n.toName

/-- The record of a compiled name, replaced. -/
def alterRecord (input : Input) (name : Lean.Name) (f : Ixon.Constant → Except String Ixon.Constant) :
    Except String Submission := do
  let some a := input.named name | throw s!"{name} was not compiled"
  unless input.constants.any (·.1 == a) do throw s!"{name} has no record of its own"
  let constants ← input.constants.mapM fun (b, c) => do
    if b == a then pure (b, ← f c) else pure (b, c)
  pure (encode { input with constants })

/-- The position of a compiled name's record (or its block's) in the
submitted order. -/
def positionOf (input : Input) (name : Lean.Name) : Option Nat := do
  let a ← input.named name
  let c ← (input.constants.find? (·.1 == a)).map (·.2)
  input.constants.findIdx? (·.1 == owner a c)

/-- The reader's name of a compiled singleton record. -/
def keyOf (input : Input) (name : Lean.Name) : Option String :=
  (input.named name).map fun a => toString (keyName (.member a 0))

def cases : List Case := [
  -- accepted
  { label := "definition", seeds := [seed "twice"], expected := .accept },
  { label := "theorem", seeds := [seed "twiceId"], expected := .accept },
  { label := "inductive-with-recursor", seeds := [seed "Color", seed "Color.nextRed"],
    expected := .accept },
  { label := "structure-with-projection", seeds := [seed "Point", seed "Point.x", seed "Point.xMk"],
    expected := .accept },
  { label := "quotient", seeds := [seed "quotLiftMk"], expected := .accept },
  { label := "nat-literal", seeds := [seed "natLit"], expected := .accept },
  { label := "nat-operation", seeds := [seed "natAdd"], expected := .accept },
  { label := "string-literal", seeds := [seed "strLit"], expected := .accept },
  { label := "nested-inductive", seeds := [seed "Tree"], expected := .accept },
  -- nested through a container that is itself nested, with the container
  -- family's instance compiled before its head (cl-m1: was a duplicate
  -- declaration of the modeller's `pack_0`)
  { label := "nested-through-nested", seeds := [seed "LTree"], expected := .accept },
  -- `Lean.Elab.InfoTree`'s shape and auxiliary order (cl-m1: was a
  -- duplicate declaration of `pack_1`)
  { label := "nested-through-nested-structure", seeds := [seed "ITree"], expected := .accept },
  { label := "partial-definition-face", seeds := [seed "loop"], expected := .accept },
  -- an equation over a `Subtype` whose levels Ix's compiler stores in
  -- canonical form, equal at every valuation (cl-m1: con-leche's level
  -- comparison did not equate them; the shape of `RatFunc.liftOn_def`)
  { label := "level-comparison", seeds := [seed "levelCanon"], expected := .accept },
  -- rejected: malformed input
  { label := "malformed-bytes", seeds := [seed "twiceId"],
    expected := .fail .rejected "decode" fun input e => match e with
      | .decode p a r =>
        p + 1 == input.constants.length && some a == input.constants.getLast?.map (·.1) && r == "EOF"
      | _ => false,
    alter := fun input =>
      let s := encode input
      pure { s with records := s.records.dropLast ++
        s.records.getLast?.toList.map fun (a, b) => (a, b.extract 0 (b.size - 1)) } },
  { label := "duplicate-constant", seeds := [seed "twiceId"],
    expected := .fail .rejected "duplicate record" fun input e => match e with
      | .duplicate .records p a => p == input.constants.length && some a == input.constants.head?.map (·.1)
      | _ => false,
    alter := fun input =>
      let s := encode input
      pure { s with records := s.records ++ s.records.take 1 } },
  { label := "duplicate-blob", seeds := [seed "natLit"],
    expected := .fail .rejected "duplicate blob" fun input e => match e with
      | .duplicate .blobs p a => p == input.blobs.length && some a == input.blobs.head?.map (·.1)
      | _ => false,
    alter := fun input =>
      let s := encode input
      pure { s with blobs := s.blobs ++ s.blobs.take 1 } },
  -- `Nat.rec`, the recursor of the pinned `Nat` block, under its own
  -- address with its K flag set: the reader regenerates the recursor and
  -- refuses the header
  { label := "wrong-shaped-pinned-recursor", seeds := [seed "natLit"],
    expected := .fail .rejected "reader: malformed" fun input e => match e with
      | .read p (.malformed m) => some p == positionOf input `Nat &&
        m == "recursor Nat.rec declares k := true; the generated recursor is not K-like"
      | _ => false,
    alter := fun input => alterRecord input `Nat.rec fun c => match c.info with
      | .recr r => pure { c with info := .recr { r with k := true } }
      | _ => throw "Nat.rec is not a recursor record" },
  -- `Nat.add`, a pinned `Nat` operation, under its own address with the
  -- value `fun n m => n`: the checker refuses the pin (a checker verdict,
  -- so a decline at the Ix API)
  { label := "wrong-valued-pinned-operation", seeds := [seed "natAdd"],
    expected := .fail .declined "checker" fun _ e => match e with
      | .kernel (.notImplemented m) _ => m == "nonstandard structural Nat operation (Nat.add)"
      | _ => false,
    alter := fun input => alterRecord input `Nat.add fun c => match c.info with
      | .defn d => pure { c with info := .defn { d with value := .leanLam (.ref 0 #[]) (.leanLam (.ref 0 #[]) (.var 1)) } }
      | _ => throw "Nat.add is not a definition record" },
  -- declined
  { label := "partial-definition", seeds := [seed "loop._unsafe_rec"],
    expected := .fail .declined "reader: safety" fun input e => match e with
      | .read p (.declined m) => some p == positionOf input (seed "loop._unsafe_rec") &&
        m == "definition with safety 'partial'"
      | _ => false },
  { label := "axiom", seeds := [seed "someAxiom"],
    expected := .fail .declined "checker" fun input e => match e, keyOf input (seed "someAxiom") with
      | .kernel (.notImplemented m) _, some key => m == s!"non-standard axiom ({key})"
      | _, _ => false },
  -- an equation at the wrong universe level, installed in Lean unchecked
  { label := "wrong-universe-level", seeds := [seed "levelWrong"],
    expected := .fail .declined "checker" fun _ e => match e with
      | .kernel (.invalid m) _ => m == "application type mismatch"
      | _ => false },
  -- `bad_thm` declares its name at the root
  { label := "false-theorem", seeds := [`falseThm],
    expected := .fail .declined "checker" fun input e => match e, keyOf input `falseThm with
      | .kernel (.invalid m) _, some key => m == s!"type mismatch in theorem {key}"
      | _, _ => false } ]

def limits : Ix.Ixon.Admission.Limits := ⟨1 <<< 14, 1 <<< 14, 1 <<< 26, 1 <<< 22, 1 <<< 20⟩

/-- The names the seeds are installed under. -/
def seedNames (input : Input) : List (Lean.Name × Option CName) :=
  input.seeds.map fun (n, a) => (n, (resolve input.cx.store a).map input.cx.nameOf)

def run (leanEnv : Lean.Environment) (test : Case) : IO Bool := do
  let started ← IO.monoMsNow
  let input ← prepare leanEnv test.seeds
  let submission ← IO.ofExcept (test.alter input)
  let result := Ix.Ixon.Admission.checkBytes limits submission.records submission.blobs input.hints.lookup
  let (outcome, detail, passed) := match result, test.expected with
    | .ok env, .accept =>
      let missing : List Lean.Name := (seedNames input).filterMap fun (seed, n) => match n with
        | some n => if env.consts.any (·.name == n) then none else some seed
        | none => some seed
      ("accept", if missing.isEmpty then "" else s!"not installed: {missing}", missing.isEmpty)
    | .ok _, .fail .. => ("accept", "", false)
    | .error e, expected =>
      let o := Ix.Ixon.Admission.outcome e
      let label := match o with | .rejected => "reject" | .declined => "decline"
      let ok := match expected with
        | .accept => false
        | .fail o' _ check => o == o' && check input e
      (label, toString e, ok)
  let ms := (← IO.monoMsNow) - started
  IO.println (Lean.Json.mkObj [
    ("case", Lean.toJson test.label), ("expected", Lean.toJson test.expected.label),
    ("outcome", Lean.toJson outcome), ("detail", Lean.toJson detail),
    ("passed", Lean.toJson passed), ("records", Lean.toJson submission.records.length),
    ("blobs", Lean.toJson submission.blobs.length), ("ms", Lean.toJson ms),
    ("leanVersion", Lean.toJson Lean.versionString)]).compress
  unless passed do
    IO.eprintln s!"{test.label}: expected {test.expected.label}, got {outcome}: {detail}"
  return passed

/-! ## The census's classification

The census (`Benchmarks.Kernel.ConLecheStep.censusLoop`) runs the same
reader and checker one record at a time and classifies each verdict: a
checker `invalid` is a reject. These cases run the census over a case's
records and check the seed's row. Cl-m1 declined a declaration that was
`invalid` but accepted at every closed instantiation of its level
parameters. Cl-level decides the level comparison's missing case by Géran's
sublevels and removed that rule, so `levelCanon` is accepted by the census
as by the entry. -/

structure CensusCase where
  label : String
  seed : Lean.Name
  outcome : String
  reason : String → Bool

def censusCases : List CensusCase := [
  { label := "census-level-comparison", seed := seed "levelCanon", outcome := "accept",
    reason := (· == "") },
  { label := "census-wrong-universe-level", seed := seed "levelWrong", outcome := "reject",
    reason := (· == "application type mismatch") },
  { label := "census-false-theorem", seed := `falseThm, outcome := "reject",
    reason := (·.startsWith "type mismatch in theorem") } ]

def runCensus (leanEnv : Lean.Environment) (test : CensusCase) : IO Bool := do
  let input ← prepare leanEnv [test.seed]
  let natPins ← IO.ofExcept builtinNatOpPins
  let rows ← IO.mkRef (#[] : Array Benchmarks.Kernel.ConLecheStep.Row)
  let _ ← Benchmarks.Kernel.ConLecheStep.censusLoop input.census natPins (fun _ => #[])
    input.census.ordered {} (emit := fun row => rows.modify (·.push row))
  let some a := input.named test.seed | throw (IO.userError s!"seed {test.seed} was not compiled")
  let row := (← rows.get).find? (·.address == a)
  let passed := match row with
    | some r => r.outcome == test.outcome && test.reason r.reason
    | none => false
  IO.println (Lean.Json.mkObj [
    ("case", Lean.toJson test.label), ("expected", Lean.toJson test.outcome),
    ("outcome", Lean.toJson ((row.map (·.outcome)).getD "none")),
    ("detail", Lean.toJson ((row.map (·.reason)).getD "")),
    ("passed", Lean.toJson passed), ("records", Lean.toJson (← rows.get).size),
    ("leanVersion", Lean.toJson Lean.versionString)]).compress
  unless passed do
    IO.eprintln s!"{test.label}: expected {test.outcome}, got {row.map (·.outcome)}: {row.map (·.reason)}"
  return passed

def main : IO UInt32 := do
  let leanEnv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let mut failed := 0
  for test in cases do
    let passed ← try run leanEnv test catch e => do
      IO.eprintln s!"{test.label}: harness error: {e}"
      pure false
    unless passed do failed := failed + 1
  for test in censusCases do
    let passed ← try runCensus leanEnv test catch e => do
      IO.eprintln s!"{test.label}: harness error: {e}"
      pure false
    unless passed do failed := failed + 1
  let total := cases.length + censusCases.length
  IO.eprintln s!"Certified entry, host-compiled cases: {total - failed}/{total} passed."
  return if failed == 0 then 0 else 1

end Tests.Ix.Kernel.EntryCases

def main : IO UInt32 := Tests.Ix.Kernel.EntryCases.main
