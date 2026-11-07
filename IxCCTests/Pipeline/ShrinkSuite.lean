import IxCCTests.Fir.Shrink
import IxCCTests.Xv.Alloc.Shrink

/-! # `tests-shrink`: shrinking and first-divergence reports (MT.5)

For each generator with a ladder (LamGen, FoGen, the Lir generator and the
allocation mutants; `IxCCTests.Support.Repro`):

* **replay**: on the first seeds, the sequences a recording run draws
  regenerate exactly the case the plain seeded generator makes, a replay of
  them draws them again unchanged, and the production pipeline agrees with
  the reference at every level of the ladder (no divergence);
* **planted**: with the ladder's planted bug, the first seed whose case
  fails is found, the failure names the planted level, its choice
  sequences are shrunk (`Support.Shrink`), the shrunk case still fails at
  that level and is smaller, it passes without the planted bug, and it is
  written out as an `ixcc/repro/1` record whose replay
  (`tests-shrink replay FILE`) gives the same failure.

`tests-shrink campaign GEN --from N --count C [--planted] [--out DIR]`
runs a ladder over seeds on the production pipeline (or with its planted
bug) and shrinks and writes out every failure it finds; `tests-shrink
replay FILE` re-runs a written record. -/

namespace IxCCTests.Pipeline.ShrinkSuite

open IxCCTests.Src (Assert expect expectEq timed)

open IxCCTests.Support.Repro (Ladder Outcome Failure Record)
open System

def ladders : List Ladder :=
  [Fir.Shrink.lamGen, Fir.Shrink.foGen, Xv.Alloc.Shrink.lirGen, Xv.Alloc.Shrink.mutants]

def ladder? (name : String) : Option Ladder := ladders.find? (·.generator == name)

/-- Seeds checked by the replay part, per ladder. -/
def replaySeeds : Nat := 12

/-- Seeds searched for a planted failure, and the shrinker's replay budget. -/
def searchSeeds : Nat := 400
def budget : Nat := 10000

/-- Shrink a failing case and make its record. -/
def shrinkCase (l : Ladder) (planted : Bool) (seed : Nat) (o : Outcome) (f : Failure) :
    IO (Record × Support.Shrink.Stats × Outcome) := do
  let aux := l.aux seed
  let test := fun (cand : Support.Shrink.Seqs) => do
    let o ← l.check planted aux cand
    return if (o.failure.map (·.level)) == some f.level then some o.seqs else none
  let (seqs, st) ← Support.Shrink.shrink test o.seqs budget
  let o' ← l.check planted aux seqs
  let f' := o'.failure.getD f
  let r : Record := { generator := l.generator, planted := if planted then some l.planted else none
                      seed, aux, seqs := o'.seqs, failure := f'
                      originalChoices := Support.Shrink.total o.seqs, shrunkChoices := Support.Shrink.total o'.seqs
                      originalSize := o.size, shrunkSize := o'.size, program := o'.text }
  return (r, st, o')

def replayPart (a : Assert) (l : Ladder) : IO String := do
  for seed in [0:replaySeeds] do
    let seqs := l.record seed
    let o ← l.check false (l.aux seed) seqs
    expect a (o.text == l.ofSeed seed) s!"{l.generator} seed {seed}: the recorded sequences regenerate another case"
    expect a (o.seqs.toList == seqs.toList) s!"{l.generator} seed {seed}: a replay draws other choices"
    if let some f := o.failure then
      expect a false s!"{l.generator} seed {seed}: the pipeline diverges: {f.render}"
  return s!"{l.generator}: {replaySeeds} seeds regenerate from their choices and agree at every level"

def plantedPart (a : Assert) (l : Ladder) (work : FilePath) : IO (Array String) := do
  let mut found : Option (Nat × Outcome × Failure) := none
  for seed in [0:searchSeeds] do
    let o ← l.check true (l.aux seed) (l.record seed)
    if let some f := o.failure then
      found := some (seed, o, f)
      break
  let some (seed, o, f) := found
    | expect a false s!"{l.generator}: the planted bug fires on none of {searchSeeds} seeds"; return #[]
  expectEq a f.level l.plantedLevel s!"{l.generator} seed {seed}: the planted failure's first level"
  let ((r, st, o'), ms) ← timed (shrinkCase l true seed o f)
  expectEq a r.failure.level l.plantedLevel s!"{l.generator}: the shrunk case's first level"
  expect a (r.shrunkChoices < r.originalChoices) s!"{l.generator}: shrinking kept {r.shrunkChoices} of {r.originalChoices} choices"
  expect a (r.shrunkSize ≤ r.originalSize) s!"{l.generator}: the shrunk program is larger"
  -- without the planted bug the shrunk case passes: the failure is the bug's
  let clean ← l.check false r.aux r.seqs
  expect a clean.failure.isNone s!"{l.generator}: the shrunk case fails without the planted bug"
  -- written out, read back and replayed
  let file := work / s!"{l.generator}-planted.json"
  r.write file
  let back ← Record.read file
  let again ← l.check back.planted.isSome back.aux back.seqs
  expect a ((again.failure.map (·.level)) == some r.failure.level)
    s!"{l.generator}: the written record does not replay to the failure"
  return #[s!"{l.generator}: planted bug ({l.planted}) fires at seed {seed}: {f.render}",
    s!"  shrunk in {ms} ms ({st.tries} replays, {st.kept} kept): {r.originalChoices} → {r.shrunkChoices} choices, \
      program {r.originalSize} → {r.shrunkSize} characters; first divergence at {r.failure.level} \
      (input {r.failure.input}: expected {r.failure.expected}, got {r.failure.got}); passes without the bug",
    s!"  written to {file} and replayed: `{Support.Repro.rerun file.toString}`",
    s!"  shrunk program:\n{indent o'.text}"]
where
  indent (s : String) : String := "\n".intercalate ((s.splitOn "\n").map ("      " ++ ·))

def suite (a : Assert) (work : FilePath) : IO Unit := do
  IO.println "tests-shrink"
  for l in ladders do
    let before ← a.get
    let (line, ms) ← timed (replayPart a l)
    IO.println s!"  replay {l.generator}: {(← a.get) - before} assertions, {ms} ms\n    {line}"
  for l in ladders do
    let before ← a.get
    let (lines, ms) ← timed (plantedPart a l work)
    IO.println s!"  planted {l.generator}: {(← a.get) - before} assertions, {ms} ms"
    for x in lines do IO.println s!"    {x}"
    (← IO.getStdout).flush

/-- `replay FILE`: regenerate and re-run; exit 1 when the failure reproduces. -/
def replayMain (file : String) : IO UInt32 := do
  let r ← Record.read file
  let some l := ladder? r.generator | IO.eprintln s!"unknown generator {r.generator}"; return 2
  let o ← l.check r.planted.isSome r.aux r.seqs
  IO.println s!"{r.generator}{if r.planted.isSome then " (planted bug)" else ""}: {Support.Shrink.total r.seqs} choices, \
    program of {o.size} characters\n{o.text}"
  match o.failure with
  | some f =>
    IO.println s!"reproduced: {f.render}"
    return 1
  | none =>
    IO.println s!"does not reproduce (recorded: {r.failure.render})"
    return 0

/-- `campaign GEN --from N --count C [--planted] [--out DIR]`. -/
def campaignMain (args : List String) : IO UInt32 := do
  let rec parse (from_ count : Nat) (planted : Bool) (out : String) :
      List String → Except String (Nat × Nat × Bool × String)
    | [] => .ok (from_, count, planted, out)
    | "--from" :: n :: rest => parse (n.toNat?.getD from_) count planted out rest
    | "--count" :: n :: rest => parse from_ (n.toNat?.getD count) planted out rest
    | "--planted" :: rest => parse from_ count true out rest
    | "--out" :: d :: rest => parse from_ count planted d rest
    | x :: _ => .error s!"unknown argument {x}"
  match args with
  | gen :: rest =>
    let some l := ladder? gen | IO.eprintln s!"unknown generator {gen} (one of {ladders.map (·.generator)})"; return 2
    let .ok (from_, count, planted, out) := parse 0 100 false "plans/shrink" rest
      | IO.eprintln "usage: tests-shrink campaign GEN [--from N] [--count C] [--planted] [--out DIR]"; return 2
    IO.FS.createDirAll out
    let mut failures := 0
    for seed in [from_:from_ + count] do
      let o ← l.check planted (l.aux seed) (l.record seed)
      if let some f := o.failure then
        failures := failures + 1
        let (r, st, _) ← shrinkCase l planted seed o f
        let file : FilePath := out / s!"{l.generator}-{seed}.json"
        r.write file
        IO.println s!"seed {seed}: {f.render}\n  shrunk ({st.tries} replays): {r.originalChoices} → {r.shrunkChoices} choices, \
          first divergence at {r.failure.level}; `{Support.Repro.rerun file.toString}`"
    IO.println s!"{l.generator}: {count} seeds from {from_}, {failures} failures"
    return (if failures == 0 then 0 else 1)
  | _ => IO.eprintln "usage: tests-shrink campaign GEN [--from N] [--count C] [--planted] [--out DIR]"; return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | ["replay", file] => replayMain file
  | "campaign" :: rest => campaignMain rest
  | _ =>
    let work? := match args with
      | ["--work", d] => some d
      | _ => none
    let a ← IO.mkRef 0
    try
      match work? with
      | some d => IO.FS.createDirAll d; suite a d
      | none => IO.FS.withTempDir fun d => suite a d
      IO.println s!"tests-shrink: {← a.get} assertions passed"
      return 0
    catch e =>
      IO.eprintln s!"tests-shrink: FAILED after {← a.get} assertions: {e}"
      return 1

end IxCCTests.Pipeline.ShrinkSuite
