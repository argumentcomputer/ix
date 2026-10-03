/-
  validate-lean-nc: does `ix validate-lean` validate the auxiliaries that are
  NOT identical to Lean's correctly? The known non-canonical fixtures are the
  test: every twin family with entries in `Tests/Ix/Compile/NonCanonical.lean`
  (`Twins/{Cliques,Repro,Proto}.lean`, `Oracle/Lib.lean`) and the prototype
  cases (`Image/C*.lean`), each through `ix validate-lean --local` with the
  switch off and on and `IX_VALIDATE_AUXTABLE` (one row per regenerated
  auxiliary and image: block status, whether it differs from Lean's own form
  by address, the phase that handled it and the verdict).

  For every auxiliary that differs from Lean's by address it prints one
  table row: family, presentation, switch, the block's status, the phase and
  verdict, and the match: a design class (image of a changed block, Lean's
  `IndPredBelow` family of a changed Prop block, the surgery path), a defect
  id, the non-canonical entries naming it, or UNMATCHED. Then it checks the
  two properties:
  1. no expected difference is wrongly rejected: every phase-6 exception is a
     recorded defect (phase 6 only judges unchanged blocks; a changed block
     is phase 7's), and every image passes phase 7;
  2. no unexpected difference is silently passed: every address difference
     on an unchanged block is a phase-6 exception with a defect id (none
     UNMATCHED), and every non-canonical entry that concerns an auxiliary
     appears in the validator's output.
  UNMATCHED rows and missing entries fail the suite.

  Run with: `lake test -- --ignored validate-lean-nc` (after `lake build ix`).
-/
import Lean.Data.Json
import Tests.Ix.Compile.Twins
import Tests.Ix.Compile.NonCanonical

open Lean

namespace Tests.Ix.Compile.ValidateLeanNC

def files : List String :=
  (["Cliques", "Repro", "Proto"].map fun s => s!"Tests/Ix/Compile/Twins/{s}.lean")
  ++ ["Tests/Ix/Compile/Oracle/Lib.lean"]
  ++ (["C1Perm", "C2Split", "C3PropSplit", "C4Evap", "C5Collapse", "C6NestedCollapse", "C7IndPred",
       "C8Collapse3", "C9Params"].map fun s => s!"Tests/Ix/Compile/Image/{s}.lean")

/-- The recorded defects a phase-6 exception may carry, by name fragment. -/
def defects : List (String × String) := [
  ("RecAlias.PA.below", "WB-B6"),
  ("UNestNeg", "WB-B9"),
  ("F8NoSplit", "A3V-IPB"),
  ("IPB.", "A3V-IPB")]

def defectOf? (n : String) : Option String :=
  defects.findSome? fun (frag, id) => if (n.splitOn frag).length > 1 then some id else none

/-- A table row of the validator. -/
structure Row where
  file : String
  switch : String
  name : String
  status : String
  differs : Bool
  phase : String
  verdict : String

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

def runOne (dir : System.FilePath) (file switch : String) : IO (Array Row × String) := do
  let stem := (System.FilePath.mk file).fileStem.getD file
  let tsv := dir / s!"{stem}-{switch}.tsv"
  let exe ← IO.FS.realPath ixExe
  let out ← IO.Process.output {
    cmd := exe.toString
    args := #["validate-lean", "--local", "--workers", "8", file]
    env := #[("LD_LIBRARY_PATH", none), ("IX_VALIDATE_AUXTABLE", some tsv.toString),
             ("IX_PASS3", if switch == "on" then some "images" else none)] }
  IO.FS.writeFile (dir / s!"{stem}-{switch}.log") (out.stdout ++ out.stderr)
  let verdicts := ((out.stdout.splitOn "\n").find? (·.startsWith "[validate-lean] VERDICTS")).getD "no verdicts"
  if !(← tsv.pathExists) then return (#[], verdicts)
  let lines := (← IO.FS.readFile tsv).splitOn "\n" |>.drop 1 |>.filter (!·.isEmpty)
  let rows := lines.toArray.filterMap fun l =>
    match l.splitOn "\t" with
    | [n, st, d, ph, v] => some { file := stem, switch, name := n, status := st,
                                  differs := d == "true", phase := ph, verdict := v }
    | _ => none
  return (rows, verdicts)

/-- The family and presentation of a name: a twin presentation's namespace,
    else the prototype case and its `Src`/`Can` part. -/
def familyOf (n : String) : String × String := Id.run do
  let mut best : Option (String × String × Nat) := none
  for f in Tests.Ix.Compile.Twins.allFamilies do
    for p in f.pres do
      let ns := p.ns.toString
      if n.startsWith (ns ++ ".") then
        let fam := (f.fixture.toString.splitOn ".").getLast!
        if best.all (·.2.2 < ns.length) then best := some (fam, p.id, ns.length)
  match best with
  | some (f, p, _) => return (f, p)
  | none =>
    -- outside every presentation: the shared data of a twin file (e.g.
    -- `Twins.Cliques.Common`), else a prototype case and its part
    let rel := ((n.dropPrefix "Tests.Ix.Compile.Twins.").toString)
    match rel.splitOn "." with
    | a :: b :: _ => return (if rel != n then s!"{a}.{b}" else a, if rel != n then "(shared)" else b)
    | _ => return (n, "")

/-- Does a non-canonical entry concern an auxiliary (a regenerated kind, or a
    constructor of a regenerated `IndPredBelow`)? -/
def ncAux (e : Tests.Ix.Compile.NonCanonical.NonCanonicalEntry) : Bool :=
  let n := Ix.Name.fromLeanName e.constant
  (Ix.AuxGen.classifyAuxGen n).isSome ||
    (match n with
     | .str p _ _ => (Ix.AuxGen.classifyAuxGen p).any (·.1 == Ix.AuxGen.AuxKind.below)
     | _ => false)

/-- The full names of an entry in its two presentations. -/
def ncNames (e : Tests.Ix.Compile.NonCanonical.NonCanonicalEntry) : List String := Id.run do
  let some fam := Tests.Ix.Compile.Twins.allFamilies.find? (·.fixture == e.fixture) | return []
  let mut out := []
  for p in fam.pres do
    if p.id == e.presA || p.id == e.presB then out := (p.ns ++ e.constant).toString :: out
  return out

def run : IO UInt32 := do
  let dir ← IO.FS.createTempDir
  let t0 ← IO.monoMsNow
  let todo := files.flatMap fun f => [(f, "off"), (f, "on")]
  let mut pending : Array (Task (Except IO.Error (Array Row × String))) := #[]
  let mut results : Array (Array Row × String) := #[]
  for (f, s) in todo do
    if pending.size ≥ 4 then
      results := results.push (← IO.ofExcept pending[0]!.get)
      pending := pending.extract 1 pending.size
    pending := pending.push (← IO.asTask (runOne dir f s))
  for t in pending do results := results.push (← IO.ofExcept (← IO.wait t))
  for ((f, s), (_, v)) in todo.zip results.toList do
    IO.println s!"[validate-lean-nc] {(System.FilePath.mk f).fileStem.getD f} {s}: {v}"
  let rows := results.foldl (fun acc (rs, _) => acc ++ rs) #[]
  -- the non-canonical entries naming each constant
  let entries := Tests.Ix.Compile.NonCanonical.nonCanonical
  let mut ncBy : Std.HashMap String (Array String) := {}
  for e in entries do
    for n in ncNames e do
      ncBy := ncBy.insert n ((ncBy.getD n #[]).push s!"{e.cause.tag} ({e.presA}/{e.presB})")
  let mut unmatched : Array String := #[]
  let mut nDiff := 0
  let mut nEqual := 0
  let mut prop1 : Array String := #[]
  IO.println "| family | presentation | auxiliary | switch | block | phase | verdict | match |"
  IO.println "|---|---|---|---|---|---|---|---|"
  for r in rows do
    if !r.differs then
      nEqual := nEqual + 1
      continue
    nDiff := nDiff + 1
    let (fam, pres) := familyOf r.name
    let nc := ", ".intercalate (ncBy.getD r.name #[]).toList
    let cls : String :=
      if r.phase.startsWith "7" then
        if r.verdict == "pass" then "image of a changed block (Def 3.4/3.5)" else "UNMATCHED (image fails phase 7)"
      else if r.phase.startsWith "8" then
        if r.verdict == "pass" then "Lean's IndPredBelow family of a changed Prop block (INDPRED-BELOW, §4.6)"
        else "UNMATCHED (provenance fails)"
      else if r.phase.startsWith "6 oracle leg: changed" then "UNMATCHED (changed block without `_ix` names under Pass 3)"
      else if r.phase.startsWith "6" then
        match defectOf? r.name with
        | some id => id
        | none => "UNMATCHED (phase-6 exception without a defect id)"
      else "surgery path (switch off; retired by Pass 3)"
    if r.phase.startsWith "6" && !r.phase.startsWith "6 oracle leg: changed" && (defectOf? r.name).isNone then
      prop1 := prop1.push r.name
    if cls.startsWith "UNMATCHED" then unmatched := unmatched.push s!"{r.file} {r.switch} {r.name}: {cls}"
    let short := (r.name.splitOn ".").drop ((r.name.splitOn ".").length - 3) |> ".".intercalate
    IO.println s!"| {fam} | {pres} | {short} | {r.switch} | {r.status} | {r.phase} | {r.verdict} | {cls}{if nc.isEmpty then "" else s!"; NC: {nc}"} |"
  -- every non-canonical entry about an auxiliary appears in the output
  let rowNames : Std.HashMap String (Array Row) := rows.foldl (fun m r =>
    m.insert r.name ((m.getD r.name #[]).push r)) {}
  let auxEntries := entries.filter ncAux
  let mut missing : Array String := #[]
  IO.println ""
  IO.println "| non-canonical entry (aux) | cause | presentations | validator rows (switch: phase verdict) |"
  IO.println "|---|---|---|---|"
  for e in auxEntries do
    let ns := ncNames e
    let hits := ns.flatMap fun n => ((rowNames.getD n #[]).toList.map fun r =>
      s!"{r.switch}: {(r.name.splitOn ".").getLast!}@{familyOf r.name |>.2} {r.phase.take 14} {r.verdict}{if r.differs then " (≠Lean)" else ""}")
    if hits.isEmpty then missing := missing.push s!"{e.fixture} {e.presA}/{e.presB} {e.constant}"
    IO.println s!"| {(e.fixture.toString.splitOn ".").getLast!}.{e.constant} | {e.cause.tag} | {e.presA}/{e.presB} | {if hits.isEmpty then "MISSING" else "; ".intercalate hits} |"
  IO.println ""
  IO.println s!"[validate-lean-nc] {rows.size} rows, {nDiff} differing from Lean's form, {nEqual} equal; \
{auxEntries.length} non-canonical entries concern an auxiliary"
  IO.println s!"[validate-lean-nc] property 1 (no expected difference wrongly rejected): \
{if prop1.isEmpty then "holds" else s!"VIOLATED by {prop1.size}"}"
  IO.println s!"[validate-lean-nc] property 2 (no unexpected difference silently passed): \
{unmatched.size} UNMATCHED row(s), {missing.size} non-canonical aux entr(ies) missing from the output"
  for u in unmatched do IO.println s!"[validate-lean-nc] UNMATCHED {u}"
  for m in missing do IO.println s!"[validate-lean-nc] MISSING {m}"
  IO.println s!"[validate-lean-nc] {(← IO.monoMsNow) - t0} ms"
  IO.FS.removeDirAll dir
  return if unmatched.isEmpty && missing.isEmpty && prop1.isEmpty then 0 else 1

end Tests.Ix.Compile.ValidateLeanNC
