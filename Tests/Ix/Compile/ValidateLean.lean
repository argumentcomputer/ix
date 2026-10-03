/-
  validate-lean: `ix validate-lean --local`, the Phase A validator of record
  (`Ix.Cli.ValidateLeanCmd`), on every fixture of `aux-cert`, the prototype's
  cases (`Tests/Ix/Compile/Image/C*.lean`), the twin families
  (`Tests/Ix/Compile/Twins/*`) and the library twins
  (`Tests/Ix/Compile/Oracle/Lib.lean`), with the Pass 3 switch off and on,
  against the expected verdict table below.

  Every phase passes, except:
  - phase 7 (image rules) skips when there is no changed block with `_ix`
    names (always with the switch off; phase 6 fails a changed block without
    `_ix` names under the switch, so a skip cannot hide a lost image);
  - the recorded pre-existing failures (`expected`), each by defect id; a
    recorded failure that passes is a problem too, so the table stays exact;
  - the files Lean itself rejects (`leanRejects`), which produce no report.

  Run with: `lake test -- --ignored validate-lean` (after `lake build ix`).
  `VALIDATE_LEAN_ONLY=<stem,…>` restricts the files; `VALIDATE_LEAN_KEEP=<dir>`
  keeps the logs and reports.
-/
import Lean.Data.Json
import Tests.Ix.Compile.AuxCert

open Lean

namespace Tests.Ix.Compile.ValidateLean

/-- A recorded failure: the file stem, the switch state (`off`, `on` or `*`),
the phases that fail, and the cause by defect id. -/
structure Expected where
  stem : String
  switch : String
  phases : List String
  cause : String

/-- The expected verdict table (A3v, 2026-10-03). The causes:
- A0 refusals on the surgery path (switch off; D13 = WB-B4): the compile
  refuses a collapse call site (phase 1), so the output is partial and the
  decompile misses the refused constants (phase 5). Pass 3 compiles them
  faithfully: these pass with the switch on.
- A0 evaporation refusal ("not a one-motive recursor", both modes): phase 1;
  the partial output's siblings of the refused component fail phases 4–5
  (REFUSED-SIBLING).
- Compile totality defects by id (WB-A2, WB-A3, WB-A7, BB-F6, BB-F8).
- Decompile and auxiliary defects by id (BB-F5, WB-B6, WB-B9).
- BELOW-ORDER: Pass 1's order of Lean's own `IndPredBelow` block of a
  collapsed Prop pair, rejected by the meta ingress's canonicity gate.
- A3V-IPB (new, found by the oracle leg): for the nested Prop block
  `F8NoSplit` (BB-F8's passing neighbour) the Ix `IndPredBelow` family's
  `.rec`/`.casesOn` (`A.below.rec`, `A.below_1.rec`, `.casesOn`) differ by
  address from Lean's own, in both switch states. -/
def expected : List Expected := [
  -- A0 collapse refusals on the surgery path
  ⟨"SurgCollapse", "off", ["1", "5"], "A0 refusal (D13: collapse call site drops distinct arguments)"⟩,
  ⟨"F4FlatAlphaUsers", "off", ["1", "5"], "A0 refusal (collapse call site is a partial application)"⟩,
  ⟨"F4_NestedAlphaUsers", "off", ["1", "5"], "A0 refusal (collapse call site is a partial application)"⟩,
  ⟨"C5Collapse", "off", ["1", "5"], "A0 refusal (D13)"⟩,
  ⟨"C6NestedCollapse", "off", ["1", "5"], "A0 refusal (collapse call site is a partial application)"⟩,
  ⟨"C7IndPred", "off", ["1", "5"], "A0 refusal (D13, on `below` call sites)"⟩,
  ⟨"C8Collapse3", "off", ["1", "5"], "A0 refusal (D13)"⟩,
  ⟨"C9Params", "off", ["1", "5"], "A0 refusal (D13)"⟩,
  ⟨"Proto", "off", ["1", "5"], "A0 refusals (D13, partial applications) of the prototype twins"⟩,
  -- A0 evaporation refusal, both modes
  ⟨"C4Evap", "off", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"C4Evap", "on", ["1", "5"], "A0 refusal (not a one-motive recursor)"⟩,
  ⟨"F3_SplitRoseRace", "*", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"NestRoseSplit", "*", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"NestMutExt", "off", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  ⟨"NestMutExt", "on", ["1", "5"], "A0 refusal (not a one-motive recursor)"⟩,
  ⟨"NestMutExtA", "*", ["1", "4", "5"], "A0 refusal (not a one-motive recursor); REFUSED-SIBLING"⟩,
  -- compile totality defects
  ⟨"AliasIdx", "*", ["1", "5"], "WB-A3"⟩,
  ⟨"KernelSpec", "*", ["1", "5"], "WB-A7"⟩,
  ⟨"SurgIdx", "off", ["1", "5"], "WB-A2 (fixed by Pass 3)"⟩,
  ⟨"F6_OrderIdxBrecOn", "off", ["1", "5"], "BB-F6 (= WB-A2; fixed by Pass 3)"⟩,
  ⟨"F8_PropSplitNested", "off", ["1", "5"], "BB-F8 (fixed by Pass 3)"⟩,
  -- decompile and auxiliary defects
  ⟨"F5_SigmaNestedNested", "*", ["5"], "BB-F5 (decompile regenerates T.rec differently)"⟩,
  ⟨"RecAlias", "*", ["5", "6", "8"], "WB-B6 (Ix's PA.below family ≠ Lean's)"⟩,
  ⟨"UnsafeI", "*", ["5", "6", "8"], "WB-B9 (Ix's UNestNeg.rec ≠ Lean's)"⟩,
  ⟨"Neighbours", "*", ["6", "8"], "A3V-IPB (F8NoSplit's IndPredBelow .rec/.casesOn ≠ Lean's)"⟩,
  -- Pass 1's IndPredBelow order of a collapsed Prop pair
  ⟨"PropCollapse", "on", ["4"], "BELOW-ORDER"⟩,
  -- the twin families: their RecAlias (WB-B6), SurgCollapse (A0) and
  -- PropCollapse (BELOW-ORDER) members
  ⟨"Repro", "off", ["1", "5", "6", "8"], "A0 refusal of Repro.Orig.SurgCollapse (D13); WB-B6"⟩,
  ⟨"Repro", "on", ["4", "5", "6", "8"], "BELOW-ORDER; WB-B6"⟩]

/-- Fixtures Lean itself rejects (the aux-cert record): no report. -/
def leanRejects : List String := ["PropEvap", "SortU", "SortURec", "SortUOpt"]

def files : List String :=
  Tests.Ix.Compile.AuxCert.fixtures.map (fun f => s!"Tests/Ix/Compile/AuxCert/{f.stem}.lean")
  ++ (["C1Perm", "C2Split", "C3PropSplit", "C4Evap", "C5Collapse", "C6NestedCollapse", "C7IndPred",
       "C8Collapse3", "C9Params"].map fun s => s!"Tests/Ix/Compile/Image/{s}.lean")
  ++ (["Cliques", "Proto", "Repro"].map fun s => s!"Tests/Ix/Compile/Twins/{s}.lean")
  ++ ["Tests/Ix/Compile/Oracle/Lib.lean"]

private def ixExe : System.FilePath := ".lake" / "build" / "bin" / "ix"

/-- A run's result: stem, switch, phase verdicts (none: no report), exit. -/
abbrev Row := String × String × Option (List (String × String)) × String

/-- One run: the phase verdicts by key (`pass`, `fail`, `skip`), or `none` when
no report was written. -/
def runOne (dir : System.FilePath) (file switch : String) :
    IO Row := do
  let stem := (System.FilePath.mk file).fileStem.getD file
  let report := dir / s!"{stem}-{switch}.json"
  let exe ← IO.FS.realPath ixExe
  let out ← IO.Process.output {
    cmd := exe.toString
    args := #["validate-lean", "--local", "--workers", "8", "--report", report.toString, file]
    env := #[("LD_LIBRARY_PATH", none),
             ("IX_PASS3", if switch == "on" then some "images" else none)] }
  IO.FS.writeFile (dir / s!"{stem}-{switch}.log") (out.stdout ++ out.stderr)
  if !(← report.pathExists) then return (stem, switch, none, s!"exit {out.exitCode}")
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile report))
  let phases ← IO.ofExcept (j.getObjValAs? (Array Json) "phases")
  let rows := phases.toList.filterMap fun p =>
    match p.getObjValAs? String "key", p.getObjValAs? String "result" with
    | .ok k, .ok r => some (k, r)
    | _, _ => none
  return (stem, switch, some rows, s!"exit {out.exitCode}")

def run : IO UInt32 := do
  let only := ((← IO.getEnv "VALIDATE_LEAN_ONLY").map (·.splitOn ",")).getD []
  let keep? := (← IO.getEnv "VALIDATE_LEAN_KEEP").map System.FilePath.mk
  let dir ← match keep? with
    | some d => do IO.FS.createDirAll d; pure d
    | none => IO.FS.createTempDir
  let todo := (files.filter fun f =>
      only.isEmpty || only.contains ((System.FilePath.mk f).fileStem.getD f)).flatMap fun f =>
    [(f, "off"), (f, "on")]
  let t0 ← IO.monoMsNow
  -- a pool of four runs at a time
  let mut results : Array Row := #[]
  let mut pending : Array (Task (Except IO.Error Row)) := #[]
  for (f, s) in todo do
    if pending.size ≥ 4 then
      results := results.push (← IO.ofExcept pending[0]!.get)
      pending := pending.extract 1 pending.size
    pending := pending.push (← IO.asTask (runOne dir f s))
  for t in pending do results := results.push (← IO.ofExcept (← IO.wait t))
  let mut problems : Array String := #[]
  for (stem, switch, rows?, exit) in results do
    let exp := expected.filter fun e => e.stem == stem && (e.switch == switch || e.switch == "*")
    let failing : List String := exp.flatMap (·.phases)
    let causes := ", ".intercalate (exp.map (·.cause))
    match rows? with
    | none =>
      if leanRejects.contains stem then
        IO.println s!"[validate-lean] {stem} {switch}: Lean rejects the file (aux-cert record; {exit})"
      else problems := problems.push s!"{stem} {switch}: no report ({exit})"
    | some rows =>
      let line := " ".intercalate (rows.map fun (k, r) => s!"{k}={r}")
      IO.println s!"[validate-lean] {stem} {switch}: {line}{if causes.isEmpty then "" else s!"  [{causes}]"}"
      if leanRejects.contains stem then
        problems := problems.push s!"{stem} {switch}: recorded as rejected by Lean, but a report was written"
      for (k, r) in rows do
        let want := failing.contains k
        if r == "fail" && !want then problems := problems.push s!"{stem} {switch}: phase {k} fails (not recorded)"
        if r != "fail" && want then problems := problems.push s!"{stem} {switch}: phase {k} recorded as failing ({causes}) but {r}"
        if r == "skip" && k != "7" then problems := problems.push s!"{stem} {switch}: phase {k} skipped"
  for p in problems do IO.println s!"[validate-lean] FAIL {p}"
  IO.println s!"[validate-lean] {results.size} runs ({todo.length / 2} files × 2 switch states), \
{problems.size} problem(s), {(← IO.monoMsNow) - t0} ms"
  if keep?.isNone then IO.FS.removeDirAll dir
  return if problems.isEmpty then 0 else 1

end Tests.Ix.Compile.ValidateLean
