/-
  pack-units: `ix pack` carries whole logical units (M1-h; design document
  §6.3; `Ix.Cli.PackCmd.packWholeUnits`).

  Source: the closure of the fixture `Tests/Ix/Compile/Pass/PackUnits.lean`'s
  own constants (`Ix.EnvScope.collectSelectedDeps`, whole units since M1-d),
  compiled by the Lean pipeline in each switch state and written as an `.ixe`.
  Per switch state:

  1. for every name the Lean environment declares, the unit view read from the compiled
     environment's names and metadata
     (`ixonUnitView`) gives, for every name of the source, the members that
     `Lean.unitMembers` gives over the Lean environment (restricted to the
     source's names);
  2. for each root, the bundle's units are whole: every member of the unit of
     every carried name (`Lean.unitMembers`, the Lean environment) that the
     source has is carried;
  3. every bundle member keeps the whole compile's bytes: each carried
     constant's bytes equal the source's at the same address, and each `Named`
     entry of the bundle has the source's address;
  4. negative control: the `--no-units` bundle of `PackU.Tree.size` lacks its
     on-demand equation lemma `PackU.Tree.size.eq_1` (the check of 2 fails on
     it), while the whole-unit bundle carries it.

  Run with: `lake test -- --ignored pack-units`.
-/
import Ix.EnvScope
import Ix.CompileM
import Ix.Cli.PackCmd
import Tests.Ix.Compile.Pass3

open Lean

namespace Tests.Ix.Compile.PackUnits

open Ix.Cli.PackCmd (ixToLeanName ixonUnitView packWholeUnits readIxe)

def roots : List Name := [`PackU.Tree.size, `PackU.useA, `PackU.node_inj, `PackU.B.b]

/-- The names of `src` whose constant `bundle` carries. -/
def carried (src bundle : Ixon.Env) : Array Name :=
  src.named.fold (init := #[]) fun acc n nd =>
    if bundle.consts.contains nd.addr then acc.push (ixToLeanName n) else acc

/-- Members of carried names' units (over the Lean environment) that the
source has and the bundle does not carry. -/
def unitGaps (env : Environment) (idx : Lean.UnitIndex) (src bundle : Ixon.Env) : Array (Name × Name) :=
  Id.run do
  let addrOf : Std.HashMap Name Address :=
    src.named.fold (fun m n nd => m.insert (ixToLeanName n) nd.addr) {}
  let mut out := #[]
  for n in carried src bundle do
    for m in Lean.unitMembers env.constants idx n do
      if let some a := addrOf.get? m then
        unless bundle.consts.contains a || bundle.assumptions.contains a do
          out := out.push (n, m)
  return out

def run : IO UInt32 := do
  let env ← getFileEnv "Tests/Ix/Compile/Pass/PackUnits.lean"
  let own := Tests.Ix.Compile.Pass3.ownConstants env
  let closure := Ix.EnvScope.collectSelectedDeps env own.toList
  let idx := Lean.unitIndex env.constants
  let dir : System.FilePath := ".lake/pack-units"
  IO.FS.createDirAll dir
  let mut errors : Array String := #[]
  for mode in [false, true] do
    let tag := if mode then "on" else "off"
    let unit : Tests.Ix.Compile.Pass3.CUnit := { name := s!"pack-units-{tag}", env, seeds := own, closure }
    let out ← Tests.Ix.Compile.Pass3.compileUnit unit mode
    unless out.cenv.ungrounded.isEmpty do
      errors := errors.push s!"{tag}: {out.cenv.ungrounded.size} refusals"
    let srcPath := dir / s!"source-{tag}.ixe"
    IO.FS.writeBinFile srcPath (Ixon.rsSerEnv out.env)
    let src ← readIxe srcPath.toString
    -- 1. the compiled unit view agrees with the Lean one
    let view := ixonUnitView src
    let vidx := view.index
    -- names the compiler introduces (synthetic `Ix.<hash>.…` block names, Pass 3's `_ix`
    -- canonical constants) have no Lean declaration and no Lean unit: counted, not compared
    let mut viewDiffs := 0
    let mut compilerNames := 0
    for (n, _) in src.named.toList do
      let ln := ixToLeanName n
      unless env.contains ln do
        compilerNames := compilerNames + 1
        continue
      let lean := (Lean.unitMembers env.constants idx ln).filter view.contains
      let ixon := view.members vidx ln
      unless lean.eraseDups.toArray.qsort Name.lt == ixon.eraseDups.toArray.qsort Name.lt do
        viewDiffs := viewDiffs + 1
        if viewDiffs ≤ 5 then
          errors := errors.push s!"{tag}: unit of {ln}: Lean {lean.eraseDups} / compiled {ixon.eraseDups}"
    IO.println s!"[pack-units] {tag}: source {src.named.size} names, {src.consts.size} constants; \
      unit view differences {viewDiffs} over the names Lean declares ({compilerNames} compiler-introduced names not compared)"
    -- 2, 3: whole units and the whole compile's bytes
    for r in roots do
      let outPath := dir / s!"{r}-{tag}.ixe"
      let (rounds, packed) ← packWholeUnits srcPath.toString (r.toString (escape := false)) #[]
        outPath.toString false false
      let b ← readIxe outPath.toString
      let gaps := unitGaps env idx src b
      let mut byteDiffs := 0
      for (a, lc) in b.consts.toList do
        match src.consts.get? a with
        | some slc => if lc.get? != slc.get? then byteDiffs := byteDiffs + 1
        | none => byteDiffs := byteDiffs + 1
      let mut namedDiffs := 0
      for (n, nd) in b.named.toList do
        if (src.named.get? n).map (·.addr) != some nd.addr then namedDiffs := namedDiffs + 1
      IO.println s!"[pack-units] {tag} {r}: {b.consts.size} constants, {(carried src b).size} names \
        ({packed} member bundle(s), {rounds} round(s)); unit gaps {gaps.size}; \
        byte differences {byteDiffs}; Named differences {namedDiffs}"
      unless b.main == ((src.named.get? (Ix.Name.fromLeanName r)).map (·.addr)) do
        errors := errors.push s!"{tag} {r}: main is not the root"
      for (n, m) in gaps.toList.take 5 do
        errors := errors.push s!"{tag} {r}: unit of {n} not whole: {m} missing"
      if byteDiffs + namedDiffs > 0 then
        errors := errors.push s!"{tag} {r}: {byteDiffs} constant(s), {namedDiffs} Named entr(ies) differ from the source"
    -- 4. negative control
    let thin := dir / s!"thin-{tag}.ixe"
    Ixon.rsPackEnv srcPath.toString "PackU.Tree.size" #[] thin.toString false false
    let tb ← readIxe thin.toString
    let eq1 := Ix.Name.fromLeanName `PackU.Tree.size.eq_1
    match src.named.get? eq1 with
    | none => errors := errors.push s!"{tag}: the source lacks PackU.Tree.size.eq_1 (fixture)"
    | some nd =>
      if tb.consts.contains nd.addr then
        errors := errors.push s!"{tag}: negative control: the value closure of PackU.Tree.size carries eq_1"
      let gaps := unitGaps env idx src tb
      unless gaps.any (·.2 == `PackU.Tree.size.eq_1) do
        errors := errors.push s!"{tag}: negative control: the unit check does not report eq_1 missing"
      IO.println s!"[pack-units] {tag} negative control (--no-units PackU.Tree.size): \
        {tb.consts.size} constants, unit gaps {gaps.size}"
  for e in errors do IO.println s!"[pack-units] FAIL {e}"
  IO.println s!"[pack-units] {if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}: \
    {roots.length} roots × 2 switch states"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.PackUnits
