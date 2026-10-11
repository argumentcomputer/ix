/-
  pack-units: `ix pack` carries the root's reference closure, never its
  compilation unit (owner, 2026-10-07; M6R slice 6; `Ix.Cli.PackCmd`). The
  suite keeps its name from M1-h, when the pack carried whole logical units
  (`packWholeUnits`, slice 5's `--rust-units`; both removed by slice 6).

  Source: the closure of the fixture `Tests/Ix/Compile/Pass/PackUnits.lean`'s
  own constants (`Ix.EnvScope.collectSelectedDeps`), compiled by the Lean
  pipeline (Pass 3) and written as an `.ixe`:

  1. **the Lean oracle** (`Tests.Ix.Compile.PackParity`): for every name of
     the source as a root (at most `PACK_UNITS_MAX`, default 2,000, the
     fixture's roots first), the Rust bundle (`Ixon.rsPackEnv`) is
     byte-identical to `Ixon.serEnv` of Lean's implementation of the closure
     (`packOracle`), and the first root's anonymous bundle too;
  2. for each root below, every bundle member keeps the whole compile's
     bytes: each carried constant's bytes equal the source's at the same
     address, and each `Named` entry of the bundle has the source's address;
  3. **the closure, not the unit**: `PackU.Tree.size`'s bundle does not carry
     its on-demand equation lemma `PackU.Tree.size.eq_1`, a member of its
     unit that it does not reference (the M1-h pack carried it), while the
     lemma's own bundle carries `PackU.Tree.size`; and some bundle carries a
     Pass 3 reserved-name constant (compiler-introduced constants travel with
     the closures that reference them; not vacuous).

  `PACK_UNITS_IXE=<a.ixe>,<b.ixe>,…` runs check 1 on stored compiles too (the
  compiled artifacts of `Tests/Ix/CompileCert/BlockDefs` and `ChangedDefs`,
  Init+Std): on one with at most 2,000 names every name is a root; otherwise
  `PACK_UNITS_IXE_MAX=<n>` (default 10) roots, a cover of the reserved-name
  shapes (`PackParity.defaultRoots`).

  Run with: `lake test -- --ignored pack-units`.
-/
import Ix.EnvScope
import Ix.CompileM
import Ix.Cli.PackCmd
import Tests.Ix.Compile.Pass3
import Tests.Ix.Compile.PackParity

open Lean

namespace Tests.Ix.Compile.PackUnits

open Ix.Cli.PackCmd (ixToLeanName readIxe)

def roots : List Name := [`PackU.Tree.size, `PackU.useA, `PackU.node_inj, `PackU.B.b]

/-- Pack `r` from `srcPath` (Rust, with metadata) and read the bundle back. -/
def pack (srcPath : System.FilePath) (dir : System.FilePath) (r : Name) : IO Ixon.Env := do
  let outPath := dir / s!"{r}.ixe"
  Ixon.rsPackEnv srcPath.toString (r.toString (escape := false)) #[] outPath.toString false false
  readIxe outPath.toString

def run : IO UInt32 := do
  let env ← getFileEnv "Tests/Ix/Compile/Pass/PackUnits.lean"
  let own := Tests.Ix.Compile.Pass3.ownConstants env
  let closure := Ix.EnvScope.collectSelectedDeps env own.toList
  let dir : System.FilePath := ".lake/pack-units"
  IO.FS.createDirAll dir
  let mut errors : Array String := #[]
  let unit : Tests.Ix.Compile.Pass3.CUnit := { name := "pack-units", env, seeds := own, closure }
  let out ← Tests.Ix.Compile.Pass3.compileUnit unit
  unless out.cenv.ungrounded.isEmpty do
    errors := errors.push s!"{out.cenv.ungrounded.size} refusals"
  let srcPath := dir / "source.ixe"
  IO.FS.writeBinFile srcPath (Ixon.rsSerEnv out.env)
  let src ← readIxe srcPath.toString
  IO.println s!"[pack-units] source {src.named.size} names, {src.consts.size} constants"
  -- 1. every name a root (bounded), against the Lean oracle
  let maxRoots := ((← IO.getEnv "PACK_UNITS_MAX").bind String.toNat?).getD 2000
  let every : Array Name := (src.named.toArray.map (ixToLeanName ·.1)).qsort (·.toString < ·.toString)
  let rs : Array Name := (roots.toArray ++ every.filter (!roots.contains ·)).extract 0 maxRoots
  errors := errors ++ (← Tests.Ix.Compile.PackParity.run "pack-units" srcPath.toString rs)
  -- 2. the whole compile's bytes
  let mut reservedCarried := 0
  for r in roots do
    let b ← pack srcPath dir r
    let mut byteDiffs := 0
    for (a, lc) in b.consts.toList do
      match src.consts.get? a with
      | some slc => if lc.get? != slc.get? then byteDiffs := byteDiffs + 1
      | none => byteDiffs := byteDiffs + 1
    let mut namedDiffs := 0
    for (n, nd) in b.named.toList do
      if (src.named.get? n).map (·.addr) != some nd.addr then namedDiffs := namedDiffs + 1
      if Tests.Ix.Compile.PackParity.hasReserved (ixToLeanName n) then
        reservedCarried := reservedCarried + 1
    IO.println s!"[pack-units] {r}: {b.consts.size} constants, {b.named.size} names; \
      byte differences {byteDiffs}; Named differences {namedDiffs}"
    unless b.main == ((src.named.get? (Ix.Name.fromLeanName r)).map (·.addr)) do
      errors := errors.push s!"{r}: main is not the root"
    if byteDiffs + namedDiffs > 0 then
      errors := errors.push s!"{r}: {byteDiffs} constant(s), {namedDiffs} Named entr(ies) differ from the source"
  -- 3. the closure, not the unit
  let addr (n : Name) : Option Address := (src.named.get? (Ix.Name.fromLeanName n)).map (·.addr)
  match addr `PackU.Tree.size, addr `PackU.Tree.size.eq_1 with
  | some sz, some eq1 =>
    let b ← pack srcPath dir `PackU.Tree.size
    if b.consts.contains eq1 then
      errors := errors.push "PackU.Tree.size's bundle carries its unit's equation lemma eq_1"
    let be ← pack srcPath dir `PackU.Tree.size.eq_1
    unless be.consts.contains sz do
      errors := errors.push "PackU.Tree.size.eq_1's bundle lacks PackU.Tree.size, which it references"
    IO.println s!"[pack-units] closure, not unit: PackU.Tree.size {b.consts.size} constants \
      (eq_1 carried: {b.consts.contains eq1}); PackU.Tree.size.eq_1 {be.consts.size} constants"
  | _, _ => errors := errors.push "the source lacks PackU.Tree.size or its eq_1 (fixture)"
  -- compiler-introduced constants travel: some bundle of the fixture's roots or of
  -- check 1's carries a reserved name
  if reservedCarried == 0 then
    let rsv := Tests.Ix.Compile.PackParity.defaultRoots src #[] 1
    match rsv[0]? with
    | some r =>
      let b ← pack srcPath dir r
      unless b.named.toList.any (Tests.Ix.Compile.PackParity.hasReserved <| ixToLeanName ·.1) do
        errors := errors.push s!"{r}: a reserved name's bundle carries no reserved name"
    | none => errors := errors.push "the source has no Pass 3 reserved name (the check is vacuous)"
  -- 1 on stored compiles
  if let some paths := ← IO.getEnv "PACK_UNITS_IXE" then
    let maxIxe := ((← IO.getEnv "PACK_UNITS_IXE_MAX").bind String.toNat?).getD 10
    for p in (paths.splitOn ",").filter (!·.isEmpty) do
      let art ← readIxe p
      let rs : Array Name := if art.named.size ≤ 2000 then
          (art.named.toArray.map (ixToLeanName ·.1)).qsort (·.toString < ·.toString)
        else Tests.Ix.Compile.PackParity.defaultRoots art #[] maxIxe
      errors := errors ++ (← Tests.Ix.Compile.PackParity.run p p rs)
  for e in errors do IO.println s!"[pack-units] FAIL {e}"
  IO.println s!"[pack-units] {if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}: \
    {rs.size} roots against the Lean oracle, {roots.length} checked for bytes (Pass 3)"
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.PackUnits
