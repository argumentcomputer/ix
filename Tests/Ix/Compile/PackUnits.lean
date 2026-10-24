/-
  pack-units: `ix pack` carries the root's reference closure, never its
  compilation unit (owner, 2026-10-07; `Ix.Cli.PackCmd`). The suite keeps
  its name from M1-h, when the pack carried whole logical units.

  Source: the selected closure of the fixture
  `Tests/Ix/Compile/Fixtures/PackUnits.lean`, that is of its own constants
  (`PackU.*`; `Ix.EnvScope.localConstList`, the `--local` scope). It is
  compiled by the Lean pipeline (`compileLeanInput`) and written as an
  `.ixe` from the output's bytes. Each root below is packed as `ix pack`
  packs it (`Ixon.rsPackEnv`, with metadata).

  2. **The source's bytes.** Every bundle member keeps the source's bytes:
     each carried constant's bytes equal the source's at the same address,
     and each `Named` entry of the bundle has the source's address. The
     bundle's `main` is the root.
  3. **The closure, not the unit.** `PackU.Tree.size`'s bundle does not
     carry `PackU.Tree.size.eq_1`. That lemma is an on-demand member of
     `Tree.size`'s unit, which the selected source carries, but
     `Tree.size` does not reference it (the M1-h pack carried it). The
     lemma's own bundle carries `PackU.Tree.size`, which it references.

  Ported from a9cf3607 `Tests/Ix/Compile/PackUnits.lean` (the M6R slice 6
  version), keeping the donor's numbering:
  - Check 1 is dropped. It is the Lean oracle `PackParity`, which uses
    `Ix.Tc` projection addresses, so it belongs to CQX.2/TT-13; so is
    `PACK_UNITS_IXE`.
  - The reserved-name check of check 3 (Pass 3's `_ix` constants) is
    dropped.
  - The source is written from `out.bytes`, not `rsSerEnv out.env`.
  - `readIxe` and `ixToLeanName` come from the closure harness, not from
    `Ix.Cli.PackCmd` (TT-13).
  - Files go to a temporary directory, not `.lake/pack-units` (R11-24).

  Run with: `lake test -- --ignored pack-units`.
-/
import Ix.Meta
import Ix.EnvScope
import Ix.Ixon
import Tests.Ix.Compile.ClosureHarness

open Lean
open Tests.Ix.Compile.ClosureHarness

namespace Tests.Ix.Compile.PackUnits

def fixture : System.FilePath := "Tests/Ix/Compile/Fixtures/PackUnits.lean"

/-- A recursive definition with on-demand equation lemmas, a definition
over a mutual block, a theorem over injectivity, and a constructor of the
mutual block. -/
def roots : List Name := [`PackU.Tree.size, `PackU.useA, `PackU.node_inj, `PackU.B.b]

/-- Pack `r` from `srcPath` as `ix pack` does (Rust, with metadata, no cut
points) and read the bundle back. -/
def pack (srcPath dir : System.FilePath) (r : Name) : IO Ixon.Env := do
  let outPath := dir / s!"{r}.ixe"
  Ixon.rsPackEnv srcPath.toString (r.toString (escape := false)) #[] outPath.toString false false
  readIxe outPath

def run : IO UInt32 := do
  let fe ← getFileEnvCore fixture
  let closure := Ix.EnvScope.localConstList fe
  let dir ← IO.FS.createTempDir
  IO.println s!"[pack-units] files in {dir}"
  let mut errors : Array String := #[]
  let out ← compileClosure fe.env closure
  unless out.cenv.ungrounded.isEmpty do
    errors := errors.push s!"{out.cenv.ungrounded.size} refusals"
  let srcPath := dir / "source.ixe"
  IO.FS.writeBinFile srcPath out.bytes
  let src ← readIxe srcPath
  IO.println s!"[pack-units] source {src.named.size} names, {src.consts.size} constants"
  let addr (n : Name) : Option Address := (src.named.get? (ixN n)).map (·.addr)
  -- 2. every bundle member keeps the source's bytes; `main` is the root
  for r in roots do
    let b ← pack srcPath dir r
    let mut byteDiffs := 0
    for (a, lc) in b.consts.toList do
      match src.consts.get? a with
      | some slc => if lc.rawBytes != slc.rawBytes then byteDiffs := byteDiffs + 1
      | none => byteDiffs := byteDiffs + 1
    let mut namedDiffs := 0
    for (n, nd) in b.named.toList do
      if (src.named.get? n).map (·.addr) != some nd.addr then namedDiffs := namedDiffs + 1
      unless b.originalHintOverrides.get? n == src.originalHintOverrides.get? n do
        errors := errors.push s!"{r}: original hint was dropped for {n.pretty}"
      if let some (original, _) := nd.original then
        unless b.consts.contains original || b.originals.contains original do
          errors := errors.push s!"{r}: missing original for {n.pretty}"
    for (a, raw) in b.originals do
      let source := (src.consts.get? a).orElse fun _ => src.originals.get? a
      unless source.map Ixon.LazyConstant.rawBytes == some raw.rawBytes && !b.consts.contains a do
        errors := errors.push s!"{r}: original bytes changed or entered canonical constants at {a}"
    for (name, hint) in b.originalHintOverrides do
      unless b.named.contains name && src.originalHintOverrides.get? name == some hint do
        errors := errors.push s!"{r}: original hint changed or lost its retained name"
    IO.println s!"[pack-units] {r}: {b.consts.size} constants, {b.named.size} names; \
      byte differences {byteDiffs}; Named differences {namedDiffs}"
    unless (addr r).isSome && b.main == addr r do
      errors := errors.push s!"{r}: main is not the root"
    if byteDiffs + namedDiffs > 0 then
      errors := errors.push s!"{r}: {byteDiffs} constant(s), {namedDiffs} Named entr(ies) differ \
        from the source"
  -- 3. the closure, not the unit
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
  for e in errors do IO.println s!"[pack-units] FAIL {e}"
  IO.println s!"[pack-units] {if errors.isEmpty then "PASS" else s!"FAIL ({errors.size})"}: \
    {roots.length} roots checked for bytes"
  if errors.isEmpty then IO.FS.removeDirAll dir
  return if errors.isEmpty then 0 else 1

end Tests.Ix.Compile.PackUnits
