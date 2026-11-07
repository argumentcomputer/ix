import Lean
import IxCC.Tools.Check

/-! Generator for `fixtures/ixon-v4/src-tables.tsv` (design note 01 §4.2).

It enumerates `@[macro_inline]` declarations over the Lean `Init`
environment of the running toolchain (excluding the generated `T.ctorIdx`
functions), requires exactly 28 of them, adds
`Bool.or`/`Bool.and` (lazy through their `Bool.rec` bodies) and
`Lean.opaqueId` (opaque-by-value), compiles their closure with the pinned ix
producer, resolves every name with `ix addr-of`, and writes one TSV row per
constant plus a provenance JSON. The by-name arity of a `lazy` row is the
number of leading λs of its Lean value.

Regeneration is a manual gate:

```
lake exe pin-src-tables --ix PATH/TO/ix --work plans/<task>/src-tables \
  --out fixtures/ixon-v4/src-tables.tsv \
  --provenance fixtures/ixon-v4/src-tables.provenance.json \
  --names fixtures/ixon-v4/src-names.tsv
```

`--diagnostics fixtures/ixon-v4/src-diag` and `--sortpoly
fixtures/ixon-v4/src-sortpoly` instead compile a roots-only fixture from the
Lean source in that directory.
-/

open Lean IxCC.Tools.Check

namespace PinSrcTables

def expectedMacroInline : Nat := 28

/-- Named constants added to the lazy rows beside the `macro_inline` set. -/
def extraLazy : List Name := [`Bool.or, `Bool.and]

def opaqueByValue : List Name := [`Lean.opaqueId]

/-- Names resolved for tests only (`src-names.tsv`, an untrusted test oracle:
the relevance census of design note 02 §13.1 and runtime-set reports). -/
def censusNames : List Name :=
  [`Eq, `Eq.rec, `HEq, `HEq.rec, `And, `And.rec, `Acc, `Acc.rec, `Acc.intro, `True, `True.rec,
   `False, `False.rec, `Empty, `Empty.rec, `Exists, `Exists.rec, `Fin, `Subtype, `BitVec,
   `UInt64, `Char, `OfNat, `HAdd, `Decidable, `Decidable.isFalse, `Decidable.isTrue,
   `Decidable.rec, `Decidable.casesOn, `Bool.rec, `Bool.casesOn, `ForInStep.rec,
   `ForInStep.casesOn]

/-- The generated `T.ctorIdx` functions of every inductive are also `macro_inline`;
they are not source declarations and stay on δ. -/
def isCtorIdx : Name → Bool
  | .str _ "ctorIdx" => true
  | _ => false

def leadingLams : Expr → Nat
  | .lam _ _ body _ => leadingLams body + 1
  | .mdata _ e => leadingLams e
  | _ => 0

def valueOf (env : Environment) (name : Name) : IO Expr := do
  match env.find? name with
  | some (.defnInfo info) => pure info.value
  | some (.opaqueInfo info) => pure info.value
  | some _ => throw (IO.userError s!"{name}: not a definition")
  | none => throw (IO.userError s!"{name}: not in the Init environment")

/-- A roots-only fixture: a Lean source in its directory, the file stem of
its closure and sidecar, and its roots. -/
structure RootsFixture where
  source : String
  stem : String
  roots : List Name

/-- The admission-diagnostics fixture `fixtures/ixon-v4/src-diag/`. -/
def diagFixture : RootsFixture where
  source := "Diag.lean"
  stem := "diag"
  roots := [`SrcDiag.rootPartial, `SrcDiag.rootMixHash, `SrcDiag.rootFloat,
    `SrcDiag.rootClassical, `SrcDiag.rootSorry, `SrcDiag.rootOpaqueId]

/-- The sort-polymorphism fixture `fixtures/ixon-v4/src-sortpoly/` (level-exact
relevance, D18). -/
def sortPolyFixture : RootsFixture where
  source := "SortPoly.lean"
  stem := "sortpoly"
  roots := [`SortPoly.comp, `SortPoly.throughRoot, `SortPoly.punitCases,
    `SortPoly.punitCasesType, `SortPoly.punitRec, `SortPoly.unitBoth, `SortPoly.sigmaRoot,
    `SortPoly.typeArg]

/-- Compile a roots-only fixture (anonymous and named), resolve its roots and
write the closure, its `ixcc/k1-equations/1` sidecar (roots only) and
a provenance record. -/
def rootsFixture (fx : RootsFixture) (ix : String) (work dir : System.FilePath)
    (revision : String) : IO Unit := do
  IO.FS.createDirAll work
  let source := dir / fx.source
  let closure := dir / s!"{fx.stem}.ixe"
  let named := work / s!"{fx.stem}.named.ixe"
  let consts := String.intercalate "," (fx.roots.map toString)
  let _ ← run ix #["compile", "--no-build", "--consts", consts, "--anon", "--out", closure.toString,
    source.toString]
  let _ ← run ix #["compile", "--no-build", "--consts", consts, "--out", named.toString,
    source.toString]
  let mut roots : Array Json := #[]
  for name in fx.roots do
    let output ← run ix #["addr-of", "--ixe", named.toString, name.toString]
    let address := (words output).getLastD ""
    need (isHex 64 address) s!"{name}: ix addr-of gave {repr output}"
    roots := roots.push (Json.mkObj [("name", name.toString), ("address", address)])
  let sidecar := dir / s!"{fx.stem}.equations.json"
  IO.FS.writeFile sidecar ((Json.mkObj [("format", "ixcc/k1-equations/1"),
    ("source", fx.source), ("roots", Json.arr roots), ("equations", Json.arr #[]),
    ("failures", Json.arr #[])]).pretty ++ "\n")
  IO.FS.writeFile (dir / "provenance.json") ((Json.mkObj [
    ("producer_version", String.intercalate " " (words (← run ix #["--version"]))),
    ("producer_revision", revision),
    ("producer_binary_sha256", ← sha256 ix),
    ("commands", toJson [
      s!"ix compile --no-build --consts <roots> --anon --out {fx.stem}.ixe {fx.source}",
      s!"ix compile --no-build --consts <roots> --out {fx.stem}.named.ixe {fx.source}",
      s!"ix addr-of --ixe {fx.stem}.named.ixe NAME, for every root"]),
    ("source_sha256", ← sha256 source),
    ("named_env_sha256", ← sha256 named),
    ("files", Json.mkObj [(s!"{fx.stem}.ixe", toJson (← sha256 closure)),
      (s!"{fx.stem}.equations.json", toJson (← sha256 sidecar))])]).pretty ++ "\n")
  IO.println s!"wrote {closure} with {fx.roots.length} roots"


/-! ## Repinning `IxCC.Src.Pinned`

After a refreeze, `--repin FILE --old-primitives OLD --old-tables OLD` rewrites
every pinned address in FILE (as a hex string or a `0x` numeral) from the old
`primitives.tsv`/`src-tables.tsv` rows to the current ones, matched by name.
An old address that two rows map to different new addresses, or a pinned
address no old row names, is an error; `tests-src` then compares the tables
with the TSVs. -/

/-- `name ↦ address` rows of a `primitives.tsv` (name, address) or
`src-tables.tsv` (kind, name, address, arity) file. -/
def tsvAddresses (path : System.FilePath) : IO (List (String × String)) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").filterMap fun line =>
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn "\t" with
      | [name, address] => some (name, address)
      | [_, name, address, _] => some (name, address)
      | _ => none

def repin (file oldPrims oldTables : System.FilePath) (newPrims newTables : System.FilePath) :
    IO Unit := do
  let old := (← tsvAddresses oldPrims) ++ (← tsvAddresses oldTables)
  let new := (← tsvAddresses newPrims) ++ (← tsvAddresses newTables)
  let mut map : List (String × String) := []
  for (name, before) in old do
    let some after := (new.find? (·.1 == name)).map (·.2)
      | throw (IO.userError s!"{name}: in the old tables, not in the new ones")
    match map.find? (·.1 == before) with
    | some (_, other) => need (other == after) s!"{before}: maps to {other} and {after}"
    | none => map := (before, after) :: map
  let mut text ← IO.FS.readFile file
  let mut replaced := 0
  -- two passes through placeholders, so a new address that equals another
  -- row's old address is never rewritten twice
  for h : i in [:map.length] do
    let before := map[i].1
    replaced := replaced + ((text.splitOn before).length - 1)
    text := text.replace before s!"@@pin{i}@@"
  for h : i in [:map.length] do
    text := text.replace s!"@@pin{i}@@" map[i].2
  -- no old address that is not also a current one is left
  let current := new.map (·.2)
  for (before, _) in map do
    need (current.contains before || (text.splitOn before).length == 1)
      s!"{before}: an old address is still pinned"
  IO.FS.writeFile file text
  IO.println s!"repinned {replaced} occurrences of {map.length} addresses in {file}"

def main (args : List String) : IO Unit := do
  let options ← checked (parseArgs ["--ix", "--work", "--out", "--provenance", "--names", "--revision",
    "--diagnostics", "--sortpoly", "--repin", "--old-primitives", "--old-tables"] args)
  if let some file := optional options "--repin" then
    let some oldPrims := optional options "--old-primitives" | throw (IO.userError "missing --old-primitives")
    let some oldTables := optional options "--old-tables" | throw (IO.userError "missing --old-tables")
    repin file oldPrims oldTables "fixtures/ixon-v4/primitives.tsv" "fixtures/ixon-v4/src-tables.tsv"
    return
  for (flag, fx) in [("--diagnostics", diagFixture), ("--sortpoly", sortPolyFixture)] do
    if let some dir := optional options flag then
      let some ix := optional options "--ix" | throw (IO.userError "missing --ix")
      rootsFixture fx ix (option options "--work" "plans/src-tables") dir
        (option options "--revision" "unrecorded")
      return
  let some ix := optional options "--ix" | throw (IO.userError "missing --ix")
  let work : System.FilePath := option options "--work" "plans/src-tables"
  let out : System.FilePath := option options "--out" "fixtures/ixon-v4/src-tables.tsv"
  let provenance : System.FilePath :=
    option options "--provenance" "fixtures/ixon-v4/src-tables.provenance.json"
  let namesOut : System.FilePath := option options "--names" "fixtures/ixon-v4/src-names.tsv"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Init }] {} (trustLevel := 1024)
  let macroInline := (env.constants.fold (init := #[]) fun acc name _ =>
    if Compiler.hasMacroInlineAttribute env name && !isCtorIdx name then acc.push name else acc).qsort
      (fun a b => a.toString < b.toString)
  need (macroInline.size == expectedMacroInline)
    s!"expected {expectedMacroInline} macro_inline declarations, found {macroInline.size}: {macroInline}"
  let lazy := macroInline.toList ++ extraLazy
  let mut rows : Array (String × Name × Option Nat) := #[]
  for name in lazy do
    let arity := leadingLams (← valueOf env name)
    need (arity ≥ 1) s!"{name}: a lazy constant needs a leading λ"
    rows := rows.push ("lazy", name, some arity)
  for name in opaqueByValue do
    let _ ← valueOf env name
    rows := rows.push ("opaque-by-value", name, none)
  IO.FS.createDirAll work
  let source := work / "SrcTables.lean"
  IO.FS.writeFile source "/-! Seed file for `ix compile --consts`: the Init environment only. -/\n"
  let named := work / "src-tables.named.ixe"
  let names := String.intercalate ","
    ((rows.toList.map fun (_, n, _) => n.toString) ++ censusNames.map toString)
  let _ ← run ix #["compile", "--no-build", "--consts", names, "--out", named.toString,
    source.toString]
  let mut lines : Array String := #[
    "# Src pinned tables (design note 01 §4.2), generated by scripts/PinSrcTables.lean.",
    "# kind\tname\taddress\tarity (by-name arity of lazy rows; - otherwise)"]
  let mut entries : Array Json := #[]
  for (kind, name, arity) in rows do
    let output ← run ix #["addr-of", "--ixe", named.toString, name.toString]
    let address := (words output).getLastD ""
    need (isHex 64 address) s!"{name}: ix addr-of gave {repr output}"
    let arityText := match arity with | some a => toString a | none => "-"
    lines := lines.push s!"{kind}\t{name}\t{address}\t{arityText}"
    entries := entries.push (Json.mkObj [("kind", kind), ("name", name.toString),
      ("address", address), ("arity", match arity with | some a => toJson a | none => Json.null)])
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  let mut nameLines : Array String := #[
    "# Test-only name resolution for the relevance census (untrusted), generated by",
    "# scripts/PinSrcTables.lean with the same ix run as src-tables.tsv.",
    "# name\taddress"]
  for name in censusNames do
    let output ← run ix #["addr-of", "--ixe", named.toString, name.toString]
    let address := (words output).getLastD ""
    need (isHex 64 address) s!"{name}: ix addr-of gave {repr output}"
    nameLines := nameLines.push s!"{name}\t{address}"
  IO.FS.writeFile namesOut (String.intercalate "\n" nameLines.toList ++ "\n")
  let version := String.intercalate " " (words (← run ix #["--version"]))
  let binary ← sha256 ix
  IO.FS.writeFile provenance ((Json.mkObj [
    ("format", "ixcc/src-tables/1"),
    ("producer_version", version),
    ("producer_revision", option options "--revision" "unrecorded"),
    ("producer_binary_sha256", binary),
    ("lean", Lean.versionString),
    ("macro_inline_count", toJson macroInline.size),
    ("commands", toJson [s!"ix compile --no-build --consts <names> --out src-tables.named.ixe SrcTables.lean",
      "ix addr-of --ixe src-tables.named.ixe NAME, for every row"]),
    ("tsv_sha256", ← sha256 out),
    ("names_tsv_sha256", ← sha256 namesOut),
    ("rows", Json.arr entries)]).pretty ++ "\n")
  IO.println s!"wrote {rows.size} rows to {out}"

end PinSrcTables

def main (args : List String) : IO UInt32 :=
  cli "pin-src-tables" (PinSrcTables.main args)
