import Lean
import IxCC.Tools.Check
import IxCCTests.Corpus.Manifest
import IxCC.Src.Word

/-! Generator for `fixtures/ixon-v4/src-tables.tsv`.

It enumerates `@[macro_inline]` declarations over the Lean `Init`
environment of the running toolchain (excluding the generated `T.ctorIdx`
functions), requires exactly 28 of them, adds
`Bool.or`/`Bool.and` (lazy through their `Bool.rec` bodies),
`Lean.opaqueId` (opaque-by-value) and the fixed-width words' constants
(`word-type`, `word-ctor`, `word-part` and `word` rows, stage W1), compiles
their closure with the pinned ix producer, resolves every name with
`ix addr-of`, and writes one TSV row per constant plus a provenance JSON. The
by-name arity of a `lazy` row is the number of leading λs of its Lean value.

Regeneration is a manual gate:

```
lake exe pin-src-tables --ix PATH/TO/ix --work plans/<task>/src-tables \
  --out fixtures/ixon-v4/src-tables.tsv \
  --provenance fixtures/ixon-v4/src-tables.provenance.json \
  --names fixtures/ixon-v4/src-names.tsv
```

`--diagnostics fixtures/ixon-v4/src-diag`, `--sortpoly
fixtures/ixon-v4/src-sortpoly`, `--words fixtures/ixon-v4/src-words` and
`--kernel-hints fixtures/ixon-v4/kernel-hints` instead compile a roots-only
fixture from the Lean source in that directory (the words fixture with
`--equations`, so that the word operations' stored equations join its closure;
the kernel-hints fixture with seeds beside its root, which the sidecar does not
name). -/

open Lean IxCC.Tools.Check

namespace PinSrcTables

def expectedMacroInline : Nat := 28

/-- Named constants added to the lazy rows beside the `macro_inline` set. -/
def extraLazy : List Name := [`Bool.or, `Bool.and]

def opaqueByValue : List Name := [`Lean.opaqueId]

/-- The fixed-width words' constants (stage W1), which no kernel role names: per width the type
and its constructor, the tower's inner constructors, `Nat.le` (the bridge's bound), and every
primitive operation (`IxCC.Src.WordOp.primitives`), each a row of its own kind. -/
def wordRows : List (String × Name) :=
  IxCC.Src.Width.all.map (fun w => ("word-type", w.name.toName)) ++
  IxCC.Src.Width.all.map (fun w => ("word-ctor", s!"{w.name}.ofBitVec".toName)) ++
  [("word-part", `BitVec.ofFin), ("word-part", `Fin.mk), ("word-part", `Nat.le)] ++
  IxCC.Src.Width.all.flatMap fun w =>
    (IxCC.Src.WordOp.primitives w).map fun op => ("word", (op.leanName w).toName)

/-- Names resolved for tests only (`src-names.tsv`, an untrusted test oracle:
the relevance census and runtime-set reports). -/
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

/-- A roots-only fixture: a Lean source (in the fixture directory, or in
`sourceRoot` relative to the repository root when it is also a Lake module),
the file stem of its closure and sidecar, and its roots. -/
structure RootsFixture where
  source : String
  sourceRoot : Option System.FilePath := none
  stem : String
  roots : List Name
  /-- Compile with `--equations` (the fixed-width words' stored equations join the closure). -/
  equations : Bool := false
  /-- Constants compiled into the closure beside the roots, which the sidecar does not name. -/
  seeds : List Name := []

/-- The admission-diagnostics fixtures `fixtures/ixon-v4/src-diag/`, from one
source: the root that uses `sorry` alone (`sorry.ixe`; the certified kernel
declines a whole artifact that holds a `sorryAx` use), and the other five
together (`diag.ixe`). -/
def diagFixtures : List RootsFixture :=
  [{ source := "Diag.lean", stem := "diag"
     roots := [`SrcDiag.rootPartial, `SrcDiag.rootMixHash, `SrcDiag.rootFloat,
       `SrcDiag.rootClassical, `SrcDiag.rootOpaqueId] },
   { source := "Diag.lean", stem := "sorry", roots := [`SrcDiag.rootSorry] }]

/-- The sort-polymorphism fixture `fixtures/ixon-v4/src-sortpoly/` (level-exact
relevance, D18). -/
def sortPolyFixture : RootsFixture where
  source := "SortPoly.lean"
  sourceRoot := some "IxCCTests/Fixtures"
  stem := "sortpoly"
  roots := [`SortPoly.comp, `SortPoly.throughRoot, `SortPoly.punitCases,
    `SortPoly.punitCasesType, `SortPoly.punitRec, `SortPoly.unitBoth, `SortPoly.sigmaRoot,
    `SortPoly.typeArg]

/-- The fixed-width words fixture `fixtures/ixon-v4/src-words/` (stage W1): every word operation
of every width, compiled with `--equations`, one root per width. -/
def wordsFixture : RootsFixture where
  source := "Words.lean"
  stem := "words"
  roots := [`Words.u8, `Words.u16, `Words.u32, `Words.u64]
  equations := true

/-- The kernel-hints fixture `fixtures/ixon-v4/kernel-hints/`: a root, and as seeds the proofs the
certified kernel checks quickly only with the artifact's reducibility hints, and a mutual block of
definitions whose hints are recorded under its members' projection records
(`IxCCTests.KernelFront.Hints`). -/
def kernelHintsFixture : RootsFixture where
  source := "KernelHints.lean"
  stem := "hints"
  roots := [`KernelHints.root]
  seeds := [`KernelHints.allOnesXor, `KernelHints.complement16, `KernelHints.complement32,
    `KernelHints.complement64, `KernelHints.ping, `KernelHints.pong]

/-- Resolve `name` against the named twin `named` (`ix addr-of`). -/
def addrOf (ix : String) (named : System.FilePath) (name : String) : IO String := do
  let output ← run ix #["addr-of", "--ixe", named.toString, name]
  let address := (words output).getLastD ""
  need (isHex 64 address) s!"{name}: ix addr-of gave {repr output}"
  return address

/-- The sidecar's `equations`, `theorems` and `failures` from `ix compile --equations`'s output
(`ix/compile-equations/2`), every name resolved against the named twin, as the corpus tool writes
them (`IxCCTests.Corpus.Build`): `theorems` only when there is one. -/
def sidecarEquations (ix : String) (named out : System.FilePath) : IO (List (String × Json)) := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile out))
  let format ← IO.ofExcept (j.getObjValAs? String "format")
  need (format == "ix/compile-equations/2") s!"{out}: format {format}"
  let str := fun (o : Json) (k : String) => IO.ofExcept (o.getObjValAs? String k)
  let mut eqs : Array Json := #[]
  for e in ← IO.ofExcept ((← IO.ofExcept (j.getObjVal? "equations")).getArr?) do
    let d ← str e "definition"
    let t ← str e "equation"
    eqs := eqs.push (Json.mkObj [("definition", d), ("definition_address", ← addrOf ix named d),
      ("equation", t), ("equation_address", ← addrOf ix named t)])
  let mut thms : Array Json := #[]
  for e in ← IO.ofExcept ((← IO.ofExcept (j.getObjVal? "theorems")).getArr?) do
    let s ← str e "subject"
    let t ← str e "theorem"
    thms := thms.push (Json.mkObj [("kind", ← str e "kind"), ("subject", s),
      ("subject_address", ← addrOf ix named s), ("theorem", t),
      ("theorem_address", ← addrOf ix named t)])
  let failures ← IO.ofExcept (j.getObjVal? "failures")
  return [("equations", Json.arr eqs)] ++
    (if thms.isEmpty then [] else [("theorems", Json.arr thms)]) ++ [("failures", failures)]

/-- Compile a roots-only fixture (anonymous and named), resolve its roots and
write the closure, its `ixcc/k1-equations/1` sidecar and a provenance record
(`STEM.provenance.json`). The sidecar names the roots; compiled with
`--equations`, it also carries `ix`'s equation associations and theorem
proposals with their addresses (`sidecarEquations`), otherwise none. -/
def rootsFixture (fx : RootsFixture) (ix : String) (work dir : System.FilePath)
    : IO Unit := do
  IO.FS.createDirAll work
  let source := (fx.sourceRoot.getD dir) / fx.source
  let closure := dir / s!"{fx.stem}.ixe"
  let named := work / s!"{fx.stem}.named.ixe"
  let consts := String.intercalate "," ((fx.roots ++ fx.seeds).map toString)
  let eqns := fun (out : String) =>
    if fx.equations then #["--equations", "--word-equations", "--equations-out", out] else #[]
  let _ ← run ix (#["compile", "--no-build", "--consts", consts, "--anon", "--out", closure.toString]
    ++ eqns (work / s!"{fx.stem}.ix-equations.json").toString ++ #[source.toString])
  let _ ← run ix (#["compile", "--no-build", "--consts", consts, "--out", named.toString]
    ++ eqns (work / s!"{fx.stem}.named.ix-equations.json").toString ++ #[source.toString])
  let mut roots : Array Json := #[]
  for name in fx.roots do
    roots := roots.push (Json.mkObj [("name", name.toString),
      ("address", ← addrOf ix named name.toString)])
  let rest ← if fx.equations then sidecarEquations ix named (work / s!"{fx.stem}.named.ix-equations.json")
    else pure [("equations", Json.arr #[]), ("failures", Json.arr #[])]
  let sidecar := dir / s!"{fx.stem}.equations.json"
  let head : List (String × Json) :=
    [("format", "ixcc/k1-equations/1"), ("source", fx.source), ("roots", Json.arr roots)]
  IO.FS.writeFile sidecar ((Json.mkObj (head ++ rest)).pretty ++ "\n")
  IO.FS.writeFile (dir / s!"{fx.stem}.provenance.json") ((Json.mkObj [
    ("producer_version", String.intercalate " " (words (← run ix #["--version"]))),
    ("producer", IxCCTests.Corpus.producerIx),
    ("commands", toJson [
      s!"ix compile --no-build --consts <roots{if fx.seeds.isEmpty then "" else " and seeds"}>{if fx.equations then " --equations --word-equations" else ""} --anon --out {fx.stem}.ixe {fx.source}",
      s!"ix compile --no-build --consts <roots{if fx.seeds.isEmpty then "" else " and seeds"}>{if fx.equations then " --equations --word-equations" else ""} --out {fx.stem}.named.ixe {fx.source}",
      s!"ix addr-of --ixe {fx.stem}.named.ixe NAME, for every root{if fx.equations then " and every name of the equations output" else ""}"]),
    ("source_sha256", ← sha256 source),
    ("named_env_sha256", ← sha256 named),
    ("files", Json.mkObj [(s!"{fx.stem}.ixe", toJson (← sha256 closure)),
      (s!"{fx.stem}.equations.json", toJson (← sha256 sidecar))])]).pretty ++ "\n")
  IO.println s!"wrote {closure} with {fx.roots.length} roots"


/-! ## Repinning `IxCC.Src.Pinned`

After a refreeze, `--repin FILE --old-primitives OLD --old-tables OLD` rewrites
every pinned address in FILE (as a hex string or a `0x` numeral) from the old
`primitives.tsv`/`src-tables.tsv` rows to the current ones, matched by name.
An old address that two rows map to different new addresses, or an address
FILE pins whose row the new tables drop, is an error (a dropped row FILE does
not pin is reported); `tests-src` then compares the tables
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
  let mut text ← IO.FS.readFile file
  for (name, before) in old do
    let some after := (new.find? (·.1 == name)).map (·.2)
      | do
          -- a row the new tables drop is an error only where FILE pins its address
          need ((text.splitOn before).length == 1)
            s!"{name}: in the old tables, not in the new ones, and {file} pins {before}"
          IO.println s!"{name}: in the old tables only, not pinned in {file}"
          continue
    match map.find? (·.1 == before) with
    | some (_, other) => need (other == after) s!"{before}: maps to {other} and {after}"
    | none => map := (before, after) :: map
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
  let options ← checked (parseArgs ["--ix", "--work", "--out", "--provenance", "--names",
    "--diagnostics", "--sortpoly", "--words", "--kernel-hints", "--repin", "--old-primitives",
    "--old-tables"] args)
  if let some file := optional options "--repin" then
    let some oldPrims := optional options "--old-primitives" | throw (IO.userError "missing --old-primitives")
    let some oldTables := optional options "--old-tables" | throw (IO.userError "missing --old-tables")
    repin file oldPrims oldTables "fixtures/ixon-v4/primitives.tsv" "fixtures/ixon-v4/src-tables.tsv"
    return
  for (flag, fxs) in [("--diagnostics", diagFixtures), ("--sortpoly", [sortPolyFixture]),
      ("--words", [wordsFixture]), ("--kernel-hints", [kernelHintsFixture])] do
    if let some dir := optional options flag then
      let some ix := optional options "--ix" | throw (IO.userError "missing --ix")
      for fx in fxs do
        rootsFixture fx ix (option options "--work" "plans/src-tables") dir
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
  for (kind, name) in wordRows do
    need (env.contains name) s!"{name}: not in the Init environment"
    rows := rows.push (kind, name, none)
  IO.FS.createDirAll work
  let source := work / "SrcTables.lean"
  IO.FS.writeFile source "/-! Seed file for `ix compile --consts`: the Init environment only. -/\n"
  let named := work / "src-tables.named.ixe"
  let names := String.intercalate ","
    ((rows.toList.map fun (_, n, _) => n.toString) ++ censusNames.map toString)
  let _ ← run ix #["compile", "--no-build", "--consts", names, "--out", named.toString,
    source.toString]
  let mut lines : Array String := #[
    "# Src pinned tables (design note 01 §4.2), generated by IxCCTests/Scripts/PinSrcTables.lean.",
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
    "# IxCCTests/Scripts/PinSrcTables.lean with the same ix run as src-tables.tsv.",
    "# name\taddress"]
  for name in censusNames do
    let output ← run ix #["addr-of", "--ixe", named.toString, name.toString]
    let address := (words output).getLastD ""
    need (isHex 64 address) s!"{name}: ix addr-of gave {repr output}"
    nameLines := nameLines.push s!"{name}\t{address}"
  IO.FS.writeFile namesOut (String.intercalate "\n" nameLines.toList ++ "\n")
  let version := String.intercalate " " (words (← run ix #["--version"]))
  IO.FS.writeFile provenance ((Json.mkObj [
    ("format", "ixcc/src-tables/1"),
    ("producer_version", version),
    ("producer", IxCCTests.Corpus.producerIx),
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
