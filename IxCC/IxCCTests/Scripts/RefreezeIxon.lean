import IxCC.Tools.Check
import IxCCTests.Corpus.Build

/-! The refreeze steps that are not `corpus rebuild`, `tests-own verdicts` or
`pin-src-tables` (`docs/corpus.md`, "Refreezing"). A manual tool: it runs the
producer ix (and `git` on an ix checkout, read only) and writes fixtures and
their provenance; required CI never runs it.

* `package --ix-repo DIR --ix-revision REV`: copy ix's Ixon fixture package
  (`Tests/Fixtures/ixon-v4/` at REV, unchanged) into `fixtures/ixon-v4`:
  the expression, addressed, claim, resource and text vectors, the handoff and
  `primitives.tsv`.
* `tc-primitives --ix-repo DIR --ix-revision REV`: rewrite IxCC's
  primitive table (`V3.PrimAddrs.canonical` in
  `IxCC/Ixon/V3/PrimAddrs.lean`) field by field from ix's table at REV
  (`Ix/PrimAddrs.lean`, or `Ix/Tc/Primitive.lean` in earlier revisions), and
  check that the two tables are equal; tables with different fields are
  refused, naming the fields.
* `rc-real-source --ix IX [--ix-path DIR]`, `rc-budget --ix IX [--ix-path DIR]`, `rc-deep --ix IX
  [--ix-path DIR]`: regenerate the RC real-source input `fixtures/rc/real-source`, the
  captured-work budget input `fixtures/rc/budget` and the certificate-depth input
  `fixtures/rc/deep` (`rcInput`).
-/

namespace RefreezeIxon

open Lean System IxCC.Tools.Check

def fixtures : FilePath := "fixtures/ixon-v4"

/-- Replace (or add) one key of a JSON object. -/
def setKey (j : Json) (key : String) (value : Json) : Json := j.setObjVal! key value

def version (ix : String) : IO String := return (← run ix #["--version"]).trimAscii.toString

/-- ix's v4 fixture package, as its test suite reads it. -/
def packageFiles : List String :=
  ["addressed.tsv", "claims.tsv", "expressions.txt", "primitives.tsv", "resource.tsv", "text.tsv",
   "handoff/accepted.claim", "handoff/accepted.ixe", "handoff/manifest.json",
   "handoff/profile.bin", "handoff/rejected-local-escape.ixe"]

/-- One file of an ix revision, read through `git cat-file` (read only). -/
def ixFile (repo revision path : String) : IO ByteArray := do
  let args := #["-C", repo, "cat-file", "blob", s!"{revision}:{path}"]
  let child ← IO.Process.spawn
    { cmd := "git", args, stdin := .null, stdout := .piped, stderr := .piped }
  let bytes ← child.stdout.readBinToEnd
  let err ← child.stderr.readToEnd
  need ((← child.wait) == 0) s!"git cat-file {revision}:{path}: {err}"
  return bytes

def package (repo revision : String) : IO Unit := do
  for file in packageFiles do
    let bytes ← ixFile repo revision s!"Tests/Fixtures/ixon-v4/{file}"
    IO.FS.writeBinFile (fixtures / file) bytes
    IO.println s!"{fixtures / file}: {bytes.size} bytes from ix {revision.take 8}"

/-- `name := h "hex"` lines of a `def canonical : PrimAddrs where` block. -/
def canonicalRows (text : String) : List (String × String) := Id.run do
  let lines := text.splitOn "\n"
  let some start := lines.findIdx? (·.startsWith "def canonical : PrimAddrs where") | return []
  let mut rows := []
  for line in lines.drop (start + 1) do
    let t := line.trimAscii.toString
    if t.isEmpty then break
    match t.splitOn " := h \"" with
    | [name, rest] => rows := rows ++ [(name, (rest.splitOn "\"").headD "")]
    | _ => break
  return rows

/-- Where ix keeps the canonical primitive table: `Ix/PrimAddrs.lean` in the
ix of this repository, `Ix/Tc/Primitive.lean` in earlier revisions. -/
def primitiveTableFiles : List String := ["Ix/PrimAddrs.lean", "Ix/Tc/Primitive.lean"]

def tcPrimitives (repo revision : String) : IO Unit := do
  let path : FilePath := "IxCC/Ixon/V3/PrimAddrs.lean"
  let mut theirs : List (String × String) := []
  let mut source := ""
  for file in primitiveTableFiles do
    if theirs.isEmpty then
      try
        let rows := canonicalRows (String.fromUTF8! (← ixFile repo revision file))
        if !rows.isEmpty then
          theirs := rows
          source := file
      catch _ => pure ()
  need (!theirs.isEmpty) s!"ix {revision}: no canonical primitive table in {primitiveTableFiles}"
  let mut text ← IO.FS.readFile path
  let ours := canonicalRows text
  let missing := ours.filter fun (n, _) => !theirs.any (·.1 == n)
  let extra := theirs.filter fun (n, _) => !ours.any (·.1 == n)
  need (ours.map (·.1) == theirs.map (·.1))
    s!"the two canonical tables have different fields: {path} has {missing.map (·.1)} that ix's {source} lacks, and lacks {extra.map (·.1)}"
  let mut changed := 0
  for ((name, old), (_, new)) in ours.zip theirs do
    need (isHex 64 new) s!"{name}: {new}"
    if old != new then
      text := text.replace s!"  {name} := h \"{old}\"" s!"  {name} := h \"{new}\""
      changed := changed + 1
  need (canonicalRows text == theirs) "the rewritten table differs from ix's"
  IO.FS.writeFile path text
  IO.println s!"{path}: {changed} of {theirs.length} primitive addresses changed (ix {revision.take 8})"

/-! ## The RC inputs: the real-source input and the captured-work budget input -/

/-- An RC input: the command that regenerates it, its directory, its source file and its roots. -/
structure RcInput where
  command : String
  dir : FilePath
  source : String
  roots : List String

def rcRealSourceInput : RcInput :=
  { command := "rc-real-source", dir := "fixtures/rc/real-source", source := "Reverse.lean",
    roots := ["IxCCTests.Own.H0.reverseList", "IxCCTests.Own.H0.reverseRepeated",
      "IxCCTests.Own.H0.sharedReverse"] }

/-- The captured-work budget input (heap stage 2): a root within `Anf.maxCapturedWork`, one past. -/
def rcBudgetInput : RcInput :=
  { command := "rc-budget", dir := "fixtures/rc/budget", source := "Fan.lean",
    roots := ["IxCCTests.Own.Budget.fanUnder", "IxCCTests.Own.Budget.fanOver"] }

/-- The certificate-depth input (the producer's read-back): a root whose plain-RC certificate nests
past the certificate text's depth limit, one within it. -/
def rcDeepInput : RcInput :=
  { command := "rc-deep", dir := "fixtures/rc/deep", source := "Deep.lean",
    roots := ["IxCCTests.Cert.Deep.deep240", "IxCCTests.Cert.Deep.deep168"] }

/-- An RC input's directory: the closure of its roots and its sidecar, by `corpus rebuild`'s
fixture step (the anonymous closure, the named twin, every root, definition and equation resolved
with `ix addr-of`; the roots have no cases), then `provenance.json` and every hash of
`manifest.sha256` (whose file list is kept). -/
def rcInput (input : RcInput) (ix : String) (ixPath : List String) (work : FilePath) : IO Unit := do
  let rcDir := input.dir
  let rcRoots := input.roots
  let ix := (← IO.FS.realPath ix).toString
  let stage ← IxCCTests.Corpus.freshWorkDir (work / input.command)
  let source := (rcDir / input.source).toString
  let m : IxCCTests.Corpus.Family :=
    { family := input.command, tier := "manual", phase := 1, directory := stage.toString,
      sourceRoot := ".", producer := { ixVersion := ← version ix },
      fixtures := [] }
  let f : IxCCTests.Corpus.Fixture :=
    { name := "anonymous", source := { path := source, license := "Apache-2.0 OR MIT", variant := "original" },
      consts := rcRoots, closure := { path := "anonymous.ixe" },
      equations := { path := "consumer.equations.json" }, census := { path := "anonymous.census.json" },
      roots := rcRoots.map fun name => { name, params := 0 } }
  let log ← IO.mkRef #[]
  let f ← IxCCTests.Corpus.rebuildFixture { ix := some ⟨ix⟩, ixPath, work } m f log
  for line in ← log.get do IO.println line
  for file in ["anonymous.ixe", "consumer.equations.json"] do
    IO.FS.writeBinFile (rcDir / file) (← IO.FS.readBinFile (stage / file))
  let lean ← run "lean" #["--version"]
  let provenance := Json.mkObj [
    ("source_path", toJson rcDir.toString),
    ("source_sha256", Json.mkObj [(input.source, toJson (← sha256 source)),
      ("anonymous.ixe", toJson (← sha256 (rcDir / "anonymous.ixe"))),
      ("consumer.equations.json", toJson (← sha256 (rcDir / "consumer.equations.json")))]),
    ("producer", toJson IxCCTests.Corpus.producerIx),
    ("producer_version", toJson m.producer.ixVersion),
    ("named_env_sha256", toJson f.namedEnvSha256),
    ("lean_version", toJson lean),
    ("regenerate", toJson s!"lake exe refreeze-ixon {input.command} --ix IX --ix-path FAKE (docs/corpus.md, Refreezing)"),
    ("commands", toJson [
      s!"ix compile --no-build --consts <roots> --equations --anon --out anonymous.ixe --equations-out anonymous.equations.json {source}",
      s!"ix compile --no-build --consts <roots> --equations --out named.ixe --equations-out named.equations.json {source}",
      "ix addr-of --ixe named.ixe NAME, for every root, definition and equation"])]
  IO.FS.writeFile (rcDir / "provenance.json") (provenance.pretty ++ "\n")
  -- the manifest's hashes, its file list kept
  let manifest := rcDir / "manifest.sha256"
  let mut lines : Array String := #[]
  for line in (← IO.FS.readFile manifest).splitOn "\n" do
    if line.isEmpty then continue
    let [_, path] := line.splitOn "  " | throw (IO.userError s!"{manifest}: malformed line {line}")
    lines := lines.push s!"{← sha256 path}  {path}"
  IO.FS.writeFile manifest (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"{rcDir}: closure {f.closure.bytes.getD 0} bytes, {f.equationCount} equations; provenance and manifest rewritten"

def usage : String :=
  "usage: refreeze-ixon package --ix-repo DIR --ix-revision REV\n" ++
  "       refreeze-ixon tc-primitives --ix-repo DIR --ix-revision REV\n" ++
  "       refreeze-ixon rc-real-source --ix IX [--ix-path DIR] [--work DIR]\n" ++
  "       refreeze-ixon rc-budget --ix IX [--ix-path DIR] [--work DIR]\n" ++
  "       refreeze-ixon rc-deep --ix IX [--ix-path DIR] [--work DIR]"

def main (args : List String) : IO Unit := do
  let (command, rest) := match args with
    | c :: r => (c, r)
    | [] => ("", [])
  let options ← checked (parseArgs ["--ix", "--ix-repo", "--ix-revision", "--work", "--ix-path"] rest)
  let req := fun (name : String) => present (optional options name) s!"missing {name}\n{usage}"
  let work : FilePath := option options "--work" "plans/refreeze"
  match command with
  | "package" => package (← req "--ix-repo") (← req "--ix-revision")
  | "tc-primitives" => tcPrimitives (← req "--ix-repo") (← req "--ix-revision")
  | "rc-real-source" => rcInput rcRealSourceInput (← req "--ix") ((optional options "--ix-path").toList) work
  | "rc-budget" => rcInput rcBudgetInput (← req "--ix") ((optional options "--ix-path").toList) work
  | "rc-deep" => rcInput rcDeepInput (← req "--ix") ((optional options "--ix-path").toList) work
  | _ => throw (IO.userError usage)

end RefreezeIxon

def main (args : List String) : IO UInt32 :=
  IxCC.Tools.Check.cli "refreeze-ixon" (RefreezeIxon.main args)
