import Compilatrix.Tools.Check
import CompilatrixTests.IxonV3.Catalog.Fixtures

/-! The refreeze steps that are not `corpus rebuild`, `tests-own verdicts` or
`pin-src-tables` (`docs/corpus.md`, "Refreezing"). A manual tool: it runs the
producer ix (and `git` on an ix checkout, read only) and writes fixtures and
their provenance; required CI never runs it.

* `producer --ix IX --revision REV --build TEXT [--lean VERSION]`: pin the
  producer (revision, binary SHA-256, `ix --version`, build note) and the
  interpreter's Lean version in every corpus manifest and in the ownership
  verdicts (their reviewed fields; `corpus rebuild` then rewrites the derived
  ones and the canonical form).
* `package --ix-repo DIR --ix-revision REV`: copy ix's Ixon fixture package
  (`Tests/Fixtures/ixon-v4/` at REV, unchanged) into `fixtures/ixon-v4`:
  the expression, addressed, claim, resource and text vectors, the handoff and
  `primitives.tsv`.
* `tc-primitives --ix-repo DIR --ix-revision REV`: rewrite the erased
  checker's primitive table (`PrimAddrs.canonical` in
  `Compilatrix/Ixon/V3/Tc/Primitive.lean`) field by field from ix's
  `Ix/Tc/Primitive.lean` at REV, and check that the two tables are equal.
* `typing --ix IX --revision REV [--work DIR]`: compile the primitive closure
  (`ix compile --consts` every `primitives.tsv` name the toolchain has), check
  every other row's address with `ix addr-of`, extract the four bundles with
  `ix pack --anon`, check them with `ix check-rs`, and write
  `typing/provenance.json`.
* `catalog --ix IX --revision REV [--work DIR]`: assemble and verify
  `catalog/fat.ixc` from the typing bundles with `ix catalog`, write
  `catalog/chunked.ixc` (`CatalogFixtures.writeChunked`), verify it with ix,
  and write `catalog/provenance.json`. -/

namespace RefreezeIxon

open Lean System Compilatrix.Tools.Check

def fixtures : FilePath := "fixtures/ixon-v4"

def manifests : List FilePath :=
  ["fixtures/ixon-v4/bench-k1/corpus.json", "fixtures/ixon-v4/k1/corpus.json",
   "fixtures/corpus/phase1-scalar/corpus.json", "fixtures/corpus/phase1-boundary/corpus.json",
   "fixtures/corpus/phase1-resource/corpus.json", "fixtures/corpus/phase1-decline/corpus.json",
   "fixtures/corpus/phase1-abi/corpus.json", "fixtures/ownership/corpus.json"]

/-- Replace (or add) one key of a JSON object. -/
def setKey (j : Json) (key : String) (value : Json) : Json := j.setObjVal! key value

def field! (j : Json) (key : String) : Json := (j.getObjVal? key).toOption.getD (Json.mkObj [])

def version (ix : String) : IO String := return (← run ix #["--version"]).trimAscii.toString

def producer (ix revision build lean : String) : IO Unit := do
  need (isHex 40 revision) s!"revision {revision}: forty hex digits"
  let digest ← sha256 ix
  let ver ← version ix
  for path in manifests do
    let m ← readJson path
    let p := field! m "producer"
    let p := setKey (setKey (setKey (setKey p "ix_revision" revision) "ix_binary_sha256" digest)
      "ix_version" ver) "ix_build" build
    let m := setKey (setKey m "producer" p) "lean" (setKey (field! m "lean") "version" lean)
    IO.FS.writeFile path (m.pretty ++ "\n")
    IO.println s!"{path}: producer {revision.take 8} {digest.take 8}, Lean {lean}"
  let path : FilePath := "fixtures/ownership/verdicts.json"
  let v ← readJson path
  let p := setKey (setKey (field! v "producer") "ix_revision" revision) "ix_binary_sha256" digest
  IO.FS.writeFile path ((setKey v "producer" p).pretty ++ "\n")
  IO.println s!"{path}: producer {revision.take 8}"

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

def tcPrimitives (repo revision : String) : IO Unit := do
  let path : FilePath := "Compilatrix/Ixon/V3/Tc/Primitive.lean"
  let theirs := canonicalRows (String.fromUTF8! (← ixFile repo revision "Ix/Tc/Primitive.lean"))
  need (!theirs.isEmpty) "ix's Ix/Tc/Primitive.lean has no canonical table"
  let mut text ← IO.FS.readFile path
  let ours := canonicalRows text
  need (ours.map (·.1) == theirs.map (·.1)) "the two canonical tables have different fields"
  let mut changed := 0
  for ((name, old), (_, new)) in ours.zip theirs do
    need (isHex 64 new) s!"{name}: {new}"
    if old != new then
      text := text.replace s!"  {name} := h \"{old}\"" s!"  {name} := h \"{new}\""
      changed := changed + 1
  need (canonicalRows text == theirs) "the rewritten table differs from ix's"
  IO.FS.writeFile path text
  IO.println s!"{path}: {changed} of {theirs.length} primitive addresses changed (ix {revision.take 8})"

/-- Run ix in `cwd`, logging to `log`; whether it exited 0. -/
def ixRun (ix : String) (args : Array String) (cwd log : FilePath) : IO Bool := do
  let result ← IO.Process.output { cmd := ix, args, cwd }
  IO.FS.writeFile log (result.stdout ++ result.stderr)
  return result.exitCode == 0

def primitiveRows : IO (List (String × String)) := do
  let text ← IO.FS.readFile (fixtures / "primitives.tsv")
  return (text.splitOn "\n").filterMap fun line =>
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn "\t" with
      | [name, address] => some (name, address)
      | _ => none

def bundles : List String := ["Nat", "Nat.add", "String", "Quot.lift"]

def typing (ix revision : String) (work : FilePath) : IO Unit := do
  let ix ← IO.FS.realPath ix
  let work := work / "typing"
  IO.FS.createDirAll work
  let work ← IO.FS.realPath work
  IO.FS.writeFile (work / "Prims.lean") "/-! Seed file for ix compile --consts: the Init environment only. -/\n"
  let rows ← primitiveRows
  -- names the toolchain lacks are dropped, one at a time, from ix's own error
  let mut names := rows.map (·.1)
  let mut absent : List String := []
  let mut compiled := false
  while !compiled do
    let args := #["compile", "--no-build", "--consts", ",".intercalate names, "--out",
      "prims.named.ixe", "Prims.lean"]
    if ← ixRun ix.toString args work (work / "compile.log") then compiled := true
    else
      let log ← IO.FS.readFile (work / "compile.log")
      match ((log.splitOn "no constant(s) named [")[1]?).bind fun rest => (rest.splitOn "]")[0]? with
      | some missing =>
        need (names.contains missing) s!"ix compile: {log}"
        names := names.erase missing
        absent := absent ++ [missing]
      | none => throw (IO.userError s!"ix compile failed:\n{log}")
  for (name, address) in rows do
    if absent.contains name then continue
    let out ← run ix.toString #["addr-of", "--ixe", (work / "prims.named.ixe").toString, name]
    need ((words out).getLastD "" == address) s!"{name}: ix addr-of {(words out).getLastD ""}, primitives.tsv {address}"
  let mut files := Json.mkObj []
  for name in bundles do
    need (← ixRun ix.toString #["pack", "--anon", "--out", s!"{name}.ixe", "prims.named.ixe", name]
      work (work / s!"pack-{name}.log")) s!"ix pack {name}"
    let checkLog := work / s!"check-{name}.log"
    need (← ixRun ix.toString #["check-rs", "--anon", "--workers", "1", s!"{name}.ixe"] work checkLog)
      s!"ix check-rs {name}"
    let log ← IO.FS.readFile checkLog
    let count (pre : String) : Nat :=
      (((log.splitOn pre)[1]?).bind fun rest => (words rest).head?.bind (·.toNat?)).getD 0
    let target := fixtures / "typing" / s!"{name}.ixe"
    IO.FS.writeBinFile target (← IO.FS.readBinFile (work / s!"{name}.ixe"))
    let main := ((rows.find? (·.1 == name)).map (·.2)).getD ""
    files := setKey files s!"{name}.ixe" (Json.mkObj [("sha256", toJson (← sha256 target)),
      ("constants", toJson (count "(")), ("main", toJson main),
      ("rust_checked_targets", toJson (count "[check] checked "))])
    IO.println s!"{target}: main {main.take 12}"
  let build := s!"ix compile --no-build --consts <every primitives.tsv name the toolchain has; absent: {absent}> --out prims.named.ixe Prims.lean (a source importing only Init); ix addr-of then reproduces every other primitives.tsv address"
  let provenance := Json.mkObj [("source_revision", toJson revision), ("source_generator", toJson build),
    ("source_environment_sha256", toJson (← sha256 (work / "prims.named.ixe"))),
    ("producer_binary_sha256", toJson (← sha256 ix.toString)), ("producer_version", toJson (← version ix.toString)),
    ("extraction", toJson "ix pack --anon --out OUTPUT.ixe prims.named.ixe NAME"),
    ("reference_check", toJson "ix check-rs --anon --workers 1 OUTPUT.ixe"), ("files", files)]
  IO.FS.writeFile (fixtures / "typing" / "provenance.json") (provenance.pretty ++ "\n")
  IO.println s!"{fixtures / "typing" / "provenance.json"}: written"

def catalog (ix revision : String) (work : FilePath) : IO Unit := do
  let ix ← IO.FS.realPath ix
  let work := work / "catalog"
  if ← work.pathExists then IO.FS.removeDirAll work
  IO.FS.createDirAll work
  let work ← IO.FS.realPath work
  let pieces := ["Nat", "Nat.add", "Quot.lift"]
  for name in pieces do
    IO.FS.writeBinFile (work / s!"{name}.ixe") (← IO.FS.readBinFile (fixtures / "typing" / s!"{name}.ixe"))
  let toolchain := ((← version ix.toString).splitOn "|").headD ""
  need (← ixRun ix.toString (#["catalog", "assemble", "--labels", ",".intercalate pieces,
      "--toolchains", toolchain, "--pins", revision, "--deps", "1:0", "fat.ixc"] ++
      (pieces.map (· ++ ".ixe")).toArray) work (work / "assemble.log")) "ix catalog assemble"
  need (← ixRun ix.toString #["catalog", "verify", "--deep", "fat.ixc"] work (work / "verify-fat.log"))
    "ix catalog verify fat.ixc"
  let fat := fixtures / "catalog" / "fat.ixc"
  for file in ["manifest"] ++ pieces.map (· ++ ".ixe") do
    IO.FS.writeBinFile (fat / file) (← IO.FS.readBinFile (work / "fat.ixc" / file))
  let chunked := fixtures / "catalog" / "chunked.ixc"
  CompilatrixTests.IxonV3.CatalogFixtures.writeChunked fat chunked
  let chunkedAbs ← IO.FS.realPath chunked
  need (← ixRun ix.toString #["catalog", "verify", "--deep", chunkedAbs.toString] work
    (work / "verify-chunked.log")) "ix catalog verify chunked.ixc"
  let log ← IO.FS.readFile (work / "assemble.log")
  let root (key : String) : String :=
    (((log.splitOn s!"{key} ")[1]?).bind fun rest => (words rest).head?).getD ""
  let mut files := Json.mkObj []
  for file in ["fat.ixc/manifest", "fat.ixc/Nat.ixe", "fat.ixc/Nat.add.ixe", "fat.ixc/Quot.lift.ixe",
      "chunked.ixc/manifest", "chunked.ixc/Nat.chunk0.ixe", "chunked.ixc/Nat.add.chunk1.ixe",
      "chunked.ixc/Quot.lift.chunk2.ixe", "chunked.ixc/members.json"] do
    files := setKey files file (toJson (← sha256 (fixtures / "catalog" / file)))
  let provenance := Json.mkObj [("schema_version", toJson (1 : Nat)), ("source_revision", toJson revision),
    ("producer_version", toJson (← version ix.toString)),
    ("producer_binary_sha256", toJson (← sha256 ix.toString)),
    ("fat_origin", toJson s!"ix catalog assemble --labels Nat,Nat.add,Quot.lift --toolchains {toolchain} --pins SOURCE_REVISION --deps 1:0 fat.ixc Nat.ixe Nat.add.ixe Quot.lift.ixe (the typing bundles), then ix catalog verify --deep fat.ixc"),
    ("chunk_origin", toJson "refreeze-ixon catalog (CatalogFixtures.writeChunked): the first-owner partition of the fat pieces; each chunk keeps its original blobs and presentation bytes and the hints and main of the constants it keeps, and lists the constants an earlier member owns as assumptions; members.json is every member's complete original address set"),
    ("independent_check", toJson "ix catalog verify --deep accepts both catalogs: the members and content roots below"),
    ("consumer_check", toJson "Required tests authenticate full sorted member lists against roots/counts, enforce first ownership/disjointness/full coverage, and typecheck every union constant."),
    ("members_root", toJson (root "members_root")), ("content_root", toJson (root "content_root")),
    ("file_sha256", files)]
  IO.FS.writeFile (fixtures / "catalog" / "provenance.json") (provenance.pretty ++ "\n")
  IO.println s!"{fixtures / "catalog"}: fat and chunked catalogs, members_root {root "members_root"}"

def usage : String :=
  "usage: refreeze-ixon producer --ix IX --revision REV --build TEXT [--lean VERSION]\n" ++
  "       refreeze-ixon package --ix-repo DIR --ix-revision REV\n" ++
  "       refreeze-ixon tc-primitives --ix-repo DIR --ix-revision REV\n" ++
  "       refreeze-ixon typing --ix IX --revision REV [--work DIR]\n" ++
  "       refreeze-ixon catalog --ix IX --revision REV [--work DIR]"

def main (args : List String) : IO Unit := do
  let (command, rest) := match args with
    | c :: r => (c, r)
    | [] => ("", [])
  let options ← checked (parseArgs ["--ix", "--revision", "--build", "--lean", "--ix-repo",
    "--ix-revision", "--work"] rest)
  let req := fun (name : String) => present (optional options name) s!"missing {name}\n{usage}"
  let work : FilePath := option options "--work" "plans/refreeze"
  match command with
  | "producer" => producer (← req "--ix") (← req "--revision") (← req "--build") (option options "--lean" Lean.versionString)
  | "package" => package (← req "--ix-repo") (← req "--ix-revision")
  | "tc-primitives" => tcPrimitives (← req "--ix-repo") (← req "--ix-revision")
  | "typing" => typing (← req "--ix") (← req "--revision") work
  | "catalog" => catalog (← req "--ix") (← req "--revision") work
  | _ => throw (IO.userError usage)

end RefreezeIxon

def main (args : List String) : IO UInt32 :=
  Compilatrix.Tools.Check.cli "refreeze-ixon" (RefreezeIxon.main args)
