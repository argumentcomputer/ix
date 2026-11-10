import IxCC.Tools.Check
import IxCCTests.IxonV3.Catalog.Fixtures

/-! The refreeze steps that are not `corpus rebuild`, `tests-own verdicts` or
`pin-src-tables` (`docs/corpus.md`, "Refreezing"). A manual tool: it runs the
producer ix (and `git` on an ix checkout, read only) and writes fixtures and
their provenance; required CI never runs it.

* `producer --ix IX --revision REV --build TEXT [--lean VERSION]`: pin the
  producer (revision, binary SHA-256, `ix --version`, build note, and the
  compile commands with `--unbound`) and the interpreter's Lean version in
  every corpus manifest and in the ownership verdicts (their reviewed fields;
  `corpus rebuild` then rewrites the derived ones and the canonical form).
* `package --ix-repo DIR --ix-revision REV`: copy ix's Ixon fixture package
  (`Tests/Fixtures/ixon-v4/` at REV, unchanged) into `fixtures/ixon-v4`:
  the expression, addressed, claim, resource and text vectors, the handoff and
  `primitives.tsv`.
* `tc-primitives --ix-repo DIR --ix-revision REV`: rewrite the erased
  checker's primitive table (`PrimAddrs.canonical` in
  `IxCC/Ixon/V3/Tc/Primitive.lean`) field by field from ix's table at REV
  (`Ix/PrimAddrs.lean`, or `Ix/Tc/Primitive.lean` in earlier revisions), and
  check that the two tables are equal; tables with different fields are
  refused, naming the fields.
* `typing --ix IX --revision REV [--work DIR]`: compile the primitive closure
  unbound (`ix compile --unbound --consts` every `primitives.tsv` name the
  toolchain has), check every other row's address with `ix addr-of`, check
  the closure with `ix check-lean` (every declaration must pass), extract the
  four bundles with `ix pack --anon`, check that each holds only constants of
  the checked closure, and write `typing/provenance.json`.
* `catalog --ix IX --revision REV [--work DIR]`: assemble and verify
  `catalog/fat.ixc` from the typing bundles with `ix catalog`, write
  `catalog/chunked.ixc` (`CatalogFixtures.writeChunked`), verify it with ix,
  and write `catalog/provenance.json`. The ix of this repository assembles
  only role-bound members, which the catalog fixtures (object format 4,
  unbound pieces) are not, so it is refused before anything is written. -/

namespace RefreezeIxon

open Lean System IxCC.Tools.Check

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

/-- A compile command with `--unbound` before `--out` (once). -/
def unboundCommand (command : Json) : Json :=
  match command.getArr? with
  | .ok args =>
    if args.contains (Json.str "--unbound") then command
    else Json.arr (args.flatMap fun a => if a == Json.str "--out" then #[Json.str "--unbound", a] else #[a])
  | .error _ => command

def producer (ix revision build lean : String) : IO Unit := do
  need (isHex 40 revision) s!"revision {revision}: forty hex digits"
  let digest ← sha256 ix
  let ver ← version ix
  for path in manifests do
    let m ← readJson path
    let p := field! m "producer"
    let p := setKey (setKey (setKey (setKey p "ix_revision" revision) "ix_binary_sha256" digest)
      "ix_version" ver) "ix_build" build
    -- the ix of this repository writes the role-bound envelope unless `--unbound`
    let p := setKey (setKey p "anonymous" (unboundCommand (field! p "anonymous")))
      "named" (unboundCommand (field! p "named"))
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

/-- Where ix keeps the canonical primitive table: `Ix/PrimAddrs.lean` in the
ix of this repository, `Ix/Tc/Primitive.lean` in earlier revisions. -/
def primitiveTableFiles : List String := ["Ix/PrimAddrs.lean", "Ix/Tc/Primitive.lean"]

def tcPrimitives (repo revision : String) : IO Unit := do
  let path : FilePath := "IxCC/Ixon/V3/Tc/Primitive.lean"
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

/-- The reference check of the primitive closure: `ix check-lean`, ix's IxCK
record checker, on the whole unbound source environment, where every inductive
block has its recursor (a bundle alone may lack one, which the checker
declines). With `--allow-declined` it exits 0 unless a declaration is rejected
(the unbound environment has no role binding, so the whole-artifact entry does
not run). Returns the declarations passed, the declarations checked, and the
addresses it did not pass (declined, or blocked by a declined one), from its
`[check-lean] [support] #ADDRESS: OUTCOME …` lines; `typing` requires that no
bundle holds one. -/
def referenceCheck (ix : String) (work : FilePath) (env : String) :
    IO (Nat × Nat × List String) := do
  let log := work / "check-lean.log"
  let args := #["check-lean", "--anon", "--workers", "1", "--allow-declined", env]
  let result ← IO.Process.output { cmd := ix, args, cwd := work }
  let output := result.stdout ++ result.stderr
  IO.FS.writeFile log output
  need (result.exitCode == 0) s!"ix check-lean {env}: exit {result.exitCode}; see {log}"
  let summary := (output.splitOn "\n").findSome? fun line =>
    match words line with
    | ["##check-lean##", _, passed, failed, targets] =>
      match passed.toNat?, failed.toNat?, targets.toNat? with
      | some p, some f, some t => some (p, f, t)
      | _, _, _ => none
    | _ => none
  let some (passed, failed, targets) := summary
    | throw (IO.userError s!"ix check-lean {env}: no summary line; see {log}")
  let notPassed := (output.splitOn "\n").filterMap fun line =>
    let label := match words line with
      | "[check-lean]" :: "support" :: l :: _ => some l
      | "[check-lean]" :: l :: _ => some l
      | _ => none
    label.bind fun l =>
      if l.startsWith "#" && l.endsWith ":" && l.length == 66 then some (String.ofList ((l.toList.drop 1).dropLast))
      else none
  need (targets > 0 && passed + failed == targets && notPassed.length ≥ failed)
    s!"ix check-lean {env}: {passed}/{targets} passed, {failed} not, {notPassed.length} listed; see {log}"
  return (passed, targets, notPassed)

/-- The constant addresses of an unbound (version-4) environment, from its
framing with ingress's readers: every object's hash is checked, but the
constants are not decoded, since a whole closure may exceed ingress's
per-constant budgets (the bundles, which ingress reads, may not). -/
def constAddresses (path : FilePath) : IO (Std.HashSet String) := do
  let read : IxCC.Ixon.V3.EnvM _ := do
    let tag ← _root_.Ixon.getTagN 4
    unless tag.flag == 0xE && tag.value == IxCC.Ixon.V3.envVersion do
      throw "expected the version-4 environment header"
    let _ ← IxCC.Ixon.V3.getAddress
    let _ ← IxCC.Ixon.V3.getOptionalAddress
    let _ ← IxCC.Ixon.V3.getAddressList
    let _ ← IxCC.Ixon.V3.getObjectTable false
    IxCC.Ixon.V3.getObjectTable false
  let consts ← checked ((_root_.Ixon.runGet read (← IO.FS.readBinFile path)).mapError (s!"{path}: " ++ ·))
  return consts.foldl (fun s (a, _) => s.insert (toString a)) {}

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
    let args := #["compile", "--no-build", "--unbound", "--consts", ",".intercalate names, "--out",
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
  let (passed, targets, notPassed) ← referenceCheck ix.toString work "prims.named.ixe"
  let source ← constAddresses (work / "prims.named.ixe")
  let mut files := Json.mkObj []
  for name in bundles do
    need (← ixRun ix.toString #["pack", "--anon", "--out", s!"{name}.ixe", "prims.named.ixe", name]
      work (work / s!"pack-{name}.log")) s!"ix pack {name}"
    let consts ← constAddresses (work / s!"{name}.ixe")
    need (consts.toList.all source.contains) s!"ix pack {name}: a constant outside the checked source environment"
    need (!notPassed.any consts.contains) s!"ix pack {name}: holds a constant ix check-lean did not pass"
    let target := fixtures / "typing" / s!"{name}.ixe"
    IO.FS.writeBinFile target (← IO.FS.readBinFile (work / s!"{name}.ixe"))
    let main := ((rows.find? (·.1 == name)).map (·.2)).getD ""
    files := setKey files s!"{name}.ixe" (Json.mkObj [("sha256", toJson (← sha256 target)),
      ("constants", toJson consts.size), ("main", toJson main)])
    IO.println s!"{target}: main {main.take 12}"
  let build := s!"ix compile --no-build --unbound --consts <every primitives.tsv name the toolchain has; absent: {absent}> --out prims.named.ixe Prims.lean (a source importing only Init); ix addr-of then reproduces every other primitives.tsv address"
  let provenance := Json.mkObj [("source_revision", toJson revision), ("source_generator", toJson build),
    ("source_environment_sha256", toJson (← sha256 (work / "prims.named.ixe"))),
    ("producer_binary_sha256", toJson (← sha256 ix.toString)), ("producer_version", toJson (← version ix.toString)),
    ("extraction", toJson "ix pack --anon --out OUTPUT.ixe prims.named.ixe NAME"),
    ("reference_check", toJson s!"ix check-lean --anon --workers 1 --allow-declined prims.named.ixe: {passed} of {targets} declarations passed and none was rejected (the unbound environment has no role binding, so the whole-artifact entry did not run); every constant of each bundle is a constant of that environment that passed"),
    ("reference_not_passed", toJson notPassed),
    ("files", files)]
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
  unless (← ixRun ix.toString (#["catalog", "assemble", "--labels", ",".intercalate pieces,
      "--toolchains", toolchain, "--pins", revision, "--deps", "1:0", "fat.ixc"] ++
      (pieces.map (· ++ ".ixe")).toArray) work (work / "assemble.log")) do
    let log ← IO.FS.readFile (work / "assemble.log")
    throw (IO.userError <| s!"ix catalog assemble failed:\n{log}" ++
      (if log.contains "role binding" then
        "\nThis ix assembles only role-bound members (version-5 envelopes); the catalog " ++
        "fixtures' pieces are the unbound typing bundles that the catalog reader (object " ++
        "format 4) reads, so this ix cannot regenerate them."
      else ""))
  need (← ixRun ix.toString #["catalog", "verify", "--deep", "fat.ixc"] work (work / "verify-fat.log"))
    "ix catalog verify fat.ixc"
  let fat := fixtures / "catalog" / "fat.ixc"
  for file in ["manifest"] ++ pieces.map (· ++ ".ixe") do
    IO.FS.writeBinFile (fat / file) (← IO.FS.readBinFile (work / "fat.ixc" / file))
  let chunked := fixtures / "catalog" / "chunked.ixc"
  IxCCTests.IxonV3.CatalogFixtures.writeChunked fat chunked
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
  IxCC.Tools.Check.cli "refreeze-ixon" (RefreezeIxon.main args)
