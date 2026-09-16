import CompilatrixTests.IxonV3.Catalog.Admission
import Compilatrix.Tools.IxonV3Catalog

namespace CompilatrixTests.IxonV3.CatalogTests

open Compilatrix.Ixon Compilatrix.Ixon.V3 Catalog
open Compilatrix.Tools.IxonV3Catalog

private def rejectIO (label : String) (action : IO α) : IO Unit := do
  let accepted ← try
    let _ ← action
    pure true
  catch _ => pure false
  require (!accepted) label

/-- Fixtures can be symlinks in Nix's source mirror. Copy their retained
bytes into a real temporary catalog before testing the filesystem adapter. -/
private def copyCatalog (source destination : System.FilePath) : IO (ByteArray × Manifest) := do
  let raw ← IO.FS.readBinFile (source / "manifest")
  let m ← checked (decodeManifest raw)
  IO.FS.createDirAll destination
  IO.FS.writeBinFile (destination / "manifest") raw
  for spec in pieceSpecs m do
    IO.FS.writeBinFile (destination / spec.filename) (← IO.FS.readBinFile (source / spec.filename))
  return (raw, m)

def files (root : System.FilePath) : IO Nat := IO.FS.withTempDir fun temporary => do
  let mut assertions := 0
  for name in ["fat.ixc", "chunked.ixc"] do
    let directory := temporary / name
    let (raw, m) ← copyCatalog (root / "catalog" / name) directory
    require (CatalogFixtures.manifestBytes m == raw) s!"catalog manifest encoding: {name}"
    let supplied ← if name == "chunked.ixc" then do
      let path := directory / "members.json"
      IO.FS.writeBinFile path (← IO.FS.readBinFile (root / "catalog" / name / "members.json"))
      pure (some (← readMemberSets {} path))
    else pure none
    let pieces ← readPieces {} directory m
    let input ← checked (admit raw pieces supplied)
    require (input.loaded.env.consts.size == 23 && m.members.size == 3 &&
      m.membersRoot.toHex == "beeaa41ba33be861b8c7c25a80e2f93293961b2cb95000a3471c3f782c0cfc5b" &&
      input.loaded.env.root.toHex == "1a40750cd8a9de7506ded7fdcfb3141e8a2453eab2a02159b50dfd506e081f76")
      s!"independent producer identities: {name}"
    require (input.loaded.memberSets.map Array.size == #[4, 18, 5]) s!"original membership: {name}"
    let args := #[directory.toString] ++ (if supplied.isSome then #[(directory / "members.json").toString] else #[])
    let result ← IO.Process.output { cmd := ".lake/build/bin/check-ixon-v3-catalog", args }
    require (result.exitCode == 0 && result.stdout.contains "validator=erased-lean-v1")
      s!"catalog CLI positive {name}: {result.stderr}"
    IO.FS.writeBinFile (directory / "manifest") (CatalogFixtures.mutate raw 17 2)
    let rejected ← IO.Process.output { cmd := ".lake/build/bin/check-ixon-v3-catalog", args }
    require (rejected.exitCode != 0 && rejected.stderr.contains "rejected") s!"catalog CLI scope: {name}"
    assertions := assertions + 5
  let file := temporary / "bounded"
  IO.FS.writeBinFile file ⟨#[1, 2, 3]⟩
  require ((← readBounded file 3) == ⟨#[1, 2, 3]⟩) "exact file byte limit"
  rejectIO "file byte limit plus one" (readBounded file 2)
  rejectIO "nonregular storage" (readBounded temporary 100)
  rejectIO "missing storage" (readBounded (temporary / "missing") 100)
  let linked := temporary / "linked"
  let linkResult ← IO.Process.output { cmd := "ln", args := #["-s", file.toString, linked.toString] }
  require (linkResult.exitCode == 0) "create symlink test fixture"
  rejectIO "symlink storage" (readBounded linked 100)
  IO.FS.writeBinFile file .empty
  require ((← readBounded file 0).isEmpty) "zero-byte file limit"
  let a := Address.replicate 1
  let good := Lean.Json.arr #[Lean.Json.arr #[Lean.Json.str a.toHex]]
  let parsed ← IO.ofExcept (memberSetsFromJson { members := 1, memberEntries := 1 } good)
  require (parsed == #[#[a]]) "exact witness count limits"
  for json in #[Lean.Json.null, Lean.Json.arr #[Lean.Json.str "wrong"],
      Lean.Json.arr #[Lean.Json.arr #[Lean.Json.str "01"]],
      Lean.Json.arr #[Lean.Json.arr #[Lean.Json.str (String.ofList (List.replicate 64 'g'))]]] do
    require ((memberSetsFromJson {} json).toOption.isNone) "malformed membership JSON"
  require ((memberSetsFromJson { members := 0 } good).toOption.isNone) "witness member budget"
  require ((memberSetsFromJson { memberEntries := 0 } good).toOption.isNone) "witness address budget"
  for bad in #[String.ofList (List.replicate 10000 '['),
      s!"[[\"{a.toHex}0\"]]", "[[123456789012345678901234567890]]", "[[{}]]",
      "[[\"\\u0030\"]]", s!"[[\"{a.toHex}\"]"] do
    IO.FS.writeFile file bad
    rejectIO "bounded witness grammar before JSON parsing" (readMemberSets {} file)
  IO.FS.writeBinFile file ⟨#[255]⟩
  rejectIO "witness UTF-8" (readMemberSets {} file)
  IO.FS.writeBinFile file ⟨Array.replicate 1025 32⟩
  rejectIO "witness byte budget" (readMemberSets { members := 0, memberEntries := 0 } file)
  let usage ← IO.Process.output { cmd := ".lake/build/bin/check-ixon-v3-catalog", args := #[] }
  require (usage.exitCode != 0 && usage.stderr.contains "usage:") "CLI usage failure"
  return assertions + 23

end CompilatrixTests.IxonV3.CatalogTests
