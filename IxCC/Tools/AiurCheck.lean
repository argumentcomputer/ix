import IxCC.Tools.Check

/-! Exact pure-source inventory for the initial Aiur target reference. -/

namespace IxCC.Tools.AiurCheck

open Lean System Check

def revision := "a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03"

def upstreamFiles : List String := [
  "Ix/Lib.lean", "Ix/IndexMap.lean", "Ix/Aiur/Goldilocks.lean",
  "Ix/Aiur/Stages/Source.lean", "Ix/Aiur/Stages/Typed.lean", "Ix/Aiur/Stages/Simple.lean",
  "Ix/Aiur/Stages/Concrete.lean", "Ix/Aiur/Stages/Bytecode.lean",
  "Ix/Aiur/Compiler/Layout.lean", "Ix/Aiur/Compiler/UnitCounter.lean", "Ix/Aiur/Compiler/CallOrder.lean",
  "LICENSE-MIT", "LICENSE-APACHE"]

def localFiles : List String := ["Ix/Aiur.lean", "README.md", "upstream.json"]

private partial def regularFiles (root : FilePath) : IO (List FilePath) := do
  need ((← root.symlinkMetadata).type == .dir) s!"Aiur inventory is not a regular directory: {root}"
  let mut result := []
  for entry in ← root.readDir do
    let kind := (← entry.path.symlinkMetadata).type
    if kind == .dir then result := result ++ (← regularFiles entry.path)
    else
      need (kind == .file) s!"Aiur inventory contains a non-regular file: {entry.path}"
      result := entry.path :: result
  return result

def verifyVendor (root : FilePath) : IO Unit := do
  let directory ← IO.FS.realPath (root / "vendor/aiur")
  let actual := (← regularFiles directory).map fun path =>
    (path.toString.drop (directory.toString.length + 1)).toString
  need (actual.mergeSort (· ≤ ·) == (upstreamFiles ++ localFiles).mergeSort (· ≤ ·))
    "Aiur vendored file inventory differs"
  let pin ← readJson (directory / "upstream.json")
  need ((← strField pin "repository") == "https://github.com/argumentcomputer/ix" &&
    (← strField pin "revision") == revision &&
    (← strField pin "upstream_toolchain") == "leanprover/lean4:v4.33.1")
    "Aiur upstream identity differs"
  let hashes ← pairs (← field pin "unchanged_files_sha256")
  need ((hashes.map Prod.fst).mergeSort (· ≤ ·) == upstreamFiles.mergeSort (· ≤ ·))
    "Aiur upstream hash inventory differs"
  let locals ← (← arrField pin "local_files").toList.mapM string
  need (locals == localFiles) "Aiur local file inventory differs"
  for (path, expected) in hashes do
    need ((← sha256 (directory / path)) == (← string expected)) s!"Aiur source digest differs: {path}"

private def mustReject (label : String) (action : IO Unit) : IO Unit := do
  let rejected ← try action; pure false catch _ => pure true
  need rejected s!"Aiur inventory mutation was accepted: {label}"

def mutationChecks (root : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let original := root / "vendor/aiur"
  let copied := temporary / "vendor/aiur"
  for path in upstreamFiles ++ localFiles do
    let target := copied / path
    if let some parent := target.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile target (← IO.FS.readBinFile (original / path))
  verifyVendor temporary
  let source := copied / "Ix/Aiur/Goldilocks.lean"
  let bytes ← IO.FS.readBinFile source
  IO.FS.writeBinFile source (bytes ++ "\n-- mutation\n".toUTF8)
  mustReject "changed source" (verifyVendor temporary)
  IO.FS.writeBinFile source bytes
  IO.FS.removeFile source
  mustReject "missing source" (verifyVendor temporary)
  IO.FS.writeBinFile source bytes
  let extra := copied / "Unexpected.lean"
  IO.FS.writeFile extra ""
  mustReject "extra source" (verifyVendor temporary)
  IO.FS.removeFile extra
  let pin := copied / "upstream.json"
  let originalPin ← IO.FS.readFile pin
  IO.FS.writeFile pin (originalPin.replace revision (String.ofList (List.replicate 40 '0')))
  mustReject "wrong revision" (verifyVendor temporary)
  IO.FS.writeFile pin originalPin
  verifyVendor temporary

def run (root : FilePath) : IO Unit := do
  verifyVendor root
  mutationChecks root
  IO.println "aiur-inventory-ok: 11 unchanged Lean modules, 2 licenses, 4 mutation rejections"

end IxCC.Tools.AiurCheck
