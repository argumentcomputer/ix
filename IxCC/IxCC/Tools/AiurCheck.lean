import IxCC.Tools.Check

/-! Exact pure-source inventory for the initial Aiur target reference.

The reference is vendored from ix under `IxCC.Vendor`, so it shares neither a
module nor a declaration name with ix's own packages: upstream module `M` is
`IxCC.Vendor.M`, at `IxCC/Vendor/<path of M>`, and every vendored declaration
`D` is `IxCC.Vendor.D`. Two mechanical edits are the only difference from
upstream: the prefix of each `Ix` import, and a `namespace IxCC.Vendor` line
right after the file's first `public section` with its `end IxCC.Vendor` right
before the file's final `end`. The check undoes both and compares the result
with the recorded upstream SHA-256. -/

namespace IxCC.Tools.AiurCheck

open Lean System Check

def revision := "a8c4d2d21eaf45ee9160bdd103dfbcefe31f7f03"

/-- The vendored tree, relative to the project root. -/
def vendorDir : FilePath := "IxCC/Vendor"

/-- Vendored module `IxCC.Vendor.M` is upstream module `M`. -/
def modulePrefix := "IxCC.Vendor."

/-- Vendored declaration `IxCC.Vendor.D` is upstream declaration `D`. -/
def vendorNamespace := "IxCC.Vendor"

def upstreamFiles : List String := [
  "Ix/Lib.lean", "Ix/IndexMap.lean", "Ix/Aiur/Goldilocks.lean",
  "Ix/Aiur/Stages/Source.lean", "Ix/Aiur/Stages/Typed.lean", "Ix/Aiur/Stages/Simple.lean",
  "Ix/Aiur/Stages/Concrete.lean", "Ix/Aiur/Stages/Bytecode.lean",
  "Ix/Aiur/Compiler/Layout.lean", "Ix/Aiur/Compiler/UnitCounter.lean", "Ix/Aiur/Compiler/CallOrder.lean",
  "LICENSE-MIT", "LICENSE-APACHE"]

def localFiles : List String := ["README.md", "upstream.json"]

private def importKeywords : List String := ["import ", "public import "]

/-- A vendored Lean source's upstream text. The `namespace IxCC.Vendor` line
must directly follow the first `public section` line and its `end IxCC.Vendor`
must directly precede the final `end` line; both are removed. Each import of
`IxCC.Vendor.M` becomes the upstream import of `M`, and an import of an `Ix`
module without the prefix is refused. Nothing else may mention `IxCC.Vendor`,
so the vendored text is exactly the upstream text under these two edits. -/
def upstreamText (path text : String) : IO String := do
  let lines := text.splitOn "\n"
  let opening := s!"namespace {vendorNamespace}"
  let closing := s!"end {vendorNamespace}"
  let some start := lines.findIdx? (· == "public section")
    | throw (IO.userError s!"vendored {path} has no public section")
  need (lines[start + 1]? == some opening) s!"vendored {path} lacks `{opening}` after `public section`"
  let count := lines.length
  need (count ≥ 3 && lines[count - 1]? == some "" && lines[count - 2]? == some "end" &&
    lines[count - 3]? == some closing) s!"vendored {path} lacks `{closing}` before its final `end`"
  let unwrapped := (lines.eraseIdx (count - 3)).eraseIdx (start + 1)
  let restored ← unwrapped.mapM fun line => do
    let some keyword := importKeywords.find? (fun keyword => line.startsWith keyword)
      | return line
    let target := (line.drop keyword.length).toString
    if target.startsWith modulePrefix then
      return keyword ++ (target.drop modulePrefix.length).toString
    need (!target.startsWith "Ix.") s!"vendored {path} imports upstream module {target}"
    return line
  let upstream := "\n".intercalate restored
  need (!upstream.contains vendorNamespace) s!"vendored {path} mentions {vendorNamespace} elsewhere"
  return upstream

private def sha256Text (text : String) : IO String :=
  IO.FS.withTempFile fun handle path => do
    handle.putStr text
    handle.flush
    sha256 path

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
  let directory ← IO.FS.realPath (root / vendorDir)
  let actual := (← regularFiles directory).map fun path =>
    (path.toString.drop (directory.toString.length + 1)).toString
  need (actual.mergeSort (· ≤ ·) == (upstreamFiles ++ localFiles).mergeSort (· ≤ ·))
    "Aiur vendored file inventory differs"
  let pin ← readJson (directory / "upstream.json")
  need ((← strField pin "repository") == "https://github.com/argumentcomputer/ix" &&
    (← strField pin "revision") == revision &&
    (← strField pin "upstream_toolchain") == "leanprover/lean4:v4.33.1" &&
    (← strField pin "module_prefix") == modulePrefix &&
    (← strField pin "namespace") == vendorNamespace)
    "Aiur upstream identity differs"
  let hashes ← pairs (← field pin "upstream_files_sha256")
  need ((hashes.map Prod.fst).mergeSort (· ≤ ·) == upstreamFiles.mergeSort (· ≤ ·))
    "Aiur upstream hash inventory differs"
  let locals ← (← arrField pin "local_files").toList.mapM string
  need (locals == localFiles) "Aiur local file inventory differs"
  for (path, expected) in hashes do
    let file := directory / path
    let digest ← if path.endsWith ".lean" then
        sha256Text (← upstreamText path (← IO.FS.readFile file))
      else sha256 file
    need (digest == (← string expected)) s!"Aiur source differs from upstream: {path}"

private def mustReject (label : String) (action : IO Unit) : IO Unit := do
  let rejected ← try action; pure false catch _ => pure true
  need rejected s!"Aiur inventory mutation was accepted: {label}"

def mutationChecks (root : FilePath) : IO Unit := IO.FS.withTempDir fun temporary => do
  let original := root / vendorDir
  let copied := temporary / vendorDir
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
  -- an upstream import left without the vendored prefix
  let importer := copied / "Ix/Aiur/Stages/Bytecode.lean"
  let text ← IO.FS.readFile importer
  let reverted := text.replace s!"import {modulePrefix}Ix.Aiur.Goldilocks" "import Ix.Aiur.Goldilocks"
  need (reverted != text) "Aiur mutation fixture lost its vendored import"
  IO.FS.writeFile importer reverted
  mustReject "unprefixed import" (verifyVendor temporary)
  IO.FS.writeFile importer text
  -- a vendored file without its namespace wrapper
  let wrapped := copied / "Ix/Aiur/Goldilocks.lean"
  let text ← IO.FS.readFile wrapped
  IO.FS.writeFile wrapped (text.replace s!"namespace {vendorNamespace}\n" "")
  mustReject "unwrapped declarations" (verifyVendor temporary)
  IO.FS.writeFile wrapped text
  verifyVendor temporary

def run (root : FilePath) : IO Unit := do
  verifyVendor root
  mutationChecks root
  IO.println "aiur-inventory-ok: 11 upstream Lean modules (modules and declarations under IxCC.Vendor), 2 licenses, 6 mutation rejections"

end IxCC.Tools.AiurCheck
