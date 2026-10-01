/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Ix.Kernel.ImportManifest

/-! # Provenance gate for the kernel `Ix/Kernel` (the vendored con-leche tree and Ix's boundary) and the pure Ixon boundary

Checks, against `Tests.Ix.Kernel.ImportManifest`:

* the inventory of `Ix/Kernel/**/*.lean` (with `Ix/Kernel.lean`) and the
  pure `Ix/Ixon/**/*.lean` boundary is exactly the ported Lean targets
  under those roots plus the authored modules (a file added or removed
  without a manifest update fails); other rows (the ported fences under
  `scripts/`, the con-leche axiom pin under `Tests/`, and the licence and
  notice files) are checked row by row;
* every row's target exists with its recorded SHA-256, and no target is
  recorded twice;
* a verbatim row records equal source and target hashes; a rewritten row's
  target starts with the vendoring header naming its source
  (`vendorHeader`), and its path is the vendoring script's destination of
  its source path (`python3 scripts/vendor-conleche.py dest`); an adapted
  Lean row starts with its origin's port header naming its source, and, if
  it declares an SPDX licence, declares its set's licence;
* with `--source <workspace>`, every jj-origin row's source hash matches the
  file at its revision in that jj workspace (`jj file show`);
* with `--source-git <checkout>`, every git-origin row's source hash matches
  the file at its revision in that git checkout (`git show <rev>:<path>`),
  every rewritten row's target hash is that of the vendoring script's
  output on that file (`vendor-conleche.py hash`, which reads the file the
  same way), so a vendored file is upstream's up to the recorded rewrite,
  and the checkout has every git origin's revision (con-leche has two since
  int-5; `plans/refs/con-leche` and `plans/refs/con-leche-upstream` hold
  both).

Both source checks stay optional: the ordinary build must not depend on an
untracked reference. Hashing shells out to `sha256sum`, the vendoring
checks to `python3`. Exit code 0 on success, 1 on any failure. -/

open System Tests.Ix.Kernel.ImportManifest

private def fail (message : String) : IO Unit := throw (IO.userError message)

private def need (ok : Bool) (message : String) : IO Unit := unless ok do fail message

private def sha256 (path : FilePath) : IO String := do
  let result ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  need (result.exitCode == 0) result.stderr
  return (result.stdout.splitOn " ").headD ""

private def sha256String (contents : String) : IO String := do
  IO.FS.withTempFile fun handle path => do
    handle.putStr contents
    handle.flush
    sha256 path

private def sameFiles (what : String) (actual expected : Array String) : IO Unit := do
  let actual := actual.qsort (· < ·)
  let expected := expected.qsort (· < ·)
  unless actual == expected do
    let missing := expected.filter (!actual.contains ·)
    let extra := actual.filter (!expected.contains ·)
    fail s!"{what} inventory changed; missing {missing}, unexpected {extra}"

private def isLean (path : String) : Bool := path.endsWith ".lean"

/-- The licences a Lean file declares in `SPDX-License-Identifier` lines. -/
private def declaredLicenses (contents : String) : List String :=
  (contents.splitOn "\n").filterMap fun line =>
    match line.trimAscii.toString.splitOn "SPDX-License-Identifier: " with
    | [_, license] => some license.trimAscii.toString
    | _ => none

private def checkRow (set : PortSet) (row : PortRow) : IO Unit := do
  need (← (FilePath.mk row.target).pathExists) s!"missing ported file: {row.target}"
  need ((← sha256 row.target) == row.targetSha256) s!"ported content changed: {row.target}"
  match row.transformation with
  | .verbatim =>
    need (row.sourceSha256 == row.targetSha256)
      s!"verbatim row with different source and target hashes: {row.target}"
  | .rewritten =>
    let contents ← IO.FS.readFile row.target
    need (contents.startsWith (vendorHeader row.source))
      s!"vendoring header missing or changed: {row.target}"
  | .adapted _ =>
    if isLean row.target then
      let contents ← IO.FS.readFile row.target
      need (contents.startsWith (set.origin.header row.source))
        s!"port header missing or changed: {row.target}"
      let declared := declaredLicenses contents
      need (declared.isEmpty || declared.contains set.license)
        s!"{row.target} declares {declared}, not its recorded licence {set.license}"

private def readSource (origin : Origin) (checkout path : String) : IO IO.Process.Output :=
  match origin.vcs with
  | .jj => IO.Process.output {
      cmd := "jj", args := #["-R", checkout, "file", "show", "-r", origin.revision, s!"root:\"{path}\""] }
  | .git => IO.Process.output {
      cmd := "git", args := #["-C", checkout, "show", s!"{origin.revision}:{path}"] }

private def checkSource (origin : Origin) (checkout : String) (row : PortRow) : IO Unit := do
  let shown ← readSource origin checkout row.source
  need (shown.exitCode == 0) s!"cannot read {row.source} at {origin.revision}: {shown.stderr}"
  need ((← sha256String shown.stdout) == row.sourceSha256) s!"source hash mismatch: {row.source}"

/-- Runs the vendoring script, which prints one line per item. -/
private def vendor (args : Array String) : IO (Array String) := do
  let out ← IO.Process.output { cmd := "python3", args := #[vendorScript] ++ args }
  need (out.exitCode == 0) s!"{vendorScript} {args.toList.take 2} failed: {out.stderr}"
  return ((out.stdout.splitOn "\n").filter (!·.isEmpty)).toArray

/-- Every rewritten row's target is the script's destination of its source. -/
private def checkDestinations (rows : Array PortRow) : IO Unit := do
  let rows := rows.filter (·.transformation == .rewritten)
  let dests ← vendor (#["dest"] ++ rows.map (·.source))
  need (dests.size == rows.size) s!"{vendorScript} dest: {dests.size} lines for {rows.size} rows"
  for (row, dest) in rows.zip dests do
    need (dest == row.target) s!"rewritten row not at the script's destination: {row.source} is {dest}, not {row.target}"

/-- With `--source-git`: every rewritten row's source hash, destination and
target hash re-derived from upstream by the script, which reads the file
with `git show` as `checkSource` does. -/
private def checkRewritten (origin : Origin) (checkout : String) (rows : Array PortRow) : IO Unit := do
  if rows.isEmpty then return
  let lines ← vendor (#["hash", checkout] ++ rows.map (s!"{origin.revision}:{·.source}"))
  need (lines.size == rows.size) s!"{vendorScript} hash: {lines.size} lines for {rows.size} rows"
  for (row, line) in rows.zip lines do
    match line.splitOn " " with
    | [source, rewritten, dest, _] =>
      need (source == row.sourceSha256) s!"source hash mismatch: {row.source}"
      need (dest == row.target) s!"rewritten row not at the script's destination: {row.source}"
      need (rewritten == row.targetSha256)
        s!"vendored file is not the rewrite of its source at {origin.revision}: {row.target}"
    | _ => fail s!"{vendorScript} hash: unexpected line {line}"

/-- The checkout must hold the origin's revision, even when no row uses it. -/
private def checkGitRevision (checkout : String) (revision : String) : IO Unit := do
  let parsed ← IO.Process.output {
    cmd := "git", args := #["-C", checkout, "rev-parse", "--verify", s!"{revision}^\{commit}"] }
  need (parsed.exitCode == 0 && parsed.stdout.trimAscii.toString == revision)
    s!"{checkout} does not hold revision {revision}: {parsed.stderr}"

private structure Options where
  jj : Option String := none
  git : Option String := none

private def usage : String :=
  "usage: kernel-provenance [--source <old-ix-jj-workspace>] [--source-git <con-leche-git-checkout>]"

private def parseArgs : List String → Options → IO Options
  | [], options => pure options
  | "--source" :: path :: rest, options => parseArgs rest { options with jj := some path }
  | "--source-git" :: path :: rest, options => parseArgs rest { options with git := some path }
  | _, _ => do fail usage; pure {}

/-- The trees whose Lean files must all be recorded (`authored` or a row). -/
private def inventoryDirs : List String := ["Ix/Kernel", "Ix/Ixon"]
private def inventoryFiles : List String := ["Ix/Kernel.lean", "Ix/Address/Core.lean"]

private def inInventory (target : String) : Bool :=
  isLean target && (inventoryFiles.contains target || inventoryDirs.any (target.startsWith <| · ++ "/"))

private def leanFiles (root : String) : IO (Array String) := do
  unless ← (FilePath.mk root).pathExists do return #[]
  return ((← (FilePath.mk root).walkDir).filter (·.extension == some "lean")).map (·.toString)

def main (args : List String) : IO UInt32 := do
  try
    let options ← parseArgs args {}
    let mut files := #[]
    for dir in inventoryDirs do files := files ++ (← leanFiles dir)
    for single in inventoryFiles do
      if ← (FilePath.mk single).pathExists then files := files.push single
    let rows := portSets.flatMap (·.rows)
    let targets := rows.map (·.target)
    let duplicates := targets.filter fun target => (targets.filter (· == target)).size > 1
    need duplicates.isEmpty s!"targets recorded more than once: {duplicates.toList.eraseDups}"
    sameFiles "Ix/Kernel and pure Ixon source" files (targets.filter inInventory ++ authored)
    for set in portSets do
      for row in set.rows do checkRow set row
    checkDestinations rows
    if let some checkout := options.git then
      for revision in ((portSets.filter (·.origin.vcs == .git)).map (·.origin.revision)).toList.eraseDups do
        checkGitRevision checkout revision
    let mut verified := #[]
    for set in portSets do
      let checkout? := match set.origin.vcs with
        | .jj => options.jj
        | .git => options.git
      if let some checkout := checkout? then
        for row in set.rows do
          unless row.transformation == .rewritten do checkSource set.origin checkout row
        checkRewritten set.origin checkout (set.rows.filter (·.transformation == .rewritten))
        verified := verified.push
          s!"{set.origin.label} {String.ofList (set.origin.revision.toList.take 8)} {set.license} ({set.rows.size})"
    -- every revision of an origin's repository counts as that origin (con-leche has two, int-5)
    let modules (origin : Origin) := (portSets.filter (·.origin.repository == origin.repository)).foldl
      (fun n set => n + (set.rows.filter (inInventory ·.target)).size) 0
    let others := (rows.filter (!inInventory ·.target)).size
    let sources := if verified.isEmpty then "" else
      s!"; source hashes verified for {", ".intercalate verified.toList}"
    let rewritten := (rows.filter (·.transformation == .rewritten)).size
    IO.println s!"Kernel provenance OK: {modules oldBranch} ported modules from the old branch, \
      {modules conLeche} from con-leche ({rewritten} rewritten by {vendorScript}, the rest adapted), \
      {authored.size} authored modules, \
      {others} other files (licences, notice, fences, tests){sources}."
    return 0
  catch e =>
    IO.eprintln s!"kernel-provenance: {e}"
    return 1
