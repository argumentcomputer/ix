import Lean

/-!
# Commit and external-path citation scanner

Pure Lean 4 replacement for `IxCC/tools/citations.sh`.

Finds every word token of 7 to 40 lowercase hex digits (with at least one `a`–`f`
letter, so pure numbers are skipped) that names a commit in the local git object
store (or a known commit missing from it), and prints TSV rows:

```
file<TAB>line<TAB>token<TAB>reachability
```

where `reachability` is:
* `main`: ancestor of `origin/main` (survives a branch squash),
* `branch-history`: ancestor of `HEAD` only (removed by a branch squash),
* `off-branch`: commit in the local object store outside both,
* `not-in-store`: matches a known missing commit prefix,
* `path`: absolute host path (`/home/`, `/nix/store/`, `/tmp/`) in `--fixtures` mode.

## Usage

```
lean --run IxCC/tools/Citations.lean             # IxCC/ (excl. plans, this script) + branch root files
lean --run IxCC/tools/Citations.lean --fixtures  # fixtures, manifests, READMEs, generated modules (non-main commits + abs paths)
lean --run IxCC/tools/Citations.lean --selftest  # run built-in unit tests
```
-/

namespace Citations

open System

def selfPath : String := "IxCC/tools/Citations.lean"

def knownMissing : Array String := #["fc058f935"]

def fixturePaths : Array String := #[
  "IxCC/fixtures",
  "IxCC/IxCCTests/Src/Artifacts",
  "IxCC/IxCCTests/Recheck/Artifacts",
  "IxCC/IxCCTests/Corpus/Artifacts",
  "IxCC/IxCCTests/Fir/Artifacts.lean",
  "IxCC/benchmarks/fixtures"
]

/-! ## Pure parsing & classification helpers -/

@[inline] def hasHexLetter (s : String) : Bool :=
  s.any fun c => 'a' ≤ c && c ≤ 'f'

/-- Split a `git grep -n` line `file:line:rest` into `(file, line, rest)`. -/
def parseGrepLine (raw : String) : Option (String × String × String) :=
  match raw.splitOn ":" with
  | file :: line :: rest =>
    if !file.isEmpty && !line.isEmpty && line.all Char.isDigit then
      some (file, line, ":".intercalate rest)
    else none
  | _ => none

/-- Match a token against a known-missing commit hash, matching `citations.sh`:
`case "$k" in "$tok"*|"${tok:0:8}"*)`. -/
def matchesKnownMissing (known tok : String) : Bool :=
  let prefix8 := String.ofList (tok.toList.take 8)
  known.startsWith tok || known.startsWith prefix8

/-- Parse one output line from `git cat-file --batch-check=%(objecttype) %(objectname)`.
Returns `some fullSha` iff the line names a commit object. -/
def parseBatchCheckCommit (line : String) : Option String :=
  match line.splitOn " " with
  | ["commit", full] =>
    if full.length == 40 then some full else none
  | _ => none

def formatRow (file line tok reach : String) : String :=
  s!"{file}\t{line}\t{tok}\t{reach}"

/-! ## Subprocess helpers -/

def runGit (cwd : FilePath) (args : Array String) (input? : Option String := none) :
    IO IO.Process.Output :=
  IO.Process.output {
    cmd := "git"
    args
    cwd := some cwd
    env := #[("GIT_TERMINAL_PROMPT", some "0")]
  } input?

def repoRoot : IO FilePath := do
  let out ← IO.Process.output {
    cmd := "git"
    args := #["rev-parse", "--show-toplevel"]
    env := #[("GIT_TERMINAL_PROMPT", some "0")]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"git rev-parse --show-toplevel failed: {out.stderr}"
  return FilePath.mk out.stdout.trimAscii.toString

def splitNonEmptyLines (s : String) : Array String :=
  ((s.splitOn "\n").map (fun l =>
    if l.endsWith "\r" then String.ofList (l.toList.dropLast) else l)).filter (!·.isEmpty)
    |>.toArray

/-- Run `git grep`, returning output lines (treats exit 1 "no matches" as empty). -/
def runGitGrep (root : FilePath) (grepArgs paths : Array String) : IO (Array String) := do
  if paths.isEmpty then return #[]
  let out ← runGit root (grepArgs ++ #["--"] ++ paths)
  if out.exitCode == 0 then
    return splitNonEmptyLines out.stdout
  else if out.exitCode == 1 then
    return #[]
  else
    throw <| IO.userError s!"git grep failed (exit {out.exitCode}): {out.stderr}"

/-- Resolve unique candidate tokens via a single batched `git cat-file --batch-check`,
writing stdin concurrently to avoid OS pipe buffer deadlocks on large token sets. -/
def resolveCommits (root : FilePath) (tokens : Array String) :
    IO (Std.HashMap String String) := do
  if tokens.isEmpty then return {}
  let child ← IO.Process.spawn {
    cmd := "git"
    args := #["cat-file", "--batch-check=%(objecttype) %(objectname)"]
    cwd := some root
    env := #[("GIT_TERMINAL_PROMPT", some "0")]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let (stdin, child) ← child.takeStdin
  let writeTask ← IO.asTask (prio := .dedicated) do
    for tok in tokens do
      stdin.putStr tok
      stdin.putStr "\n"
    stdin.flush
  let errTask ← IO.asTask (prio := .dedicated) child.stderr.readToEnd
  let stdout ← child.stdout.readToEnd
  let _ ← IO.ofExcept (← IO.wait writeTask)
  let stderr ← IO.ofExcept (← IO.wait errTask)
  let exitCode ← child.wait
  unless exitCode == 0 do
    throw <| IO.userError s!"git cat-file --batch-check failed (exit {exitCode}): {stderr}"
  let lines := splitNonEmptyLines stdout
  unless lines.size == tokens.size do
    throw <| IO.userError
      s!"git cat-file returned {lines.size} lines for {tokens.size} tokens"
  let mut result : Std.HashMap String String := {}
  for i in [0:tokens.size] do
    if let some full := parseBatchCheckCommit lines[i]! then
      result := result.insert tokens[i]! full
  return result

/-- Classify a full commit hash against `origin/main` and `HEAD`. -/
def classifyReach (root : FilePath) (full : String) : IO String := do
  let onMain ← runGit root #["merge-base", "--is-ancestor", full, "origin/main"]
  if onMain.exitCode == 0 then return "main"
  let onHead ← runGit root #["merge-base", "--is-ancestor", full, "HEAD"]
  if onHead.exitCode == 0 then return "branch-history"
  return "off-branch"

/-! ## Main scan -/

def scan (fixtures : Bool) : IO Unit := do
  let root ← repoRoot
  let paths ← if fixtures then
    -- Check for absolute host paths in fixtures/artifacts first (matches citations.sh order).
    let absLines ← runGitGrep root #["grep", "-I", "-n", "-E", "(/home/|/nix/store/|/tmp/)"] fixturePaths
    for raw in absLines do
      if let some (file, line, _) := parseGrepLine raw then
        IO.println (formatRow file line "absolute path" "path")
    pure fixturePaths
  else
    let diffOut ← runGit root
      #["diff", "--name-only", "--diff-filter=AM", "origin/main...HEAD", "--", ".", ":!IxCC"]
    let rootFiles := if diffOut.exitCode == 0 then splitNonEmptyLines diffOut.stdout else #[]
    pure (#["IxCC", ":!IxCC/plans", s!":!{selfPath}"] ++ rootFiles)

  let hexLines ← runGitGrep root #["grep", "-I", "-n", "-o", "-w", "-E", "[0-9a-f]{7,40}"] paths
  let mut rows : Array (String × String × String) := Array.emptyWithCapacity hexLines.size
  let mut seenTok : Std.HashSet String := {}
  let mut uniqueToks : Array String := #[]
  for raw in hexLines do
    if let some (file, line, tok) := parseGrepLine raw then
      if hasHexLetter tok then
        rows := rows.push (file, line, tok)
        if !seenTok.contains tok then
          seenTok := seenTok.insert tok
          uniqueToks := uniqueToks.push tok

  let commitByTok ← resolveCommits root uniqueToks
  let mut reachByFull : Std.HashMap String String := {}
  for (_, full) in commitByTok.toList do
    if !reachByFull.contains full then
      let r ← classifyReach root full
      reachByFull := reachByFull.insert full r

  for (file, line, tok) in rows do
    match commitByTok.get? tok with
    | some full =>
      let reach := reachByFull.getD full "off-branch"
      if fixtures && reach == "main" then
        continue
      IO.println (formatRow file line tok reach)
    | none =>
      for k in knownMissing do
        if matchesKnownMissing k tok then
          IO.println (formatRow file line tok "not-in-store")

/-! ## Built-in unit self-tests -/

def assertTrue (label : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"selftest FAILED [{label}]"

def runSelfTests : IO Unit := do
  -- 1. Pure-digit hex tokens skipped; tokens with a-f kept
  assertTrue "all digits skipped" (!hasHexLetter "1234567890")
  assertTrue "hex with letter kept" (hasHexLetter "123456a")
  assertTrue "all letters kept" (hasHexLetter "abcdef0")

  -- 2. Grep line parser (including extra colons in matched text)
  assertTrue "parseGrepLine hex"
    (parseGrepLine "IxCC/docs/a.md:42:deadbeef" == some ("IxCC/docs/a.md", "42", "deadbeef"))
  assertTrue "parseGrepLine abs path with colons"
    (parseGrepLine "IxCC/fixtures/x.json:7:  \"p\": \"/nix/store/abc\"" ==
      some ("IxCC/fixtures/x.json", "7", "  \"p\": \"/nix/store/abc\""))
  assertTrue "parseGrepLine rejects non-numeric line"
    (parseGrepLine "file:notnum:tok" == none)

  -- 3. Known-missing matching (matches bash `"$tok"*|"${tok:0:8}"*`)
  assertTrue "knownMissing exact" (matchesKnownMissing "fc058f935" "fc058f935")
  assertTrue "knownMissing 7-char prefix" (matchesKnownMissing "fc058f935" "fc058f9")
  assertTrue "knownMissing 8-char prefix" (matchesKnownMissing "fc058f935" "fc058f93")
  assertTrue "knownMissing longer matching first 8" (matchesKnownMissing "fc058f935" "fc058f93abcdef")
  assertTrue "knownMissing unrelated" (!matchesKnownMissing "fc058f935" "deadbeef")

  -- 4. Batch-check output parser
  let sha40 := "0123456789abcdef0123456789abcdef01234567"
  assertTrue "batch commit" (parseBatchCheckCommit s!"commit {sha40}" == some sha40)
  assertTrue "batch blob ignored" (parseBatchCheckCommit s!"blob {sha40}" == none)
  assertTrue "batch missing ignored" (parseBatchCheckCommit "deadbeef missing" == none)
  assertTrue "batch ambiguous ignored" (parseBatchCheckCommit "1234567 ambiguous" == none)

  -- 5. TSV formatting
  assertTrue "formatRow"
    (formatRow "IxCC/fixtures/a" "12" "absolute path" "path" ==
      "IxCC/fixtures/a\t12\tabsolute path\tpath")

  IO.println "[citations] selftest passed (all 16 assertions)"

/-! ## CLI entry point -/

def usageText : String :=
  "Usage: lean --run IxCC/tools/Citations.lean [--fixtures | --selftest | --help]"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => scan false; return 0
  | ["--fixtures"] => scan true; return 0
  | ["--selftest"] => runSelfTests; return 0
  | ["--help"] | ["-h"] => IO.println usageText; return 0
  | other =>
    IO.eprintln s!"citations: unknown argument(s): {other}\n{usageText}"
    return 2

end Citations

def main (args : List String) : IO UInt32 := Citations.main args
