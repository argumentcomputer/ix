import Lean

/-!
# Rename `IxC` → `IxCK` (`«ix-kernel»` → `«ix-ck»`)

Deterministic, idempotent, re-runnable tool for renaming ix's certified-kernel
package from `IxC` (`«ix-kernel»`) to `IxCK` (`«ix-ck»`):

* directory:    `IxC/`        → `IxCK/`
* module root:  `IxC.*`       → `IxCK.*`
* Lake package: `«ix-kernel»` → `«ix-ck»` (lakefiles, manifests, Nix, prose)
* build dir:    `../.lake/kernel` unchanged (`flake.nix` `LEAN_PATH`, CI caches)

Declaration namespaces (`Ix.Kernel.*`, `Ixon.*`, `Univ.*`, ...) do not change.
Identifiers that merely contain the letters (`IxCC`, `IxccAiur`, `opSIxC`,
`IxCompileVerify`, `IxCertified`, `genIxConstantVal`, `jcb/ix-kernel-consistency`,
`ix-kernel-bridge`, `.ixc`, `IXC`) are left untouched.

## Usage (from repository root)

```
lean --run Scripts/RenameIxCToIxCK.lean [FLAGS]
```

Flags:
* *(default)*                Run mechanical rename (steps 1–3) + all 5
                             post-rename regeneration steps (4a–4e) + `--check`.
* `--no-regen`               Run mechanical rename (steps 1–3) only, skipping
                             the build/regeneration steps 4a–4e.
* `--only-regen`             Skip mechanical steps 1–3 and run regeneration
                             steps only (all 5 unless specific `--regen-*`
                             flags are passed).
* `--regen-role-data`        Step 4a: regenerate `IxCK/Kernel/Ixon/RoleData.lean`
                             via `kernel-pin-gen` (converging to fixed point).
* `--regen-closure-manifest` Step 4b: regenerate
                             `Tests/Fixtures/circuit-composed-closure-manifest.txt`
                             and `pinnedDigest` in
                             `IxVMRefinement/Endpoint/ClosureManifest.lean`.
* `--regen-initstd`          Step 4c: re-measure `CompileInitStd` and update
                             `Tests/Fixtures/initstd-reference.txt` if its
                             BLAKE3 digest or byte size moved.
* `--regen-ixcc-fixtures`    Step 4d: when `IxCC/tools/Regenerate.lean` is present,
                             refreeze IxCC's `.ixe` fixtures, censuses, and manifests
                             for the renamed `IxCK` role-evidence names (`IX_RENAME_JOBS`
                             overrides parallelism, default 16).
* `--regen-trusted-externs`  Step 4e: when `IxCC/` is present, re-hash
                             `lean_dependencies["«ix-ck»"].closure`, verify
                             `check-build-graph`, and re-pin
                             `IxCC/docs/trusted-externs.json` via
                             `IxCC/tools/RecordLedgerPins.lean`.
* `--check`                  Read-only verification mode: exit 0 iff no `IxC`
                             paths, whole-word text occurrences, un-rewritten
                             package names, `.ndjson.zst` `"str":"IxC"` entries,
                             or stale `ClosureManifest` digest remain.
* `--selftest`               Run built-in unit tests for all rewrite rules and
                             idempotence, then exit.
* `--help`, `-h`             Print usage and exit.

Running this script twice is a no-op on the second run.
-/

namespace RenameIxCToIxCK

open System

/-- Repository-relative path of this script, excluded from self-rewriting and `--check`. -/
def selfPath : String := "Scripts/RenameIxCToIxCK.lean"

/-! ## Low-level byte helpers (O(n), UTF-8 safe) -/

@[inline] def isWordByte (b : UInt8) : Bool :=
  (0x41 ≤ b && b ≤ 0x5A) || -- A-Z
  (0x61 ≤ b && b ≤ 0x7A) || -- a-z
  (0x30 ≤ b && b ≤ 0x39) || -- 0-9
  b == 0x5F                 -- _

@[inline] def isSpaceOrTab (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09

@[inline] def isAsciiWhitespace (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D

@[inline] def isDigitByte (b : UInt8) : Bool :=
  0x30 ≤ b && b ≤ 0x39

/-- Check whether `bs` matches `pat` starting at byte index `i`. -/
def matchesAt (bs pat : ByteArray) (i : Nat) : Bool :=
  if i + pat.size > bs.size then false
  else Id.run do
    for j in [0:pat.size] do
      if bs[i + j]! != pat[j]! then
        return false
    return true

/-- Append `pat` onto `out`. -/
@[inline] def pushBytes (out pat : ByteArray) : ByteArray :=
  out ++ pat

/-- Append slice `bs[lo:hi]` onto `out`. -/
def pushSlice (out bs : ByteArray) (lo hi : Nat) : ByteArray :=
  out ++ bs.extract lo hi

/-- Fixed UTF-8 byte literals. -/
def bGuillemetKernel : ByteArray := "«ix-kernel»".toUTF8
def bGuillemetCk : ByteArray := "«ix-ck»".toUTF8
def bBacktickKernel : ByteArray := "`ix-kernel`".toUTF8
def bBacktickCk : ByteArray := "`ix-ck`".toUTF8
def bNameEqKernel : ByteArray := "name = \"ix-kernel\"".toUTF8
def bNameEqCk : ByteArray := "name = \"ix-ck\"".toUTF8
def bIxC : ByteArray := "IxC".toUTF8
def bIxCK : ByteArray := "IxCK".toUTF8
def bIxCSlash : ByteArray := "IxC/".toUTF8
def bIxCKSlash : ByteArray := "IxCK/".toUTF8
def bExpansionPrefix : ByteArray := "`IxC` (Ix".toUTF8
def bExpansionOutPrefix : ByteArray := "`IxCK` (Ix".toUTF8
def bCertifiedClose : ByteArray := "Certified)".toUTF8
def bCertifiedKernelClose : ByteArray := "Certified Kernel)".toUTF8

-- IxCC/nix/build.nix specific ASCII package directory spellings
def bNixKernelSrc : ByteArray := "\"ix-kernel-src\"".toUTF8
def bNixCkSrc : ByteArray := "\"ix-ck-src\"".toUTF8
def bNixThenKernel : ByteArray := "then \"ix-kernel\"".toUTF8
def bNixThenCk : ByteArray := "then \"ix-ck\"".toUTF8
def bNixPkgKernel : ByteArray := ".lake/packages/ix-kernel".toUTF8
def bNixPkgCk : ByteArray := ".lake/packages/ix-ck".toUTF8
def bNixMangledKernel : ByteArray := "302253ix-kernel302273".toUTF8
def bNixMangledCk : ByteArray := "302253ix-ck302273".toUTF8

/-- Left word boundary for `IxC` at byte index `i`.
Also treats a Lean/C escape sequence `\t`, `\n`, `\r` (not preceded by `\\`) as
a word boundary so string-literal labels such as `"\tIxC="` rewrite cleanly. -/
def isLeftBoundary (bs : ByteArray) (i : Nat) : Bool :=
  if i == 0 then true
  else
    let prev := bs[i - 1]!
    if !isWordByte prev then true
    else if i ≥ 2 && bs[i - 2]! == 0x5C && (prev == 0x74 || prev == 0x6E || prev == 0x72) then
      i < 3 || bs[i - 3]! != 0x5C
    else false

/-- Right word boundary for `IxC` ending at `endIdx = i + 3`. -/
def isRightBoundary (bs : ByteArray) (endIdx : Nat) : Bool :=
  endIdx ≥ bs.size || !isWordByte bs[endIdx]!

/-- Check whether byte index `i` is at the start of a line (index 0 or preceded by `\n`). -/
@[inline] def isLineStart (bs : ByteArray) (i : Nat) : Bool :=
  i == 0 || bs[i - 1]! == 0x0A

/-- Check whether `bs` at line start `i` matches `^[ \t]*name = "ix-kernel"[ \t]*(\r?\n|$)`.
Returns `some (endIdx, replacementBytes)` if matched. -/
def matchLineNameEqKernel (bs : ByteArray) (i : Nat) : Option (Nat × ByteArray) := Id.run do
  if !isLineStart bs i then return none
  let mut p := i
  while p < bs.size && isSpaceOrTab bs[p]! do
    p := p + 1
  if !matchesAt bs bNameEqKernel p then return none
  let afterPat := p + bNameEqKernel.size
  let mut q := afterPat
  while q < bs.size && isSpaceOrTab bs[q]! do
    q := q + 1
  if q == bs.size || bs[q]! == 0x0A || bs[q]! == 0x0D then
    let rep := (bs.extract i p) ++ bNameEqCk ++ (bs.extract afterPat q)
    return some (q, rep)
  return none

/-- Check whether `bs` at line start `i` matches `^([ \t]*)IxC(/\S+) ( +)`
(for column-aligned tables like `Tests/Ix/Kernel/TrustSurface.lean`).
Returns `some (endIdx, replacementBytes)` with one space absorbed. -/
def matchAlignedPathLine (bs : ByteArray) (i : Nat) : Option (Nat × ByteArray) := Id.run do
  if !isLineStart bs i then return none
  let mut p := i
  while p < bs.size && isSpaceOrTab bs[p]! do
    p := p + 1
  if !matchesAt bs bIxCSlash p then return none
  let pathStart := p + 3 -- points at '/'
  let mut q := pathStart + 1
  while q < bs.size && !isAsciiWhitespace bs[q]! do
    q := q + 1
  -- Need at least one non-whitespace char after '/' and at least 2 spaces after path
  if q == pathStart + 1 then return none
  let spaceStart := q
  while q < bs.size && bs[q]! == 0x20 do
    q := q + 1
  let nSpaces := q - spaceStart
  if nSpaces ≥ 2 then
    let indent := bs.extract i p
    let restOfPath := bs.extract pathStart spaceStart
    let spaces := bs.extract (spaceStart + 1) q -- nSpaces - 1 spaces
    return some (q, indent ++ bIxCK ++ restOfPath ++ spaces)
  return none

/-- Check whether `bs` at `i` matches `` `IxC` (Ix<ws+>Certified) ``.
Returns `some (endIdx, replacementBytes)` preserving the exact whitespace. -/
def matchProseExpansion (bs : ByteArray) (i : Nat) : Option (Nat × ByteArray) := Id.run do
  if !matchesAt bs bExpansionPrefix i then return none
  let wsStart := i + bExpansionPrefix.size
  let mut p := wsStart
  while p < bs.size && isAsciiWhitespace bs[p]! do
    p := p + 1
  if p == wsStart then return none
  if !matchesAt bs bCertifiedClose p then return none
  let ws := bs.extract wsStart p
  return some (p + bCertifiedClose.size, bExpansionOutPrefix ++ ws ++ bCertifiedKernelClose)

/-- Fast compiled-C++ substring check via `String.splitOn`. -/
@[inline] def containsSubstr (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

/-- Rewrite a single line's bytes (no internal `\n`) according to all `IxC → IxCK` rules. -/
def rewriteLineBytes (isIxccBuildNix : Bool) (bs : ByteArray) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.emptyWithCapacity (bs.size + 16)
  let mut i := 0
  if let some (nextI, rep) := matchLineNameEqKernel bs 0 then
    out := out ++ rep
    i := nextI
  else if let some (nextI, rep) := matchAlignedPathLine bs 0 then
    out := out ++ rep
    i := nextI
  while i < bs.size do
    if matchesAt bs bGuillemetKernel i then
      out := out ++ bGuillemetCk
      i := i + bGuillemetKernel.size
      continue
    if matchesAt bs bBacktickKernel i then
      out := out ++ bBacktickCk
      i := i + bBacktickKernel.size
      continue
    if isIxccBuildNix then
      if matchesAt bs bNixKernelSrc i then
        out := out ++ bNixCkSrc
        i := i + bNixKernelSrc.size
        continue
      if matchesAt bs bNixThenKernel i then
        out := out ++ bNixThenCk
        i := i + bNixThenKernel.size
        continue
      if matchesAt bs bNixPkgKernel i then
        out := out ++ bNixPkgCk
        i := i + bNixPkgKernel.size
        continue
      if matchesAt bs bNixMangledKernel i then
        out := out ++ bNixMangledCk
        i := i + bNixMangledKernel.size
        continue
    if matchesAt bs bExpansionPrefix i then
      if let some (nextI, rep) := matchProseExpansion bs i then
        out := out ++ rep
        i := nextI
        continue
    if matchesAt bs bIxC i && isLeftBoundary bs i && isRightBoundary bs (i + 3) then
      out := out ++ bIxCK
      i := i + 3
      continue
    out := out.push bs[i]!
    i := i + 1
  return out

/-- Rewrite multiline `` `IxC` (Ix<ws+>Certified) `` occurrences (only runs when
`` `IxC` (Ix `` appears, e.g. `docs/kernel-module-root.md`). -/
def rewriteProseExpansions (text : String) : String :=
  if !containsSubstr text "`IxC` (Ix" then text
  else
    let bs := text.toUTF8
    let out := Id.run do
      let mut acc : ByteArray := ByteArray.emptyWithCapacity (bs.size + 16)
      let mut i := 0
      while i < bs.size do
        if matchesAt bs bExpansionPrefix i then
          if let some (nextI, rep) := matchProseExpansion bs i then
            acc := acc ++ rep
            i := nextI
            continue
        acc := acc.push bs[i]!
        i := i + 1
      return acc
    String.fromUTF8! out

/-- Rewrite a tracked text file according to all `IxC → IxCK` rules.
Pure, deterministic, idempotent, and fast under `lean --run` (lines without
`IxC` or `ix-kernel` are skipped via compiled `String.splitOn`). -/
def rewriteText (path : String) (text : String) : String :=
  if !containsSubstr text "IxC" && !containsSubstr text "ix-kernel" then text
  else
    let text := rewriteProseExpansions text
    let isIxccBuildNix := path == "IxCC/nix/build.nix" || path.endsWith "/IxCC/nix/build.nix"
    let lines := text.splitOn "\n"
    let outLines := lines.map fun line =>
      if !containsSubstr line "IxC" && !containsSubstr line "ix-kernel" then line
      else String.fromUTF8! (rewriteLineBytes isIxccBuildNix line.toUTF8)
    "\n".intercalate outLines

def rewriteBytes (path : String) (bs : ByteArray) : ByteArray :=
  match String.fromUTF8? bs with
  | some s => (rewriteText path s).toUTF8
  | none => bs

/-! ## Toolchain `.ndjson` name-table line rewriter -/

def bNdjsonPrefix1 : ByteArray := "{\"in\":".toUTF8
def bNdjsonMid : ByteArray := ",\"str\":{\"pre\":".toUTF8
def bNdjsonTailOld : ByteArray := ",\"str\":\"IxC\"}}".toUTF8
def bNdjsonTailNew : ByteArray := ",\"str\":\"IxCK\"}}".toUTF8

/-- Check if a single NDJSON line (without `\n`, optional trailing `\r`) is a
name-table entry `{"in":N,"str":{"pre":M,"str":"IxC"}}`. -/
def isNdjsonIxCLine (line : ByteArray) : Option Nat := Id.run do
  let effLen := if line.size > 0 && line[line.size - 1]! == 0x0D then line.size - 1 else line.size
  if !matchesAt line bNdjsonPrefix1 0 then return none
  let mut p := bNdjsonPrefix1.size
  let d1Start := p
  while p < effLen && isDigitByte line[p]! do p := p + 1
  if p == d1Start then return none
  if !matchesAt line bNdjsonMid p then return none
  p := p + bNdjsonMid.size
  let d2Start := p
  while p < effLen && isDigitByte line[p]! do p := p + 1
  if p == d2Start then return none
  if p + bNdjsonTailOld.size == effLen && matchesAt line bNdjsonTailOld p then
    return some p
  return none

/-- Rewrite all matching name-table lines in decompressed NDJSON text.
Fast under `lean --run`: uses compiled `String.splitOn` to skip non-matching lines.
Returns `(rewrittenText, countOfRewrittenLines)`. -/
def rewriteNdjsonText (text : String) : String × Nat :=
  if !containsSubstr text ",\"str\":\"IxC\"}}" then (text, 0)
  else Id.run do
    let lines := text.splitOn "\n"
    let mut outLines : Array String := Array.emptyWithCapacity lines.length
    let mut count := 0
    for line in lines do
      if !containsSubstr line ",\"str\":\"IxC\"}}" then
        outLines := outLines.push line
      else
        let bs := line.toUTF8
        match isNdjsonIxCLine bs with
        | some tailPos =>
          let hasCR := bs.size > 0 && bs[bs.size - 1]! == 0x0D
          let mut rep := bs.extract 0 tailPos ++ bNdjsonTailNew
          if hasCR then rep := rep.push 0x0D
          outLines := outLines.push (String.fromUTF8! rep)
          count := count + 1
        | none =>
          outLines := outLines.push line
    return ("\n".intercalate outLines.toList, count)

def rewriteNdjsonBytes (bs : ByteArray) : ByteArray × Nat :=
  let (s, n) := rewriteNdjsonText (String.fromUTF8! bs)
  (s.toUTF8, n)

/-! ## Built-in unit self-tests -/

def assertEq (label : String) (got want : String) : IO Unit := do
  unless got == want do
    throw <| IO.userError s!"selftest FAILED [{label}]:\n  got:  {repr got}\n  want: {repr want}"

def runSelfTests : IO Unit := do
  -- Whole-word IxC -> IxCK and non-matches preserved
  let sample1 :=
    "import IxC.Kernel.Core\n\
     import IxCC.Src.Syntax\n\
     import IxCCAiur.Lower\n\
     def opSIxC_sim := opSIxC + genIxConstantVal + IxCompileVerify + IxCertified\n\
     let x := \"foo.ixc\" ++ \"IXC\" ++ \"IxC/Kernel/Core.lean\"\n\
     IO.println s!\"IV\\tLean={a}\\tIxC={b}\\tIxVM={c}\"\n"
  let want1 :=
    "import IxCK.Kernel.Core\n\
     import IxCC.Src.Syntax\n\
     import IxCCAiur.Lower\n\
     def opSIxC_sim := opSIxC + genIxConstantVal + IxCompileVerify + IxCertified\n\
     let x := \"foo.ixc\" ++ \"IXC\" ++ \"IxCK/Kernel/Core.lean\"\n\
     IO.println s!\"IV\\tLean={a}\\tIxCK={b}\\tIxVM={c}\"\n"
  assertEq "whole-word + exclusions" (rewriteText "Test.lean" sample1) want1
  assertEq "idempotence sample1" (rewriteText "Test.lean" want1) want1

  -- Package names (and exclusions like jcb/ix-kernel-consistency & ix-kernel-bridge)
  let sample2 :=
    "package «ix-kernel» where\n\
     -- `ix-kernel` and `jcb/ix-kernel-consistency`\n\
     name = \"ix-kernel-bridge\"\n\
     name = \"ix-kernel\"\n"
  let want2 :=
    "package «ix-ck» where\n\
     -- `ix-ck` and `jcb/ix-kernel-consistency`\n\
     name = \"ix-kernel-bridge\"\n\
     name = \"ix-ck\"\n"
  assertEq "package names" (rewriteText "lakefile.toml" sample2) want2
  assertEq "idempotence sample2" (rewriteText "lakefile.toml" want2) want2

  -- Column alignment in TrustSurface.lean
  let sample3 :=
    "  IxC/Kernel/Expr.lean          computed_field\n\
       Ix/Address/Admission.lean     implemented_by\n"
  let want3 :=
    "  IxCK/Kernel/Expr.lean         computed_field\n\
       Ix/Address/Admission.lean     implemented_by\n"
  assertEq "TrustSurface column alignment" (rewriteText "Tests/Ix/Kernel/TrustSurface.lean" sample3) want3
  assertEq "idempotence sample3" (rewriteText "Tests/Ix/Kernel/TrustSurface.lean" want3) want3

  -- Multiline prose expansion in docs/kernel-module-root.md
  let sample4 := "module root of their own, `IxC` (Ix\nCertified). Module paths"
  let want4 := "module root of their own, `IxCK` (Ix\nCertified Kernel). Module paths"
  assertEq "prose expansion" (rewriteText "docs/kernel-module-root.md" sample4) want4
  assertEq "idempotence sample4" (rewriteText "docs/kernel-module-root.md" want4) want4

  -- IxCC/nix/build.nix package dir overrides
  let sample5 :=
    "  ixCSrc = pkgs.runCommand \"ix-kernel-src\" {} ''\n\
     package «ix-kernel» where\n\
     lean_lib IxC where\n\
     dir = name: if name == \"«ix-kernel»\" then \"ix-kernel\" else name;\n\
     mv \".lake/packages/«ix-kernel»\" .lake/packages/ix-kernel\n"
  let want5 :=
    "  ixCSrc = pkgs.runCommand \"ix-ck-src\" {} ''\n\
     package «ix-ck» where\n\
     lean_lib IxCK where\n\
     dir = name: if name == \"«ix-ck»\" then \"ix-ck\" else name;\n\
     mv \".lake/packages/«ix-ck»\" .lake/packages/ix-ck\n"
  assertEq "IxCC/nix/build.nix" (rewriteText "IxCC/nix/build.nix" sample5) want5
  assertEq "idempotence sample5" (rewriteText "IxCC/nix/build.nix" want5) want5

  -- Toolchain NDJSON name table
  let ndIn :=
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Init\"}}\n\
     {\"in\":4086,\"str\":{\"pre\":610,\"str\":\"IxC\"}}\n\
     {\"in\":4087,\"str\":{\"pre\":610,\"str\":\"IxCC\"}}\n"
  let ndWant :=
    "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"Init\"}}\n\
     {\"in\":4086,\"str\":{\"pre\":610,\"str\":\"IxCK\"}}\n\
     {\"in\":4087,\"str\":{\"pre\":610,\"str\":\"IxCC\"}}\n"
  let (ndOut, ndCount) := rewriteNdjsonBytes ndIn.toUTF8
  assertEq "ndjson rewrite" (String.fromUTF8! ndOut) ndWant
  unless ndCount == 1 do
    throw <| IO.userError s!"selftest FAILED [ndjson count]: got {ndCount}, want 1"
  let (ndOut2, ndCount2) := rewriteNdjsonBytes ndOut
  assertEq "ndjson idempotence" (String.fromUTF8! ndOut2) ndWant
  unless ndCount2 == 0 do
    throw <| IO.userError s!"selftest FAILED [ndjson idempotence count]: got {ndCount2}, want 0"

  -- IxCC/tools Lean scripts: IxCC preserved, «ix-kernel» -> «ix-ck»
  let sample6 :=
    "lean --run IxCC/tools/Regenerate.lean --check\n\
     lean --run IxCC/tools/Citations.lean --fixtures\n\
     let pkg := \"«ix-kernel»\"\n"
  let want6 :=
    "lean --run IxCC/tools/Regenerate.lean --check\n\
     lean --run IxCC/tools/Citations.lean --fixtures\n\
     let pkg := \"«ix-ck»\"\n"
  assertEq "IxCC/tools Lean scripts" (rewriteText "IxCC/tools/RecordLedgerPins.lean" sample6) want6
  assertEq "idempotence sample6" (rewriteText "IxCC/tools/RecordLedgerPins.lean" want6) want6

  IO.println "[rename-ixc-ixck] selftest passed (all 14 assertions)"

/-! ## Subprocess & filesystem utilities -/

def defaultSubprocessEnv (extra : Array (String × Option String)) : Array (String × Option String) :=
  #[("GIT_TERMINAL_PROMPT", some "0")] ++ extra

def runCapture (cmd : String) (args : Array String)
    (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  IO.Process.output { cmd, args, cwd, env := defaultSubprocessEnv env }

def runChecked (cmd : String) (args : Array String)
    (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO String := do
  let out ← runCapture cmd args cwd env
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"command failed (exit {out.exitCode}): {cmd} {" ".intercalate args.toList}\n\
        stdout:\n{out.stdout}\nstderr:\n{out.stderr}"
  return out.stdout

def runStreaming (cmd : String) (args : Array String)
    (cwd : Option FilePath := none)
    (env : Array (String × Option String) := #[]) : IO Unit := do
  IO.println s!"  $ {cmd} {" ".intercalate args.toList}"
  let child ← IO.Process.spawn
    { cmd, args, cwd, env := defaultSubprocessEnv env, stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do
    throw <| IO.userError s!"command failed (exit {code}): {cmd} {" ".intercalate args.toList}"

def splitNul (s : String) : List String :=
  (s.splitOn "\x00").filter (!·.isEmpty)

def sha256File (path : FilePath) : IO String := do
  let out ← runChecked "sha256sum" #[path.toString]
  match out.trimAscii.toString.splitOn " " with
  | h :: _ =>
    unless h.length == 64 do
      throw <| IO.userError s!"unexpected sha256sum output for {path}: {out}"
    return h
  | [] => throw <| IO.userError s!"empty sha256sum output for {path}"

def requireTool (tool : String) : IO Unit := do
  let pathVal := (← IO.getEnv "PATH").getD ""
  for dir in pathVal.splitOn ":" do
    if dir.isEmpty then continue
    let candidate := FilePath.mk dir / tool
    if ← candidate.pathExists then
      return
  throw <| IO.userError s!"required tool '{tool}' not found on PATH"

def resolveLeanExe : IO String := do
  if let some l := ← IO.getEnv "LEAN" then
    if !l.isEmpty then return l
  let probe ← runCapture "lean" #["--version"]
  if probe.exitCode == 0 then return "lean"
  let app ← IO.appPath
  if let some dir := app.parent then
    let sibling := dir / "lean"
    if ← sibling.pathExists then return sibling.toString
  return app.toString

def checkRepoRoot : IO Unit := do
  let topOut ← runCapture "git" #["rev-parse", "--show-toplevel"]
  unless topOut.exitCode == 0 do
    throw <| IO.userError "not inside a git checkout"
  let top ← IO.FS.realPath topOut.stdout.trimAscii.toString
  let cwd ← IO.FS.realPath "."
  unless top == cwd do
    throw <| IO.userError s!"run from the repository root ({top}), not {cwd}"
  unless (← FilePath.pathExists "lakefile.lean") && (← FilePath.pathExists "flake.nix") do
    throw <| IO.userError "missing lakefile.lean or flake.nix: not an ix checkout?"
  unless (← FilePath.pathExists "IxC") || (← FilePath.pathExists "IxCK") do
    throw <| IO.userError "neither IxC/ nor IxCK/ exists"

def listNdjsonFixtures : IO (Array FilePath) := do
  let dir : FilePath := "Tests/Fixtures/toolchains"
  unless ← dir.pathExists do return #[]
  let entries ← dir.readDir
  let mut out : Array FilePath := #[]
  for e in entries do
    if e.fileName.endsWith ".ndjson.zst" then
      out := out.push (dir / e.fileName)
  return out.qsort (fun a b => a.toString < b.toString)

/-! ## Step 1: Move `IxC/` → `IxCK/` -/

def step1MoveDir : IO Unit := do
  IO.println "[step 1] Checking tracked files under IxC/..."
  let tracked := splitNul (← runChecked "git" #["ls-files", "-z", "IxC"])
  if tracked.isEmpty then
    IO.println "  IxC/ has no tracked files (already moved)."
  else
    if !(← FilePath.pathExists "IxCK") then
      runStreaming "git" #["mv", "IxC", "IxCK"]
    else
      -- Partial earlier run: move remaining tracked files individually without overwriting
      for f in tracked do
        let rel := (f.dropPrefix? "IxC/").map (·.toString) |>.getD f
        let dest : FilePath := "IxCK" / rel
        if ← dest.pathExists then
          throw <| IO.userError s!"both {f} and {dest} exist"
        if let some parent := dest.parent then
          IO.FS.createDirAll parent
        let _ ← runChecked "git" #["mv", f, dest.toString]
    IO.println s!"  Moved {tracked.length} tracked files from IxC/ to IxCK/."
  if ← FilePath.pathExists "IxC" then
    IO.eprintln "  note: IxC/ still holds untracked files (e.g. a local build dir); left in place."

/-! ## Step 2: Rewrite tracked text files -/

def step2RewriteText : IO Unit := do
  IO.println "[step 2] Rewriting tracked text files..."
  let out ← runCapture "git" #["grep", "-lIz", "-E", "IxC|ix-kernel", "--", "."]
  -- git grep exits 1 when there are no matches
  unless out.exitCode == 0 || out.exitCode == 1 do
    throw <| IO.userError s!"git grep failed (exit {out.exitCode}): {out.stderr}"
  let files := (splitNul out.stdout).toArray.qsort (· < ·)
  let mut changed := 0
  for f in files do
    if f == selfPath then continue
    let raw ← IO.FS.readBinFile f
    let rewritten := rewriteBytes f raw
    if rewritten != raw then
      IO.FS.writeBinFile f rewritten
      changed := changed + 1
  IO.println s!"  Rewrote {changed} tracked text files (scanned {files.size} candidates)."

/-! ## Step 3: Rewrite toolchain `.ndjson.zst` fixtures -/

def step3RewriteToolchains : IO Unit := do
  IO.println "[step 3] Checking toolchain .ndjson.zst name tables..."
  let fixtures ← listNdjsonFixtures
  if fixtures.isEmpty then
    IO.println "  No toolchain fixtures found."
    return
  requireTool "zstd"
  let mut rewrittenFiles := 0
  for f in fixtures do
    let tmpIn : FilePath := f.toString ++ ".rename-in.tmp"
    let tmpOut : FilePath := f.toString ++ ".rename-out.tmp"
    try
      let _ ← runChecked "zstd" #["-dcq", f.toString, "-o", tmpIn.toString]
      let raw ← IO.FS.readBinFile tmpIn
      let (updated, nLines) := rewriteNdjsonBytes raw
      if nLines > 0 then
        IO.FS.writeBinFile tmpOut updated
        let _ ← runChecked "zstd" #["-19", "-q", "-f", tmpOut.toString, "-o", f.toString]
        IO.println s!"  Rewrote {nLines} name-table record(s) in {f}."
        rewrittenFiles := rewrittenFiles + 1
    finally
      if ← tmpIn.pathExists then IO.FS.removeFile tmpIn
      if ← tmpOut.pathExists then IO.FS.removeFile tmpOut
  if rewrittenFiles == 0 then
    IO.println "  All toolchain fixtures already renamed."

/-! ## Step 4a: Regenerate `IxCK/Kernel/Ixon/RoleData.lean` (`kernel-pin-gen`) -/

def cleanStaleKernelIxC : IO Unit := do
  for stale in #[FilePath.mk ".lake/kernel/lib/lean/IxC",
                 FilePath.mk ".lake/kernel/ir/IxC",
                 FilePath.mk ".lake/build/lib/lean/IxC",
                 FilePath.mk ".lake/build/ir/IxC"] do
    if ← stale.pathExists then
      IO.FS.removeDirAll stale
      IO.println s!"  Removed stale build directory {stale}."

def extractRoleDataInitDigest (path : FilePath) : IO (Option String) := do
  unless ← path.pathExists do return none
  let text ← IO.FS.readFile path
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.startsWith "def source : String := \"blake3:" then
      let rest := (t.dropPrefix? "def source : String := \"blake3:").map (·.toString) |>.getD ""
      match rest.splitOn " " with
      | d :: _ => if d.length == 64 then return some d
      | [] => pure ()
  return none

def queryCertConsts : IO String := do
  let script :=
    "import Ix.RoleEvidence\n\
     #eval IO.println (\",\".intercalate (Ix.RoleEvidence.allCertTheorems.flatMap (·.2) |>.map toString))\n"
  let dir ← IO.FS.createTempDir
  try
    let f := dir / "cert_consts.lean"
    IO.FS.writeFile f script
    let out ← runChecked "lake" #["env", "lean", f.toString]
    let consts := out.trimAscii.toString
    unless !consts.isEmpty do
      throw <| IO.userError "failed to query Ix.RoleEvidence.allCertTheorems"
    return consts
  finally
    IO.FS.removeDirAll dir

def blake3OfFileViaLake (artifact : FilePath) : IO String := do
  let rustLib : FilePath := ".lake/packages/Blake3/.lake/build/lib/libBlake3_Blake3Rust.so"
  let leanLib : FilePath := ".lake/packages/Blake3/.lake/build/lib/libBlake3_Blake3.so"
  unless (← rustLib.pathExists) && (← leanLib.pathExists) do
    runStreaming "lake" #["build", "Blake3/Blake3:shared"]
  let script :=
    s!"import Ix.FileDigest\n\
       #eval do IO.println (← Ix.FileDigest.blake3File {artifact.toString.quote})\n"
  let dir ← IO.FS.createTempDir
  try
    let f := dir / "blake3_file.lean"
    IO.FS.writeFile f script
    let out ← runChecked "lake"
      #["env", "lean",
        s!"--load-dynlib={rustLib}",
        s!"--load-dynlib={leanLib}",
        f.toString]
    let digest := out.trimAscii.toString
    unless digest.length == 64 do
      throw <| IO.userError s!"unexpected blake3 output for {artifact}: {out}"
    return digest
  finally
    IO.FS.removeDirAll dir

def step4aRegenRoleData : IO Unit := do
  IO.println "[step 4a] Regenerating IxCK/Kernel/Ixon/RoleData.lean via kernel-pin-gen..."
  cleanStaleKernelIxC
  runStreaming "lake" #["-d", "IxCK", "build", "--wfail"]
  runStreaming "lake" #["-d", "IxCK", "build", "IxCK.Kernel.PinGen.Certs"]
  runStreaming "lake" #["build", "ix", "kernel-pin-gen"]
  let certConsts ← queryCertConsts
  IO.FS.createDirAll ".lake/envs"
  let initPath := ".lake/envs/initstd.ixe"
  let certsPath := ".lake/envs/certs.ixe"
  let roleDataPath : FilePath := "IxCK/Kernel/Ixon/RoleData.lean"
  runStreaming ".lake/build/bin/ix"
    #["compile", "Benchmarks/Compile/CompileInitStd.lean", "--no-build", "--out", initPath]
  runStreaming ".lake/build/bin/ix"
    #["compile", "IxCK/Kernel/PinGen/Certs.lean", "--no-build", "--out", certsPath,
      "--consts", certConsts]
  runStreaming ".lake/build/bin/kernel-pin-gen"
    #[initPath, certsPath, roleDataPath.toString]
  -- Rebuild RoleData + ix with the newly renamed private cert names, then converge
  -- to the exact fixed point so RoleData.source records the final initstd.ixe digest.
  runStreaming "lake" #["-d", "IxCK", "build", "IxCK.Kernel.Ixon.RoleData"]
  runStreaming "lake" #["build", "ix"]
  runStreaming ".lake/build/bin/ix"
    #["compile", "Benchmarks/Compile/CompileInitStd.lean", "--no-build", "--out", initPath]
  let newInitDigest ← blake3OfFileViaLake initPath
  let recordedInitDigest ← extractRoleDataInitDigest roleDataPath
  if recordedInitDigest != some newInitDigest then
    IO.println s!"  Converging RoleData.lean provenance digest ({recordedInitDigest.getD "?"} -> {newInitDigest})..."
    runStreaming ".lake/build/bin/kernel-pin-gen"
      #[initPath, certsPath, roleDataPath.toString]
    runStreaming "lake" #["-d", "IxCK", "build", "IxCK.Kernel.Ixon.RoleData"]
    runStreaming "lake" #["build", "ix"]
  IO.println s!"  RoleData.lean regenerated and converged (initstd blake3 = {newInitDigest})."

/-! ## Step 4b: Regenerate `ClosureManifest.lean` + `circuit-composed-closure-manifest.txt` -/

def closureManifestLean : FilePath := "IxVMRefinement/Endpoint/ClosureManifest.lean"
def closureManifestTxt : FilePath := "Tests/Fixtures/circuit-composed-closure-manifest.txt"

def extractPinnedDigest (text : String) : Option String := Id.run do
  let prefix_ := "def pinnedDigest : String := \""
  for line in text.splitOn "\n" do
    if line.startsWith prefix_ then
      let rest := (line.dropPrefix? prefix_).map (·.toString) |>.getD ""
      match rest.splitOn "\"" with
      | d :: _ => if d.length == 64 then return some d
      | [] => pure ()
  return none

def replacePinnedDigest (text newDigest : String) : Except String String := do
  let some oldDigest := extractPinnedDigest text
    | throw s!"could not locate `def pinnedDigest : String := \"<64 hex>\"` in {closureManifestLean}"
  let oldLine := s!"def pinnedDigest : String := \"{oldDigest}\""
  let newLine := s!"def pinnedDigest : String := \"{newDigest}\""
  let parts := text.splitOn oldLine
  unless parts.length == 2 do
    throw s!"expected exactly one pinnedDigest line in {closureManifestLean}, found {parts.length - 1}"
  return newLine.intercalate parts

def step4bRegenClosureManifest : IO Unit := do
  unless ← closureManifestLean.pathExists do
    IO.println "[step 4b] IxVMRefinement/Endpoint/ClosureManifest.lean not present; skipping."
    return
  IO.println "[step 4b] Regenerating ClosureManifest + circuit-composed-closure-manifest.txt..."
  requireTool "sha256sum"
  cleanStaleKernelIxC
  runStreaming "lake" #["build", "Ix.IxVM.Consistency.TableValid"]
  IO.println s!"  $ IXVM_CLOSURE_MANIFEST_WRITE={closureManifestTxt} lake env lean {closureManifestLean}"
  let out ← runCapture "lake" #["env", "lean", closureManifestLean.toString] none
    #[("IXVM_CLOSURE_MANIFEST_WRITE", some closureManifestTxt.toString)]
  let combined := out.stdout ++ "\n" ++ out.stderr
  unless (combined.splitOn "closure manifest written to").length > 1 do
    throw <| IO.userError
      s!"ClosureManifest did not write {closureManifestTxt} (exit {out.exitCode}):\n{combined}"
  let digest ← sha256File closureManifestTxt
  let leanText ← IO.FS.readFile closureManifestLean
  let updatedLean ← IO.ofExcept (replacePinnedDigest leanText digest)
  if updatedLean != leanText then
    IO.FS.writeFile closureManifestLean updatedLean
    IO.println s!"  Updated pinnedDigest in {closureManifestLean} -> {digest}."
  else
    IO.println s!"  pinnedDigest in {closureManifestLean} already matches {digest}."
  -- Re-verify by building the module cleanly (must pass `#check_closure_manifest`!)
  runStreaming "lake" #["build", "IxVMRefinement.Endpoint.ClosureManifest"]
  IO.println s!"  ClosureManifest built and verified cleanly (sha256 = {digest})."

/-! ## Step 4c: Re-measure & update `Tests/Fixtures/initstd-reference.txt` -/

def initStdRefPath : FilePath := "Tests/Fixtures/initstd-reference.txt"

def updateInitStdRefText (text newDigest : String) (newBytes : Nat) : Except String (String × Bool) := Id.run do
  let mut sawBlake3 := false
  let mut sawBytes := false
  let mut changed := false
  let mut outLines : Array String := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "blake3\t" then
      sawBlake3 := true
      let want := s!"blake3\t{newDigest}"
      if line != want then changed := true
      outLines := outLines.push want
    else if line.startsWith "bytes\t" then
      sawBytes := true
      let want := s!"bytes\t{newBytes}"
      if line != want then changed := true
      outLines := outLines.push want
    else
      outLines := outLines.push line
  unless sawBlake3 && sawBytes do
    return .error s!"{initStdRefPath} missing blake3 or bytes line"
  return .ok ("\n".intercalate outLines.toList, changed)

def step4cRegenInitStd (existingArtifact : Option FilePath := none) : IO Unit := do
  unless ← initStdRefPath.pathExists do
    IO.println "[step 4c] Tests/Fixtures/initstd-reference.txt not present; skipping."
    return
  IO.println "[step 4c] Measuring Init+Std reference artifact..."
  let dir ← IO.FS.createTempDir
  try
    let artifact ← match existingArtifact with
      | some p =>
        if ← p.pathExists then
          IO.println s!"  Reusing converged artifact {p} from step 4a."
          pure p
        else
          runStreaming "lake" #["build", "ix"]
          let a := dir / "initstd.ixe"
          runStreaming ".lake/build/bin/ix"
            #["compile-lean", "Benchmarks/Compile/CompileInitStd.lean", "--no-build",
              "--out", a.toString]
          pure a
      | none =>
        runStreaming "lake" #["build", "ix"]
        let a := dir / "initstd.ixe"
        runStreaming ".lake/build/bin/ix"
          #["compile-lean", "Benchmarks/Compile/CompileInitStd.lean", "--no-build",
            "--out", a.toString]
        pure a
    let digest ← blake3OfFileViaLake artifact
    let size := (← artifact.metadata).byteSize.toNat
    let text ← IO.FS.readFile initStdRefPath
    let (updated, changed) ← IO.ofExcept (updateInitStdRefText text digest size)
    if changed then
      IO.FS.writeFile initStdRefPath updated
      IO.println s!"  Updated {initStdRefPath}: blake3={digest}, bytes={size}."
    else
      IO.println s!"  {initStdRefPath} unchanged (blake3={digest}, bytes={size})."
    -- Sanity-check strict kernel checking on the artifact:
    -- exit 0 = all subjects accepted (post-§7.10 inert compiler-trust declarations);
    -- exit 3 = strict refusal of compiler-trust roles; any other exit (1/2) is an error.
    let chk ← runCapture ".lake/build/bin/ix" #["check-lean", artifact.toString, "--anon"]
    unless chk.exitCode == 0 || chk.exitCode == 3 do
      throw <| IO.userError
        s!"expected `ix check-lean --anon` on Init+Std artifact to exit 0 or 3, got {chk.exitCode}\n\
          stdout:\n{chk.stdout}\nstderr:\n{chk.stderr}"
    IO.println s!"  Verified `ix check-lean --anon` on Init+Std artifact (exit {chk.exitCode})."
  finally
    IO.FS.removeDirAll dir

/-! ## Step 4d: Regenerate IxCC fixtures (`IxCC/tools/Regenerate.lean`, when present) -/

def ixccRegenScript : FilePath := "IxCC/tools/Regenerate.lean"
def ixccRecordPinsScript : FilePath := "IxCC/tools/RecordLedgerPins.lean"

def step4dRegenIxccFixtures : IO Unit := do
  unless ← ixccRegenScript.pathExists do
    IO.println "[step 4d] IxCC/tools/Regenerate.lean not present; skipping."
    return
  IO.println "[step 4d] Regenerating IxCC fixtures via IxCC/tools/Regenerate.lean..."
  let leanExe ← resolveLeanExe
  let jobs := (← IO.getEnv "IX_RENAME_JOBS").getD "16"
  let dir ← IO.FS.createTempDir
  try
    runStreaming leanExe #["--run", ixccRegenScript.toString, "--work", dir.toString, "--jobs", jobs]
  finally
    IO.FS.removeDirAll dir

/-! ## Step 4e: Re-pin `IxCC/docs/trusted-externs.json` (when `IxCC/` is present) -/

def ixccLedgerPath : FilePath := "IxCC/docs/trusted-externs.json"

def step4eRegenTrustedExterns : IO Unit := do
  unless ← ixccLedgerPath.pathExists do
    IO.println "[step 4e] IxCC/docs/trusted-externs.json not present; skipping."
    return
  IO.println "[step 4e] Re-pinning IxCC/docs/trusted-externs.json..."
  requireTool "sha256sum"
  let leanExe ← resolveLeanExe
  -- Clean stale «ix-kernel» / ix-kernel package dirs under IxCC/.lake if present
  for stale in #[FilePath.mk "IxCC/.lake/packages/«ix-kernel»",
                 FilePath.mk "IxCC/.lake/packages/ix-kernel"] do
    if ← stale.pathExists then
      IO.FS.removeDirAll stale
  -- 1. Re-hash every file recorded in lean_dependencies[lake_package == "«ix-ck»"].closure
  let ledgerText ← IO.FS.readFile ixccLedgerPath
  let ledgerJson ← IO.ofExcept (Lean.Json.parse ledgerText)
  let mut closureUpdates : List (String × Lean.Json) := []
  match ledgerJson.getObjVal? "lean_dependencies" with
  | .ok (.arr deps) =>
    for dep in deps do
      let pkg := (dep.getObjValAs? String "lake_package").toOption.getD ""
      if pkg == "«ix-ck»" then
        let wsPath := ((dep.getObjVal? "pins").bind (·.getObjValAs? String "workspace_path")).toOption.getD "../IxCK"
        let srcDir := (dep.getObjValAs? String "source_dir").toOption.getD ".."
        let baseDir : FilePath := FilePath.mk "IxCC" / wsPath / srcDir
        match dep.getObjVal? "closure" with
        | .ok (.obj kvs) =>
          for (relPath, _) in kvs.toList do
            let fullPath := baseDir / relPath
            let h ← sha256File fullPath
            closureUpdates := (relPath, Lean.Json.str h) :: closureUpdates
        | _ => pure ()
  | _ => pure ()
  let dir ← IO.FS.createTempDir
  try
    if !closureUpdates.isEmpty then
      let closureFile := dir / "closure.json"
      IO.FS.writeFile closureFile (Lean.Json.mkObj closureUpdates.reverse).pretty
      runStreaming leanExe
        #["--run", ixccRecordPinsScript.toString, "--closure", "«ix-ck»",
          closureFile.toString, ixccLedgerPath.toString]
      IO.println s!"  Re-hashed {closureUpdates.length} IxCK closure file(s) in {ixccLedgerPath}."
    -- 2. Verify build graph and re-record mechanical pins via check-trusted-externs --record
    runStreaming "lake" #["-d", "IxCC", "build", "check-trusted-externs", "check-build-graph"]
    runStreaming "IxCC/.lake/build/bin/check-build-graph" #["--root", "IxCC"]
    let pinsOut ← runChecked "IxCC/.lake/build/bin/check-trusted-externs" #["--record", "--root", "IxCC"]
    let pinsFile := dir / "pins.json"
    IO.FS.writeFile pinsFile pinsOut
    runStreaming leanExe
      #["--run", ixccRecordPinsScript.toString, pinsFile.toString, ixccLedgerPath.toString]
    -- 3. Verify the ledger passes audit cleanly
    runStreaming "IxCC/.lake/build/bin/check-trusted-externs" #["--root", "IxCC"]
    IO.println s!"  {ixccLedgerPath} re-pinned and verified cleanly."
  finally
    IO.FS.removeDirAll dir

/-! ## Verification mode (`--check`) -/

def runCheck : IO Unit := do
  IO.println "[check] Verifying IxC → IxCK rename invariants..."
  let mut errors : Array String := #[]

  -- 1. No tracked paths under IxC/ or with component IxC
  let allTracked := splitNul (← runChecked "git" #["ls-files", "-z"])
  for p in allTracked do
    let comps := p.splitOn "/"
    if comps.contains "IxC" then
      errors := errors.push s!"tracked path still names IxC: {p}"

  -- 2. No tracked text file (except selfPath) would change under rewriteBytes
  let grepOut ← runCapture "git" #["grep", "-lIz", "-E", "IxC|ix-kernel", "--", "."]
  unless grepOut.exitCode == 0 || grepOut.exitCode == 1 do
    throw <| IO.userError s!"git grep failed (exit {grepOut.exitCode}): {grepOut.stderr}"
  for f in (splitNul grepOut.stdout).toArray.qsort (· < ·) do
    if f == selfPath then continue
    let raw ← IO.FS.readBinFile f
    if rewriteBytes f raw != raw then
      errors := errors.push s!"tracked text file still needs IxC/ix-kernel rewrite: {f}"

  -- 3. No toolchain .ndjson.zst contains `"str":"IxC"`
  let fixtures ← listNdjsonFixtures
  if !fixtures.isEmpty then
    requireTool "zstd"
    for f in fixtures do
      let tmp : FilePath := f.toString ++ ".check.tmp"
      try
        let _ ← runChecked "zstd" #["-dcq", f.toString, "-o", tmp.toString]
        let raw ← IO.FS.readBinFile tmp
        let (_, nLines) := rewriteNdjsonBytes raw
        if nLines > 0 then
          errors := errors.push s!"toolchain fixture still has {nLines} IxC name-table entries: {f}"
      finally
        if ← tmp.pathExists then IO.FS.removeFile tmp

  -- 4. ClosureManifest pinnedDigest == sha256(circuit-composed-closure-manifest.txt)
  if (← closureManifestLean.pathExists) && (← closureManifestTxt.pathExists) then
    requireTool "sha256sum"
    let leanText ← IO.FS.readFile closureManifestLean
    match extractPinnedDigest leanText with
    | none => errors := errors.push s!"missing pinnedDigest in {closureManifestLean}"
    | some pinned =>
      let actual ← sha256File closureManifestTxt
      if pinned != actual then
        errors := errors.push
          s!"ClosureManifest pinnedDigest mismatch: pinned={pinned}, actual={actual}"

  if !errors.isEmpty then
    IO.eprintln s!"[check] FAILED ({errors.size} issue(s)):"
    for e in errors.toList.take 40 do
      IO.eprintln s!"  - {e}"
    if errors.size > 40 then
      IO.eprintln s!"  ... and {errors.size - 40} more"
    IO.Process.exit 1

  IO.println "[check] PASS: 0 IxC tracked paths, 0 un-rewritten text files, 0 IxC toolchain entries, ClosureManifest digest pinned."

/-! ## CLI entry point -/

structure Config where
  checkOnly : Bool := false
  selfTestOnly : Bool := false
  showHelp : Bool := false
  runMechanical : Bool := true
  regenRoleData : Bool := false
  regenClosureManifest : Bool := false
  regenInitStd : Bool := false
  regenIxccFixtures : Bool := false
  regenTrustedExterns : Bool := false
  explicitRegen : Bool := false
  noRegen : Bool := false

def parseArgs (args : List String) : Except String Config := do
  let mut cfg : Config := {}
  for a in args do
    match a with
    | "--check" => cfg := { cfg with checkOnly := true }
    | "--selftest" => cfg := { cfg with selfTestOnly := true }
    | "--help" | "-h" => cfg := { cfg with showHelp := true }
    | "--no-regen" => cfg := { cfg with noRegen := true }
    | "--only-regen" => cfg := { cfg with runMechanical := false }
    | "--regen-role-data" => cfg := { cfg with regenRoleData := true, explicitRegen := true }
    | "--regen-closure-manifest" =>
      cfg := { cfg with regenClosureManifest := true, explicitRegen := true }
    | "--regen-initstd" => cfg := { cfg with regenInitStd := true, explicitRegen := true }
    | "--regen-ixcc-fixtures" =>
      cfg := { cfg with regenIxccFixtures := true, explicitRegen := true }
    | "--regen-trusted-externs" =>
      cfg := { cfg with regenTrustedExterns := true, explicitRegen := true }
    | other => throw s!"unknown argument: {other} (try --help)"
  if cfg.noRegen && cfg.explicitRegen then
    throw "--no-regen cannot be combined with explicit --regen-* flags"
  if !cfg.noRegen && !cfg.explicitRegen then
    cfg := { cfg with
      regenRoleData := true
      regenClosureManifest := true
      regenInitStd := true
      regenIxccFixtures := true
      regenTrustedExterns := true }
  return cfg

def usageText : String :=
  "Usage: lean --run Scripts/RenameIxCToIxCK.lean [FLAGS]\n\
   \n\
   Flags:\n\
     (default)                   Mechanical rename (steps 1-3) + all 5 regen steps + --check\n\
     --no-regen                  Mechanical rename (steps 1-3) only\n\
     --only-regen                Run regeneration steps without steps 1-3\n\
     --regen-role-data           Step 4a: regenerate IxCK/Kernel/Ixon/RoleData.lean\n\
     --regen-closure-manifest    Step 4b: regenerate ClosureManifest + manifest txt\n\
     --regen-initstd             Step 4c: re-measure Tests/Fixtures/initstd-reference.txt\n\
     --regen-ixcc-fixtures       Step 4d: regenerate IxCC fixtures via Regenerate.lean (if present)\n\
     --regen-trusted-externs     Step 4e: re-pin IxCC/docs/trusted-externs.json via RecordLedgerPins.lean\n\
     --check                     Read-only verification of rename & ClosureManifest pin\n\
     --selftest                  Run built-in unit tests and exit\n\
     --help, -h                  Show this help"

def main (args : List String) : IO Unit := do
  let cfg ← IO.ofExcept (parseArgs args)
  if cfg.showHelp then
    IO.println usageText
    return
  if cfg.selfTestOnly then
    runSelfTests
    return
  requireTool "git"
  checkRepoRoot
  if cfg.checkOnly then
    runCheck
    return
  runSelfTests
  if cfg.runMechanical then
    step1MoveDir
    step2RewriteText
    step3RewriteToolchains
  if cfg.regenRoleData then
    step4aRegenRoleData
  if cfg.regenClosureManifest then
    step4bRegenClosureManifest
  if cfg.regenInitStd then
    step4cRegenInitStd (if cfg.regenRoleData then some ".lake/envs/initstd.ixe" else none)
  if cfg.regenIxccFixtures then
    step4dRegenIxccFixtures
  if cfg.regenTrustedExterns then
    step4eRegenTrustedExterns
  if cfg.runMechanical && !cfg.noRegen then
    runCheck
  else if cfg.noRegen then
    IO.println "[rename-ixc-ixck] mechanical rename done (--no-regen); run --only-regen to regenerate RoleData/ClosureManifest/initstd-reference/ixcc-fixtures/trusted-externs, then --check."

end RenameIxCToIxCK

def main (args : List String) : IO Unit := RenameIxCToIxCK.main args
