import Runner.Build

/-! Provenance, file-invalidation, and SHA-256 verification helpers shared by
the K4/K5 benchmark runner (`BenchK45`). -/

namespace Runner

open Lean System

/-- Unconditionally remove `path` if it exists, ignoring `ENOENT`. -/
def unlinkIfExists (path : FilePath) : IO Unit := do
  try
    IO.FS.removeFile path
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e => throw e

private def isHexChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Compute the lowercase 64-hex-character SHA-256 digest of `path` via `sha256sum`.
Throws an `IO.Error` if `path` does not exist or `sha256sum` fails. -/
def sha256File (path : FilePath) : IO String := do
  unless ← path.pathExists do
    throw (IO.userError s!"sha256File: file does not exist: {path}")
  let out ← IO.Process.output { cmd := "sha256sum", args := #[path.toString] }
  if out.exitCode != 0 then
    throw (IO.userError s!"sha256sum {path} exited {out.exitCode}: {out.stderr.trimAscii}")
  let token := ((out.stdout.trimAscii.toString.splitOn " ").headD "").trimAscii.toString
  let digest := (if token.startsWith "\\" then (token.drop 1).toString else token).toLower
  unless digest.length == 64 && digest.all isHexChar do
    throw (IO.userError s!"sha256sum returned malformed digest for {path}: {out.stdout.trimAscii}")
  return digest

/-- Compute the SHA-256 digest of `path` if it exists on disk, else `none`. -/
def sha256File? (path : FilePath) : IO (Option String) := do
  if ← path.pathExists then some <$> sha256File path else pure none

/-- Resolve an executable path directly or via `which` on `PATH`. -/
def resolveExecutablePath (cmd : String) : IO (Option FilePath) := do
  if cmd.isEmpty then return none
  let p := FilePath.mk cmd
  if ← p.pathExists then
    try return some (← IO.FS.realPath p) catch _ => return some p
  try
    let out ← IO.Process.output { cmd := "which", args := #[cmd] }
    if out.exitCode == 0 then
      let resolved := FilePath.mk out.stdout.trimAscii.toString
      if ← resolved.pathExists then
        try return some (← IO.FS.realPath resolved) catch _ => return some resolved
    return none
  catch _ => return none

/-- Git commit SHA and dirty status of `repoDir` (`../..` from `benchmarks/runner`). -/
def gitProvenance (repoDir : String := "../..") : IO (String × Option Bool) := do
  let commit ← try
      let out ← IO.Process.output { cmd := "git", args := #["-C", repoDir, "rev-parse", "HEAD"] }
      if out.exitCode == 0 then pure out.stdout.trimAscii.toString else pure "unavailable"
    catch _ => pure "unavailable"
  let dirty ← try
      let out ← IO.Process.output { cmd := "git", args := #["-C", repoDir, "status", "--porcelain"] }
      if out.exitCode == 0 then pure (some (!out.stdout.trimAscii.toString.isEmpty))
      else pure none
    catch _ => pure none
  return (commit, dirty)

/-- Hostname snapshot (`unavailable` if `hostname` cannot run). -/
def hostName : IO String :=
  firstLine "hostname" []

/-- Toolchain versions recorded in `k45-build.json`, including `gcc` and `g++`. -/
def k45Versions (ixccCmd : List String) : IO (Json × Option String) := do
  let ixccSha? ← match ← resolveExecutablePath (ixccCmd.headD "") with
    | some p => sha256File? p
    | none => pure none
  let v := Json.mkObj [
    ("lean", Json.str (← firstLine "lean" ["--version"])),
    ("leanc", Json.str (← firstLine "leanc" ["--version"])),
    ("clang", Json.str (← firstLine "clang" ["--version"])),
    ("clang++", Json.str (← firstLine "clang++" ["--version"])),
    ("gcc", Json.str (← firstLine "gcc" ["--version"])),
    ("g++", Json.str (← firstLine "g++" ["--version"])),
    ("objdump", Json.str (← firstLine "objdump" ["--version"])),
    ("ixcc", Json.str (" ".intercalate ixccCmd)),
    ("ixcc_sha256", match ixccSha? with | some h => Json.str h | none => Json.str "unavailable"),
    ("repository", Json.str (← firstLine "git" ["-C", "../..", "describe", "--always", "--dirty", "--abbrev=12"]))]
  return (v, ixccSha?)

/-- POSIX-safe single-argument quoting for `repro_cmd`. -/
def shellQuote (arg : String) : String :=
  let safe (c : Char) : Bool :=
    c.isAlphanum || c == '/' || c == '.' || c == '-' || c == '_' || c == ':' || c == '=' || c == ',' || c == '@'
  if !arg.isEmpty && arg.all safe then arg
  else "'" ++ arg.replace "'" "'\\''" ++ "'"

/-- Reconstruct an exact reproducible CLI command string from raw `main` arguments. -/
def reproCommand (rawArgs : List String) : String :=
  "lake exe bench-k45 " ++ " ".intercalate (rawArgs.map shellQuote)

end Runner
