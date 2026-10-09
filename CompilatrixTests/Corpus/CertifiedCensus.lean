import CompilatrixTests.Corpus.Manifest

/-! Optional, non-gating census of an external certified checker.

This tool invokes a separately built and SHA-256-pinned `kernel-check-ixe`.
It never imports the kernel or supplies evidence to compiler admission. Every
run uses a fresh directory and a timeout; incomplete runs retain partial rows
without reporting them as a completed environment check. -/

namespace CompilatrixTests.Corpus.CertifiedCensus

open Lean System Compilatrix.Tools.Check

structure Counts where
  accepted : Nat := 0
  rejected : Nat := 0
  declined : Nat := 0
  blocked : Nat := 0
  deriving BEq, Inhabited

def Counts.total (c : Counts) : Nat :=
  c.accepted + c.rejected + c.declined + c.blocked

def Counts.json (c : Counts) : Json := Json.mkObj [
  ("accepted", toJson c.accepted), ("rejected", toJson c.rejected),
  ("declined", toJson c.declined), ("blocked", toJson c.blocked)]

/-- A completed record stream has a final newline, unique addresses and
known outcomes. An empty or truncated stream cannot establish acceptance. -/
def readCounts (text : String) : Except String Counts := do
  unless text.endsWith "\n" do throw "missing final newline in checker rows"
  let mut counts : Counts := {}
  let mut seen : Std.HashSet String := {}
  for line in (text.splitOn "\n").dropLast do
    if line.isEmpty then throw "empty checker record"
    let row ← Json.parse line
    let address ← row.getObjValAs? String "address"
    unless isHex 64 address do throw "invalid record address"
    if seen.contains address then throw "duplicate record address"
    seen := seen.insert address
    let kind ← row.getObjValAs? String "kind"
    if kind.isEmpty then throw "missing record kind"
    let _ ← row.getObjValAs? String "reason"
    let _ ← row.getObjValAs? Nat "micros"
    match ← row.getObjValAs? String "outcome" with
    | "accept" => counts := { counts with accepted := counts.accepted + 1 }
    | "reject" => counts := { counts with rejected := counts.rejected + 1 }
    | "decline" => counts := { counts with declined := counts.declined + 1 }
    | "blocked" => counts := { counts with blocked := counts.blocked + 1 }
    | other => throw s!"unknown checker outcome {other}"
  if counts.total == 0 then throw "checker wrote no records"
  return counts

def completed (exitCode : UInt32) (stderr : String) (rows : String) : Except String Counts := do
  unless exitCode == 0 do throw s!"checker exited {exitCode}"
  let done := (stderr.splitOn "\n").filter (·.startsWith "check-ixe: done in ")
  unless done.length == 1 do throw "missing or repeated checker completion record"
  readCounts rows

structure Input where
  path : FilePath
  /-- A manifest pin, if this is a frozen fixture. -/
  expectedSha256 : Option String := none
  deriving Inhabited

structure Options where
  checker : FilePath
  revision : String
  binarySha256 : String
  out : FilePath
  timeoutSeconds : Nat := 60
  recursors : String := "as-frozen"
  manifests : List FilePath := []
  inputs : List FilePath := []

def options (args : List String) : Except String Options := do
  let kvs ← parseArgs ["--checker", "--revision", "--sha256", "--out", "--timeout",
    "--recursors", "--manifest", "--input"] args ["--manifest", "--input"]
  let get (key : String) : Except String String :=
    match optional kvs key with
    | some value => pure value
    | none => throw s!"required option {key}"
  let checker ← get "--checker"
  let revision ← get "--revision"
  let binarySha256 ← get "--sha256"
  let out ← get "--out"
  unless isHex 40 revision do throw "--revision must be a complete Git revision"
  unless isHex 64 binarySha256 do throw "--sha256 must be a complete SHA-256"
  let some seconds := (option kvs "--timeout" "60").toNat?
    | throw "--timeout must be a positive number of seconds"
  unless 0 < seconds && seconds ≤ 3600 do throw "--timeout must be between 1 and 3600 seconds"
  let recursors := option kvs "--recursors" "as-frozen"
  unless ["as-frozen", "explicitly-seeded", "unknown"].contains recursors do
    throw "--recursors must be as-frozen, explicitly-seeded, or unknown"
  let manifests := kvs.filterMap fun (k, v) => if k == "--manifest" then some (FilePath.mk v) else none
  let inputs := kvs.filterMap fun (k, v) => if k == "--input" then some (FilePath.mk v) else none
  return {
    checker, revision, binarySha256, out, timeoutSeconds := seconds, recursors
    manifests := if manifests.isEmpty && inputs.isEmpty then families else manifests
    inputs }

def inputs (cfg : Options) : IO (Array Input) := do
  let mut result : Array Input := #[]
  for path in cfg.manifests do
    let m ← Family.read path
    for f in m.fixtures do
      result := result.push {
        path := FilePath.mk m.directory / f.closure.path
        expectedSha256 := some f.closure.sha256 }
  for path in cfg.inputs do result := result.push { path }
  need (!result.isEmpty) "no census inputs"
  return result

def one (cfg : Options) (index : Nat) (input : Input) : IO (Json × Bool) := do
  let digest ← sha256 input.path
  if let some expected := input.expectedSha256 then
    need (digest == expected) s!"{input.path}: closure SHA-256 differs from manifest"
  let stem := cfg.out / toString index
  let rows := stem.addExtension "jsonl"
  let args := #["--verbose", "--kill-after=5s", s!"{cfg.timeoutSeconds}s", cfg.checker.toString,
    "--load", "stream", "--jobs", "1", input.path.toString, rows.toString]
  let start ← IO.monoMsNow
  let result ← IO.Process.output { cmd := "timeout", args, env := #[("LC_ALL", some "C")] }
  let elapsed := (← IO.monoMsNow) - start
  IO.FS.writeFile (stem.addExtension "stdout") result.stdout
  IO.FS.writeFile (stem.addExtension "stderr") result.stderr
  let text ← if ← rows.pathExists then IO.FS.readFile rows else pure ""
  let parsed := completed result.exitCode result.stderr text
  let timeout := result.exitCode == 124 || (result.exitCode == 137 &&
    result.stderr.contains "timeout: sending signal KILL to command")
  let (status, diagnostic, counts, complete) := match parsed with
    | .ok counts => ("completed", "", counts.json, true)
    | .error why => (if timeout then "timed-out" else "failed", why,
        match readCounts text with | .ok c => c.json | .error _ => Json.null, false)
  IO.println s!"{input.path}: {status} ({elapsed} ms)"
  return (Json.mkObj [
    ("input", toJson input.path.toString), ("input_sha256", toJson digest),
    ("manifest_pinned", toJson input.expectedSha256.isSome),
    ("status", toJson status), ("complete", toJson complete),
    ("records", counts), ("diagnostic", toJson diagnostic),
    ("exit_code", toJson result.exitCode.toNat), ("elapsed_ms", toJson elapsed),
    ("rows", toJson rows.toString), ("command", toJson (#["timeout"] ++ args))], complete)

/-- A diagnostic census returns nonzero only for operational failures and
timeouts; a completed rejection, decline or dependency block is report data. -/
def run (cfg : Options) : IO Unit := do
  need ((← sha256 cfg.checker) == cfg.binarySha256)
    "checker SHA-256 differs from the requested pin"
  let work ← inputs cfg
  need (!(← cfg.out.pathExists)) s!"output directory already exists: {cfg.out}"
  if let some parent := cfg.out.parent then IO.FS.createDirAll parent
  IO.FS.createDir cfg.out
  let started := (← Compilatrix.Tools.Check.run "date" #["-u", "+%Y-%m-%dT%H:%M:%SZ"]).trimAscii.toString
  let mut reports := #[]
  let mut complete := 0
  for i in [:work.size] do
    let (report, ok) ← one cfg i work[i]!
    reports := reports.push report
    if ok then complete := complete + 1
    -- Keep finished evidence even if a later invocation fails.
    IO.FS.writeFile (cfg.out / "report.json") ((Json.mkObj [
      ("format", toJson "compilatrix/certified-census/1"), ("gating", toJson false),
      ("started_utc", toJson started), ("checker", toJson cfg.checker.toString),
      ("checker_revision", toJson cfg.revision),
      ("revision_source", toJson "caller-supplied; executable SHA-256 verified"),
      ("checker_sha256", toJson cfg.binarySha256), ("recursors", toJson cfg.recursors),
      ("recursor_source", toJson "caller-supplied; census does not recompile inputs"),
      ("timeout_seconds", toJson cfg.timeoutSeconds),
      ("planned_inputs", toJson work.size), ("completed_inputs", toJson complete),
      ("runs", Json.arr reports)]).pretty ++ "\n")
  need (complete == work.size) s!"census incomplete: {work.size - complete} timed-out or failed inputs; see {cfg.out}"

def selfTest : IO Unit := do
  let row (address outcome : String) := (Json.mkObj [
    ("address", toJson address), ("kind", toJson "definition"),
    ("outcome", toJson outcome), ("reason", toJson ""), ("micros", toJson (0 : Nat))]).compress ++ "\n"
  let a := String.ofList (List.replicate 64 'a')
  let b := String.ofList (List.replicate 64 'b')
  let good := row a "accept" ++ row b "decline"
  let done := "check-ixe: done in 1 ms; [(accept, 1), (decline, 1)]\n"
  let c ← checked (completed 0 done good)
  need (c == { accepted := 1, declined := 1 }) "valid mixed census"
  let rejected := fun (r : Except String Counts) => match r with | .error _ => true | .ok _ => false
  for bad in ["", "\n", (row a "accept").trimAscii.toString,
      row a "accept" ++ row a "accept", row a "unexpected", row "bad" "accept"] do
    need (rejected (readCounts bad)) "malformed census was accepted"
  need (rejected (completed 124 done good)) "timeout was accepted"
  need (rejected (completed 1 done good)) "nonzero checker exit was accepted"
  need (rejected (completed 0 "" good)) "missing completion was accepted"
  need (rejected (completed 0 (done ++ done) good)) "duplicate completion was accepted"
  IO.println "certified-census: 11 protocol checks passed"

def main (args : List String) : IO UInt32 := cli "certified-census" do
  if args == ["--self-test"] then selfTest
  else run (← checked (options args))

end CompilatrixTests.Corpus.CertifiedCensus
