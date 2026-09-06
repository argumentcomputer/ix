import Lean

/-!
Bounded paired anonymous FLT subject checks, orchestrated in Lean.
No builds, downloads, corpus rewriting, or full-environment checks occur here.
The Rust subject helper trusts dependencies. See README.md for scope/metrics.
-/

open Lean System

namespace Benchmarks.AnthropicFLT

def suiteDir : FilePath := "Benchmarks/Kernel/AnthropicFLT"

structure Case where
  id : String
  address : String
  category : String
  core : Bool
  fuel : Option Nat := none
  timeout_seconds : Option Nat := none
  deriving FromJson, ToJson, Inhabited

structure Defaults where
  fuel : Nat
  timeout_seconds : Nat
  memory_gib : Nat
  workers : Nat
  deriving FromJson, ToJson

structure Artifact where
  filename : String
  bytes : Nat
  sha256 : String
  deriving FromJson, ToJson

structure Manifest where
  schema : Nat
  artifact : Artifact
  defaults : Defaults
  cases : Array Case
  deriving FromJson

structure Resolution where
  requested : String
  primary : String
  targets : Nat
  deriving FromJson, ToJson, BEq, Inhabited

structure Group where
  primary : String
  targets : Nat
  fuel : Nat
  timeoutSeconds : Nat
  caseIds : Array String
  categories : Array String
  requested : Array String
  deriving ToJson, Inhabited

def isHex (s : String) : Bool :=
  s.length == 64 && s.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

def isId (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => c.isLower || c.isDigit || c == '-')

def need (value : Except String α) : IO α :=
  match value with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def validate (m : Manifest) : Except String Unit := do
  unless m.schema == 1 && isHex m.artifact.sha256 do throw "invalid manifest/artifact"
  unless m.defaults.workers == 1 do throw "suite requires one fresh worker"
  unless 0 < m.defaults.memory_gib && m.defaults.memory_gib ≤ 96 do
    throw "memory budget must be between 1 and 96 GiB"
  let mut ids := #[]
  let mut addresses := #[]
  for c in m.cases do
    unless isId c.id && !ids.contains c.id do throw "invalid or duplicate case ID"
    unless isHex c.address && !addresses.contains c.address do throw "invalid or duplicate address"
    unless #["tail", "depth", "fuel", "control"].contains c.category do throw "unknown category"
    let fuel := c.fuel.getD m.defaults.fuel
    let timeout := c.timeout_seconds.getD m.defaults.timeout_seconds
    unless 0 < fuel && fuel ≤ 40000000 do throw "invalid fuel budget"
    unless 0 < timeout && timeout ≤ 600 do throw "invalid time budget"
    ids := ids.push c.id
    addresses := addresses.push c.address

def normalize (cases : Array Case) (rows : Array Resolution) (d : Defaults) :
    Except String (Array Group) := do
  let mut groups : Array Group := #[]
  for c in cases do
    let some r := rows.find? (·.requested == c.address) | throw s!"unresolved target {c.address}"
    unless isHex r.primary && r.targets > 0 do throw "invalid resolver output"
    let fuel := c.fuel.getD d.fuel
    let timeout := c.timeout_seconds.getD d.timeout_seconds
    if let some i := groups.findIdx? (fun g => g.primary == r.primary && g.fuel == fuel) then
      let g := groups[i]!
      groups := groups.set! i { g with
        timeoutSeconds := max g.timeoutSeconds timeout
        caseIds := g.caseIds.push c.id
        categories := g.categories.push c.category
        requested := g.requested.push c.address }
    else
      groups := groups.push {
        primary := r.primary, targets := r.targets, fuel, timeoutSeconds := timeout
        caseIds := #[c.id], categories := #[c.category], requested := #[c.address] }
  return groups

def field (j : Json) (key : String) : Json := (j.getObjVal? key).toOption.getD .null
def str (j : Json) (key : String) : String := (j.getObjValAs? String key).toOption.getD ""

def classify (code : Nat) (report : Json) : String := Id.run do
  if code == 124 then return "timeout"
  if code == 137 then return "killed" -- Not automatically an OOM diagnosis.
  if code ≥ 128 then return "crash"
  if str report "scope" != "subject-only" then return "harness_error"
  if code == 0 && field report "passed" == toJson true then return "pass"
  if code != 1 || field report "passed" != toJson false then return "harness_error"
  return match str report "error" with
    | "recursive fuel exhausted" => "fuel_exhausted"
    | "max recursion depth exceeded" => "depth_exceeded"
    | _ => "kernel_error"

def compare (baseline adaptive : Json) (allowWorkChanges : Bool := false) : Json := Id.run do
  let a := str baseline "outcome"
  let b := str adaptive "outcome"
  let mut result := Json.mkObj [("baseline", toJson a), ("adaptive", toJson b)]
  let incomplete := #["timeout", "killed", "crash", "harness_error"]
  if incomplete.contains a || incomplete.contains b then
    return result.setObjVal! "comparison" (toJson "incomplete")
  let ar := field baseline "report"
  let br := field adaptive "report"
  let keys := #["passed", "error", "targets", "last_member_fuel", "last_member_def_eq_peak",
    "subst", "whnf", "def_eq", "intern", "nat_arith"]
  let mismatches := keys.filter (fun k => field ar k != field br k)
  result := result.setObjVal! "mismatched_fields" (toJson mismatches)
  let verdictChanged := a != b ||
    #["passed", "error", "targets"].any (fun k => field ar k != field br k)
  result := result.setObjVal! "comparison" (toJson
    (if verdictChanged then "mismatch"
     else if mismatches.isEmpty then "same_outcome_and_work"
     else if allowWorkChanges then "same_outcome_changed_work"
     else "mismatch"))
  if let (.ok baseTime, .ok adaptiveTime) :=
      (ar.getObjValAs? Float "check_secs", br.getObjValAs? Float "check_secs") then
    if baseTime > 0 then
      result := result.setObjVal! "adaptive_over_baseline_check_time" (toJson (adaptiveTime / baseTime))
  return result

def announce (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

def saveJson (path : FilePath) (j : Json) : IO Unit := do
  if ← path.pathExists then throw (IO.userError s!"refusing to overwrite {path}")
  IO.FS.writeFile path (j.pretty ++ "\n")

def lastJson (path : FilePath) : IO Json := do
  if !(← path.pathExists) then return .null
  let mut result := Json.null
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if let .ok (.obj obj) := Json.parse line then result := .obj obj
  return result

def checkedOutput (cmd : String) (args : Array String) : IO String := do
  let r ← IO.Process.output { cmd, args }
  unless r.exitCode == 0 do throw (IO.userError s!"{cmd}: {r.stderr}")
  return r.stdout.trimAscii.toString

def digest (path : FilePath) : IO String := do
  let output ← checkedOutput "sha256sum" #["--", path.toString]
  let hash := (output.splitOn " ").head!
  unless isHex hash do throw (IO.userError "invalid sha256sum output")
  return hash

def identities (paths : Array FilePath) : IO (Array String) :=
  paths.mapM fun p => checkedOutput "stat" #["-c", "%d:%i:%s:%y", "--", p.toString]

def timeFormat : String :=
  "{\"elapsed_seconds\":%e,\"user_seconds\":%U,\"system_seconds\":%S,\"peak_rss_kib\":%M,\"exit_code\":%x}"

def scopeArgs (unit user : String) (binary : FilePath) (args : Array String)
    (timing : FilePath) (seconds fuel memory : Nat) : Array String :=
  #["-n", "systemd-run", "--quiet", "--scope", s!"--unit={unit}",
    "-p", s!"MemoryMax={memory}G", "-p", "MemorySwapMax=0",
    "sudo", "-u", user, "/usr/bin/env", "-i", "PATH=/usr/bin:/bin", "LANG=C", "LC_ALL=C",
    "LEAN_NUM_THREADS=1", "RAYON_NUM_THREADS=1", s!"IX_MAX_REC_FUEL={fuel}",
    "/usr/bin/time", "-f", timeFormat, "-o", timing.toString,
    "/usr/bin/timeout", "--signal=TERM", "--kill-after=10s", toString seconds,
    binary.toString] ++ args

partial def pump (src dst : IO.FS.Handle) (echo : Bool) : IO Unit := do
  let line ← src.getLine
  unless line.isEmpty do
    dst.putStr line
    dst.flush
    if echo then
      (← IO.getStdout).putStr line
      (← IO.getStdout).flush
    pump src dst echo

structure Invocation where
  exitCode : Nat
  report : Json
  timing : Json
  wrapperSeconds : Float

def limited (binary : FilePath) (args : Array String) (out : FilePath)
    (name runId user : String) (seconds fuel memory : Nat) : IO Invocation := do
  let unit := s!"ix-flt-suite-{runId}-{name}"
  let timing := out / s!"{name}.time.json"
  let argv := scopeArgs unit user binary args timing seconds fuel memory
  saveJson (out / s!"{name}.command.json") (Json.mkObj [
    ("unit", toJson unit), ("argv", toJson (#["sudo"] ++ argv))])
  announce s!"START {name}: timeout={seconds}s fuel={fuel} memory={memory}GiB"
  let log ← IO.FS.Handle.mk (out / s!"{name}.log") .write
  let err ← IO.FS.Handle.mk (out / s!"{name}.stderr.log") .write
  let child ← IO.Process.spawn {
    cmd := "sudo", args := argv, stdin := .null, stdout := .piped, stderr := .piped, setsid := true }
  let stdoutTask ← IO.asTask (pump child.stdout log false) .dedicated
  let stderrTask ← IO.asTask (pump child.stderr err true) .dedicated
  let start ← IO.monoMsNow
  let mut lastNotice := start
  let code ← try
    let mut status : Option UInt32 := none
    while status.isNone do
      status ← child.tryWait
      if status.isNone then
        let now ← IO.monoMsNow
        if now - start > (seconds + 40) * 1000 then
          throw (IO.userError s!"scope wrapper exceeded timeout for {name}")
        if now - lastNotice ≥ 30000 then
          announce s!"WAIT {name}: {(now - start) / 1000}s (process cap {seconds}s)"
          lastNotice := now
        IO.sleep 250
    pure status.get!
  catch e =>
    let _ ← IO.Process.output { cmd := "sudo", args := #["-n", "systemctl", "kill",
      "--signal=KILL", "--kill-whom=all", unit] }
    child.kill
    throw e
  IO.ofExcept stdoutTask.get
  IO.ofExcept stderrTask.get
  let report ← lastJson (out / s!"{name}.log")
  let measured ← lastJson timing
  let finish ← IO.monoMsNow
  return {
    exitCode := code.toNat
    report := report
    timing := measured
    wrapperSeconds := (finish - start).toFloat / 1000
  }

structure Options where
  ixe : String := ""
  baseline : String := ""
  adaptive : String := ""
  output : String := ""
  manifest : String := (suiteDir / "cases.json").toString
  all : Bool := false
  cases : Array String := #[]
  rounds : Nat := 1
  selfTest : Bool := false
  allowWorkChanges : Bool := false

def parseArgs : List String → Options → Except String Options
  | [], opts => .ok opts
  | "--self-test" :: rest, opts => parseArgs rest { opts with selfTest := true }
  | "--allow-work-changes" :: rest, opts => parseArgs rest { opts with allowWorkChanges := true }
  | "--ixe" :: v :: rest, opts => parseArgs rest { opts with ixe := v }
  | "--baseline" :: v :: rest, opts => parseArgs rest { opts with baseline := v }
  | "--adaptive" :: v :: rest, opts => parseArgs rest { opts with adaptive := v }
  | "--output" :: v :: rest, opts => parseArgs rest { opts with output := v }
  | "--manifest" :: v :: rest, opts => parseArgs rest { opts with manifest := v }
  | "--case" :: v :: rest, opts => parseArgs rest { opts with cases := opts.cases.push v }
  | "--suite" :: v :: rest, opts =>
    if v == "all" || v == "core" then parseArgs rest { opts with all := v == "all" }
    else .error "--suite must be core or all"
  | "--rounds" :: v :: rest, opts => do
    let some n := v.toNat? | throw "invalid --rounds"
    unless 0 < n && n ≤ 10 do throw "--rounds must be 1..10"
    parseArgs rest { opts with rounds := n }
  | flag :: _, _ => .error s!"unknown or incomplete option {flag}"

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def selfTest (m : Manifest) : IO Unit := do
  need (validate m)
  ensure (m.cases.size == 132) "inventory size"
  let core := m.cases.filter (·.core)
  ensure (core.size == 15) "core size"
  for (category, count) in #[("tail", 5), ("depth", 4), ("fuel", 4), ("control", 2)] do
    ensure ((core.filter (·.category == category)).size == count) s!"core {category}"
  ensure ((m.cases.filter (·.category == "fuel")).size == 120) "extended fuel count"
  for c in #[{ m.cases[0]! with fuel := some 0 },
             { m.cases[0]! with timeout_seconds := some 601 },
             { m.cases[0]! with id := "../bad" }] do
    ensure ((validate { m with cases := #[c] }).toOption.isNone) "manifest guard"
  let a := String.ofList (List.replicate 64 'a')
  let b := String.ofList (List.replicate 64 'b')
  let cases : Array Case := #[
    { id := "one", address := a, category := "depth", core := true },
    { id := "two", address := b, category := "depth", core := true }]
  let resolutions : Array Resolution := #[
    { requested := a, primary := a, targets := 2 },
    { requested := b, primary := a, targets := 2 }]
  let groups ← need (normalize cases resolutions m.defaults)
  ensure (groups.size == 1 && groups[0]!.caseIds.size == 2) "block alias dedup"
  ensure ((normalize cases #[] m.defaults).toOption.isNone) "unresolved target must fail"
  let different := cases.set! 1 { cases[1]! with fuel := some 20000000 }
  ensure ((← need (normalize different resolutions m.defaults)).size == 2) "distinct budgets"
  let fail := Json.mkObj [("scope", toJson "subject-only"), ("passed", toJson false),
    ("error", toJson "recursive fuel exhausted")]
  ensure (classify 1 fail == "fuel_exhausted") "fuel classification"
  ensure (classify 0 fail == "harness_error") "inconsistent exit/report"
  ensure (classify 0 .null == "harness_error") "missing report"
  ensure (classify 124 .null == "timeout" && classify 137 .null == "killed") "resource outcomes"
  ensure (classify 1 (fail.setObjVal! "error" (toJson "max recursion depth exceeded")) ==
    "depth_exceeded") "depth outcome"
  let report := Json.mkObj [("passed", toJson true), ("last_member_fuel", toJson (7 : Nat)),
    ("check_secs", toJson (2 : Nat))]
  let row := Json.mkObj [("outcome", toJson "pass"), ("report", report)]
  ensure (str (compare row row) "comparison" == "same_outcome_and_work") "matching work"
  let changed := row.setObjVal! "report" (report.setObjVal! "last_member_fuel" (toJson (8 : Nat)))
  ensure (str (compare row changed) "comparison" == "mismatch") "fuel mismatch"
  ensure (str (compare row changed true) "comparison" == "same_outcome_changed_work")
    "explicit algorithmic comparison retains changed work"
  for changed in #[row.setObjVal! "outcome" (toJson "depth_exceeded"),
      row.setObjVal! "report" (report.setObjVal! "passed" (toJson false)),
      row.setObjVal! "report" (report.setObjVal! "targets" (toJson (2 : Nat))),
      row.setObjVal! "report" (report.setObjVal! "error" (toJson "new error"))] do
    ensure (str (compare row changed true) "comparison" == "mismatch")
      "algorithmic comparison must not permit outcome/target/error changes"
  let timedOut := Json.mkObj [("outcome", toJson "timeout")]
  let censored := compare timedOut row
  ensure (str censored "comparison" == "incomplete" &&
    field censored "adaptive_over_baseline_check_time" == .null) "no invented timeout speedup"
  let cmd := scopeArgs "test-unit" "test-user" "/binary" #[] "/time" 120 100 96
  for flag in #["MemoryMax=96G", "MemorySwapMax=0", "-i", "RAYON_NUM_THREADS=1",
                "IX_MAX_REC_FUEL=100", "--kill-after=10s", "--unit=test-unit"] do
    ensure (cmd.contains flag) s!"missing guard {flag}"
  announce "Lean suite self-tests passed."

def run (opts : Options) : IO UInt32 := do
  let manifestJson ← need (Json.parse (← IO.FS.readFile opts.manifest))
  let m : Manifest ← need (fromJson? manifestJson)
  need (validate m)
  if opts.selfTest then selfTest m; return 0
  unless [opts.ixe, opts.baseline, opts.adaptive, opts.output].all (!·.isEmpty) do
    throw (IO.userError "required: --ixe FILE --baseline BIN --adaptive BIN --output NEW_DIR")
  for id in opts.cases do
    ensure (m.cases.any (·.id == id)) s!"unknown case {id}"
  let selected := m.cases.filter fun c =>
    if opts.cases.isEmpty then opts.all || c.core else opts.cases.contains c.id
  let paths ← #[opts.ixe, opts.baseline, opts.adaptive].mapM (IO.FS.realPath ∘ FilePath.mk)
  let ixe := paths[0]!
  let binaries := paths.extract 1 3
  let initial ← identities paths
  ensure ((← ixe.metadata).byteSize.toNat == m.artifact.bytes) "artifact size mismatch"
  let out : FilePath := opts.output
  ensure (!(← out.pathExists)) s!"refusing to overwrite directory {out}"
  IO.FS.createDir out
  let out ← IO.FS.realPath out
  announce "Fingerprinting input and executables before timed checks..."
  let hashes ← paths.mapM digest
  ensure (hashes[0]! == m.artifact.sha256) "artifact SHA-256 mismatch"
  ensure (hashes[1]! != hashes[2]!) "baseline/adaptive binaries are identical"
  ensure ((← identities paths) == initial) "input changed during fingerprinting"
  let runId := s!"{← IO.Process.getPID}-{← IO.monoMsNow}"
  let user ← checkedOutput "id" #["-un"]
  saveJson (out / "run.json") (Json.mkObj [
    ("schema", toJson (1 : Nat)), ("run_id", toJson runId), ("manifest", manifestJson),
    ("selected_case_ids", toJson (selected.map (·.id))),
    ("paths", toJson (paths.map (·.toString))), ("sha256", toJson hashes),
    ("file_identity", toJson initial), ("rounds", toJson opts.rounds),
    ("allow_work_changes", toJson opts.allowWorkChanges),
    ("host", toJson (← checkedOutput "uname" #["-a"])),
    ("driver_sha256", toJson (← digest (suiteDir / "RunSuite.lean"))),
    ("started_utc", toJson (← checkedOutput "date" #["-u", "+%Y-%m-%dT%H:%M:%SZ"])),
    ("scope", toJson "subject-only; dependencies trusted"), ("workers", toJson (1 : Nat))])
  -- Explicit prototype source snapshot; no unrelated worktree files.
  for relative in #["crates/kernel/src/env.rs", "crates/kernel/src/env/scratch.rs",
    "crates/kernel/src/subst.rs", "crates/kernel/src/subst/scratch_tests.rs",
    "crates/kernel/src/infer.rs", "crates/kernel/src/infer/binders.rs",
    "crates/kernel/src/infer/binders/tests.rs",
    "crates/kernel/src/def_eq.rs", "crates/kernel/src/tc.rs",
    "crates/kernel/src/def_eq/projection_tests.rs",
    "crates/ffi/examples/check_anon_subject.rs", "Cargo.lock", "rust-toolchain.toml",
    ".cargo/config.toml", "Benchmarks/Kernel/AnthropicFLT/RunSuite.lean"] do
    let src : FilePath := relative
    if ← src.pathExists then
      let dst := out / "source" / relative
      if let some parent := dst.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile dst (← IO.FS.readBinFile src)
  let requested := m.cases.map (·.address)
  let mut resolutions : Array Resolution := #[]
  for (binary, variant) in binaries.zip #["baseline", "adaptive"] do
    let result ← limited binary (#["--resolve", ixe.toString] ++ requested) out
      s!"resolve-{variant}" runId user 120 m.defaults.fuel m.defaults.memory_gib
    ensure (result.exitCode == 0 && str result.report "scope" == "index-only")
      s!"{variant} resolution failed; see its logs"
    let rows : Array Resolution ← need (result.report.getObjValAs? _ "resolutions")
    ensure (rows.map (·.requested) == requested) "incomplete/reordered resolution"
    if variant == "baseline" then resolutions := rows
    else ensure (rows == resolutions) "variants disagree on work-item resolution"
  let groups ← need (normalize selected resolutions m.defaults)
  saveJson (out / "resolved.json") (Json.mkObj [
    ("all_targets", toJson resolutions), ("selected_work", toJson groups)])
  announce s!"Resolved {requested.size} targets; running {groups.size} work items × 2 variants × {opts.rounds} rounds"
  let results ← IO.FS.Handle.mk (out / "results.jsonl") .write
  let mut pairs : Array Json := #[]
  for round in [:opts.rounds] do
    for i in [:groups.size] do
      let g := groups[i]!
      let order := if (round + i) % 2 == 0 then #[1, 0] else #[0, 1]
      let mut rows := #[Json.null, Json.null]
      for v in order do
        ensure ((← identities paths) == initial) "input/binary changed during suite"
        let variant := if v == 0 then "baseline" else "adaptive"
        let name := s!"r{round + 1}-{g.caseIds[0]!}-{variant}"
        let r ← limited binaries[v]! #[ixe.toString, g.primary] out name runId user
          g.timeoutSeconds g.fuel m.defaults.memory_gib
        ensure ((← identities paths) == initial) "input/binary changed during check"
        let mut outcome := classify r.exitCode r.report
        if str r.report "scope" == "subject-only" then
          if str r.report "primary" != g.primary || field r.report "targets" != toJson g.targets ||
              field r.report "fuel_cap_per_member" != toJson g.fuel then
            outcome := "harness_error"
        let row := Json.mkObj [
          ("work", toJson g), ("variant", toJson variant), ("round", toJson (round + 1)),
          ("exit_code", toJson r.exitCode), ("outcome", toJson outcome),
          ("report", r.report), ("time", r.timing), ("wrapper_seconds", toJson r.wrapperSeconds)]
        results.putStrLn row.compress
        results.flush
        rows := rows.set! v row
        announce s!"DONE {name}: {outcome} check={(field r.report "check_secs").compress}s peak_rss={(field r.timing "peak_rss_kib").compress}KiB"
        ensure (outcome != "harness_error") s!"harness error in {name}; stopping"
      let pair := (compare rows[0]! rows[1]! opts.allowWorkChanges).setObjVal! "case_ids" (toJson g.caseIds)
        |>.setObjVal! "round" (toJson (round + 1))
      pairs := pairs.push pair
      announce s!"PAIR {pair.compress}"
  saveJson (out / "summary.json") (Json.mkObj [
    ("complete", toJson true), ("pairs", toJson pairs),
    ("warning", toJson "Completed harness is not full-corpus verification; timeouts remain unresolved.")])
  return if pairs.any (fun p => str p "comparison" == "mismatch") then 1 else 0

end Benchmarks.AnthropicFLT

def main (args : List String) : IO UInt32 := do
  try
    let opts ← Benchmarks.AnthropicFLT.need (Benchmarks.AnthropicFLT.parseArgs args {})
    Benchmarks.AnthropicFLT.run opts
  catch e =>
    IO.eprintln s!"FLT suite: {e}"
    return 2
