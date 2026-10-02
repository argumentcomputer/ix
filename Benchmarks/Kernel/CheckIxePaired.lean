import Benchmarks.Kernel.CheckIxeRows

/-! # Paired environment-check runs (untrusted tooling)

Alternate native environment-check runs and compare coverage separately from
timing. The environment check measures supported-profile coverage, not a
`checkEnv` verdict; run under a memory cap and without concurrent builds or
benchmark processes.

`kernel-check-ixe --compare <baseline.jsonl> <current.jsonl> [--output <f>]
[--top N]` compares two row files, including partial runs: per-side outcome
counts, outcome transitions, rows only on one side, lost and gained
acceptances, changed diagnostics, and the row timings of the acceptances the
two share. It exits 1 when the current rows lose a baseline acceptance.

`kernel-check-ixe --paired --binary <b> --baseline-binary <b>
--baseline-revision <rev> --input <ixe> --output-dir <new dir> [--revision
<rev>] [--baseline-source-sha256 <h>] [--source <dir>] [--limit N] [--fuel N]
[--runs N] [--warmups N] [--timeout s] [--time-binary <GNU time>] [--top N]`
alternates fresh processes of the two binaries over the same `.ixe` (one
warmup and three measured samples each by default, the order swapped every
pair), with the `CHECK_IXE_*` variables removed from their environment, each
under GNU time (peak RSS, user and system time) in its own session with a
timeout, and keeps every sample's rows and log in the output directory, with
`summary.json` rewritten after each sample: the input, source, toolchain,
runner and binary fingerprints, the machine, every sample, the comparison of
every measured pair, and the wall-time medians. A side whose outcomes or
diagnostics change between its samples is an error; so is a binary, input or
source that changes during the run. It exits 1 when a pair loses a baseline
acceptance, 2 on an error.

The comparison's JSON is `Benchmarks.Kernel.CheckIxeRows`'s. The runner's own
fingerprint (`runner_sha256`) is that of the executable running it, and
`--fuel`, which the current driver does not take, is passed only when
given. -/

namespace Benchmarks.Kernel.CheckIxePaired

open Benchmarks.Kernel.CheckIxeRows

def outcomesAllowed : List String := ["accept", "decline", "reject", "blocked"]

/-- An insertion-ordered map from address to row. -/
structure Rows where
  order : Array String := #[]
  byAddress : Std.HashMap String Value := {}

def Rows.get (r : Rows) (a : String) : Value := r.byAddress.getD a .null

def Rows.contains (r : Rows) (a : String) : Bool := r.byAddress.contains a

/-- The validated rows of a row file: a nonempty address, unique; a known
outcome; a string reason; names a list of strings; `micros` (and
`readMicros`, if present) a nonnegative integer. -/
def readRows (path : String) : IO Rows := do
  let text ← IO.FS.readFile path
  let mut rows : Rows := {}
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    if line.trimAscii.toString.isEmpty then continue
    let err (msg : String) : IO Unit := throw <| IO.userError s!"{path}:{n}: {msg}"
    let row ← match parse line with
      | .ok row => pure row
      | .error e => throw <| IO.userError s!"{path}:{n}: {e}"
    let some address := (row.get? "address").bind Value.str? | err "missing address"; continue
    if address.isEmpty then err "missing address"
    if rows.contains address then err s!"duplicate address {address}"
    let some outcome := (row.get? "outcome").bind Value.str? | err "missing outcome"; continue
    unless outcomesAllowed.contains outcome do err s!"unknown outcome '{outcome}'"
    unless ((row.get? "reason").bind Value.str?).isSome do err "reason must be a string"
    let namesOk := match row.get? "names" with
      | some (.arr xs) => xs.all (·.str?.isSome)
      | _ => false
    unless namesOk do err "names must be an array of strings"
    for (key, required) in [("micros", true), ("readMicros", false)] do
      match row.get? key with
      | some (.int v) => if v < 0 then err s!"invalid {key}"
      | none => if required then err s!"missing {key}"
      | _ => err s!"invalid {key}"
    rows := { order := rows.order.push address, byAddress := rows.byAddress.insert address row }
  if rows.order.isEmpty then throw <| IO.userError s!"{path}: no check rows"
  return rows

def sortedCounts (keys : Array String) : Value :=
  let c := keys.foldl (fun c k => c.add k) ({} : Counter)
  .obj ((c.items.qsort (fun a b => a.1 < b.1)).map fun (k, n) => (k, .int n))

def rowSummary (rows : Rows) : Array (String × Value) :=
  #[("records", .int rows.order.size),
    ("outcomes", sortedCounts (rows.order.map fun a => field (rows.get a) "outcome"))]

def outcome (rows : Rows) (a : String) : String := field (rows.get a) "outcome"

def reason (rows : Rows) (a : String) : String := field (rows.get a) "reason"

def namesOf (row : Value) : Value := (row.get? "names").getD (.arr #[])

/-- The comparison of two row sets (the former `compare`). -/
def compare (before after : Rows) (top : Nat) : Value := Id.run do
  let sorted (xs : Array String) := xs.qsort (· < ·)
  let shared := sorted (before.order.filter after.contains)
  let commonAccepts := shared.filter fun a => outcome before a == "accept" && outcome after a == "accept"
  let side (rows : Rows) (a : String) : Value :=
    if rows.contains a then
      .obj #[("outcome", .str (outcome rows a)), ("reason", .str (reason rows a))]
    else .null
  let change (a : String) : Value :=
    let row := if after.contains a then after.get a else before.get a
    .obj #[("address", .str a), ("names", namesOf row), ("before", side before a), ("after", side after a)]
  let lost := sorted (before.order.filter fun a =>
    outcome before a == "accept" && (!after.contains a || outcome after a != "accept"))
  let gained := sorted (after.order.filter fun a =>
    outcome after a == "accept" && (!before.contains a || outcome before a != "accept"))
  let sumMicros (rows : Rows) := commonAccepts.foldl (fun s a => s + micros (rows.get a)) (0 : Int)
  let beforeMicros := sumMicros before
  let afterMicros := sumMicros after
  let slowest := (commonAccepts.qsort fun a b =>
    micros (after.get a) > micros (after.get b) ||
      (micros (after.get a) == micros (after.get b) && a < b)).extract 0 top
  let transitions := shared.map fun a => s!"{outcome before a} -> {outcome after a}"
  return .obj #[
    ("baseline", .obj (rowSummary before)), ("current", .obj (rowSummary after)),
    ("transitions", sortedCounts transitions),
    ("baseline_only", .arr ((sorted (before.order.filter (!after.contains ·))).map change)),
    ("current_only", .arr ((sorted (after.order.filter (!before.contains ·))).map change)),
    ("lost_accepts", .arr (lost.map change)),
    ("gained_accepts", .arr (gained.map change)),
    ("changed_diagnostics", .arr ((shared.filter fun a =>
      outcome before a == outcome after a && reason before a != reason after a).map change)),
    ("common_accepted_records", .int commonAccepts.size),
    ("common_accepted_row_micros", .obj #[("baseline", .int beforeMicros), ("current", .int afterMicros)]),
    ("common_accepted_row_ratio",
      if beforeMicros == 0 then .null else .float (Float.ofInt afterMicros / Float.ofInt beforeMicros)),
    ("timing_scope",
      .str "row diagnostics; family/recursor rows duplicate admission timings; not wall time"),
    ("slowest_common_accepts", .arr (slowest.map fun a => .obj #[
      ("address", .str a), ("names", namesOf (after.get a)),
      ("baseline_micros", .int (micros (before.get a))),
      ("current_micros", .int (micros (after.get a)))]))]

def lostAny (result : Value) : Bool :=
  match result.get? "lost_accepts" with
  | some (.arr xs) => !xs.isEmpty
  | _ => false

/-- Write JSON (sorted keys, indent 2) atomically. -/
def writeJson (path : String) (v : Value) : IO Unit := do
  let tmp := path ++ ".tmp"
  IO.FS.writeFile tmp (v.dumps 2 true ++ "\n")
  IO.FS.rename tmp path

def sha256 (path : System.FilePath) : IO String := do
  let out ← IO.Process.output { cmd := "sha256sum", args := #["--", path.toString] }
  unless out.exitCode == 0 do throw <| IO.userError s!"sha256sum {path}: {out.stderr}"
  return (out.stdout.splitOn " ").headD ""

/-- Python's `Path` order: component by component. -/
def pathLt (a b : String) : Bool :=
  let rec go : List String → List String → Bool
    | [], [] => false
    | [], _ => true
    | _, [] => false
    | x :: xs, y :: ys => if x == y then go xs ys else x < y
  go (a.splitOn "/") (b.splitOn "/")

def leanFiles (root : System.FilePath) (dir : String) : IO (Array String) := do
  let d := root / dir
  unless ← d.isDir do return #[]
  let mut out := #[]
  for p in ← d.walkDir do
    if (p.fileName.getD "").endsWith ".lean" && !(← p.isDir) then out := out.push p.toString
  return out

/-- Hash local Lean sources and build pins; this does not verify a build. -/
def sourceFingerprint (root : System.FilePath) : IO String := do
  let mut paths : Array String :=
    #["Ix.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain"].map
      fun (n : String) => (root / n).toString
  for dir in ["Ix", "Benchmarks/Kernel"] do paths := paths ++ (← leanFiles root dir)
  let prefix_ := root.toString ++ "/"
  IO.FS.withTempFile fun h tmp => do
    for p in paths.qsort pathLt do
      h.write ((p.drop prefix_.length).toString.toUTF8 ++ ⟨#[0]⟩)
      h.write ((← IO.FS.readBinFile p) ++ ⟨#[0]⟩)
    h.flush
    sha256 tmp

/-- `shutil.which`. -/
def which (cmd : String) : IO (Option String) := do
  for dir in ((← IO.getEnv "PATH").getD "").splitOn ":" do
    let p : System.FilePath := (if dir.isEmpty then "." else dir) / cmd
    if (← p.pathExists) && !(← p.isDir) then return some p.toString
  return none

/-- Python's `Path.resolve()`, for a path that may not exist yet. -/
def resolve (p : String) : IO String := do
  if ← System.FilePath.pathExists p then return (← IO.FS.realPath p).toString
  let cwd ← IO.currentDir
  let abs := if p.startsWith "/" then p else cwd.toString ++ "/" ++ p
  return pathStr abs

/-- The variables starting with `CHECK_IXE_`, from this process's environment. -/
def checkIxeVars : IO (Array String) := do
  let raw ← try IO.FS.readBinFile "/proc/self/environ" catch _ => pure ByteArray.empty
  let entries := (String.fromUTF8? raw |>.getD "").splitOn "\x00"
  return (entries.filterMap fun e =>
    let name := (e.splitOn "=").headD ""
    if name.startsWith "CHECK_IXE_" then some name else none).toArray

def uname : IO Value := do
  let field (flag : String) : IO String := do
    let out ← IO.Process.output { cmd := "uname", args := #[flag] }
    return out.stdout.trimAscii.toString
  let processor ← field "-p"
  return .obj #[("system", .str (← field "-s")), ("node", .str (← field "-n")),
    ("release", .str (← field "-r")), ("version", .str (← field "-v")),
    ("machine", .str (← field "-m")),
    ("processor", .str (if processor == "unknown" then "" else processor))]

partial def pump (src : IO.FS.Handle) (dst : IO.FS.Handle) : IO Unit := do
  let chunk ← src.read 65536
  unless chunk.isEmpty do
    dst.write chunk
    dst.flush
    pump src dst

structure Options where
  binary : String := ""
  baselineBinary : String := ""
  input : String := ""
  outputDir : String := ""
  source : Option String := none
  revision : Option String := none
  baselineRevision : String := ""
  baselineSourceSha : Option String := none
  limit : Nat := 4300
  fuel : Option Nat := none
  runs : Nat := 3
  warmups : Nat := 1
  timeout : Float := 180
  /-- Whether `--timeout` was given (the default is recorded as the integer
  180, a given value as a float, as Python's `argparse` records them). -/
  timeoutGiven : Bool := false
  timeBinary : Option String := none
  top : Nat := 15

/-- A float option (`--timeout`): digits with at most one point. -/
def parseFloat (s : String) : Option Float := do
  let parts := s.splitOn "."
  match parts with
  | [w] => return (← w.toNat?).toFloat
  | [w, f] =>
    let wn ← if w.isEmpty then some 0 else w.toNat?
    let fn ← f.toNat?
    return wn.toFloat + fn.toFloat / (10.0 ^ f.length.toFloat)
  | _ => none

/-- One sample: `binary input rows limit [fuel]` under GNU time, in its own
session, its output in `<stem>.log`. -/
def sample (binary timer : String) (o : Options) (stem : String) : IO (Array (String × Value)) := do
  let rowsPath := stem ++ ".jsonl"
  let logPath := stem ++ ".log"
  let metricsPath := stem ++ ".resources"
  let args := #["-q", "-f", "%M %U %S", "-o", metricsPath, binary, o.input, rowsPath, toString o.limit] ++
    (o.fuel.map (#[toString ·])).getD #[]
  -- these diagnostic modes alter the checked population or timing behaviour
  let env := (← checkIxeVars).map fun v => (v, (none : Option String))
  let started ← IO.monoNanosNow
  let log ← IO.FS.Handle.mk logPath .write
  let spawnArgs : IO.Process.SpawnArgs := {
    cmd := timer, args := args, env := env, setsid := true
    stdin := .null, stdout := .piped, stderr := .piped }
  let child ← IO.Process.spawn spawnArgs
  let outTask ← IO.asTask (pump child.stdout log) .dedicated
  let errTask ← IO.asTask (pump child.stderr log) .dedicated
  let deadline := started + (o.timeout * 1e9).toUInt64.toNat
  let mut status : Option UInt32 := none
  let mut timedOut := false
  while status.isNone do
    status ← child.tryWait
    if status.isNone then
      if (← IO.monoNanosNow) > deadline then
        let _ ← IO.Process.output { cmd := "kill", args := #["-KILL", "--", s!"-{child.pid}"] }
        status := some (← child.wait)
        timedOut := true
      else IO.sleep 20
  let _ ← IO.wait outTask
  let _ ← IO.wait errTask
  let wall := (← IO.monoNanosNow) - started
  let mut result : Array (String × Value) := #[("rows", .str rowsPath), ("log", .str logPath),
    ("exit_code", .int (status.getD 0).toNat), ("timed_out", .bool timedOut), ("wall_ns", .int wall)]
  let metrics ← try some <$> IO.FS.readFile metricsPath catch _ => pure none
  match metrics.map (fun m => (m.splitOn " ").filter (· != "") |>.map (·.trimAscii.toString)) with
  | some [rss, user, system] =>
    match rss.toNat?, reprDecimal user, reprDecimal system with
    | some r, some u, some s =>
      result := result ++ #[("peak_rss_kib", .int r), ("user_seconds", .num u), ("system_seconds", .num s)]
    | _, _, _ => result := result.push ("resources_error", .str s!"unreadable resources {metrics}")
  | _ => result := result.push ("resources_error", .str s!"no resources in {metricsPath}")
  try
    let rows ← readRows rowsPath
    result := result ++ rowSummary rows ++ #[("rows_sha256", .str (← sha256 rowsPath))]
  catch e => result := result.push ("rows_error", .str (toString e))
  return result

/-- Python's `repr` of a `{str: int}` dict, for the progress lines. -/
def dictRepr (v : Value) : String :=
  match v with
  | .obj kvs => "{" ++ ", ".intercalate (kvs.toList.map fun (k, x) =>
      s!"'{k}': {match x with | .int n => toString n | _ => "?"}") ++ "}"
  | _ => "{}"

def median (xs : Array Int) : Value :=
  let s := xs.qsort (· < ·)
  let n := s.size
  if n % 2 == 1 then .int s[n / 2]!
  else .float (Float.ofInt (s[n / 2 - 1]! + s[n / 2]!) / 2)

def toFloat : Value → Float
  | .int n => Float.ofInt n
  | .float f => f
  | _ => 0

def run (o : Options) : IO UInt32 := do
  let outputDir := o.outputDir
  if ← System.FilePath.pathExists outputDir then
    throw <| IO.userError s!"[Errno 17] File exists: '{outputDir}'"
  IO.FS.createDirAll outputDir
  let summaryPath := outputDir ++ "/summary.json"
  let binaries := #[("baseline", ← resolve o.baselineBinary), ("current", ← resolve o.binary)]
  let timer ← match o.timeBinary with
    | some t => pure t
    | none => match ← which "time" with
      | some t => pure t
      | none => throw <| IO.userError "GNU time is required (or pass --time-binary)"
  let source := o.source.getD "."
  let binaryShas ← binaries.mapM fun (_, p) => sha256 p
  let inputSha ← sha256 o.input
  let sourceSha ← sourceFingerprint source
  let optStr (s : Option String) : Value := (s.map Value.str).getD .null
  let header : Array (String × Value) := #[("schema", .int 1),
    ("scope", .str "environment-check supported-profile coverage; not a certified whole-environment verdict"),
    ("input", .obj #[("path", .str o.input), ("sha256", .str inputSha)]),
    ("source_sha256", .str sourceSha),
    ("source_note", .str "local source at invocation; caller must build the binary from this source"),
    ("baseline_source_sha256", optStr o.baselineSourceSha),
    ("toolchain", .str (← IO.FS.readFile (source ++ "/lean-toolchain")).trimAscii.toString),
    ("runner_sha256", .str (← sha256 (← IO.appPath))),
    ("machine", ← uname),
    ("limit", .int o.limit), ("fuel", (o.fuel.map (Value.int ·)).getD .null), ("runs", .int o.runs),
    ("warmups", .int o.warmups), ("timeout_seconds", if o.timeoutGiven then .float o.timeout else .int 180),
    ("binaries", .obj ((binaries.zip binaryShas).map fun ((side, path), sha) =>
      (side, .obj #[("path", .str path), ("sha256", .str sha),
        ("revision", if side == "baseline" then .str o.baselineRevision else optStr o.revision)])))]
  let mut samples : Array Value := #[]
  let mut pairs : Array Value := #[]
  let report (samples pairs : Array Value) (completed : Bool) (extra : Array (String × Value)) :
      Value :=
    .obj (#[("completed", .bool completed)] ++ header ++
      #[("samples", .arr samples), ("pairs", .arr pairs)] ++ extra)
  writeJson summaryPath (report samples pairs false #[])
  let mut signatures : Std.HashMap String (Array (String × String × String)) := {}
  for index in [0:o.warmups + o.runs] do
    let warmup := index < o.warmups
    let order := if index % 2 == 0 then #["baseline", "current"] else #["current", "baseline"]
    let mut paired : Std.HashMap String Rows := {}
    for side in order do
      let kind := if warmup then "warmup" else "sample"
      let idx := if index < 10 then s!"0{index}" else toString index
      let stem := s!"{outputDir}/{idx}-{kind}-{side}"
      let binary := ((binaries.find? (·.1 == side)).map (·.2)).getD ""
      let result := Value.mkObj ((← sample binary timer o stem) ++
        #[("side", .str side), ("warmup", .bool warmup)])
      samples := samples.push result
      writeJson summaryPath (report samples pairs false #[])
      let wall := toFloat ((result.get? "wall_ns").getD .null)
      IO.println s!"{side} {kind}: exit {match result.get? "exit_code" with | some (.int n) => n | _ => 0}, \
        {fixed (wall / 1e9) 3} s, {dictRepr ((result.get? "outcomes").getD (.obj #[]))}"
      let failed := (result.get? "timed_out" matches some (.bool true)) ||
        !(result.get? "exit_code" matches some (.int 0)) ||
        (result.get? "rows_error").isSome || (result.get? "resources_error").isSome
      if failed then
        IO.eprintln s!"Incomplete run; retained evidence at {summaryPath}"
        return 1
      let rows ← readRows (stem ++ ".jsonl")
      let signature := rows.order.map fun a => (a, outcome rows a, reason rows a)
      if let some prior := signatures[side]? then
        if prior != signature then
          writeJson summaryPath (report samples pairs false #[("error",
            .str s!"{side} coverage or diagnostics changed between samples")])
          return 1
      signatures := signatures.insert side signature
      paired := paired.insert side rows
    if !warmup then
      pairs := pairs.push (compare (paired.getD "baseline" {}) (paired.getD "current" {}) o.top)
      writeJson summaryPath (report samples pairs false #[])
  for ((side, path), sha) in binaries.zip binaryShas do
    if (← sha256 path) != sha then throw <| IO.userError s!"{side} binary changed during the run"
  if (← sha256 o.input) != inputSha || (← sourceFingerprint source) != sourceSha then
    throw <| IO.userError "input or source changed during the run"
  let mut wall : Array (String × Value) := #[]
  let mut medians : Std.HashMap String Float := {}
  for (side, _) in binaries do
    let measured := samples.filter fun s =>
      field s "side" == side && (s.get? "warmup" matches some (.bool false))
    let walls := measured.map fun s => micros s "wall_ns"
    let m := median walls
    medians := medians.insert side (toFloat m)
    wall := wall.push (side, .obj #[("median_ns", m),
      ("min_ns", .int (walls.foldl min walls[0]!)), ("max_ns", .int (walls.foldl max walls[0]!)),
      ("peak_rss_kib", .int ((measured.map (micros · "peak_rss_kib")).foldl max 0))])
  let outcomesOf (side : String) := ((signatures.getD side #[]).map fun (a, o, _) => (a, o)).qsort
    (fun x y => x.1 < y.1)
  let sameCoverage := outcomesOf "baseline" == outcomesOf "current"
  let fullOf (side : String) := (signatures.getD side #[]).qsort (fun x y => x.1 < y.1)
  writeJson summaryPath (.obj (((report samples pairs true #[("wall", .obj wall),
      ("identical_outcomes", .bool sameCoverage),
      ("identical_outcomes_and_diagnostics", .bool (fullOf "baseline" == fullOf "current")),
      ("wall_current_over_baseline", .float (medians.getD "current" 0 / medians.getD "baseline" 1)),
      ("wall_comparison_note", .str (if sameCoverage then "identical coverage" else
        "coverage differs; inspect transitions before comparing wall times"))]) |> fun v =>
        match v with | .obj kvs => kvs | _ => #[])))
  IO.println summaryPath
  return if pairs.any lostAny then 1 else 0

def usage : String :=
  "usage: kernel-check-ixe --compare <baseline.jsonl> <current.jsonl> [--output <f>] [--top N]\n       \
   kernel-check-ixe --paired --binary <b> --baseline-binary <b> --baseline-revision <rev> \
   --input <ixe> --output-dir <new dir> [--revision <rev>] [--baseline-source-sha256 <h>] \
   [--source <dir>] [--limit N] [--fuel N] [--runs N] [--warmups N] [--timeout s] \
   [--time-binary <path>] [--top N]"

def runCompare (args : List String) : IO UInt32 := do
  let rec parse : List String → Array String → Option String → Nat →
      Option (Array String × Option String × Nat)
    | [], pos, out, top => some (pos, out, top)
    | "--output" :: f :: rest, pos, _, top => parse rest pos (some f) top
    | "--top" :: n :: rest, pos, out, _ => n.toNat?.bind (parse rest pos out ·)
    | a :: rest, pos, out, top => if a.startsWith "-" then none else parse rest (pos.push a) out top
  let some (#[baseline, current], output, top) := parse args #[] none 15
    | IO.eprintln usage; return 2
  try
    let result := compare (← readRows baseline) (← readRows current) top
    let result := match result with
      | .obj kvs => Value.obj (kvs.push ("completion_note",
          .str "standalone rows do not establish whether either process completed"))
      | v => v
    match output with
    | some f => writeJson f result
    | none => IO.println (result.dumps 2 true)
    return if lostAny result then 1 else 0
  catch e =>
    IO.eprintln s!"error: {e}"
    return 2

def runPaired (args : List String) : IO UInt32 := do
  let rec parse : List String → Options → Option Options
    | [], o => some o
    | "--binary" :: v :: rest, o => parse rest { o with binary := v }
    | "--baseline-binary" :: v :: rest, o => parse rest { o with baselineBinary := v }
    | "--input" :: v :: rest, o => parse rest { o with input := v }
    | "--output-dir" :: v :: rest, o => parse rest { o with outputDir := v }
    | "--source" :: v :: rest, o => parse rest { o with source := some v }
    | "--revision" :: v :: rest, o => parse rest { o with revision := some v }
    | "--baseline-revision" :: v :: rest, o => parse rest { o with baselineRevision := v }
    | "--baseline-source-sha256" :: v :: rest, o => parse rest { o with baselineSourceSha := some v }
    | "--limit" :: v :: rest, o => v.toNat?.bind fun n => parse rest { o with limit := n }
    | "--fuel" :: v :: rest, o => v.toNat?.bind fun n => parse rest { o with fuel := some n }
    | "--runs" :: v :: rest, o => v.toNat?.bind fun n => parse rest { o with runs := n }
    | "--warmups" :: v :: rest, o => v.toNat?.bind fun n => parse rest { o with warmups := n }
    | "--timeout" :: v :: rest, o => (parseFloat v).bind fun t => parse rest { o with timeout := t, timeoutGiven := true }
    | "--time-binary" :: v :: rest, o => parse rest { o with timeBinary := some v }
    | "--top" :: v :: rest, o => v.toNat?.bind fun n => parse rest { o with top := n }
    | _, _ => none
  let some o := parse args {} | IO.eprintln usage; return 2
  if o.binary.isEmpty || o.baselineBinary.isEmpty || o.input.isEmpty || o.outputDir.isEmpty ||
      o.baselineRevision.isEmpty then
    IO.eprintln usage; return 2
  if o.limit < 1 || o.runs < 1 || o.timeout ≤ 0 then
    IO.eprintln s!"{usage}\nerror: limit/runs/timeout must be positive; fuel/warmups must be nonnegative"
    return 2
  try
    let input ← resolve o.input
    let outputDir ← resolve o.outputDir
    let source ← resolve (o.source.getD ".")
    run { o with input := input, outputDir := outputDir, source := some source }
  catch e =>
    IO.eprintln s!"error: {e}"
    return 2

end Benchmarks.Kernel.CheckIxePaired
