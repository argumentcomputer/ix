import Runner.Build
import Runner.Measure
import Runner.Provenance
import Runner.Report
import Runner.Stats

/-! Pure-Lean K4/K5 (and full K1–K5) reproducible benchmark runner.

Builds unhardened `lean-clang`, `clang-O2`/`clang-O3` (with automatic GMP
resolution for C+GMP twins), optional `gcc-O2`/`gcc-O3` (`--gcc`), optional
single-threaded intrusive-RC recycling C++ controls (`--rc-twins`), and
optional `ixcc` standalone executables (`--closures DIR`, `--rc`, `--opt`,
`--bignat`, `--bignat-lib`, `--embed-cert`, `--blake3-harness`). The `--opt` and
`--bignat` rows are not covered by certificate replay: they are compiled with
`ixcc compile --uncertified`, and their reports say so.

Hardened provenance guarantees:
- Unconditionally unlinks stale binaries, objects, and `.cert` sidecars before
  invoking any compiler in every `build*Row`.
- Writes `k45-build.json` (`format: "ixcc/k45-build/2"`) with full provenance
  and SHA-256 digests of every built binary, object, closure, equations sidecar,
  harness source, compiler binary, and optional BigNat library.
- Uses `k45-build.json` as the SOLE source of truth in `cmdCheck` and
  `cmdMeasure`: refuses missing manifests, ignores/skips non-`"built"` rows,
  recomputes SHA-256 on every executable and fails hard on mismatch or missing
  file, and enforces `ixcc verify-exe` on every `embed_cert == true` row.
- Persists raw per-block nanosecond samples and deterministic 10,000-resample
  bootstrap 95% CIs (wall time and paired ratios) to `k45-samples.json`, and
  generates manifest-driven `k45-report.md` and `k45-report.json` with exact
  `repro_cmd` and allocator annotations. -/

namespace BenchK45

open Lean System Runner

def k45BuildFormat : String := "ixcc/k45-build/2"
def k45SamplesFormat : String := "ixcc/k45-samples/2"
def k45BootstrapRounds : Nat := 10000

def hasSubstr (haystack needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

structure Options where
  rungs : List String := ["K4", "K5"]
  fixtures : Option (List String) := none
  cpu : Nat := 2
  blocks : Nat := 10
  warmup : Nat := 1
  timeout : Option Nat := none
  ixcc : List String := ["../../.lake/build/bin/ixcc"]
  ixccExplicit : Bool := false
  closures : Option FilePath := none
  rcMode : String := "off"
  rcExplicit : Bool := false
  opt : Bool := false
  bignat : Bool := false
  bignatLib : Option FilePath := none
  gcc : Bool := false
  embedCert : Bool := false
  blake3Harness : Bool := false
  rcTwins : Bool := false
  stackBytes : Option Nat := none
  regionBytes : Option Nat := none
  rawArgs : List String := []

def Options.selects (o : Options) (f : Fixture) : Bool :=
  match o.fixtures with
  | some names => names.contains f.name
  | none => o.rungs.contains f.rung

structure IxccRowSpec where
  rowName : String
  rcFlag : String
  opt : Bool
  bignat : Bool
  deriving Repr, BEq

def configuredIxccSpecs (o : Options) : List IxccRowSpec :=
  if o.closures.isNone then []
  else
    -- When `--bignat` is requested without an explicit `--rc`, build only the
    -- BigNat rows (`ixcc-bignat`, plus `ixcc-bignat-opt` with `--opt`) so K4/K5
    -- runs do not compile Stage-W1/W2 non-array/fixnum rows that cannot execute
    -- K4/K5 workloads. Passing `--rc` explicitly alongside `--bignat` builds both.
    let base : List IxccRowSpec :=
      if o.bignat && !o.rcExplicit then []
      else if o.rcMode == "both" then
        [{ rowName := "ixcc-off", rcFlag := "off", opt := false, bignat := false }] ++
        (if o.opt then [{ rowName := "ixcc-opt", rcFlag := "off", opt := true, bignat := false }] else []) ++
        [{ rowName := "ixcc-on", rcFlag := "on", opt := false, bignat := false }] ++
        (if o.opt then [{ rowName := "ixcc-on-opt", rcFlag := "on", opt := true, bignat := false }] else [])
      else if o.rcMode == "on" then
        [{ rowName := "ixcc-on", rcFlag := "on", opt := false, bignat := false }] ++
        (if o.opt then [{ rowName := "ixcc-on-opt", rcFlag := "on", opt := true, bignat := false }] else [])
      else
        [{ rowName := "ixcc", rcFlag := o.rcMode, opt := false, bignat := false }] ++
        (if o.opt then [{ rowName := "ixcc-opt", rcFlag := o.rcMode, opt := true, bignat := false }] else [])
    let bn : List IxccRowSpec :=
      if o.bignat then
        [{ rowName := "ixcc-bignat", rcFlag := "off", opt := false, bignat := true }] ++
        (if o.opt then [{ rowName := "ixcc-bignat-opt", rcFlag := "off", opt := true, bignat := true }] else [])
      else []
    base ++ bn

def configuredRowOrder (o : Options) : List String :=
  ["lean-clang", "clang-O2", "clang-O3"] ++
  (if o.rcTwins then ["clang-O2-rc", "clang-O3-rc"] else []) ++
  (if o.gcc then ["gcc-O2", "gcc-O3"] else []) ++
  (if o.gcc && o.rcTwins then ["gcc-O2-rc", "gcc-O3-rc"] else []) ++
  (configuredIxccSpecs o).map (·.rowName)

/-- Relative path to the intrusive-RC C++ sibling for fixtures that provide one. -/
def rcTwinRelPath? (f : Fixture) : Option FilePath :=
  match f.name with
  | "nqueens" => some (FilePath.mk "nqueens/nqueens_rc.cpp")
  | "const_fold" => some (FilePath.mk "const_fold/cfold_rc.cpp")
  | _ => none

def rcTwinTemplate : List String :=
  ["clang++", "-O2", "-std=c++17", "-o", "{out}", "{src}"]

def binPath (out : FilePath) (row : String) (f : Fixture) : FilePath :=
  out / "bin" / row / f.name

def objPath (out : FilePath) (row : String) (f : Fixture) : FilePath :=
  out / "ixcc" / row / s!"{f.name}.o"

def certSidecars (out : FilePath) (row : String) (f : Fixture) : List FilePath :=
  [ out / "ixcc" / row / s!"{f.name}.cert.json"
  , out / "ixcc" / row / s!"{f.name}.cert"
  , out / "bin" / row / s!"{f.name}.cert"
  , FilePath.mk ((binPath out row f).toString ++ ".cert") ]

/-- Unconditionally unlink stale binary, object, stats, and `.cert` sidecars
for `(row, f)` before invoking any compiler. -/
def unlinkRowArtifacts (out : FilePath) (row : String) (f : Fixture) : IO Unit := do
  unlinkIfExists (binPath out row f)
  unlinkIfExists (objPath out row f)
  unlinkIfExists (out / "ixcc" / row / s!"{f.name}.stats.txt")
  for p in certSidecars out row f do
    unlinkIfExists p

/-! ## Manifest records (`ixcc/k45-build/2`) -/

structure BuildRecord where
  fixture : String
  rung : String
  row : String
  status : String
  binaryPath : Option String := none
  binarySha256 : Option String := none
  objectPath : Option String := none
  objectSha256 : Option String := none
  closureSha256 : Option String := none
  equationsSha256 : Option String := none
  harnessSha256 : Option String := none
  compileArgs : List String := []
  embedCert : Bool := false
  compileMs : Option Float := none
  textBytes : Option Nat := none
  detail : Option String := none

private def optStrJson : Option String → Json
  | some s => Json.str s
  | none => Json.null

private def optNatJson : Option Nat → Json
  | some n => toJson n
  | none => Json.null

private def optFloatJson : Option Float → Json
  | some x => toJson x
  | none => Json.null

def BuildRecord.toJson (r : BuildRecord) : Json :=
  let base : List (String × Json) := [
    ("fixture", Json.str r.fixture),
    ("rung", Json.str r.rung),
    ("row", Json.str r.row),
    ("status", Json.str r.status),
    ("binary_path", optStrJson r.binaryPath),
    ("binary_sha256", optStrJson r.binarySha256),
    ("object_path", optStrJson r.objectPath),
    ("object_sha256", optStrJson r.objectSha256),
    ("closure_sha256", optStrJson r.closureSha256),
    ("equations_sha256", optStrJson r.equationsSha256),
    ("harness_sha256", optStrJson r.harnessSha256),
    ("compile_args", Lean.toJson r.compileArgs),
    ("embed_cert", Lean.toJson r.embedCert),
    ("compile_ms", optFloatJson r.compileMs),
    ("text_bytes", optNatJson r.textBytes)
  ]
  let withDetail := match r.detail with
    | some d => base ++ [("detail", Json.str d)]
    | none => base
  Json.mkObj withDetail

private def getOptStr (j : Json) (k : String) : Except String (Option String) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => some <$> v.getStr?

private def getOptNat (j : Json) (k : String) : Except String (Option Nat) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => some <$> v.getNat?

private def getOptFloat (j : Json) (k : String) : Except String (Option Float) :=
  match j.getObjVal? k with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => (fun n => some n.toFloat) <$> v.getNum?

def BuildRecord.fromJson (j : Json) : Except String BuildRecord := do
  let fixture ← (← j.getObjVal? "fixture").getStr?
  let rung ← (← j.getObjVal? "rung").getStr?
  let row ← (← j.getObjVal? "row").getStr?
  let status ← (← j.getObjVal? "status").getStr?
  let binaryPath ← getOptStr j "binary_path"
  let binarySha256 ← getOptStr j "binary_sha256"
  let objectPath ← getOptStr j "object_path"
  let objectSha256 ← getOptStr j "object_sha256"
  let closureSha256 ← getOptStr j "closure_sha256"
  let equationsSha256 ← getOptStr j "equations_sha256"
  let harnessSha256 ← getOptStr j "harness_sha256"
  let compileArgs ← match j.getObjVal? "compile_args" with
    | .ok v => (← v.getArr?).toList.mapM (·.getStr?)
    | .error _ => pure []
  let embedCert ← match j.getObjVal? "embed_cert" with
    | .ok v => v.getBool?
    | .error _ => pure false
  let compileMs ← getOptFloat j "compile_ms"
  let textBytes ← getOptNat j "text_bytes"
  let detail ← getOptStr j "detail"
  return {
    fixture, rung, row, status, binaryPath, binarySha256, objectPath, objectSha256,
    closureSha256, equationsSha256, harnessSha256, compileArgs, embedCert,
    compileMs, textBytes, detail
  }

structure BuildManifest where
  format : String
  provenance : Json
  ixccCmd : List String
  reproCmd : String
  rowOrder : List String
  rows : Array BuildRecord

def loadBuildManifest (out : FilePath) : IO (BuildManifest × String) := do
  let manifestPath := out / "k45-build.json"
  unless ← manifestPath.pathExists do
    throw (IO.userError s!"missing build manifest {manifestPath}; run 'bench-k45 build' first")
  let manifestSha ← sha256File manifestPath
  let text ← IO.FS.readFile manifestPath
  let json ← IO.ofExcept ((Json.parse text).mapError (s!"invalid JSON in {manifestPath}: {·}"))
  let parsed ← IO.ofExcept do
    let fmt ← (← json.getObjVal? "format").getStr?
    unless fmt == k45BuildFormat do
      throw s!"unsupported k45-build.json format '{fmt}' (expected '{k45BuildFormat}')"
    let prov ← json.getObjVal? "provenance"
    let ixccCmd ← match prov.getObjVal? "ixcc_cmd" with
      | .ok v => (← v.getArr?).toList.mapM (·.getStr?)
      | .error _ => pure ["../../.lake/build/bin/ixcc"]
    let reproCmd := (prov.getObjValD "repro_cmd").getStr?.toOption.getD ""
    let rowOrder ← match json.getObjVal? "row_order" with
      | .ok v => (← v.getArr?).toList.mapM (·.getStr?)
      | .error _ => pure []
    let rawRows ← (← json.getObjVal? "rows").getArr?
    let rows ← rawRows.mapM BuildRecord.fromJson
    return ({ format := fmt, provenance := prov, ixccCmd, reproCmd, rowOrder, rows } : BuildManifest)
  return (parsed, manifestSha)

/-- Verify that a manifest record has `status == "built"`, that its executable
exists at `binary_path`, and that its recomputed SHA-256 matches `binary_sha256`.
Fails hard on any missing file or digest mismatch. -/
def verifyManifestArtifact (rec : BuildRecord) : IO FilePath := do
  unless rec.status == "built" do
    throw (IO.userError s!"refusing non-built row {rec.row}/{rec.fixture} (status: {rec.status})")
  let some binStr := rec.binaryPath
    | throw (IO.userError s!"manifest row {rec.row}/{rec.fixture} has status 'built' but null binary_path")
  let some wantSha := rec.binarySha256
    | throw (IO.userError s!"manifest row {rec.row}/{rec.fixture} has status 'built' but null binary_sha256")
  let p := FilePath.mk binStr
  unless ← p.pathExists do
    throw (IO.userError s!"missing built binary for {rec.row}/{rec.fixture}: {p} (expected sha256 {wantSha})")
  let actualSha ← sha256File p
  unless actualSha == wantSha do
    throw (IO.userError s!"SHA-256 mismatch for {rec.row}/{rec.fixture} ({p}): expected {wantSha}, got {actualSha}")
  return p

/-! ## Binary inspection & timed execution -/

/-- Query `.text` section size in bytes via `objdump -h` (`none` if unavailable). -/
def textSizeBytes (path : FilePath) : IO (Option Nat) := do
  try
    let out ← IO.Process.output { cmd := "objdump", args := #["-h", path.toString] }
    if out.exitCode != 0 then return none
    for line in out.stdout.splitOn "\n" do
      let cols := (line.splitOn " ").filter (!·.isEmpty)
      match cols with
      | _ :: ".text" :: hexSize :: _ =>
        let val := hexSize.foldl (fun acc c =>
          let d :=
            if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
            else if 'a' ≤ c && c ≤ 'f' then 10 + c.toNat - 'a'.toNat
            else if 'A' ≤ c && c ≤ 'F' then 10 + c.toNat - 'A'.toNat
            else 0
          acc * 16 + d) 0
        return some val
      | _ => pure ()
    return none
  catch _ => return none

/-- Find GNU `time` binary supporting `-f %M` for peak RSS measurement, if installed. -/
def findGnuTime : IO (Option String) := do
  for cand in ["/usr/bin/time", "time"] do
    try
      let out ← IO.Process.output { cmd := cand, args := #["-f", "%M", "true"] }
      if out.exitCode == 0 && out.stderr.trimAscii.toString.toNat?.isSome then
        return some cand
    catch _ => pure ()
  return none

/-- Check whether `prlimit --stack=unlimited` is available (for deep-recursion fixtures like `const_fold`). -/
def hasPrlimit : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "prlimit", args := #["--stack=unlimited", "true"] }
    return out.exitCode == 0
  catch _ => return false

def envOfFixture (f : Fixture) : Array (String × Option String) :=
  f.env.toArray.map fun (k, v) => (k, some v)

def runExec (timeoutSec : Option Nat) (usePrlimit : Bool) (cmd : String) (args : List String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let (c1, a1) := if usePrlimit then ("prlimit", ["--stack=unlimited", cmd] ++ args) else (cmd, args)
  let (c2, a2) := match timeoutSec with
    | some secs => ("timeout", [toString secs, c1] ++ a1)
    | none => (c1, a1)
  let out ← IO.Process.output { cmd := c2, args := a2.toArray, env }
  if timeoutSec.isSome && out.exitCode == 124 then
    throw (IO.userError s!"{cmd} {" ".intercalate args} timed out after {timeoutSec.getD 0}s")
  return out

/-- Run `bin args` pinned to `cpu`, returning `(stdout, wallNanos, peakRssKiB?)`. -/
def runTimed (gnuTime : Option String) (prlimitOk : Bool) (timeoutSec : Option Nat)
    (cpu : Nat) (f : Fixture) (bin : FilePath) (args : List String) :
    IO (String × Nat × Option Nat) := do
  let usePrlimit := prlimitOk && f.name == "const_fold"
  let env := envOfFixture f
  match gnuTime with
  | some t =>
    let start ← IO.monoNanosNow
    let out ← runExec timeoutSec usePrlimit t
      (["-f", "%M", "taskset", "-c", toString cpu, bin.toString] ++ args) env
    let stop ← IO.monoNanosNow
    if out.exitCode != 0 then
      throw (IO.userError s!"{bin} {" ".intercalate args} exited {out.exitCode}:\n{out.stderr}")
    let lines := (out.stderr.trimAscii.toString.splitOn "\n").filter (!·.isEmpty)
    let rss := lines.getLast?.bind (fun s => s.trimAscii.toString.toNat?)
    return (out.stdout, stop - start, rss)
  | none =>
    let start ← IO.monoNanosNow
    let out ← runExec timeoutSec usePrlimit "taskset"
      (["-c", toString cpu, bin.toString] ++ args) env
    let stop ← IO.monoNanosNow
    if out.exitCode != 0 then
      throw (IO.userError s!"{bin} {" ".intercalate args} exited {out.exitCode}:\n{out.stderr}")
    return (out.stdout, stop - start, none)

/-! ## Row builders (every builder unlinks stale artifacts FIRST) -/

/-- Build the `lean-clang` (unhardened `leanc`) row. -/
def buildLeanRow (manifest : Manifest) (root out : FilePath) (f : Fixture) : IO BuildRecord := do
  unlinkRowArtifacts out "lean-clang" f
  let c := out / "c" / s!"{f.name}.c"
  unlinkIfExists c
  IO.FS.createDirAll (c.parent.getD out)
  let target := binPath out "lean-clang" f
  IO.FS.createDirAll (target.parent.getD out)
  let subst := [("src", f.lean), ("c", c.toString), ("out", target.toString)]
  let compile := expand manifest.leanCompile subst
  let link := expand manifest.leanLink subst
  let linkArgs :=
    if link.tail!.any (fun w => w == "-O3" || w == "-O2") then
      link.tail!.flatMap fun w => if w == "-O3" || w == "-O2" then w :: omitFpFlags else [w]
    else
      omitFpFlags ++ link.tail!
  let start ← IO.monoNanosNow
  let _ ← Runner.run compile.head! compile.tail! (cwd := some root)
  let _ ← Runner.run link.head! linkArgs (env := ccEnv)
  let stop ← IO.monoNanosNow
  let wallMs := (stop - start).toFloat / 1e6
  let binSha ← sha256File target
  let sz ← textSizeBytes target
  return {
    fixture := f.name, rung := f.rung, row := "lean-clang", status := "built",
    binaryPath := some target.toString, binarySha256 := some binSha,
    compileArgs := compile ++ ["--"] ++ (link.head! :: linkArgs),
    embedCert := false, compileMs := some wallMs, textBytes := sz
  }

/-- Build a `clang` / `clang++` row (`clang-O2`, `clang-O3`, `clang-O2-rc`, `clang-O3-rc`). -/
def buildClangRow (root out : FilePath) (rowName level : String) (srcRel : FilePath)
    (template : List String) (getGmp : IO (List String)) (f : Fixture) : IO BuildRecord := do
  unlinkRowArtifacts out rowName f
  let target := binPath out rowName f
  IO.FS.createDirAll (target.parent.getD out)
  let command := expand template [("src", (root / srcRel).toString), ("out", target.toString)]
  let args :=
    if command.tail!.any (fun w => w == "-O2" || w == "-O3") then
      command.tail!.flatMap fun w => if w == "-O2" || w == "-O3" then level :: omitFpFlags else [w]
    else
      level :: omitFpFlags ++ command.tail!
  let args ← if args.contains "-lgmp" then do
      let gmp ← getGmp
      pure (args.flatMap fun w => if w == "-lgmp" then gmp ++ [w] else [w])
    else pure args
  let start ← IO.monoNanosNow
  let _ ← Runner.run command.head! args (env := ccEnv)
  let stop ← IO.monoNanosNow
  let wallMs := (stop - start).toFloat / 1e6
  let binSha ← sha256File target
  let sz ← textSizeBytes target
  return {
    fixture := f.name, rung := f.rung, row := rowName, status := "built",
    binaryPath := some target.toString, binarySha256 := some binSha,
    compileArgs := command.head! :: args,
    embedCert := false, compileMs := some wallMs, textBytes := sz
  }

/-- Build a `gcc` / `g++` row (`gcc-O2`, `gcc-O3`, `gcc-O2-rc`, `gcc-O3-rc`). -/
def buildGccRow (root out : FilePath) (rowName level : String) (srcRel : FilePath)
    (template : List String) (getGmp : IO (List String)) (f : Fixture) : IO BuildRecord := do
  unlinkRowArtifacts out rowName f
  let target := binPath out rowName f
  IO.FS.createDirAll (target.parent.getD out)
  let command := expand template [("src", (root / srcRel).toString), ("out", target.toString)]
  let gccCmd :=
    if command.head! == "clang++" || srcRel.toString.endsWith ".cpp" then "g++"
    else "gcc"
  let args :=
    if command.tail!.any (fun w => w == "-O2" || w == "-O3") then
      command.tail!.flatMap fun w => if w == "-O2" || w == "-O3" then level :: omitFpFlags else [w]
    else
      level :: omitFpFlags ++ command.tail!
  let args ← if args.contains "-lgmp" then do
      let gmp ← getGmp
      pure (args.flatMap fun w => if w == "-lgmp" then gmp ++ [w] else [w])
    else pure args
  let start ← IO.monoNanosNow
  let _ ← Runner.run gccCmd args (env := ccEnv)
  let stop ← IO.monoNanosNow
  let wallMs := (stop - start).toFloat / 1e6
  let binSha ← sha256File target
  let sz ← textSizeBytes target
  return {
    fixture := f.name, rung := f.rung, row := rowName, status := "built",
    binaryPath := some target.toString, binarySha256 := some binSha,
    compileArgs := gccCmd :: args,
    embedCert := false, compileMs := some wallMs, textBytes := sz
  }

/-- The `ixcc compile` flags of a row. `--opt` and `--bignat` rows are not covered by certificate
replay, so `ixcc` needs `--uncertified` with them (and marks their objects' provenance notes). -/
private def ixccModeArgs (o : Options) (spec : IxccRowSpec) : List String :=
  (if spec.opt || spec.bignat then ["--uncertified"] else []) ++
  (if spec.bignat then
    ["--bignat"] ++ (match o.bignatLib with | some l => ["--bignat-lib", l.toString] | none => [])
   else
    ["--rc", spec.rcFlag]) ++
  (if spec.opt then ["--opt"] else [])

private def ixccLayoutArgs (o : Options) : List String :=
  (match o.stackBytes with | some s => ["--stack", toString s] | none => []) ++
  (match o.regionBytes with | some r => ["--region", toString r] | none => [])

/-- Build an `ixcc` standalone executable (`--exe`) when a frozen closure exists.
Unconditionally unlinks any stale binary, object, and `.cert` sidecars BEFORE invoking `ixcc`. -/
def buildIxccRow (o : Options) (out : FilePath) (spec : IxccRowSpec) (f : Fixture) :
    IO (Option BuildRecord) := do
  let some dir := o.closures | return none
  unlinkRowArtifacts out spec.rowName f
  let closure := dir / s!"{f.name}.ixe"
  let equations := dir / s!"{f.name}.equations.json"
  let closSha ← sha256File? closure
  let eqSha ← sha256File? equations
  unless ← closure.pathExists do
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"unavailable: no closure {closure}",
      closureSha256 := closSha, equationsSha256 := eqSha
    }
  unless ← equations.pathExists do
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"unavailable: no equations {equations}",
      closureSha256 := closSha, equationsSha256 := eqSha
    }
  let target := binPath out spec.rowName f
  IO.FS.createDirAll (target.parent.getD out)
  let objDir := out / "ixcc" / spec.rowName
  IO.FS.createDirAll objDir
  let obj := objPath out spec.rowName f
  let cmd := o.ixcc.headD "ixcc"
  let lead := o.ixcc.drop 1
  let modeArgs := ixccModeArgs o spec
  let layoutArgs := ixccLayoutArgs o
  let mkExeArgs (embed : Bool) : List String :=
    lead ++ ["compile", closure.toString, "--equations", equations.toString] ++
    modeArgs ++ ["-o", obj.toString, "--exe", target.toString] ++
    (if embed then ["--embed-cert"] else []) ++ layoutArgs ++ ["--stats"]
  let start ← IO.monoNanosNow
  let firstArgs := mkExeArgs o.embedCert
  let res0 ← IO.Process.output { cmd, args := firstArgs.toArray }
  -- If `--embed-cert` was requested on an `--opt` or `--bignat` row and this `ixcc`
  -- binary explicitly declines combining them (CLI exit 2), retry without `--embed-cert`
  -- and record `embed_cert = false` honestly in the manifest.
  let (res, usedArgs, usedEmbed, note?) ←
    if o.embedCert && (spec.opt || spec.bignat) && res0.exitCode == 2 &&
        hasSubstr res0.stderr "cannot combine" then
      unlinkRowArtifacts out spec.rowName f
      let retryArgs := mkExeArgs false
      let res1 ← IO.Process.output { cmd, args := retryArgs.toArray }
      pure (res1, retryArgs, false, some s!"--embed-cert unsupported for {spec.rowName} by this ixcc binary")
    else
      pure (res0, firstArgs, o.embedCert, none)
  let stop ← IO.monoNanosNow
  let wallMs := (stop - start).toFloat / 1e6
  if res.exitCode == 0 then
    IO.FS.writeFile (objDir / s!"{f.name}.stats.txt") res.stdout
    let binSha ← sha256File target
    let objSha ← sha256File? obj
    let sz ← textSizeBytes obj
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName, status := "built",
      binaryPath := some target.toString, binarySha256 := some binSha,
      objectPath := objSha.map fun _ => obj.toString, objectSha256 := objSha,
      closureSha256 := closSha, equationsSha256 := eqSha,
      compileArgs := cmd :: usedArgs, embedCert := usedEmbed,
      compileMs := some wallMs, textBytes := sz, detail := note?
    }
  else
    -- Ensure no partial/stale executable remains before falling back to object-only.
    unlinkIfExists target
    unlinkIfExists obj
    let objArgs := lead ++ ["compile", closure.toString, "--equations", equations.toString] ++
      modeArgs ++ ["-o", obj.toString, "--stats"]
    let objRes ← IO.Process.output { cmd, args := objArgs.toArray }
    if objRes.exitCode == 0 then
      IO.FS.writeFile (objDir / s!"{f.name}.stats.txt") objRes.stdout
      let objSha ← sha256File? obj
      let sz ← textSizeBytes obj
      return some {
        fixture := f.name, rung := f.rung, row := spec.rowName,
        status := s!"object-only ({res.stderr.trimAscii.toString})",
        binaryPath := none, binarySha256 := none,
        objectPath := objSha.map fun _ => obj.toString, objectSha256 := objSha,
        closureSha256 := closSha, equationsSha256 := eqSha,
        compileArgs := cmd :: objArgs, embedCert := false,
        compileMs := some wallMs, textBytes := sz
      }
    unlinkIfExists obj
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"declined: {res.stderr.trimAscii.toString}",
      binaryPath := none, binarySha256 := none,
      objectPath := none, objectSha256 := none,
      closureSha256 := closSha, equationsSha256 := eqSha,
      compileArgs := cmd :: usedArgs, embedCert := false,
      compileMs := some wallMs, textBytes := none
    }

/-- Build a runnable K4 `blake3` executable by compiling `blake3.o` via `ixcc`
and linking it against `benchmarks/fixtures/blake3/harness.c`.
Unconditionally unlinks stale artifacts BEFORE invoking any compiler. -/
def buildBlake3HarnessRow (o : Options) (root out : FilePath) (spec : IxccRowSpec) (f : Fixture) :
    IO (Option BuildRecord) := do
  let some dir := o.closures | return none
  unlinkRowArtifacts out spec.rowName f
  let closure := dir / s!"{f.name}.ixe"
  let equations := dir / s!"{f.name}.equations.json"
  let harnessSrc := root / "blake3" / "harness.c"
  let closSha ← sha256File? closure
  let eqSha ← sha256File? equations
  let harnessSha ← sha256File? harnessSrc
  unless ← closure.pathExists do
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"unavailable: no closure {closure}",
      closureSha256 := closSha, equationsSha256 := eqSha, harnessSha256 := harnessSha
    }
  unless ← equations.pathExists do
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"unavailable: no equations {equations}",
      closureSha256 := closSha, equationsSha256 := eqSha, harnessSha256 := harnessSha
    }
  unless ← harnessSrc.pathExists do
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"unavailable: no blake3 harness {harnessSrc}",
      closureSha256 := closSha, equationsSha256 := eqSha, harnessSha256 := none
    }
  let target := binPath out spec.rowName f
  IO.FS.createDirAll (target.parent.getD out)
  let objDir := out / "ixcc" / spec.rowName
  IO.FS.createDirAll objDir
  let obj := objPath out spec.rowName f
  let cmd := o.ixcc.headD "ixcc"
  let lead := o.ixcc.drop 1
  let modeArgs := ixccModeArgs o spec
  let ixccArgs := lead ++ ["compile", closure.toString, "--equations", equations.toString] ++
    modeArgs ++ ["-o", obj.toString, "--stats"]
  let start ← IO.monoNanosNow
  let res ← IO.Process.output { cmd, args := ixccArgs.toArray }
  if res.exitCode != 0 then
    let stop ← IO.monoNanosNow
    unlinkIfExists obj
    unlinkIfExists target
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"declined: {res.stderr.trimAscii.toString}",
      closureSha256 := closSha, equationsSha256 := eqSha, harnessSha256 := harnessSha,
      compileArgs := cmd :: ixccArgs, embedCert := false,
      compileMs := some ((stop - start).toFloat / 1e6)
    }
  IO.FS.writeFile (objDir / s!"{f.name}.stats.txt") res.stdout
  let objSha ← sha256File obj
  let sz ← textSizeBytes obj
  let linkArgs := ["-O2"] ++ omitFpFlags ++ ["-Wall", "-Wextra", "-Werror",
    "-o", target.toString, harnessSrc.toString, obj.toString]
  let linkRes ← IO.Process.output { cmd := "clang", args := linkArgs.toArray, env := ccEnv }
  let stop ← IO.monoNanosNow
  let wallMs := (stop - start).toFloat / 1e6
  if linkRes.exitCode != 0 then
    unlinkIfExists target
    return some {
      fixture := f.name, rung := f.rung, row := spec.rowName,
      status := s!"harness-link-failed: {linkRes.stderr.trimAscii.toString}",
      objectPath := some obj.toString, objectSha256 := some objSha,
      closureSha256 := closSha, equationsSha256 := eqSha, harnessSha256 := harnessSha,
      compileArgs := (cmd :: ixccArgs) ++ ["--"] ++ ("clang" :: linkArgs),
      embedCert := false, compileMs := some wallMs, textBytes := sz
    }
  let binSha ← sha256File target
  return some {
    fixture := f.name, rung := f.rung, row := spec.rowName, status := "built",
    binaryPath := some target.toString, binarySha256 := some binSha,
    objectPath := some obj.toString, objectSha256 := some objSha,
    closureSha256 := closSha, equationsSha256 := eqSha, harnessSha256 := harnessSha,
    compileArgs := (cmd :: ixccArgs) ++ ["--"] ++ ("clang" :: linkArgs),
    embedCert := false, compileMs := some wallMs, textBytes := sz,
    detail := some "linked via benchmarks/fixtures/blake3/harness.c"
  }

/-! ## Subcommands: build, check, measure, report -/

def cmdBuild (manifest : Manifest) (root out : FilePath) (o : Options) : IO Unit := do
  IO.FS.createDirAll out
  let out ← IO.FS.realPath out
  let fixtures := manifest.fixtures.filter o.selects
  let bignatLibSha? ← match o.bignatLib with
    | some p => some <$> sha256File p
    | none => pure none
  let gmpCache ← IO.mkRef (none : Option (List String))
  let getGmp : IO (List String) := do
    match ← gmpCache.get with
    | some fs => pure fs
    | none =>
      let fs ← resolveGmpFlags
      gmpCache.set (some fs)
      pure fs
  let ixccSpecs := configuredIxccSpecs o
  let mut records : Array BuildRecord := #[]
  for f in fixtures do
    -- lean-clang (unhardened)
    records := records.push (← buildLeanRow manifest root out f)
    -- clang-O2 and clang-O3 (unhardened, automatic GMP flags)
    for (rowName, level) in [("clang-O2", "-O2"), ("clang-O3", "-O3")] do
      records := records.push (← buildClangRow root out rowName level (FilePath.mk f.twin.path) f.twin.compile getGmp f)
    -- optional intrusive-RC C++ sibling controls (clang)
    if o.rcTwins then
      if let some rcRel := rcTwinRelPath? f then
        for (rowName, level) in [("clang-O2-rc", "-O2"), ("clang-O3-rc", "-O3")] do
          records := records.push (← buildClangRow root out rowName level rcRel rcTwinTemplate getGmp f)
    -- optional gcc-O2 and gcc-O3
    if o.gcc then
      for (rowName, level) in [("gcc-O2", "-O2"), ("gcc-O3", "-O3")] do
        records := records.push (← buildGccRow root out rowName level (FilePath.mk f.twin.path) f.twin.compile getGmp f)
      if o.rcTwins then
        if let some rcRel := rcTwinRelPath? f then
          for (rowName, level) in [("gcc-O2-rc", "-O2"), ("gcc-O3-rc", "-O3")] do
            records := records.push (← buildGccRow root out rowName level rcRel rcTwinTemplate getGmp f)
    -- optional ixcc rows
    for spec in ixccSpecs do
      let rec? ←
        if f.name == "blake3" && o.blake3Harness && spec.bignat then
          buildBlake3HarnessRow o root out spec f
        else
          buildIxccRow o out spec f
      if let some r := rec? then
        records := records.push r
    IO.println s!"built {f.name} ({f.rung})"

  let (gitCommit, gitDirty) ← gitProvenance
  let (vers, ixccSha?) ← k45Versions o.ixcc
  let envHost ← environment o.cpu
  let hn ← hostName
  let hostJson := Json.mkObj [("hostname", Json.str hn), ("environment", envHost)]
  let repro := reproCommand o.rawArgs
  let provenance := Json.mkObj [
    ("git_commit", Json.str gitCommit),
    ("git_dirty", match gitDirty with | some b => toJson b | none => Json.null),
    ("ixcc_cmd", toJson o.ixcc),
    ("ixcc_sha256", optStrJson ixccSha?),
    ("bignat_lib", optStrJson (o.bignatLib.map FilePath.toString)),
    ("bignat_lib_sha256", optStrJson bignatLibSha?),
    ("versions", vers),
    ("host", hostJson),
    ("cli_args", toJson o.rawArgs),
    ("repro_cmd", Json.str repro)
  ]
  let optionsJson := Json.mkObj [
    ("rc_mode", Json.str o.rcMode),
    ("opt", toJson o.opt),
    ("bignat", toJson o.bignat),
    ("gcc", toJson o.gcc),
    ("embed_cert", toJson o.embedCert),
    ("blake3_harness", toJson o.blake3Harness),
    ("rc_twins", toJson o.rcTwins),
    ("closures", optStrJson (o.closures.map FilePath.toString)),
    ("bignat_lib", optStrJson (o.bignatLib.map FilePath.toString)),
    ("stack_bytes", optNatJson o.stackBytes),
    ("region_bytes", optNatJson o.regionBytes),
    ("cpu", toJson o.cpu),
    ("blocks", toJson o.blocks),
    ("warmup", toJson o.warmup),
    ("timeout", optNatJson o.timeout)
  ]
  let manifestJson := Json.mkObj [
    ("format", Json.str k45BuildFormat),
    ("provenance", provenance),
    ("rungs", toJson o.rungs),
    ("fixtures", Json.arr (fixtures.map (Json.str ·.name))),
    ("row_order", toJson (configuredRowOrder o)),
    ("cc_env", Json.str "NIX_HARDENING_ENABLE="),
    ("omit_fp_flags", toJson omitFpFlags),
    ("options", optionsJson),
    ("rows", Json.arr (records.map BuildRecord.toJson))
  ]
  IO.FS.writeFile (out / "k45-build.json") (manifestJson.pretty ++ "\n")

def cmdCheck (manifest : Manifest) (root out : FilePath) (o : Options) : IO Unit := do
  let (bm, _) ← loadBuildManifest out
  let fixtures := manifest.fixtures.filter o.selects
  let ixccCmd := if o.ixccExplicit then o.ixcc else bm.ixccCmd
  let prlimitOk ← hasPrlimit
  let mut checked := 0
  let mut verified := 0
  let mut failures := 0
  for f in fixtures do
    let expectedTest ← IO.FS.readFile (root / f.expected)
    let recs := bm.rows.toList.filter fun r => r.fixture == f.name && r.status == "built"
    let usePrlimit := prlimitOk && f.name == "const_fold"
    let env := envOfFixture f
    for rec in recs do
      let bin ← verifyManifestArtifact rec
      if rec.embedCert then
        let cmd := ixccCmd.headD "ixcc"
        let args := ixccCmd.drop 1 ++ ["verify-exe", bin.toString]
        let vout ← IO.Process.output { cmd, args := args.toArray }
        if vout.exitCode != 0 then
          throw (IO.userError s!"ixcc verify-exe FAILED for {rec.row}/{f.name} ({bin}):\n{vout.stderr}")
        verified := verified + 1
      let outTest ← runExec o.timeout usePrlimit bin.toString f.testArgs env
      if outTest.exitCode != 0 then
        throw (IO.userError s!"{rec.row}/{f.name} test run exited {outTest.exitCode}:\n{outTest.stderr}")
      checked := checked + 1
      if outTest.stdout != expectedTest then
        failures := failures + 1
        IO.eprintln s!"FAIL test {rec.row}/{f.name}: got {outTest.stdout.trimAscii}, expected {expectedTest.trimAscii}"
      if let some expectedBench := f.benchExpected then
        let outBench ← runExec o.timeout usePrlimit bin.toString f.benchArgs env
        if outBench.exitCode != 0 then
          throw (IO.userError s!"{rec.row}/{f.name} bench run exited {outBench.exitCode}:\n{outBench.stderr}")
        checked := checked + 1
        if outBench.stdout != expectedBench then
          failures := failures + 1
          IO.eprintln s!"FAIL bench {rec.row}/{f.name}: got {outBench.stdout.trimAscii}, expected {expectedBench.trimAscii}"
  if checked == 0 then
    throw (IO.userError "no built rows in k45-build.json for selected fixtures")
  if failures > 0 then throw (IO.userError s!"{failures} of {checked} K4/K5 checks failed")
  IO.println s!"checked {checked} K4/K5 outputs ({verified} embedded certs verified, all SHA-256 digests matched)"

private def statSummaryJson (values : Array Float) (rounds : Nat) : Json :=
  let (lo, hi) := bootstrap values rounds
  Json.mkObj [
    ("median", toJson (median values)),
    ("iqr", toJson (iqr values)),
    ("ci95_low", toJson lo),
    ("ci95_high", toJson hi)
  ]

def cmdMeasure (manifest : Manifest) (out : FilePath) (o : Options) : IO Unit := do
  let (bm, manifestSha) ← loadBuildManifest out
  let fixtures := manifest.fixtures.filter o.selects
  -- Verify EVERY built binary's SHA-256 up front before running any workload.
  let mut verifiedPlan : Array (Fixture × List (BuildRecord × FilePath)) := #[]
  let mut totalBuiltRows := 0
  for f in fixtures do
    let recs := bm.rows.toList.filter fun r => r.fixture == f.name && r.status == "built"
    let mut pairs : List (BuildRecord × FilePath) := []
    for rec in recs do
      let bin ← verifyManifestArtifact rec
      pairs := pairs ++ [(rec, bin)]
    unless pairs.isEmpty do
      totalBuiltRows := totalBuiltRows + pairs.length
      verifiedPlan := verifiedPlan.push (f, pairs)
  if totalBuiltRows == 0 then
    throw (IO.userError "no built rows in k45-build.json to measure for selected fixtures")

  let gnuTime ← findGnuTime
  let prlimitOk ← hasPrlimit
  let envStart ← environment o.cpu
  let mut samples : Array (String × String × String × Nat × Nat × Option Nat) := #[]
  for ((f, built), idx) in verifiedPlan.toList.zipIdx do
    for _ in [:o.warmup] do
      for (_, bin) in built do
        let _ ← runTimed gnuTime prlimitOk o.timeout o.cpu f bin f.benchArgs
    for block in [:o.blocks] do
      let mut outputs : List String := []
      for (rec, bin) in shuffle (block * 1000 + idx) built do
        let (stdout, ns, rss) ← runTimed gnuTime prlimitOk o.timeout o.cpu f bin f.benchArgs
        outputs := stdout :: outputs
        samples := samples.push (f.name, f.rung, rec.row, block, ns, rss)
      unless outputs.all (· == outputs.headD "") do
        throw (IO.userError s!"{f.name}: rows disagree in block {block}")
      if let some want := f.benchExpected then
        unless outputs.headD "" == want do
          throw (IO.userError s!"{f.name}: output differs from bench_expected in block {block}")
    IO.println s!"measured {f.name} ({f.rung}): {o.blocks} blocks × {built.length} rows (warmup {o.warmup})"

  let samplesJson := samples.map fun (fx, rg, rw, blk, ns, rss) => Json.mkObj [
    ("fixture", Json.str fx), ("rung", Json.str rg), ("row", Json.str rw),
    ("block", toJson blk), ("ns", toJson ns),
    ("rss_kib", optNatJson rss)
  ]

  -- Precompute deterministic 10,000-resample bootstrap summaries directly in k45-samples.json
  let mut summaries : Array Json := #[]
  for (f, built) in verifiedPlan do
    let of (row : String) := samples.filter fun (fx, _, r, _, _, _) => fx == f.name && r == row
    let paired (row base : String) : Array Float :=
      let baseRows := of base
      (of row).filterMap fun (_, _, _, blk, ns, _) =>
        (baseRows.find? fun (_, _, _, b, _, _) => b == blk).map fun (_, _, _, _, bns, _) =>
          ns.toFloat / bns.toFloat
    for (rec, _) in built do
      let rs := of rec.row
      let nsVals := rs.map fun (_, _, _, _, ns, _) => ns.toFloat
      let msVals := nsVals.map (· / 1e6)
      let rssVals := rs.filterMap fun (_, _, _, _, _, k) => k.map (·.toFloat)
      let ratioObj (base : String) : Json :=
        if rec.row == base then Json.null
        else
          let p := paired rec.row base
          if p.isEmpty then Json.null else statSummaryJson p k45BootstrapRounds
      summaries := summaries.push (Json.mkObj [
        ("fixture", Json.str f.name),
        ("rung", Json.str f.rung),
        ("row", Json.str rec.row),
        ("n", toJson rs.size),
        ("wall_ns", statSummaryJson nsVals k45BootstrapRounds),
        ("wall_ms", statSummaryJson msVals k45BootstrapRounds),
        ("rss_kib", if rssVals.isEmpty then Json.null else Json.mkObj [
          ("median", toJson (median rssVals)), ("iqr", toJson (iqr rssVals))]),
        ("ratio_to_lean_clang", ratioObj "lean-clang"),
        ("ratio_to_clang_O2", ratioObj "clang-O2"),
        ("ratio_to_clang_O3", ratioObj "clang-O3")
      ])

  let repro := if bm.reproCmd.isEmpty then reproCommand o.rawArgs else bm.reproCmd
  IO.FS.writeFile (out / "k45-samples.json") ((Json.mkObj [
    ("format", Json.str k45SamplesFormat),
    ("build_manifest", Json.str (out / "k45-build.json").toString),
    ("build_manifest_sha256", Json.str manifestSha),
    ("repro_cmd", Json.str repro),
    ("environment", envStart),
    ("environment_end", ← environment o.cpu),
    ("blocks", toJson o.blocks),
    ("warmup", toJson o.warmup),
    ("timeout", optNatJson o.timeout),
    ("bootstrap_resamples", toJson k45BootstrapRounds),
    ("gnu_time", optStrJson gnuTime),
    ("samples", Json.arr samplesJson),
    ("summaries", Json.arr summaries)
  ]).pretty ++ "\n")

private def rowSemanticLabel (row : String) : String :=
  if row == "lean-clang" then "Lean 4 runtime (`leanc -O3`, Lean RC)"
  else if row == "clang-O2" || row == "clang-O3" then
    "C/C++ baseline (`clang`/`clang++`; upstream `nqueens`/`const_fold` intentionally leak)"
  else if row == "gcc-O2" || row == "gcc-O3" then
    "C/C++ baseline (`gcc`/`g++`; upstream `nqueens`/`const_fold` intentionally leak)"
  else if row == "clang-O2-rc" || row == "clang-O3-rc" then
    "Intrusive-RC recycling C++ control (`clang++`, single-threaded non-atomic RC + reuse, zero leaks)"
  else if row == "gcc-O2-rc" || row == "gcc-O3-rc" then
    "Intrusive-RC recycling C++ control (`g++`, single-threaded non-atomic RC + reuse, zero leaks)"
  else if row == "ixcc-on-opt" then
    "IxCC plain-RC (`--rc on --uncertified --opt`: not covered by certificate replay; single-threaded RC with cell recycling)"
  else if row == "ixcc-on" then
    "IxCC plain-RC (`--rc on`, single-threaded RC with cell recycling)"
  else if row == "ixcc-bignat" || row == "ixcc-bignat-opt" then
    "IxCC BigNat immortal (`--uncertified --bignat`: no certificate; arbitrary-precision Nat, bump-allocated region)"
  else if row == "ixcc-opt" then
    "IxCC immortal (`--rc off --uncertified --opt`: not covered by certificate replay; bump-allocated region)"
  else if row.startsWith "ixcc" then
    "IxCC immortal (`--rc off`/`auto`, bump-allocated region)"
  else "custom row"

def cmdReport (manifest : Manifest) (out : FilePath) (o : Options) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (out / "k45-samples.json")))
  let rawSamples ← IO.ofExcept ((json.getObjValD "samples").getArr?)
  let samples ← IO.ofExcept do
    rawSamples.mapM fun s => do
      return (← (← s.getObjVal? "fixture").getStr?, ← (← s.getObjVal? "rung").getStr?,
        ← (← s.getObjVal? "row").getStr?, ← (← s.getObjVal? "block").getNat?,
        ← (← s.getObjVal? "ns").getNat?, (s.getObjValD "rss_kib").getNat?.toOption)
  let buildInfo? ← try some <$> loadBuildManifest out catch _ => pure none
  let buildRecOf (fixture row : String) : Option BuildRecord := do
    let (bm, _) ← buildInfo?
    bm.rows.find? fun r => r.fixture == fixture && r.row == row

  -- Manifest-driven row ordering (zero hardcoded row lists)
  let sampleRowsInOrder : List String :=
    samples.foldl (fun acc (_, _, r, _, _, _) => if acc.contains r then acc else acc ++ [r]) []
  let orderedCandidates : List String :=
    match buildInfo? with
    | some (bm, _) =>
      let extras := sampleRowsInOrder.filter fun r => !bm.rowOrder.contains r
      bm.rowOrder ++ extras
    | none => sampleRowsInOrder
  let allRows := orderedCandidates.filter fun r => samples.any (·.2.2.1 == r)
  let hasLean := allRows.contains "lean-clang"
  let nonLean := allRows.filter (· != "lean-clang")
  let clangBase? : Option String :=
    if allRows.contains "clang-O3" then some "clang-O3"
    else if allRows.contains "clang-O2" then some "clang-O2"
    else none

  let env := json.getObjValD "environment"
  let reproCmd := (json.getObjValD "repro_cmd").getStr?.toOption.getD
    ((buildInfo?.map (·.1.reproCmd)).getD "")
  let manifestSha := (json.getObjValD "build_manifest_sha256").getStr?.toOption.getD
    ((buildInfo?.map (·.2)).getD "unavailable")
  let prov := (buildInfo?.map (·.1.provenance)).getD Json.null
  let gitCommit := (prov.getObjValD "git_commit").getStr?.toOption.getD "unavailable"
  let gitDirty := (prov.getObjValD "git_dirty").getBool?.toOption
  let ixccSha := (prov.getObjValD "ixcc_sha256").getStr?.toOption.getD "unavailable"
  let bignatLibSha? := (prov.getObjValD "bignat_lib_sha256").getStr?.toOption
  let blocksStr := (json.getObjValD "blocks").compress
  let warmupStr := (json.getObjValD "warmup").compress
  let timeoutStr := match (json.getObjValD "timeout").getNat?.toOption with
    | some t => s!"{t}s"
    | none => "none"
  let resamples := (json.getObjValD "bootstrap_resamples").getNat?.toOption.getD k45BootstrapRounds

  let mut lines : Array String := #[
    "# K4/K5 benchmark report (process profile, unhardened)", "",
    "## Provenance & Reproducibility", "",
    s!"- **Repro command:** `{reproCmd}`",
    s!"- **Git commit:** `{gitCommit}`" ++
      (match gitDirty with | some true => " (dirty)" | some false => " (clean)" | none => ""),
    s!"- **Build manifest SHA-256:** `{manifestSha}`",
    s!"- **ixcc SHA-256:** `{ixccSha}`"
  ]
  if let some bnSha := bignatLibSha? then
    lines := lines.push s!"- **BigNat library SHA-256:** `{bnSha}`"
  lines := lines ++ #[
    s!"- **Host:** {env.getObjValD "cpu_model" |>.compress}, worker CPU {env.getObjValD "worker_cpu" |>.compress}, load {env.getObjValD "loadavg" |>.compress}",
    s!"- **Sampling:** {blocksStr} randomized paired blocks, {warmupStr} warmup run(s), timeout {timeoutStr}, {resamples}-resample deterministic percentile bootstrap 95% CIs",
    "",
    "## Wall time (median ms [95% CI], IQR ms)", "",
    "| Fixture | Rung | Args | " ++ " | ".intercalate (allRows.map (s!"{·} ms")) ++ " |",
    "| --- | --- | --- | " ++ " | ".intercalate (allRows.map fun _ => "---:") ++ " |"
  ]

  let mut leanRatioRows : Array String := #[]
  let mut clangRatioRows : Array String := #[]
  let mut rungLeanRatios : Array (String × String × Array Float) := #[]
  let mut rungClangRatios : Array (String × String × Array Float) := #[]
  let mut fixturesJson : Array Json := #[]
  let selectedFixtures := manifest.fixtures.filter o.selects

  for f in selectedFixtures do
    let of (row : String) := samples.filter fun (fx, _, r, _, _, _) => fx == f.name && r == row
    if allRows.all fun r => (of r).isEmpty then continue
    let msVals (row : String) := (of row).map fun (_, _, _, _, ns, _) => ns.toFloat / 1e6
    let rssMed (row : String) : Option Float :=
      let vs := (of row).filterMap fun (_, _, _, _, _, k) => k.map (·.toFloat)
      if vs.isEmpty then none else some (median vs)
    let paired (row base : String) : Array Float :=
      let baseRows := of base
      (of row).filterMap fun (_, _, _, blk, ns, _) =>
        (baseRows.find? fun (_, _, _, b, _, _) => b == blk).map fun (_, _, _, _, bns, _) =>
          ns.toFloat / bns.toFloat
    let wallCell (row : String) : String :=
      let vs := msVals row
      if vs.isEmpty then "-"
      else
        let (lo, hi) := bootstrap vs resamples
        s!"{fmt (median vs) 2} [{fmt lo 2}, {fmt hi 2}] (IQR {fmt (iqr vs) 2})"
    lines := lines.push (s!"| {f.name} | {f.rung} | `{" ".intercalate f.benchArgs}` | " ++
      " | ".intercalate (allRows.map wallCell) ++ " |")

    if hasLean && !(of "lean-clang").isEmpty then
      let cells := nonLean.map fun r =>
        let rs := paired r "lean-clang"
        if rs.isEmpty then "-"
        else
          let (lo, hi) := bootstrap rs resamples
          fmtInterval (median rs) lo hi
      for r in nonLean do
        let rs := paired r "lean-clang"
        unless rs.isEmpty do rungLeanRatios := rungLeanRatios.push (f.rung, r, rs)
      leanRatioRows := leanRatioRows.push (s!"| {f.name} | {f.rung} | " ++ " | ".intercalate cells ++ " |")

    if let some cb := clangBase? then
      if !(of cb).isEmpty then
        let others := allRows.filter (· != cb)
        let cells := others.map fun r =>
          let rs := paired r cb
          if rs.isEmpty then "-"
          else
            let (lo, hi) := bootstrap rs resamples
            fmtInterval (median rs) lo hi
        for r in others do
          let rs := paired r cb
          unless rs.isEmpty do rungClangRatios := rungClangRatios.push (f.rung, r, rs)
        clangRatioRows := clangRatioRows.push (s!"| {f.name} | {f.rung} | " ++ " | ".intercalate cells ++ " |")

    fixturesJson := fixturesJson.push (Json.mkObj [
      ("fixture", Json.str f.name), ("rung", Json.str f.rung), ("bench_args", toJson f.benchArgs),
      ("wall_ms", Json.mkObj (allRows.filterMap fun r =>
        let vs := msVals r
        if vs.isEmpty then none else some (r, statSummaryJson vs resamples))),
      ("median_ms", Json.mkObj (allRows.filterMap fun r =>
        let vs := msVals r
        if vs.isEmpty then none else some (r, toJson (median vs)))),
      ("median_rss_kib", Json.mkObj (allRows.filterMap fun r =>
        (rssMed r).map fun k => (r, toJson k))),
      ("text_bytes", Json.mkObj (allRows.filterMap fun r =>
        (buildRecOf f.name r).bind (·.textBytes) |>.map fun n => (r, toJson n))),
      ("ratio_to_lean_clang", Json.mkObj (nonLean.filterMap fun r =>
        let rs := paired r "lean-clang"
        if rs.isEmpty then none else some (r, statSummaryJson rs resamples))),
      ("ratio_to_clang", match clangBase? with
        | some cb => Json.mkObj ((allRows.filter (· != cb)).filterMap fun r =>
            let rs := paired r cb
            if rs.isEmpty then none else some (r, statSummaryJson rs resamples))
        | none => Json.null)
    ])

  if !leanRatioRows.isEmpty then
    lines := lines ++ #[
      "", "## Paired ratios vs `lean-clang` (< 1 is faster than `lean-clang`)", "",
      "| Fixture | Rung | " ++ " | ".intercalate (nonLean.map (s!"{·} / lean-clang")) ++ " |",
      "| --- | --- | " ++ " | ".intercalate (nonLean.map fun _ => "---:") ++ " |"
    ] ++ leanRatioRows

  if let some cb := clangBase? then
    if !clangRatioRows.isEmpty then
      let others := allRows.filter (· != cb)
      lines := lines ++ #[
        "", s!"## Paired ratios vs `{cb}` (< 1 is faster than `{cb}`)", "",
        "| Fixture | Rung | " ++ " | ".intercalate (others.map (s!"{·} / {cb}")) ++ " |",
        "| --- | --- | " ++ " | ".intercalate (others.map fun _ => "---:") ++ " |"
      ] ++ clangRatioRows

  -- Peak RSS table if available
  if samples.any (·.2.2.2.2.2.isSome) then
    lines := lines ++ #["", "## Peak RSS (KiB)", "",
      "| Fixture | Rung | " ++ " | ".intercalate (allRows.map (s!"{·} KiB")) ++ " |",
      "| --- | --- | " ++ " | ".intercalate (allRows.map fun _ => "---:") ++ " |"]
    for f in selectedFixtures do
      let of (row : String) := samples.filter fun (fx, _, r, _, _, _) => fx == f.name && r == row
      if allRows.all fun r => (of r).isEmpty then continue
      let rssCell (row : String) : String :=
        let vs := (of row).filterMap fun (_, _, _, _, _, k) => k.map (·.toFloat)
        if vs.isEmpty then "-" else fmt (median vs) 0
      lines := lines.push (s!"| {f.name} | {f.rung} | " ++ " | ".intercalate (allRows.map rssCell) ++ " |")

  -- Geometric means per rung
  let mut geoJson : Array Json := #[]
  if !rungLeanRatios.isEmpty then
    lines := lines ++ #["", "## Geometric means by rung (ratio to `lean-clang`)", "",
      "| Rung | Row | Geomean [95%] | Fixtures |",
      "| --- | --- | ---: | ---: |"]
    for rung in ["K1", "K2", "K3", "K4", "K5"] do
      for r in nonLean do
        let groups := rungLeanRatios.filterMap fun (rg, rw, rs) => if rg == rung && rw == r then some rs else none
        unless groups.isEmpty do
          let (pt, lo, hi) := geomeanBootstrap groups resamples
          lines := lines.push s!"| {rung} | {r} | {fmtInterval pt lo hi} | {groups.size} |"
          geoJson := geoJson.push (Json.mkObj [
            ("baseline", Json.str "lean-clang"),
            ("rung", Json.str rung), ("row", Json.str r),
            ("geomean", toJson pt), ("low", toJson lo), ("high", toJson hi),
            ("fixtures", toJson groups.size)])

  if let some cb := clangBase? then
    if !rungClangRatios.isEmpty then
      let others := allRows.filter (· != cb)
      lines := lines ++ #["", s!"## Geometric means by rung (ratio to `{cb}`)", "",
        "| Rung | Row | Geomean [95%] | Fixtures |",
        "| --- | --- | ---: | ---: |"]
      for rung in ["K1", "K2", "K3", "K4", "K5"] do
        for r in others do
          let groups := rungClangRatios.filterMap fun (rg, rw, rs) => if rg == rung && rw == r then some rs else none
          unless groups.isEmpty do
            let (pt, lo, hi) := geomeanBootstrap groups resamples
            lines := lines.push s!"| {rung} | {r} | {fmtInterval pt lo hi} | {groups.size} |"
            geoJson := geoJson.push (Json.mkObj [
              ("baseline", Json.str cb),
              ("rung", Json.str rung), ("row", Json.str r),
              ("geomean", toJson pt), ("low", toJson lo), ("high", toJson hi),
              ("fixtures", toJson groups.size)])

  -- Build metadata & non-built rows
  if let some (bm, _) := buildInfo? then
    let builtRows := bm.rows.filter fun r =>
      r.status == "built" && (selectedFixtures.any (·.name == r.fixture))
    unless builtRows.isEmpty do
      lines := lines ++ #["", "## Build provenance & code size", "",
        "| Fixture | Row | `.text` B | Compile ms | `embed_cert` | Binary SHA-256 (prefix) | Notes |",
        "| --- | --- | ---: | ---: | :---: | --- | --- |"]
      for r in builtRows do
        let szStr := match r.textBytes with | some n => toString n | none => "-"
        let cmStr := match r.compileMs with | some m => fmt m 1 | none => "-"
        let ecStr := if r.embedCert then "yes (`verify-exe`)" else "no"
        let shaStr := match r.binarySha256 with | some h => s!"`{(h.take 12).toString}`" | none => "-"
        let noteStr :=
          match r.harnessSha256, r.detail with
          | some hh, some d => s!"{d}; harness `{(hh.take 12).toString}`"
          | some hh, none => s!"harness `{(hh.take 12).toString}`"
          | none, some d => d
          | none, none => ""
        lines := lines.push s!"| {r.fixture} | {r.row} | {szStr} | {cmStr} | {ecStr} | {shaStr} | {noteStr} |"
    let skipped := bm.rows.filter fun r =>
      r.status != "built" && (selectedFixtures.any (·.name == r.fixture))
    unless skipped.isEmpty do
      lines := lines ++ #["", "## Rows not measured (non-`built` status in `k45-build.json`)", ""]
      for r in skipped do
        lines := lines.push s!"- `{r.row}/{r.fixture}`: {r.status}"

  -- Allocator & semantic comparison notes (explicitly distinguishing leaky vs RC vs immortal)
  lines := lines ++ #["", "## Allocator & Semantic Notes", "",
    "- **Upstream leaky C++ vs intrusive-RC C++ controls vs IxCC immortal/RC:**",
    "  - `clang-O2`, `clang-O3`, `gcc-O2`, `gcc-O3` on `nqueens` (`upstream/nqueens.cpp`) and `const_fold` (`cfold.cpp`) intentionally **do not free memory**, preserving upstream Koka/Perceus benchmark parity.",
    "  - `clang-O2-rc`, `clang-O3-rc`, `gcc-O2-rc`, `gcc-O3-rc` (enabled via `--rc-twins`) compile `nqueens_rc.cpp` and `cfold_rc.cpp`, which implement single-threaded non-atomic intrusive reference counting with Perceus-style in-place unique-cell reuse and zero memory leaks.",
    "  - `ixcc`, `ixcc-off`, `ixcc-opt`, `ixcc-bignat`, `ixcc-bignat-opt` use **IxCC immortal** bump-allocated regions (no per-cell freeing).",
    "  - `ixcc-on`, `ixcc-on-opt` use **IxCC plain-RC** (single-threaded reference counting with cell recycling).",
    "  - `lean-clang` uses Lean 4's compiled C backend (`leanc -O3`) and Lean's reference-counted runtime.",
    "", "| Row | Semantics / Allocator |", "| --- | --- |"]
  for r in allRows do
    lines := lines.push s!"| `{r}` | {rowSemanticLabel r} |"

  IO.FS.writeFile (out / "k45-report.md") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out / "k45-report.json") ((Json.mkObj [
    ("format", Json.str "ixcc/k45-report/2"),
    ("build_manifest_sha256", Json.str manifestSha),
    ("repro_cmd", Json.str reproCmd),
    ("provenance", prov),
    ("environment", env),
    ("rows", toJson allRows),
    ("fixtures", Json.arr fixturesJson),
    ("geomeans", Json.arr geoJson)
  ]).pretty ++ "\n")
  IO.println s!"wrote {out / "k45-report.md"}"

/-! ## Pure-Lean negative regression tests (`BenchK45 self-test`) -/

private def expectErrorContaining (label needle : String) (act : IO Unit) : IO Unit := do
  let caught ← try
      act
      pure none
    catch e =>
      pure (some (toString e))
  match caught with
  | none =>
    throw (IO.userError s!"SELF-TEST FAIL ({label}): expected error containing '{needle}', but succeeded")
  | some msg =>
    unless hasSubstr msg needle do
      throw (IO.userError s!"SELF-TEST FAIL ({label}): error '{msg}' did not contain '{needle}'")

/-- Run pure-Lean negative regression tests verifying stale-binary invalidation
(Test A) and SHA-256 tamper detection in both `cmdCheck` and `cmdMeasure` (Test B). -/
def cmdSelfTest (manifest : Manifest) (root : FilePath) (outOpt : Option FilePath) (o : Options) : IO Unit := do
  let stamp ← IO.monoNanosNow
  let testRoot := outOpt.getD (FilePath.mk s!"/tmp/bench-k45-selftest-{stamp}")
  IO.FS.createDirAll testRoot
  let testRoot ← IO.FS.realPath testRoot

  let some blake3Fx := manifest.fixtures.find? (·.name == "blake3")
    | throw (IO.userError "self-test: fixture 'blake3' not found in manifest")
  let some cfoldFx := manifest.fixtures.find? (·.name == "const_fold")
    | throw (IO.userError "self-test: fixture 'const_fold' not found in manifest")
  let some fibFx := manifest.fixtures.find? (·.name == "fib")
    | throw (IO.userError "self-test: fixture 'fib' not found in manifest")

  -- =========================================================================
  -- Test A1: Plant stale dummy binary + .o + .cert, run failing/object-only
  -- buildIxccRow, assert stale binary was unlinked and cmdCheck/cmdMeasure
  -- refuse to run or measure it.
  -- =========================================================================
  let dirA := testRoot / "testA"
  let specA : IxccRowSpec := { rowName := "ixcc", rcFlag := "off", opt := false, bignat := false }
  let liveCfold ← match o.closures with
    | some cdir =>
      pure ((← (cdir / "const_fold.ixe").pathExists) && (← (FilePath.mk (o.ixcc.headD "")).pathExists))
    | none => pure false
  let targetFxA := if liveCfold then cfoldFx else blake3Fx
  IO.FS.createDirAll (dirA / "bin" / "ixcc")
  IO.FS.createDirAll (dirA / "ixcc" / "ixcc")
  let staleBin := binPath dirA "ixcc" targetFxA
  let staleObj := objPath dirA "ixcc" targetFxA
  let staleCert := dirA / "ixcc" / "ixcc" / s!"{targetFxA.name}.cert.json"
  IO.FS.writeFile staleBin "#!/bin/sh\necho STALE_DUMMY\n"
  IO.FS.writeFile staleObj "STALE_OBJECT"
  IO.FS.writeFile staleCert "{}"
  unless (← staleBin.pathExists) && (← staleObj.pathExists) && (← staleCert.pathExists) do
    throw (IO.userError "self-test Test A: failed to plant stale artifacts")

  let (recA, modeLabel) ←
    if liveCfold then
      let oReal : Options := { o with blake3Harness := false, embedCert := false }
      let some r ← buildIxccRow oReal dirA specA targetFxA
        | throw (IO.userError "self-test Test A: buildIxccRow returned none")
      unless r.status.startsWith "object-only" do
        throw (IO.userError s!"self-test Test A FAIL: expected object-only status on const_fold, got '{r.status}'")
      pure (r, "live object-only ixcc build on const_fold")
    else
      let fakeClos := dirA / "fake-closures"
      IO.FS.createDirAll fakeClos
      IO.FS.writeFile (fakeClos / s!"{targetFxA.name}.ixe") "not-a-valid-ixe"
      IO.FS.writeFile (fakeClos / s!"{targetFxA.name}.equations.json") "{}"
      let oFail : Options := { o with closures := some fakeClos, ixcc := ["false"], blake3Harness := false }
      let some r ← buildIxccRow oFail dirA specA targetFxA
        | throw (IO.userError "self-test Test A: buildIxccRow returned none")
      pure (r, s!"failing buildIxccRow on {targetFxA.name}")

  if ← staleBin.pathExists then
    throw (IO.userError s!"self-test Test A FAIL: stale binary {staleBin} still exists after {modeLabel}!")
  if ← staleCert.pathExists then
    throw (IO.userError s!"self-test Test A FAIL: stale cert {staleCert} still exists after {modeLabel}!")
  if recA.status == "built" then
    throw (IO.userError s!"self-test Test A FAIL: expected non-built status, got 'built'")

  -- Write manifest containing ONLY this non-built row, AND re-plant a rogue dummy
  -- binary on disk to verify cmdCheck and cmdMeasure NEVER fall back to `.pathExists`!
  let manifestA := Json.mkObj [
    ("format", Json.str k45BuildFormat),
    ("provenance", Json.mkObj [("ixcc_cmd", toJson o.ixcc), ("repro_cmd", Json.str "self-test")]),
    ("row_order", toJson ["ixcc"]),
    ("rows", Json.arr #[recA.toJson])
  ]
  IO.FS.writeFile (dirA / "k45-build.json") (manifestA.pretty ++ "\n")
  IO.FS.writeFile staleBin "#!/bin/sh\necho ROGUE_UNMANIFESTED\n"
  let oCheckA : Options := { o with fixtures := some [targetFxA.name], blocks := 1, warmup := 0 }
  expectErrorContaining "Test A cmdCheck refuses non-built row" "no built rows"
    (cmdCheck manifest root dirA oCheckA)
  expectErrorContaining "Test A cmdMeasure refuses non-built row" "no built rows"
    (cmdMeasure manifest dirA oCheckA)

  -- Test A2: Missing k45-build.json must be refused even when a binary exists on disk
  let dirMissing := testRoot / "testA_missing_manifest"
  IO.FS.createDirAll (dirMissing / "bin" / "clang-O2")
  IO.FS.writeFile (binPath dirMissing "clang-O2" fibFx) "ROGUE"
  let oFib : Options := { o with fixtures := some ["fib"], blocks := 1, warmup := 0 }
  expectErrorContaining "Test A2 cmdCheck refuses missing manifest" "missing build manifest"
    (cmdCheck manifest root dirMissing oFib)
  expectErrorContaining "Test A2 cmdMeasure refuses missing manifest" "missing build manifest"
    (cmdMeasure manifest dirMissing oFib)
  IO.println s!"PASS Test A: stale-binary invalidation ({modeLabel}) & non-built/missing manifest refusal"

  -- =========================================================================
  -- Test B: Real build of `fib`, untampered check passes, then mutate 1 byte
  -- of built `clang-O2` binary and assert BOTH cmdCheck and cmdMeasure fail
  -- with an explicit SHA-256 mismatch error.
  -- =========================================================================
  let dirB := testRoot / "testB"
  let oBuildB : Options := {
    rungs := ["K1"],
    fixtures := some ["fib"],
    cpu := o.cpu,
    blocks := 1,
    warmup := 0,
    timeout := o.timeout,
    closures := none,
    gcc := false,
    opt := false,
    bignat := false,
    embedCert := false,
    blake3Harness := false,
    rcTwins := false,
    rawArgs := ["self-test"]
  }
  cmdBuild manifest root dirB oBuildB
  cmdCheck manifest root dirB oBuildB
  let targetB := binPath dirB "clang-O2" fibFx
  let bytes ← IO.FS.readBinFile targetB
  if bytes.isEmpty then
    throw (IO.userError s!"self-test Test B: built binary {targetB} is empty")
  let lastIdx := bytes.size - 1
  let mutated := bytes.set! lastIdx (bytes[lastIdx]! ^^^ 0xFF)
  IO.FS.writeBinFile targetB mutated
  expectErrorContaining "Test B cmdCheck detects 1-byte mutation" "SHA-256 mismatch"
    (cmdCheck manifest root dirB oBuildB)
  expectErrorContaining "Test B cmdMeasure detects 1-byte mutation" "SHA-256 mismatch"
    (cmdMeasure manifest dirB oBuildB)
  IO.println s!"PASS Test B: 1-byte binary mutation rejected with SHA-256 mismatch in both cmdCheck and cmdMeasure"
  IO.println s!"bench-k45 self-test: ALL PASSED (work dir: {testRoot})"

/-! ## CLI parsing & entry point -/

def usage : String :=
  "usage: bench-k45 COMMAND [OPTIONS] [OUT]\n\
   \n\
   run       [--rungs K4,K5] [--fixtures a,b] [--cpu N] [--blocks B] [--warmup W]\n\
   \x20         [--timeout SEC] [--ixcc CMD] [--closures DIR] [--rc off|on|auto|both]\n\
   \x20         [--opt] [--bignat] [--bignat-lib FILE] [--gcc] [--embed-cert]\n\
   \x20         [--blake3-harness] [--rc-twins] [--stack BYTES] [--region BYTES] OUT\n\
   build     [same build options] OUT\n\
   check     [--rungs K4,K5] [--fixtures a,b] [--timeout SEC] [--ixcc CMD] OUT\n\
   measure   [--rungs K4,K5] [--fixtures a,b] [--cpu N] [--blocks B] [--warmup W]\n\
   \x20         [--timeout SEC] OUT\n\
   report    [--rungs K4,K5] [--fixtures a,b] OUT\n\
   self-test [--cpu N] [--ixcc CMD] [--closures DIR] [OUT]\n\
   \n\
   Run from IxCC/benchmarks/runner; reads ../fixtures/manifest.json."

def boolFlags : List String :=
  ["opt", "bignat", "gcc", "embed-cert", "blake3-harness", "rc-twins"]

def valueFlags : List String :=
  ["rungs", "fixtures", "cpu", "blocks", "warmup", "timeout",
   "ixcc", "closures", "rc", "bignat-lib", "stack", "region"]

def parseFlags : List String → Except String (List (String × String) × List String × Option String)
  | [] => .ok ([], [], none)
  | arg :: rest =>
    if arg.startsWith "--" then
      let name := (arg.drop 2).toString
      if boolFlags.contains name then do
        let (vopts, bopts, out) ← parseFlags rest
        return (vopts, name :: bopts, out)
      else if valueFlags.contains name then
        match rest with
        | value :: rest' => do
          let (vopts, bopts, out) ← parseFlags rest'
          return ((name, value) :: vopts, bopts, out)
        | [] => .error s!"option --{name} requires a value\n{usage}"
      else
        .error s!"unknown option --{name}\n{usage}"
    else do
      let (vopts, bopts, out) ← parseFlags rest
      if out.isSome then .error usage
      return (vopts, bopts, some arg)

end BenchK45

open BenchK45 Runner System in
def main (args : List String) : IO UInt32 := do
  let root : FilePath := "../fixtures"
  try
    if args == ["--help"] || args == ["-h"] then
      IO.println usage
      return 0
    let manifest ← Manifest.load (root / "manifest.json")
    let (command, rest) ← match args with
      | c :: r => pure (c, r)
      | [] => throw (IO.userError usage)
    let (vopts, bopts, out?) ← IO.ofExcept (parseFlags rest |>.mapError IO.userError)
    let get (name : String) : Option String := (vopts.find? (·.1 == name)).map (·.2)
    let hasFlag (name : String) : Bool := bopts.contains name
    let nat (name : String) (default : Nat) : IO Nat :=
      match get name with
      | none => pure default
      | some v => match v.toNat? with
        | some n => pure n
        | none => throw (IO.userError s!"--{name} expects a number, got {v}")
    let optNat (name : String) : IO (Option Nat) :=
      match get name with
      | none => pure none
      | some v => match v.toNat? with
        | some n => pure (some n)
        | none => throw (IO.userError s!"--{name} expects a number, got {v}")
    let rcMode := (get "rc").getD "off"
    unless ["off", "on", "auto", "both"].contains rcMode do
      throw (IO.userError s!"unknown --rc mode '{rcMode}' (expected off|on|auto|both)")
    let bignat := hasFlag "bignat"
    let bignatLib := (get "bignat-lib").map FilePath.mk
    if bignatLib.isSome && !bignat then
      throw (IO.userError "--bignat-lib requires --bignat")
    let o : BenchK45.Options := {
      rungs := ((get "rungs").map (·.splitOn ",")).getD ["K4", "K5"]
      fixtures := (get "fixtures").map (·.splitOn ",")
      cpu := ← nat "cpu" 2
      blocks := ← nat "blocks" 10
      warmup := ← nat "warmup" 1
      timeout := ← optNat "timeout"
      ixcc := ((get "ixcc").map (·.splitOn " " |>.filter (!·.isEmpty))).getD
        ["../../.lake/build/bin/ixcc"]
      ixccExplicit := (get "ixcc").isSome
      closures := (get "closures").map FilePath.mk
      rcMode
      rcExplicit := (get "rc").isSome
      opt := hasFlag "opt"
      bignat
      bignatLib
      gcc := hasFlag "gcc"
      embedCert := hasFlag "embed-cert"
      blake3Harness := hasFlag "blake3-harness"
      rcTwins := hasFlag "rc-twins"
      stackBytes := ← optNat "stack"
      regionBytes := ← optNat "region"
      rawArgs := args
    }
    if command == "self-test" then
      cmdSelfTest manifest root out? o
      return 0
    let some out := out? | throw (IO.userError usage)
    match command with
    | "build" => cmdBuild manifest root out o
    | "check" => cmdCheck manifest root out o
    | "measure" => cmdMeasure manifest out o
    | "report" => cmdReport manifest out o
    | "run" =>
      cmdBuild manifest root out o
      cmdCheck manifest root out o
      cmdMeasure manifest out o
      cmdReport manifest out o
    | _ => throw (IO.userError usage)
    return 0
  catch e =>
    IO.eprintln s!"bench-k45: {e}"
    return 1
