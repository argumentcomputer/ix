import Runner.Build
import Runner.Measure
import Runner.Report
import Runner.Stats

/-! Pure-Lean K4/K5 (and full K1–K5) apples-to-apples benchmark runner.

Builds unhardened `lean-clang`, `clang-O2`, `clang-O3` (with automatic GMP
resolution for C+GMP twins), and optional `ixcc` standalone executables
(`--rc off|on|auto|both` from `--closures DIR`), checks outputs against
`expected.txt` and `bench_expected`, times randomized paired blocks pinned to
`--cpu`, records peak RSS and `.text` size where available, and writes
`k45-report.md` and `k45-report.json`. -/

namespace BenchK45

open Lean System Runner

structure Options where
  rungs : List String := ["K4", "K5"]
  fixtures : Option (List String) := none
  cpu : Nat := 2
  blocks : Nat := 10
  ixcc : List String := ["../../.lake/build/bin/ixcc"]
  closures : Option FilePath := none
  rcMode : String := "off"
  stackBytes : Option Nat := none
  regionBytes : Option Nat := none

def Options.selects (o : Options) (f : Fixture) : Bool :=
  match o.fixtures with
  | some names => names.contains f.name
  | none => o.rungs.contains f.rung

def allPossibleRows : List String :=
  ["lean-clang", "clang-O2", "clang-O3", "ixcc", "ixcc-off", "ixcc-on"]

def binPath (out : FilePath) (row : String) (f : Fixture) : FilePath :=
  out / "bin" / row / f.name

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

/-- Run `bin args` pinned to `cpu`, returning `(stdout, wallNanos, peakRssKiB?)`. -/
def runTimed (gnuTime : Option String) (cpu : Nat) (bin : FilePath) (args : List String) :
    IO (String × Nat × Option Nat) := do
  match gnuTime with
  | some t =>
    let start ← IO.monoNanosNow
    let out ← IO.Process.output {
      cmd := t
      args := (#["-f", "%M", "taskset", "-c", toString cpu, bin.toString] ++ args.toArray)
    }
    let stop ← IO.monoNanosNow
    if out.exitCode != 0 then
      throw (IO.userError s!"{bin} {" ".intercalate args} exited {out.exitCode}:\n{out.stderr}")
    let lines := (out.stderr.trimAscii.toString.splitOn "\n").filter (!·.isEmpty)
    let rss := lines.getLast?.bind (fun s => s.trimAscii.toString.toNat?)
    return (out.stdout, stop - start, rss)
  | none =>
    let start ← IO.monoNanosNow
    let out ← IO.Process.output {
      cmd := "taskset"
      args := (#["-c", toString cpu, bin.toString] ++ args.toArray)
    }
    let stop ← IO.monoNanosNow
    if out.exitCode != 0 then
      throw (IO.userError s!"{bin} {" ".intercalate args} exited {out.exitCode}:\n{out.stderr}")
    return (out.stdout, stop - start, none)

/-- Build an `ixcc` standalone executable (`--exe`) when a frozen closure exists. -/
def buildIxccRow (o : Options) (out : FilePath) (rowName rcFlag : String) (f : Fixture) :
    IO (Option (String × Option Nat × Float)) := do
  let some dir := o.closures | return none
  let closure := dir / s!"{f.name}.ixe"
  let equations := dir / s!"{f.name}.equations.json"
  unless ← closure.pathExists do
    return some (s!"unavailable: no closure {closure}", none, 0.0)
  let target := binPath out rowName f
  IO.FS.createDirAll (target.parent.getD out)
  let objDir := out / "ixcc" / rowName
  IO.FS.createDirAll objDir
  let obj := objDir / s!"{f.name}.o"
  let cmd := o.ixcc.headD "ixcc"
  let lead := o.ixcc.drop 1
  let layoutArgs : List String :=
    (match o.stackBytes with | some s => ["--stack", toString s] | none => []) ++
    (match o.regionBytes with | some r => ["--region", toString r] | none => [])
  let args := lead ++ ["compile", closure.toString, "--equations", equations.toString,
    "--rc", rcFlag, "-o", obj.toString, "--exe", target.toString] ++ layoutArgs ++ ["--stats"]
  let start ← IO.monoNanosNow
  let res ← IO.Process.output { cmd, args := args.toArray }
  let stop ← IO.monoNanosNow
  let wallMs := (stop - start).toFloat / 1e6
  if res.exitCode == 0 then
    IO.FS.writeFile (objDir / s!"{f.name}.stats.txt") res.stdout
    let sz ← textSizeBytes obj
    return some ("built", sz, wallMs)
  else
    -- Fall back to object-only compile for non-exe result shapes (e.g. ByteArray/tuples)
    let objArgs := lead ++ ["compile", closure.toString, "--equations", equations.toString,
      "--rc", rcFlag, "-o", obj.toString, "--stats"]
    let objRes ← IO.Process.output { cmd, args := objArgs.toArray }
    if objRes.exitCode == 0 then
      IO.FS.writeFile (objDir / s!"{f.name}.stats.txt") objRes.stdout
      let sz ← textSizeBytes obj
      return some (s!"object-only ({res.stderr.trimAscii.toString})", sz, wallMs)
    return some (s!"declined: {res.stderr.trimAscii.toString}", none, wallMs)

def cmdBuild (manifest : Manifest) (root out : FilePath) (o : Options) : IO Unit := do
  IO.FS.createDirAll out
  let out ← IO.FS.realPath out
  let fixtures := manifest.fixtures.filter o.selects
  let gmpCache ← IO.mkRef (none : Option (List String))
  let getGmp : IO (List String) := do
    match ← gmpCache.get with
    | some fs => pure fs
    | none =>
      let fs ← resolveGmpFlags
      gmpCache.set (some fs)
      pure fs
  let mut records : Array Json := #[]
  for f in fixtures do
    -- lean-clang (unhardened)
    let c := out / "c" / s!"{f.name}.c"
    IO.FS.createDirAll (c.parent.getD out)
    let leanTarget := binPath out "lean-clang" f
    IO.FS.createDirAll (leanTarget.parent.getD out)
    let subst := [("src", f.lean), ("c", c.toString), ("out", leanTarget.toString)]
    let compile := expand manifest.leanCompile subst
    let _ ← Runner.run compile.head! compile.tail! (cwd := some root)
    let link := expand manifest.leanLink subst
    let linkArgs :=
      if link.tail!.any (fun w => w == "-O3" || w == "-O2") then
        link.tail!.flatMap fun w => if w == "-O3" || w == "-O2" then w :: omitFpFlags else [w]
      else
        omitFpFlags ++ link.tail!
    let _ ← Runner.run link.head! linkArgs (env := ccEnv)
    let leanText ← textSizeBytes leanTarget
    records := records.push (Json.mkObj [
      ("fixture", Json.str f.name), ("rung", Json.str f.rung), ("row", Json.str "lean-clang"),
      ("status", Json.str "built"),
      ("text_bytes", match leanText with | some n => toJson n | none => Json.null)])

    -- clang-O2 and clang-O3 (unhardened, with automatic GMP flags if needed)
    for (rowName, level) in [("clang-O2", "-O2"), ("clang-O3", "-O3")] do
      let target := binPath out rowName f
      IO.FS.createDirAll (target.parent.getD out)
      let command := expand f.twin.compile
        [("src", (root / f.twin.path).toString), ("out", target.toString)]
      let args :=
        if command.tail!.any (fun w => w == "-O2" || w == "-O3") then
          command.tail!.flatMap fun w => if w == "-O2" || w == "-O3" then level :: omitFpFlags else [w]
        else
          level :: omitFpFlags ++ command.tail!
      let args ← if args.contains "-lgmp" then do
          let gmp ← getGmp
          pure (args.flatMap fun w => if w == "-lgmp" then gmp ++ [w] else [w])
        else pure args
      let _ ← Runner.run command.head! args (env := ccEnv)
      let sz ← textSizeBytes target
      records := records.push (Json.mkObj [
        ("fixture", Json.str f.name), ("rung", Json.str f.rung), ("row", Json.str rowName),
        ("status", Json.str "built"),
        ("text_bytes", match sz with | some n => toJson n | none => Json.null)])

    -- optional ixcc row(s)
    if o.closures.isSome then
      let modes :=
        if o.rcMode == "both" then [("ixcc-off", "off"), ("ixcc-on", "on")]
        else [("ixcc", o.rcMode)]
      for (rowName, rcFlag) in modes do
        if let some (status, sz, compileMs) ← buildIxccRow o out rowName rcFlag f then
          records := records.push (Json.mkObj [
            ("fixture", Json.str f.name), ("rung", Json.str f.rung), ("row", Json.str rowName),
            ("status", Json.str status), ("compile_ms", toJson compileMs),
            ("text_bytes", match sz with | some n => toJson n | none => Json.null)])
    IO.println s!"built {f.name} ({f.rung})"

  IO.FS.writeFile (out / "k45-build.json") ((Json.mkObj [
    ("format", Json.str "ixcc/benchmark-k45-build/1"),
    ("rungs", toJson o.rungs),
    ("fixtures", Json.arr (fixtures.map (Json.str ·.name))),
    ("cc_env", Json.str "NIX_HARDENING_ENABLE="),
    ("omit_fp_flags", toJson omitFpFlags),
    ("rows", Json.arr records)]).pretty ++ "\n")

def cmdCheck (manifest : Manifest) (root out : FilePath) (o : Options) : IO Unit := do
  let fixtures := manifest.fixtures.filter o.selects
  let rows := allPossibleRows
  let mut checked := 0
  let mut failures := 0
  for f in fixtures do
    let expectedTest ← IO.FS.readFile (root / f.expected)
    for row in rows do
      let bin := binPath out row f
      unless ← bin.pathExists do continue
      let outTest ← Runner.run bin.toString f.testArgs
      checked := checked + 1
      if outTest.stdout != expectedTest then
        failures := failures + 1
        IO.eprintln s!"FAIL test {row}/{f.name}: got {outTest.stdout.trimAscii}, expected {expectedTest.trimAscii}"
      if let some expectedBench := f.benchExpected then
        let outBench ← Runner.run bin.toString f.benchArgs
        checked := checked + 1
        if outBench.stdout != expectedBench then
          failures := failures + 1
          IO.eprintln s!"FAIL bench {row}/{f.name}: got {outBench.stdout.trimAscii}, expected {expectedBench.trimAscii}"
  if failures > 0 then throw (IO.userError s!"{failures} of {checked} K4/K5 checks failed")
  IO.println s!"checked {checked} K4/K5 outputs (all pass)"

def cmdMeasure (manifest : Manifest) (out : FilePath) (o : Options) : IO Unit := do
  let fixtures := manifest.fixtures.filter o.selects
  let rows := allPossibleRows
  let gnuTime ← findGnuTime
  let envStart ← environment o.cpu
  let mut samples : Array Json := #[]
  for (f, idx) in fixtures.toList.zipIdx do
    let built ← rows.filterM fun r => (binPath out r f).pathExists
    if built.isEmpty then continue
    -- one untimed warmup run per built row
    for r in built do
      let _ ← runTimed gnuTime o.cpu (binPath out r f) f.benchArgs
    for block in [:o.blocks] do
      let mut outputs : List String := []
      for r in shuffle (block * 1000 + idx) built do
        let (stdout, ns, rss) ← runTimed gnuTime o.cpu (binPath out r f) f.benchArgs
        outputs := stdout :: outputs
        samples := samples.push (Json.mkObj [
          ("fixture", Json.str f.name), ("rung", Json.str f.rung), ("row", Json.str r),
          ("block", toJson block), ("ns", toJson ns),
          ("rss_kib", match rss with | some k => toJson k | none => Json.null)])
      unless outputs.all (· == outputs.headD "") do
        throw (IO.userError s!"{f.name}: rows disagree in block {block}")
      if let some want := f.benchExpected then
        unless outputs.headD "" == want do
          throw (IO.userError s!"{f.name}: output differs from bench_expected in block {block}")
    IO.println s!"measured {f.name} ({f.rung}): {o.blocks} blocks × {built.length} rows"
  IO.FS.writeFile (out / "k45-samples.json") ((Json.mkObj [
    ("format", Json.str "ixcc/benchmark-k45-samples/1"),
    ("environment", envStart),
    ("environment_end", ← environment o.cpu),
    ("blocks", toJson o.blocks),
    ("gnu_time", match gnuTime with | some t => Json.str t | none => Json.null),
    ("samples", Json.arr samples)]).pretty ++ "\n")

def cmdReport (manifest : Manifest) (out : FilePath) (o : Options) : IO Unit := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile (out / "k45-samples.json")))
  let rawSamples ← IO.ofExcept ((json.getObjValD "samples").getArr?)
  let samples ← IO.ofExcept do
    rawSamples.mapM fun s => do
      return (← (← s.getObjVal? "fixture").getStr?, ← (← s.getObjVal? "rung").getStr?,
        ← (← s.getObjVal? "row").getStr?, ← (← s.getObjVal? "block").getNat?,
        ← (← s.getObjVal? "ns").getNat?, (s.getObjValD "rss_kib").getNat?.toOption)
  let buildJson? ← try some <$> IO.ofExcept (Json.parse (← IO.FS.readFile (out / "k45-build.json")))
    catch _ => pure none
  let textBytesOf (fixture row : String) : Option Nat := do
    let bj ← buildJson?
    let arr ← (bj.getObjValD "rows").getArr?.toOption
    let entry ← arr.find? fun e =>
      e.getObjValD "fixture" == Json.str fixture && e.getObjValD "row" == Json.str row
    (entry.getObjValD "text_bytes").getNat?.toOption
  let env := json.getObjValD "environment"
  let allRows := ["lean-clang", "clang-O2", "clang-O3", "ixcc", "ixcc-off", "ixcc-on"].filter fun r =>
    samples.any (·.2.2.1 == r)
  let others := allRows.filter (· != "lean-clang")
  let mut lines : Array String := #[
    "# K4/K5 benchmark report (process profile, unhardened)", "",
    s!"Host: {env.getObjValD "cpu_model" |>.compress}, worker CPU {env.getObjValD "worker_cpu" |>.compress}, load {env.getObjValD "loadavg" |>.compress}.",
    s!"Blocks per fixture: {json.getObjValD "blocks" |>.compress}. Ratio = row / lean-clang (< 1 is faster than lean-clang); 95% paired percentile-bootstrap intervals.", "",
    "| Fixture | Rung | Args | " ++ " | ".intercalate (allRows.map (s!"{·} ms")) ++ " | " ++
      " | ".intercalate (others.map (s!"{·} / lean-clang")) ++ " |",
    "| --- | --- | --- | " ++ " | ".intercalate ((allRows ++ others).map fun _ => "---:") ++ " |"]
  let mut rungRatios : Array (String × String × Array Float) := #[]
  let mut fixturesJson : Array Json := #[]
  for f in manifest.fixtures.filter o.selects do
    let of (row : String) := samples.filter fun (fx, _, r, _, _, _) => fx == f.name && r == row
    let base := of "lean-clang"
    if base.isEmpty then continue
    let ms (row : String) := median ((of row).map fun (_, _, _, _, ns, _) => ns.toFloat / 1e6)
    let rssMed (row : String) : Option Float :=
      let vs := (of row).filterMap fun (_, _, _, _, _, k) => k.map (·.toFloat)
      if vs.isEmpty then none else some (median vs)
    let paired (row : String) : Array Float := (of row).filterMap fun (_, _, _, blk, ns, _) =>
      (base.find? fun (_, _, _, b, _, _) => b == blk).map fun (_, _, _, _, bns, _) => ns.toFloat / bns.toFloat
    let ratioCell (row : String) : String :=
      let rs := paired row
      if rs.isEmpty then "-"
      else
        let (lo, hi) := bootstrap rs
        fmtInterval (median rs) lo hi
    for r in others do
      let rs := paired r
      unless rs.isEmpty do rungRatios := rungRatios.push (f.rung, r, rs)
    lines := lines.push (s!"| {f.name} | {f.rung} | `{" ".intercalate f.benchArgs}` | " ++
      " | ".intercalate (allRows.map fun r => if (of r).isEmpty then "-" else fmt (ms r) 2) ++ " | " ++
      " | ".intercalate (others.map ratioCell) ++ " |")
    fixturesJson := fixturesJson.push (Json.mkObj [
      ("fixture", Json.str f.name), ("rung", Json.str f.rung), ("bench_args", toJson f.benchArgs),
      ("median_ms", Json.mkObj (allRows.filterMap fun r =>
        if (of r).isEmpty then none else some (r, toJson (ms r)))),
      ("median_rss_kib", Json.mkObj (allRows.filterMap fun r =>
        (rssMed r).map fun k => (r, toJson k))),
      ("text_bytes", Json.mkObj (allRows.filterMap fun r =>
        (textBytesOf f.name r).map fun n => (r, toJson n))),
      ("ratio_to_lean_clang", Json.mkObj (others.filterMap fun r =>
        let rs := paired r
        if rs.isEmpty then none else
        let (lo, hi) := bootstrap rs
        some (r, Json.mkObj [("median", toJson (median rs)), ("low", toJson lo), ("high", toJson hi)])))])

  -- Peak RSS table if available
  if samples.any (·.2.2.2.2.2.isSome) then
    lines := lines ++ #["", "## Peak RSS (KiB)", "",
      "| Fixture | Rung | " ++ " | ".intercalate (allRows.map (s!"{·} KiB")) ++ " |",
      "| --- | --- | " ++ " | ".intercalate (allRows.map fun _ => "---:") ++ " |"]
    for f in manifest.fixtures.filter o.selects do
      let of (row : String) := samples.filter fun (fx, _, r, _, _, _) => fx == f.name && r == row
      if (of "lean-clang").isEmpty then continue
      let rssCell (row : String) : String :=
        let vs := (of row).filterMap fun (_, _, _, _, _, k) => k.map (·.toFloat)
        if vs.isEmpty then "-" else fmt (median vs) 0
      lines := lines.push (s!"| {f.name} | {f.rung} | " ++ " | ".intercalate (allRows.map rssCell) ++ " |")

  -- Geometric means per rung
  lines := lines ++ #["", "## Geometric means by rung (ratio to lean-clang)", "",
    "| Rung | Row | Geomean [95%] | Fixtures |",
    "| --- | --- | ---: | ---: |"]
  let mut geoJson : Array Json := #[]
  for rung in ["K1", "K2", "K3", "K4", "K5"] do
    for r in others do
      let groups := rungRatios.filterMap fun (rg, rw, rs) => if rg == rung && rw == r then some rs else none
      unless groups.isEmpty do
        let (pt, lo, hi) := geomeanBootstrap groups
        lines := lines.push s!"| {rung} | {r} | {fmtInterval pt lo hi} | {groups.size} |"
        geoJson := geoJson.push (Json.mkObj [
          ("rung", Json.str rung), ("row", Json.str r),
          ("geomean", toJson pt), ("low", toJson lo), ("high", toJson hi),
          ("fixtures", toJson groups.size)])

  IO.FS.writeFile (out / "k45-report.md") ("\n".intercalate lines.toList ++ "\n")
  IO.FS.writeFile (out / "k45-report.json") ((Json.mkObj [
    ("environment", env), ("fixtures", Json.arr fixturesJson), ("geomeans", Json.arr geoJson)]).pretty ++ "\n")
  IO.println s!"wrote {out / "k45-report.md"}"

def usage : String :=
  "usage: bench-k45 COMMAND [OPTIONS] OUT\n\
   \n\
   run      [--rungs K4,K5] [--fixtures a,b] [--cpu N] [--blocks B]\n\
   \x20        [--ixcc CMD] [--closures DIR] [--rc off|on|auto|both]\n\
   \x20        [--stack BYTES] [--region BYTES]\n\
   build    [same build options]\n\
   check    [--rungs K4,K5] [--fixtures a,b]\n\
   measure  [--rungs K4,K5] [--fixtures a,b] [--cpu N] [--blocks B]\n\
   report   [--rungs K4,K5] [--fixtures a,b]\n\
   \n\
   Run from IxCC/benchmarks/runner; reads ../fixtures/manifest.json."

def parseFlags : List String → Except String (List (String × String) × Option String)
  | [] => .ok ([], none)
  | flag :: value :: rest =>
    if flag.startsWith "--" then do
      let (opts, out) ← parseFlags rest
      return ((flag.drop 2 |>.toString, value) :: opts, out)
    else do
      let (opts, out) ← parseFlags (value :: rest)
      if out.isSome then throw usage
      return (opts, some flag)
  | [last] => if last.startsWith "--" then .error usage else .ok ([], some last)

end BenchK45

open BenchK45 Runner System in
def main (args : List String) : IO UInt32 := do
  let root : FilePath := "../fixtures"
  try
    let manifest ← Manifest.load (root / "manifest.json")
    let (command, rest) ← match args with
      | c :: r => pure (c, r)
      | [] => throw (IO.userError usage)
    let (opts, out) ← IO.ofExcept (parseFlags rest |>.mapError IO.userError)
    let some out := out | throw (IO.userError usage)
    let get (name : String) : Option String := (opts.find? (·.1 == name)).map (·.2)
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
    let known := ["rungs", "fixtures", "cpu", "blocks", "ixcc", "closures", "rc", "stack", "region"]
    for (name, _) in opts do
      unless known.contains name do throw (IO.userError s!"unknown option --{name}\n{usage}")
    let o : BenchK45.Options := {
      rungs := ((get "rungs").map (·.splitOn ",")).getD ["K4", "K5"]
      fixtures := (get "fixtures").map (·.splitOn ",")
      cpu := ← nat "cpu" 2
      blocks := ← nat "blocks" 10
      ixcc := ((get "ixcc").map (·.splitOn " " |>.filter (!·.isEmpty))).getD
        ["../../.lake/build/bin/ixcc"]
      closures := (get "closures").map FilePath.mk
      rcMode := (get "rc").getD "off"
      stackBytes := ← optNat "stack"
      regionBytes := ← optNat "region"
    }
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
