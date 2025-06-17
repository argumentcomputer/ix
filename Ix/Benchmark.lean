import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Ixon.Expr
import Ix.Address
import Batteries

open Batteries (RBMap)

/--
Benchmarking library modeled after Criterion in Haskell and Rust

Limitations:
- Measures time in nanoseconds using `IO.monoNanosNow`, which is less precise than the picoseconds used in Criterion.rs
-/

-- This prevents inline optimization for benchmarking, but doesn't work if the result is never used
--@[never_extract, noinline]
--def blackBox : α → α := id

-- Compute the result and then discard the result
@[never_extract, noinline]
def blackBoxIO (f : α → β) (a : α) : IO β := do
  pure $ f a

def Float.toNanos (f : Float) : Float := f * 10 ^ 9

def Float.toSeconds (f : Float) : Float := f / 10 ^ 9

def Nat.toSeconds (n : Nat) : Float := Float.ofNat n / 10 ^ 9

-- TODO: Maybe add tenths place before M and B
def Nat.natPretty (n : Nat) : String :=
  if n ≥ 10 ^ 9
  then
    toString (n / 10 ^ 9) ++ "B"
  else if n ≥ 10 ^ 6
  then
    toString (n / 10 ^ 6 ) ++ "M"
  else
    toString n

def putStrNat (tup : String × Nat) : Ixon.PutM := do
  Ixon.putExpr $ .strl tup.fst
  Ixon.putExpr $ .natl tup.snd

def putCron (cron: Cronos) : Ixon.PutM := do
  Ixon.putArray (fun x => putStrNat x) cron.data.toList

def toIxon (c : Cronos) : ByteArray := Ixon.runPut (putCron c)

-- TODO: Not self-describing, add a 4-bit prefix for tuples generally
def getStrNat : Ixon.GetM (String × Nat) := do
  match (← Ixon.getExpr) with
  | .strl s =>
    match (← Ixon.getExpr) with
    | .natl n => return (s, n)
    | x => throw s!"expected Expr.Nat, got {repr x}"
  | x => throw s!"expected Expr.String, got {repr x}"

instance : Ixon.Serialize (RBMap String Nat compare) where
  put xs := (Ixon.runPut ∘ (Ixon.putArray (fun x => putStrNat x))) xs.toList
  get xs := (Ixon.runGet (Ixon.getArray getStrNat) xs).map (fun x => RBMap.ofList x compare)

def getStr : Ixon.GetM String := do
  match (← Ixon.getExpr) with
  | .strl s => return s
  | x => throw s!"expected Expr.String, got {repr x}"

instance : Ixon.Serialize (List String) where
  put := (Ixon.runPut ∘ (Ixon.putArray (fun x => Ixon.putExpr (.strl x))))
  get := Ixon.runGet (Ixon.getArray getStr)

def putFloat (x : Float): Ixon.PutM := Ixon.putUInt64LE x.toBits
def getFloat : Ixon.GetM Float := Ixon.getUInt64LE.map Float.ofBits

instance : Ixon.Serialize Float where
  put := Ixon.runPut ∘ putFloat
  get := Ixon.runGet getFloat

structure BenchData where
  mean : Float
  stdDev : Float
deriving Repr

def putBenchData (bd : BenchData) : Ixon.PutM := do
  putFloat bd.mean
  putFloat bd.stdDev

def getBenchData : Ixon.GetM BenchData := do
  return { mean := (← getFloat), stdDev := (← getFloat) }

instance : Ixon.Serialize BenchData where
  put := Ixon.runPut ∘ putBenchData
  get := Ixon.runGet getBenchData

inductive SamplingMode where
  | flat : SamplingMode
  | linear : SamplingMode
deriving Repr

structure Config where
  -- Warmup time in seconds
  warmupTime : Float := 3.0
  -- Target sample time in seconds. If the time per iteration is too long then the actual sample time will run longer and print a warning
  sampleTime : Float := 5.0
  -- Number of samples run
  numSamples : Nat := 100
  -- Sample in flat or linear mode
  samplingMode : SamplingMode := .flat
  -- Number of bootstrap samples (with replacement) to ru
  bootstrapSamples : Nat := 100000
  -- Noise threshold when comparing two benchmark means, if percent change is within this threshold then it's considered noise
  noiseThreshold : Float := 0.02 -- 2%
deriving Repr

structure BenchGroup where
  name : String
  config : Config

def percentChange (old : Float) (new : Float) : Float :=
  (new - old) / old.abs * 100

def Float.variablePrecision (float : Float) (precision : Nat) : Float :=
  let moveDecimal := Float.ofNat $ 10 ^ precision
  -- Move the decimal right to the desired precision, round to the nearest integer, then move the decimal back
  (float * moveDecimal).round / moveDecimal

-- Panics if float is a NaN
def Float.floatPretty (float : Float) (precision : Nat): String :=
  let precise := float.variablePrecision precision
  let parts := precise.toString.splitOn "."
  let integer := parts[0]!
  let fractional := parts[1]!.take precision
  if !fractional.isEmpty
  then integer ++ "." ++ fractional
  else integer

-- Formats a time in ns as an xx.yy string with correct units
def Float.formatNanos (f : Float) : String :=
  if f ≥ 10 ^ 9
  then
    (f / 10 ^ 9).floatPretty 2 ++ "s"
  else if f ≥ 10 ^ 6
  then
    (f / 10 ^ 6).floatPretty 2 ++ "ms"
  else if f ≥ 10 ^ 3
  then
    (f / 10 ^ 3).floatPretty 2 ++ "µs"
  else
    f.floatPretty 2  ++ "ns"

def BenchGroup.analyzeStats (bg : BenchGroup) (baseData : BenchData) (newData : BenchData) : IO BenchData := do
  let change ← if baseData.mean == 0
  then
    IO.println s!"Percent change is infinite, `baseData` mean is 0"
    pure 0.0
  else
    let change := percentChange baseData.mean newData.mean
    IO.println s!"Percent change: {change.floatPretty 2}%"
    pure change
  let nT := bg.config.noiseThreshold * 100
  --IO.println s!"Noise threshold: {nT}%"
  if change.abs > nT
  then
    if change > 0
    then IO.println "Performance has regressed"
    else IO.println "Performance has improved"
  else IO.println "Change within noise threshold"
  let changeData : BenchData := { mean := change , stdDev := 1.0 }
  return changeData

-- Store `BenchData` values as ixon on disk
-- Compare performance against prior run
-- TODO: Factor out into helper functions
def BenchGroup.comparePrev (bg : BenchGroup) (name : String) (benchData : BenchData) : IO Unit := do
  let ixon := Ixon.Serialize.put benchData -- TODO: move this later, after File IO
  let benchPath := System.mkFilePath [".", ".lake", "benches", name]
  let benchDir := benchPath.toString
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", benchDir] }
  let basePath := benchPath / "base"
  let baseDir := basePath.toString
  -- If the user has already run the benchmark at least once, then write the new data to disk
  if (← System.FilePath.pathExists basePath)
  then
    let newPath := benchPath / "new"
    let newDir := newPath.toString
    -- If there have been 2 or more prior runs, overwrite old `base` with old `new`, then write latest data to `new`
    if (← System.FilePath.pathExists newPath) then
      let _out ← IO.Process.run {cmd := "rm", args := #["-r", baseDir] }
      let _out ← IO.Process.run {cmd := "mv", args := #[newDir, baseDir] }
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", newDir] }
    IO.FS.writeBinFile (newPath / "estimates") ixon
    -- Get `base` data for comparison
    let baseBytes ← IO.FS.readBinFile (basePath / "estimates")
    let baseData ← match (Ixon.Serialize.get baseBytes : Except String BenchData) with
    | .ok bd' => pure bd'
    | e => throw $ IO.userError s!"expected benchData, got {repr e}"
    -- Then do statistical analysis and write changes to disk
    let changeData ← bg.analyzeStats baseData benchData
    let changeIxon := Ixon.Serialize.put changeData
    let changePath := benchPath / "change"
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", changePath.toString ] }
    IO.FS.writeBinFile (changePath / "estimates") changeIxon
  else
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir] }
    IO.FS.writeBinFile (basePath / "estimates") ixon

structure Benchmarkable (α β : Type) where
  name : String
  func : α → β
  arg : α

def bench (name : String) (func : α → β) (arg : α) : Benchmarkable α β := ⟨ name, func, arg ⟩

def BenchGroup.warmup (bg : BenchGroup) (bench : Benchmarkable α β) : IO Float := do
  IO.println s!"Warming up for {bg.config.warmupTime.floatPretty 2}s"
  let mut count := 0
  let warmupNanos := Cronos.secToNano bg.config.warmupTime
  let mut elapsed := 0
  let startTime ← IO.monoNanosNow
  while elapsed < warmupNanos do
    let _res ← blackBoxIO bench.func bench.arg
    count := count + 1
    let now ← IO.monoNanosNow
    elapsed := now - startTime
  let mean := Float.ofNat elapsed / Float.ofNat count
  --IO.println s!"{bench.name} warmup avg: {mean}ns"
  --IO.println s!"Ran {count} iterations in {bg.config.warmupTime.floatPretty 2}s\n"
  return mean

-- TODO: Combine with other sampling functions, DRY
-- TODO: Recommend sample count if expectedTime >>> bg.config.sampleTime (i.e. itersPerSample == 1)
def BenchGroup.sampleFlat (bg : BenchGroup) (bench : Benchmarkable α β)
(warmupMean : Float) : IO (List Float) := do
  let targetTime := bg.config.sampleTime.toNanos
  let timePerSample := targetTime / (Float.ofNat bg.config.numSamples)
  let itersPerSample := (timePerSample / warmupMean).ceil.toUInt64.toNat.max 1
  let totalIters := itersPerSample * bg.config.numSamples
  let expectedTime := warmupMean * Float.ofNat itersPerSample * bg.config.numSamples.toSeconds
  if itersPerSample == 1
  then
    IO.eprintln s!"Warning: Unable to complete {bg.config.numSamples} samples in {bg.config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  IO.println s!"Running {bg.config.numSamples} samples in {expectedTime.floatPretty 2}s ({totalIters} iterations)"
  --IO.println s!"Flat sample. Iters per sample: {itersPerSample}"
  let mut timings : List Float := []
  for _s in List.range bg.config.numSamples do
    --IO.println s!"Running sample {s}"
    let mut sum := 0
    for _ in List.range itersPerSample do
      let start ← IO.monoNanosNow
      let _res ← blackBoxIO bench.func bench.arg
      let finish ← IO.monoNanosNow
      sum := sum + (finish - start)
    let mean := Float.ofNat sum / Float.ofNat itersPerSample
    --IO.println s!"{bench.name} run {s} avg: {mean}ns"
    timings := mean :: timings
  return timings.reverse

-- Runs the samples as a sequence of linearly increasing iterations [d, 2d, 3d, ..., Nd]
-- where `N` is the total number of samples and `d` is a factor derived from the warmup iteration time. The sum of this series should be roughly equivalent to the total `sampleTime`
def BenchGroup.sampleLinear (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (List Float) := do
  -- `d` has a minimum value of 1 if the `warmupMean` is sufficiently large
  -- In this case,
  let totalRuns := bg.config.numSamples * (bg.config.numSamples + 1) / 2
  let targetTime := bg.config.sampleTime.toNanos
  let d := (targetTime / warmupMean / (Float.ofNat totalRuns)).ceil.toUInt64.toNat.max 1
  let expectedTime := (Float.ofNat totalRuns) * (Float.ofNat d) * warmupMean.toSeconds
  let totalIters := (List.range bg.config.numSamples).map (fun x => (x + 1) * d)
  if d == 1
  then
    IO.eprintln s!"Warning: Unable to complete {bg.config.numSamples} samples in {bg.config.sampleTime.floatPretty 2}s. You may wish to increase target time to {expectedTime.floatPretty 2}s"
  IO.println s!"Running {bg.config.numSamples} samples in {expectedTime.floatPretty 2}s ({totalIters.sum.natPretty} iterations)"
  --IO.println s!"Linear sample. Iters increase by a factor of {d} per sample"
  let mut timings : List Float := []
  for iters in totalIters do
    --IO.println s!"Sample {s} with {iters} iterations"
    let mut sum := 0
    for _i in List.range iters do
      let start ← IO.monoNanosNow
      let _res ← blackBoxIO bench.func bench.arg
      let finish ← IO.monoNanosNow
      sum := sum + (finish - start)
    let mean := Float.ofNat sum / Float.ofNat iters
    --IO.println s!"Avg: {mean}ns"
    timings := mean :: timings
  return timings.reverse

def BenchGroup.sample (bg : BenchGroup) (bench : Benchmarkable α β) (warmupMean : Float) : IO (List Float) := do
  match bg.config.samplingMode with
  | .flat => bg.sampleFlat bench warmupMean
  | .linear => bg.sampleLinear bench warmupMean

def percentile? (data : List Float) (p : Float): Option Float :=
  if data.isEmpty || p > 100
  then .none
  else
    let data := data.sortBy (fun x y => compareOfLessAndBEq x y)
    let r := (p / 100) * (Float.ofNat data.length - 1) + 1
    let rf := r - r.floor
    if rf == 0
    then
      data[r.toUInt64.toNat - 1]?
    else
      let ri := r.floor.toUInt64.toNat
      -- TODO: use fallible ? indices and monadically chain state
      .some $ data[ri-1]! + (rf) * (data[ri]! - data[ri-1]!)

-- Outliers are classified following https://bheisler.github.io/criterion.rs/book/analysis.html#outlier-classification
structure Outliers where
  outliers : List Float
  highSevere : Nat
  highMild : Nat
  lowMild : Nat
  lowSevere : Nat
deriving Repr

def Outliers.getTotal (o : Outliers) : Nat :=
  o.highSevere + o.highMild + o.lowMild + o.lowSevere

-- TODO: Refactor to cut down verbosity, and return the list for plotting
def tukey (data : List Float) : IO Unit := do
  let upper := (percentile? data 75).get!
  let lower := (percentile? data 25).get!
  let iqr := upper - lower
  let fences := [lower - 3 * iqr, lower - 1.5 * iqr, upper + 1.5 * iqr, upper + 3 * iqr]
  let mut out : Outliers := ⟨ [], 0, 0, 0, 0 ⟩
  for elem in data do
    if elem < fences[1]!
    then
      if elem < fences[0]! then
        out := { out with outliers := elem :: out.outliers, lowSevere := out.lowSevere + 1 }
      else
        out := { out with outliers := elem :: out.outliers, lowMild := out.lowMild + 1 }
    else if elem > fences[2]! then
      if elem > fences[3]! then
        out := { out with outliers := elem :: out.outliers, highSevere := out.highSevere + 1 }
      else
        out := { out with outliers := elem :: out.outliers, highMild := out.highMild + 1 }
  let outLength := out.outliers.length
  if outLength > 0 then
    let samples := data.length
    IO.println s!"Found {outLength} outliers among {samples} measurements"
    if out.lowMild > 0 then
      let pct := Float.ofNat out.lowMild / (Float.ofNat samples) * 100
      IO.println s!"  {out.lowMild} ({pct.floatPretty 2}%) low mild"
    if out.lowSevere > 0 then
      let pct := Float.ofNat out.lowSevere / (Float.ofNat samples) * 100
      IO.println s!"  {out.lowSevere} ({pct.floatPretty 2}%) low severe"
    if out.highMild > 0 then
      let pct := Float.ofNat out.highMild / (Float.ofNat samples) * 100
      IO.println s!"  {out.highMild} ({pct.floatPretty 2}%) high mild"
    if out.highSevere > 0 then
      let pct := Float.ofNat out.highSevere / (Float.ofNat samples) * 100
      IO.println s!"  {out.highSevere} ({pct.floatPretty 2}%) high severe"

structure RunningStats where
  count : Nat
  mean : Float
  m2 : Float

-- Reference implementation: https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Welford's_online_algorithm
def RunningStats.update (stt: RunningStats) (newValue : Float) : RunningStats :=
  let count := stt.count + 1
  let delta := newValue - stt.mean
  let mean := stt.mean + delta / Float.ofNat count
  let delta' := newValue - mean
  let m2 := stt.m2 + delta * delta'
  { count, mean, m2 }

def RunningStats.finalize (stt: RunningStats) : BenchData :=
  if stt.count < 2
  then { mean := 0, stdDev := 0 }
  else
    { mean := stt.mean, stdDev := (stt.m2 / (Float.ofNat stt.count - 1)).sqrt }

def pickRandom (xs : List Float) (gen : StdGen) : (Float × StdGen) :=
  let (res, gen') := randNat gen 0 (xs.length - 1)
  (xs[res]!, gen')

-- TODO: Rewrite with state monad
def resample (xs : List Float) (gen : StdGen) (sampleSize : Nat) : (List Float × StdGen) :=
  go xs gen sampleSize []
  where
    go xs gen n ys :=
      match n with
      | 0 => (ys.reverse, gen)
      | n + 1 =>
          let (res, gen') := pickRandom xs gen
          go xs gen' n (res :: ys)

-- TODO: Rewrite as pure function with state monad
def bootstrap (xs : List Float) (gen : StdGen) (numSamples : Nat) : IO BenchData := do
  if numSamples < 2
  then
    IO.eprintln "Error: need at least 2 samples to perform analysis"
  let mut gen' := gen
  let mut stt : RunningStats := { count := 0, mean := 0, m2 := 0 }
  for _s in List.range numSamples do
    let (res, gen'') := resample xs gen' xs.length
    --IO.println res
    let mean := res.sum / Float.ofNat res.length
    stt := stt.update mean
    gen' := gen''
  return stt.finalize

-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
-- A benchmark group defines a collection of related benchmarks that share a configuration, such as number of runs and noise threshold
def bgroup {α β : Type} (name: String) (benches : List (Benchmarkable α β)) (config : Config := {}) : IO Unit := do
  let bg : BenchGroup := { name, config }
  IO.println s!"Running bench group {name}\n"
  for b in benches do
    let warmupMean ← bg.warmup b
    IO.println s!"Running {b.name}"
    let timings ← bg.sample b warmupMean
    tukey timings
    -- TODO: Add proper randomness with OsRng
    let bd ← bootstrap timings mkStdGen bg.config.bootstrapSamples
    IO.println s!"Mean: {bd.mean.formatNanos}"
    IO.println s!"Standard deviation: {bd.stdDev}"
    bg.comparePrev b.name bd
    IO.println ""
