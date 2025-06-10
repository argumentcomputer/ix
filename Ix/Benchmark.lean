import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Ixon.Expr
import Ix.Address
import Batteries

open Batteries (RBMap)

-- Get the average Cronos time in nanoseconds
def avgTime (c : Cronos) : Float :=
  let timings := c.data.valuesList
  Float.ofNat timings.sum / Float.ofNat timings.length

-- This prevents inline optimization for benchmarking, but doesn't work if the result is never used
--@[never_extract, noinline]
--def blackBox : α → α := id

-- Compute the result and then discard the result
@[never_extract, noinline]
def blackBoxIO (f : α → β) (a : α) : IO β := do
  pure $ f a

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

def getCron : Ixon.GetM Cronos := do
  let c ← (Ixon.getArray getStrNat).run
  return { refs := RBMap.empty, data := RBMap.ofList c compare}

def fromIxon (ixon: ByteArray) : Except String Cronos := Ixon.runGet getCron ixon

def cron : Cronos :=
  let cron' := Cronos.new
  { cron' with data := cron'.data.insert "hey" 1}

instance : Ixon.Serialize (RBMap String Nat compare) where
  put xs := (Ixon.runPut ∘ (Ixon.putArray (fun x => putStrNat x))) xs.toList
  get xs := (Ixon.runGet (Ixon.getArray getStrNat) xs).map (fun x => RBMap.ofList x compare)

--#eval (Ixon.Serialize.get (Ixon.Serialize.put cron.data) : Except String (RBMap String Nat compare))

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

--#eval (Ixon.Serialize.get (Ixon.Serialize.put 100.58) : Except String Float)

-- TODO: Add proper stat analysis
-- Upper bound, lower bound, stdDev, mean, median
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

--def myBD : BenchData := { mean := 100, stdDev := 1.0 }
--#eval (Ixon.Serialize.get (Ixon.Serialize.put myBD) : Except String BenchData)

structure Config where
  numRuns : Nat := 1000
  noiseThreshold : Float := 0.02
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

--#eval Float.variablePrecision 10.12345 4

def Float.floatPretty (float : Float) (precision : Nat): String :=
  let precise := float.variablePrecision precision
  precise.toString.dropRightWhile (· == '0')

--#eval Float.floatPretty 10.12345 4

-- TODO: Pretty-print units based on nearest precision (nano, micro, etc)
--def convertUnits

def BenchGroup.analyzeStats (bg : BenchGroup) (baseData : BenchData) (newData : BenchData) : IO BenchData := do
  let change := percentChange baseData.mean newData.mean
  IO.println s!"Percent change: {change.floatPretty 2}%"
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
-- TODO: Rename this function and factor out into helpers
def BenchGroup.storeBench (bg : BenchGroup) (name : String) (benchData : BenchData) : IO Unit := do
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

def BenchGroup.runBench (bg : BenchGroup) (bench : Benchmarkable α β) : IO Unit := do
  let mut cron := Cronos.new
  for run in List.range bg.config.numRuns do
    let benchName := s!"{bench.name} run {run}"
    --IO.println benchName
    cron ← cron.clock benchName
    let _res ← blackBoxIO bench.func bench.arg
    cron ← cron.clock benchName
  let results : BenchData := { mean := avgTime cron, stdDev := Float.ofNat 1 }
  IO.println s!"{bench.name} avg: {results.mean}ns"
  bg.storeBench bench.name results

-- TODO: Add warm-up time to prevent slow first runs
-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
-- A benchmark group defines a collection of related benchmarks that share a configuration, such as number of runs and noise threshold
def bgroup {α β : Type} (name: String) (benches : List (Benchmarkable α β)) (config : Config := {}) : IO Unit := do
  let benchGroup : BenchGroup := { name, config }
  --IO.println s!"My config: {repr config}"
  IO.println s!"Running bench group {name}\n"
  for b in benches do
    let _results ← benchGroup.runBench b
    IO.println ""

--#eval Float.ofBits (Float.ofNat 1000).toBits
