import Ix.Claim
import Ix.Address
import Ix.Meta
import Ix.CompileM
import Ix.Cronos
import Ix.Ixon.Expr
import Ix.Address
import Batteries

open Batteries (RBMap)

-- TODO: Make this configurable
def numRuns : Nat := 5

-- Get the average Cronos time in seconds
def avgTime (c : Cronos) : Float :=
  let timings := c.data.valuesList
  Float.ofNat (timings.sum / timings.length) / 1000000000

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
structure BenchData where
  avgBench : Float
  stdDev : Float
deriving Repr

def putBenchData (bd : BenchData) : Ixon.PutM := do
  putFloat bd.avgBench
  putFloat bd.stdDev

def getBenchData : Ixon.GetM BenchData := do
  return { avgBench := (← getFloat), stdDev := (← getFloat) }

instance : Ixon.Serialize BenchData where
  put := Ixon.runPut ∘ putBenchData
  get := Ixon.runGet getBenchData

--def myBD : BenchData := { avgBench := 100, stdDev := 1.0 }
--#eval (Ixon.Serialize.get (Ixon.Serialize.put myBD) : Except String BenchData)

-- Store `BenchData` values as ixon on disk
-- Compare performance against prior run
-- TODO: Rename this function and factor out into helpers
def storeBench (name : String) (bd : BenchData) : IO Unit := do
  let ixon := Ixon.Serialize.put bd
  let benchPath := System.mkFilePath [".", ".lake", "benches", name]
  let benchDir := benchPath.toString
  let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", benchDir] }
  let basePath := benchPath / "base"
  let baseDir := basePath.toString
  if (← System.FilePath.pathExists basePath)
  then
    -- First write results to disk
    let newPath := benchPath / "new"
    let newDir := newPath.toString
    -- If there's been 2 or more prior runs, rename new to base, discarding old base, then write bd to new
    if (← System.FilePath.pathExists newPath) then
      let _out ← IO.Process.run {cmd := "mv", args := #[newDir, baseDir] }
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", newDir] }
    IO.FS.writeBinFile (newPath / "estimates") ixon
    -- Then do statistical analysis and write changes to disk
    let baseBytes ← IO.FS.readBinFile (basePath / "estimates")
    let baseData ← match (Ixon.Serialize.get baseBytes : Except String BenchData) with
    | .ok bd' => pure bd'
    | e => throw $ IO.userError s!"expected benchData, got {repr e}"
    let avgDiff := bd.avgBench - baseData.avgBench
    IO.println s!"Avg diff {avgDiff}s"
    if avgDiff > 0
    then IO.println "Performance has decreased"
    else if avgDiff < 0
    then IO.println "Performance has increased"
    else IO.println "No change in performance"
    let changeData : BenchData := { avgBench := avgDiff, stdDev := 1.0 }
    let changeIxon := Ixon.Serialize.put changeData
    let changePath := benchPath / "new"
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", changePath.toString ] }
    IO.FS.writeBinFile (changePath / "estimates") changeIxon
  else
    let _out ← IO.Process.run {cmd := "mkdir", args := #["-p", baseDir] }
    IO.FS.writeBinFile (basePath / "estimates") ixon

-- TODO: Add warm-up time to prevent slow first runs
-- TODO: Make sure compiler isn't caching partial evaluation result for future runs of the same function (measure first vs subsequent runs)
def benchmark {α β : Type} (benches : List (String × (α → β) × α)) : IO Cronos := do
  let mut benchTimes := Cronos.new
  for (name,f,a) in benches do
    let mut cron := Cronos.new
    for run in List.range numRuns do
      let benchName := s!"{name} run {run}"
      cron ← cron.clock benchName
      let _res ← blackBoxIO f a
      cron ← cron.clock benchName
    let results : BenchData := { avgBench := avgTime cron, stdDev := Float.ofNat 1 }
    IO.println s!"{name} avg: {results.avgBench}s"
    storeBench name results
  return benchTimes

--#eval Float.ofBits (Float.ofNat 1000).toBits

-- TODO: Make a DSL or otherwise allow functions that can take multiple arguments, without needing to input a tuple
-- See Criterion syntax at http://www.serpentine.com/criterion/tutorial.html
-- Expected input
--benchmark [
--  "fib" fib 1,
--  "add" add 1 2,
--]
-- Actual input
--#eval benchmark [
--  ("fib 1", fib, 1),
--  ("fib 2", fib, 2),
--  ("fib 30", fib, 30)
--  ]
