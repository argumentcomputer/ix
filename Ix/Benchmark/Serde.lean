module
public import Ix.Ixon
public import Ix.Benchmark.Change
public import Ix.Benchmark.OneShot

public section

open Ixon

-- Local Serialize instances for benchmark data types (ephemeral format)

instance : Serialize Nat where
  put n := putU64LE n.toUInt64
  get := do let v ← getU64LE; return v.toNat

instance [Serialize α] : Serialize (List α) where
  put xs := do
    putU64LE xs.length.toUInt64
    for x in xs do Serialize.put x
  get := do
    let n ← getU64LE
    let mut xs := []
    for _ in List.range n.toNat do
      xs := (← Serialize.get) :: xs
    return xs.reverse

@[inline] def putFloat (x : Float) : PutM Unit := putU64LE x.toBits
@[inline] def getFloat : GetM Float := getU64LE.map Float.ofBits

instance : Serialize Float where
  put := putFloat
  get := getFloat

def putTupleNat (xy : Nat × Nat) : PutM Unit := do
  Serialize.put xy.fst
  Serialize.put xy.snd

def getTupleNat : GetM (Nat × Nat) := do
  return (← Serialize.get, ← Serialize.get)

instance : Serialize (Nat × Nat) where
  put := putTupleNat
  get := getTupleNat

def putData (data : Data) : PutM Unit := do
  Serialize.put data.d.toList

def getData : GetM Data := do
  let data : List (Nat × Nat) ← Serialize.get
  return { d := data.toArray }

instance : Serialize Data where
  put := putData
  get := getData

def putConfidenceInterval (ci : ConfidenceInterval) : PutM Unit := do
  putFloat ci.confidenceLevel
  putFloat ci.lowerBound
  putFloat ci.upperBound

def getConfidenceInterval : GetM ConfidenceInterval := do
  return { confidenceLevel := (← getFloat), lowerBound := (← getFloat), upperBound := (← getFloat)}

instance : Serialize ConfidenceInterval where
  put := putConfidenceInterval
  get := getConfidenceInterval

def putEstimate (est : Estimate) : PutM Unit := do
  putConfidenceInterval est.confidenceInterval
  putFloat est.pointEstimate
  putFloat est.stdErr

def getEstimate : GetM Estimate := do
  return { confidenceInterval := (← getConfidenceInterval), pointEstimate := (← getFloat), stdErr := (← getFloat)}

instance : Serialize Estimate where
  put := putEstimate
  get := getEstimate

def putEstimates (est : Estimates) : PutM Unit := do
  putEstimate est.mean
  putEstimate est.median
  putEstimate est.medianAbsDev
  if let .some x := est.slope
  then
    putU8 1
    putEstimate x
  else
    putU8 0
  putEstimate est.stdDev

def getEstimates : GetM Estimates := do
  let mean ← getEstimate
  let median ← getEstimate
  let medianAbsDev ← getEstimate
  let slope ← match (← getU8) with
    | 1 => pure $ some (← getEstimate)
    | _ => pure none
  let stdDev ← getEstimate
  return { mean, median, medianAbsDev, slope, stdDev }

instance : Serialize Estimates where
  put := putEstimates
  get := getEstimates

def putChangeEstimates (changeEst : ChangeEstimates) : PutM Unit := do
  putEstimate changeEst.mean
  putEstimate changeEst.median

def getChangeEstimates : GetM ChangeEstimates := do
  let mean ← getEstimate
  let median ← getEstimate
  return { mean, median }

instance : Serialize ChangeEstimates where
  put := putChangeEstimates
  get := getChangeEstimates

def getOneShot: GetM OneShot := do
  return { benchTime := (← Serialize.get) }

instance : Serialize OneShot where
  put os := Serialize.put os.benchTime
  get := getOneShot

/-- Writes JSON to disk at `benchPath/fileName` -/
def storeJson [Lean.ToJson α] (data : α) (benchPath : System.FilePath) : IO Unit := do
  let json := Lean.toJson data
  IO.FS.writeFile benchPath json.pretty

/-- Writes Ixon to disk at `benchPath/fileName` -/
def storeIxon [Serialize α] (data : α) (benchPath : System.FilePath) : IO Unit := do
  let ixon := ser data
  IO.FS.writeBinFile benchPath ixon

def storeFile [Lean.ToJson α] [Serialize α] (fmt : SerdeFormat) (data: α) (path : System.FilePath) : IO Unit := do
  match fmt with
  | .json => storeJson data path
  | .ixon => storeIxon data path

def loadJson [Lean.FromJson α] (path : System.FilePath) : IO α := do
  let jsonStr ← IO.FS.readFile path
  let json ← match Lean.Json.parse jsonStr with
  | .ok js => pure js
  | .error e => throw $ IO.userError s!"{repr e}"
  match Lean.fromJson? json with
  | .ok d => pure d
  | .error e => throw $ IO.userError s!"{repr e}"

def loadIxon [Serialize α] (path : System.FilePath) : IO α := do
  let ixonBytes ← IO.FS.readBinFile path
  match de ixonBytes with
  | .ok d => pure d
  | .error e => throw $ IO.userError s!"expected a, got {repr e}"

def loadFile [Lean.FromJson α] [Serialize α] (format : SerdeFormat) (path : System.FilePath) : IO α := do
  match format with
  | .json => loadJson path
  | .ixon => loadIxon path

end
