import Ix.Ixon
import Ix.Benchmark.Change
import Ix.Benchmark.OneShot

@[inline] def putFloat (x : Float) : Ixon.PutM Unit := Ixon.putUInt64LE x.toBits
@[inline] def getFloat : Ixon.GetM Float := Ixon.getUInt64LE.map Float.ofBits

instance : Ixon.Serialize Float where
  put := putFloat
  get := getFloat

def putTupleNat (xy : Nat × Nat) : Ixon.PutM Unit := do
  Ixon.putNat Ixon.putBytesTagged xy.fst
  Ixon.putNat Ixon.putBytesTagged xy.snd

def getTupleNat : Ixon.GetM (Nat × Nat) := do
  return (← Ixon.Serialize.get, ← Ixon.Serialize.get)

instance : Ixon.Serialize (Nat × Nat) where
  put := putTupleNat
  get := getTupleNat 

def putData (data : Data) : Ixon.PutM Unit := do
  Ixon.Serialize.put data.d.toList

def getData : Ixon.GetM Data := do
  let data : List (Nat × Nat) ← Ixon.Serialize.get
  return { d := data.toArray } 

instance : Ixon.Serialize Data where
  put := putData 
  get := getData

def putConfidenceInterval (ci : ConfidenceInterval) : Ixon.PutM Unit := do
  putFloat ci.confidenceLevel
  putFloat ci.lowerBound
  putFloat ci.upperBound

def getConfidenceInterval : Ixon.GetM ConfidenceInterval := do
  return { confidenceLevel := (← getFloat), lowerBound := (← getFloat), upperBound := (← getFloat)}

instance : Ixon.Serialize ConfidenceInterval where
  put := putConfidenceInterval 
  get := getConfidenceInterval 

def putEstimate (est : Estimate) : Ixon.PutM Unit := do
  putConfidenceInterval est.confidenceInterval
  putFloat est.pointEstimate
  putFloat est.stdErr

def getEstimate : Ixon.GetM Estimate := do
  return { confidenceInterval := (← getConfidenceInterval), pointEstimate := (← getFloat), stdErr := (← getFloat)}

instance : Ixon.Serialize Estimate where
  put := putEstimate
  get := getEstimate

def putEstimates (est : Estimates) : Ixon.PutM Unit := do
  putEstimate est.mean
  putEstimate est.median
  putEstimate est.medianAbsDev
  if let .some x := est.slope
  then
    Ixon.putUInt8 1
    putEstimate x
  else
    Ixon.putUInt8 0
  putEstimate est.stdDev

def getEstimates : Ixon.GetM Estimates := do
  let mean ← getEstimate
  let median ← getEstimate
  let medianAbsDev ← getEstimate
  let slope ← match (← Ixon.getUInt8) with
    | 1 => pure $ some (← getEstimate)
    | _ => pure none
  let stdDev ← getEstimate
  return { mean, median, medianAbsDev, slope, stdDev }

instance : Ixon.Serialize Estimates where
  put := putEstimates
  get := getEstimates

def putChangeEstimates (changeEst : ChangeEstimates) : Ixon.PutM Unit := do
  putEstimate changeEst.mean
  putEstimate changeEst.median

def getChangeEstimates : Ixon.GetM ChangeEstimates := do
  let mean ← getEstimate
  let median ← getEstimate
  return { mean, median }

instance : Ixon.Serialize ChangeEstimates where
  put := putChangeEstimates
  get := getChangeEstimates

def getOneShot: Ixon.GetM OneShot := do
  return { benchTime := (← Ixon.Serialize.get) }

instance : Ixon.Serialize OneShot where
  put os := Ixon.Serialize.put os.benchTime
  get := getOneShot

/-- Writes JSON to disk at `benchPath/fileName` -/
def storeJson [Lean.ToJson α] (data : α) (benchPath : System.FilePath) : IO Unit := do
  let json := Lean.toJson data
  IO.FS.writeFile benchPath json.pretty

/-- Writes Ixon to disk at `benchPath/fileName` -/
def storeIxon [Ixon.Serialize α] (data : α) (benchPath : System.FilePath) : IO Unit := do
  let ixon := Ixon.ser data
  IO.FS.writeBinFile benchPath ixon

def storeFile [Lean.ToJson α] [Ixon.Serialize α] (fmt : SerdeFormat) (data: α) (path : System.FilePath) : IO Unit := do
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

def loadIxon [Ixon.Serialize α] (path : System.FilePath) : IO α := do
  let ixonBytes ← IO.FS.readBinFile path
  match Ixon.de ixonBytes with
  | .ok d => pure d
  | .error e => throw $ IO.userError s!"expected a, go {repr e}"

def loadFile [Lean.FromJson α] [Ixon.Serialize α] (format : SerdeFormat) (path : System.FilePath) : IO α := do
  match format with
  | .json => loadJson path
  | .ixon => loadIxon path

