import Ix.IxonOld
import Ix.Benchmark.Change
import Ix.Benchmark.OneShot

@[inline] def putFloat (x : Float) : IxonOld.PutM Unit := IxonOld.putUInt64LE x.toBits
@[inline] def getFloat : IxonOld.GetM Float := IxonOld.getUInt64LE.map Float.ofBits

instance : IxonOld.Serialize Float where
  put := putFloat
  get := getFloat

def putTupleNat (xy : Nat × Nat) : IxonOld.PutM Unit := do
  IxonOld.putNat IxonOld.putBytesTagged xy.fst
  IxonOld.putNat IxonOld.putBytesTagged xy.snd

def getTupleNat : IxonOld.GetM (Nat × Nat) := do
  return (← IxonOld.Serialize.get, ← IxonOld.Serialize.get)

instance : IxonOld.Serialize (Nat × Nat) where
  put := putTupleNat
  get := getTupleNat 

def putData (data : Data) : IxonOld.PutM Unit := do
  IxonOld.Serialize.put data.d.toList

def getData : IxonOld.GetM Data := do
  let data : List (Nat × Nat) ← IxonOld.Serialize.get
  return { d := data.toArray } 

instance : IxonOld.Serialize Data where
  put := putData 
  get := getData

def putConfidenceInterval (ci : ConfidenceInterval) : IxonOld.PutM Unit := do
  putFloat ci.confidenceLevel
  putFloat ci.lowerBound
  putFloat ci.upperBound

def getConfidenceInterval : IxonOld.GetM ConfidenceInterval := do
  return { confidenceLevel := (← getFloat), lowerBound := (← getFloat), upperBound := (← getFloat)}

instance : IxonOld.Serialize ConfidenceInterval where
  put := putConfidenceInterval 
  get := getConfidenceInterval 

def putEstimate (est : Estimate) : IxonOld.PutM Unit := do
  putConfidenceInterval est.confidenceInterval
  putFloat est.pointEstimate
  putFloat est.stdErr

def getEstimate : IxonOld.GetM Estimate := do
  return { confidenceInterval := (← getConfidenceInterval), pointEstimate := (← getFloat), stdErr := (← getFloat)}

instance : IxonOld.Serialize Estimate where
  put := putEstimate
  get := getEstimate

def putEstimates (est : Estimates) : IxonOld.PutM Unit := do
  putEstimate est.mean
  putEstimate est.median
  putEstimate est.medianAbsDev
  if let .some x := est.slope
  then
    IxonOld.putUInt8 1
    putEstimate x
  else
    IxonOld.putUInt8 0
  putEstimate est.stdDev

def getEstimates : IxonOld.GetM Estimates := do
  let mean ← getEstimate
  let median ← getEstimate
  let medianAbsDev ← getEstimate
  let slope ← match (← IxonOld.getUInt8) with
    | 1 => pure $ some (← getEstimate)
    | _ => pure none
  let stdDev ← getEstimate
  return { mean, median, medianAbsDev, slope, stdDev }

instance : IxonOld.Serialize Estimates where
  put := putEstimates
  get := getEstimates

def putChangeEstimates (changeEst : ChangeEstimates) : IxonOld.PutM Unit := do
  putEstimate changeEst.mean
  putEstimate changeEst.median

def getChangeEstimates : IxonOld.GetM ChangeEstimates := do
  let mean ← getEstimate
  let median ← getEstimate
  return { mean, median }

instance : IxonOld.Serialize ChangeEstimates where
  put := putChangeEstimates
  get := getChangeEstimates

def getOneShot: IxonOld.GetM OneShot := do
  return { benchTime := (← IxonOld.Serialize.get) }

instance : IxonOld.Serialize OneShot where
  put os := IxonOld.Serialize.put os.benchTime
  get := getOneShot

/-- Writes JSON to disk at `benchPath/fileName` -/
def storeJson [Lean.ToJson α] (data : α) (benchPath : System.FilePath) : IO Unit := do
  let json := Lean.toJson data
  IO.FS.writeFile benchPath json.pretty

/-- Writes Ixon to disk at `benchPath/fileName` -/
def storeIxon [IxonOld.Serialize α] (data : α) (benchPath : System.FilePath) : IO Unit := do
  let ixon := IxonOld.ser data
  IO.FS.writeBinFile benchPath ixon

def storeFile [Lean.ToJson α] [IxonOld.Serialize α] (fmt : SerdeFormat) (data: α) (path : System.FilePath) : IO Unit := do
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

def loadIxon [IxonOld.Serialize α] (path : System.FilePath) : IO α := do
  let ixonBytes ← IO.FS.readBinFile path
  match IxonOld.de ixonBytes with
  | .ok d => pure d
  | .error e => throw $ IO.userError s!"expected a, go {repr e}"

def loadFile [Lean.FromJson α] [IxonOld.Serialize α] (format : SerdeFormat) (path : System.FilePath) : IO α := do
  match format with
  | .json => loadJson path
  | .ixon => loadIxon path

