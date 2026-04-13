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

def putLabel (s : String) : PutM Unit := do
  let bytes := s.toUTF8
  putU64LE bytes.size.toUInt64
  putBytes bytes

def getLabel : GetM String := do
  let len ← getU64LE
  let bytes ← getBytes len.toNat
  return String.fromUTF8! bytes

def putThroughput (t : Throughput) : PutM Unit := do
  match t with
  | .Bits n => putU8 0; putU64LE n
  | .Bytes n => putU8 1; putU64LE n
  | .BytesDecimal n => putU8 2; putU64LE n
  | .Elements n label => putU8 3; putU64LE n; putLabel label
  | .ElementsAndBytes e b label => putU8 4; putU64LE e; putU64LE b; putLabel label

def getThroughput : GetM Throughput := do
  let tag ← getU8
  match tag with
  | 0 => return .Bits (← getU64LE)
  | 1 => return .Bytes (← getU64LE)
  | 2 => return .BytesDecimal (← getU64LE)
  | 3 =>
    let n ← getU64LE
    let label ← getLabel
    return .Elements n label
  | 4 =>
    let e ← getU64LE
    let b ← getU64LE
    let label ← getLabel
    return .ElementsAndBytes e b label
  | _ => throw s!"invalid Throughput tag {tag}"

instance : Serialize Throughput where
  put := putThroughput
  get := getThroughput

def putSamplingMode (m : SamplingMode) : PutM Unit := do
  match m with
  | .flat => putU8 0
  | .linear => putU8 1
  | .auto => panic! "SamplingMode.auto must be resolved before persisting"

def getSamplingMode : GetM SamplingMode := do
  let tag ← getU8
  match tag with
  | 0 => return .flat
  | 1 => return .linear
  | _ => throw s!"invalid SamplingMode tag {tag}"

instance : Serialize SamplingMode where
  put := putSamplingMode
  get := getSamplingMode

def putSerdeFormat (f : SerdeFormat) : PutM Unit := do
  match f with
  | .json => putU8 0
  | .ixon => putU8 1

def getSerdeFormat : GetM SerdeFormat := do
  let tag ← getU8
  match tag with
  | 0 => return .json
  | 1 => return .ixon
  | _ => throw s!"invalid SerdeFormat tag {tag}"

instance : Serialize SerdeFormat where
  put := putSerdeFormat
  get := getSerdeFormat

def putVerbosity (v : Verbosity) : PutM Unit := do
  match v with
  | .quiet => putU8 0
  | .normal => putU8 1
  | .verbose => putU8 2

def getVerbosity : GetM Verbosity := do
  let tag ← getU8
  match tag with
  | 0 => return .quiet
  | 1 => return .normal
  | 2 => return .verbose
  | _ => throw s!"invalid Verbosity tag {tag}"

instance : Serialize Verbosity where
  put := putVerbosity
  get := getVerbosity

instance [Serialize α] : Serialize (Option α) where
  put
    | none => putU8 0
    | some a => do putU8 1; Serialize.put a
  get := do
    let tag ← getU8
    match tag with
    | 0 => return none
    | 1 => return some (← Serialize.get)
    | _ => throw s!"invalid Option tag {tag}"

def putConfig (c : Config) : PutM Unit := do
  putFloat c.warmupTime
  putFloat c.sampleTime
  Serialize.put c.numSamples
  Serialize.put c.samplingMode
  Serialize.put c.bootstrapSamples
  putFloat c.confidenceLevel
  putFloat c.significanceLevel
  putFloat c.noiseThreshold
  Serialize.put c.serde
  putU8 (if c.oneShot then 1 else 0)
  putU8 (if c.report then 1 else 0)
  Serialize.put c.throughput
  putU8 (if c.avgThroughput then 1 else 0)
  -- `verbosity`, `color`, and `overwrite` are runtime display preferences, not persisted.

def getConfig : GetM Config := do
  let warmupTime ← getFloat
  let sampleTime ← getFloat
  let numSamples : Nat ← Serialize.get
  let samplingMode ← getSamplingMode
  let bootstrapSamples : Nat ← Serialize.get
  let confidenceLevel ← getFloat
  let significanceLevel ← getFloat
  let noiseThreshold ← getFloat
  let serde ← getSerdeFormat
  let oneShot ← (· != 0) <$> getU8
  let report ← (· != 0) <$> getU8
  let throughput : Option Throughput ← Serialize.get
  let avgThroughput ← (· != 0) <$> getU8
  return {
    warmupTime, sampleTime, numSamples, samplingMode, bootstrapSamples,
    confidenceLevel, significanceLevel, noiseThreshold, serde,
    oneShot, report, throughput, avgThroughput
  }

instance : Serialize Config where
  put := putConfig
  get := getConfig

def putOneShot (os : OneShot) : PutM Unit := do
  Serialize.put os.benchTime
  match os.throughput with
  | none => putU8 0
  | some t => putU8 1; putThroughput t

def getOneShot: GetM OneShot := do
  let benchTime : Nat ← Serialize.get
  let tag ← getU8
  let throughput ← match tag with
    | 0 => pure none
    | 1 => pure (some (← getThroughput))
    | _ => throw s!"invalid OneShot throughput flag {tag}"
  return { benchTime, throughput }

instance : Serialize OneShot where
  put := putOneShot
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
