import Ix.Ixon
import Ix.Benchmark.Change

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
