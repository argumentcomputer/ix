import Ix.Ixon.Expr
import Ix.Benchmark.Change

@[inline] def putFloat (x : Float): Ixon.PutM := Ixon.putUInt64LE x.toBits
@[inline] def getFloat : Ixon.GetM Float := Ixon.getUInt64LE.map Float.ofBits

instance : Ixon.Serialize Float where
  put := Ixon.runPut ∘ putFloat
  get := Ixon.runGet getFloat

def putTupleNat (xy : Nat × Nat) : Ixon.PutM := do
  Ixon.putNatl xy.fst
  Ixon.putNatl xy.snd

def putData (data : Data) : Ixon.PutM := do
  Ixon.putArray putTupleNat data.d.toList

def getTupleNat : Ixon.GetM (Nat × Nat) := do
  return (← Ixon.getNatl, ← Ixon.getNatl)

def getData : Ixon.GetM Data := do
  let data ← Ixon.getArray getTupleNat
  return { d := data.toArray }

instance : Ixon.Serialize Data where
  put := Ixon.runPut ∘ putData
  get := Ixon.runGet getData

def putConfidenceInterval (ci : ConfidenceInterval) : Ixon.PutM := do
  putFloat ci.confidenceLevel
  putFloat ci.lowerBound
  putFloat ci.upperBound

def getConfidenceInterval : Ixon.GetM ConfidenceInterval := do
  return { confidenceLevel := (← getFloat), lowerBound := (← getFloat), upperBound := (← getFloat)}

def putEstimate (est : Estimate) : Ixon.PutM := do
  putConfidenceInterval est.confidenceInterval
  putFloat est.pointEstimate
  putFloat est.stdErr

def getEstimate : Ixon.GetM Estimate := do
  return { confidenceInterval := (← getConfidenceInterval), pointEstimate := (← getFloat), stdErr := (← getFloat)}

def putEstimates (est : Estimates) : Ixon.PutM := do
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
  put := Ixon.runPut ∘ putEstimates
  get := Ixon.runGet getEstimates

def putChangeEstimates (changeEst : ChangeEstimates) : Ixon.PutM := do
  putEstimate changeEst.mean
  putEstimate changeEst.median

def getChangeEstimates : Ixon.GetM ChangeEstimates := do
  let mean ← getEstimate
  let median ← getEstimate
  return { mean, median }

instance : Ixon.Serialize ChangeEstimates where
  put := Ixon.runPut ∘ putChangeEstimates
  get := Ixon.runGet getChangeEstimates
