import Lean.Data.Json
import Ix.Benchmark.Common

structure ConfidenceInterval where
  confidenceLevel : Float
  lowerBound : Float
  upperBound : Float
  deriving Repr, Lean.ToJson, Lean.FromJson

structure Estimate where
  confidenceInterval : ConfidenceInterval
  pointEstimate : Float
  stdErr : Float
  deriving Repr, Lean.ToJson, Lean.FromJson

def Estimate.formatPercents (est : Estimate) (color : Bool) : (String × String × String) :=
  let lb := formatPercent est.confidenceInterval.lowerBound
  let pointEst := bold <| formatPercent est.pointEstimate
  let ub := formatPercent est.confidenceInterval.upperBound
  let pointEst := if color then
    if est.pointEstimate < 0 then
      green pointEst
    else
      red pointEst
  else
    pointEst
  (lb, pointEst, ub)

structure Estimates where
  mean : Estimate
  median : Estimate
  medianAbsDev : Estimate
  slope : Option Estimate
  stdDev : Estimate
  deriving Repr, Lean.ToJson, Lean.FromJson

def Estimates.typical (est : Estimates) : Estimate :=
  est.slope.getD est.mean

structure PointEstimates where
  mean : Float
  median : Float
  medianAbsDev : Float
  stdDev : Float

