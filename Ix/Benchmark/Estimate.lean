import Lean.Data.Json

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

structure Estimates where
  mean : Estimate
  median : Estimate
  medianAbsDev : Estimate
  slope : Option Estimate
  stdDev : Estimate
  deriving Repr, Lean.ToJson, Lean.FromJson

structure PointEstimates where
  mean : Float
  median : Float
  medianAbsDev : Float
  stdDev : Float

