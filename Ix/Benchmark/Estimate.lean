structure ConfidenceInterval where
  confidenceLevel : Float
  lowerBound : Float
  upperBound : Float
deriving Repr

structure Estimate where
  confidenceInterval : ConfidenceInterval
  pointEstimate : Float
  stdErr : Float
deriving Repr

structure Estimates where
  mean : Estimate
  median : Estimate
  medianAbsDev : Estimate
  slope : Option Estimate
  stdDev : Estimate
deriving Repr

structure PointEstimates where
  mean : Float
  median : Float
  medianAbsDev : Float
  stdDev : Float
