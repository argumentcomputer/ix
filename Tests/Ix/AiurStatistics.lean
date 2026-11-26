module
public import Ix.Aiur.Statistics
public import Tests.Aiur.Cost

public section
namespace Tests.Ix.AiurStatistics
open Aiur LSpec Lean

set_option compiler.extract_closed false

private def shape : CircuitShape :=
  { mainWidth := 3, stage2Width := 3, quotientDegree := 2,
    preprocessedWidth := 100, preprocessedHeight := 0 }

private def measurement (name : String) (rows hits : Nat) : CircuitMeasurement :=
  { name, shape, height := rows, cacheHits := hits }

private def rawCircuit (rows hits fixed : Nat) : Json := Json.mkObj [
  ("name", toJson "fixture"), ("stage1_width", toJson (3 : Nat)),
  ("stage2_width", toJson (3 : Nat)), ("quotient_degree", toJson (2 : Nat)),
  ("preprocessed_width", toJson (100 : Nat)), ("preprocessed_height", toJson fixed),
  ("rows", toJson rows), ("cache_hits", toJson hits)]

private def raw (c : Json) (degree : Nat := 3) : Json := Json.mkObj [
  ("log_blowup", toJson (2 : Nat)), ("extension_degree", toJson degree),
  ("circuits", .arr #[c])]

def suite : LSpec.Spec := do
  AiurTests.Cost.tests
  it "cached and uncached totals use the same model" do
    let stats := computeStats { logBlowup := 2, circuits := #[measurement "small" 1 3, measurement "large" 4 0] }
    expect (stats.roundedFftCost == 780 && stats.totalUncachedFftCost == 1392.0 && stats.totalCacheHits == 3)
  it "display ranks circuits by cost" do
    let stats := computeStats { logBlowup := 2, circuits := #[measurement "small" 1 3, measurement "large" 4 0] }
    expect (stats.circuits[0]!.name == "large")
  itBool "decode real host field names"
    ((ExecutionMeasurements.fromJson (raw (rawCircuit 3 2 0))).toOption.any fun m =>
      m.circuits.size == 1 && m.circuits[0]!.height == 3 && m.circuits[0]!.cacheHits == 2)
  itBool "fixed tables keep their full height"
    ((ExecutionMeasurements.fromJson (raw (rawCircuit 4 0 4))).isOk)
  itBool "reject truncated fixed tables"
    ((ExecutionMeasurements.fromJson (raw (rawCircuit 3 0 4))).toOption.isNone)
  itBool "reject cache savings on fixed tables"
    ((ExecutionMeasurements.fromJson (raw (rawCircuit 4 1 4))).toOption.isNone)
  itBool "reject missing counts"
    ((ExecutionMeasurements.fromJson (raw (Json.mkObj []))).toOption.isNone)
  itBool "reject an incompatible extension degree"
    ((ExecutionMeasurements.fromJson (raw (rawCircuit 4 0 0) 2)).toOption.isNone)
  it "benchmark reports contain Lean-computed FFT costs" do
    let report := Json.mkObj [("execution_statistics", raw (rawCircuit 4 0 0)),
      ("verified", toJson true)]
    let enriched := enrichExecutionReport report
    expect ((enriched >>= (·.getObjValAs? Nat "fft-cost")).toOption == some 696)
  it "keep existing report fields" do
    let report := Json.mkObj [("execution_statistics", raw (rawCircuit 4 0 0)),
      ("verified", toJson true)]
    let enriched := enrichExecutionReport report
    expect ((enriched >>= (·.getObjValAs? Bool "verified")).toOption == some true)
  itBool "a missing execution does not fabricate zero cost"
    (((enrichExecutionReport (Json.mkObj [])) >>= (·.getObjVal? "fft-cost")).toOption.isNone)
  itBool "malformed measurements fail the report"
    ((enrichExecutionReport (Json.mkObj [("execution_statistics", .null)])).toOption.isNone)

end Tests.Ix.AiurStatistics
end
