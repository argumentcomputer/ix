import Compilatrix.Ixby.SymbolicWire
import Compilatrix.Ixby.Report

namespace Compilatrix.Ixby

def DataExpr.json : DataExpr → Lean.Json
  | .parameter index => Lean.Json.mkObj [("parameter", Lean.toJson index)]
  | .nat n => Lean.Json.mkObj [("nat", Lean.toJson (toString n))]
  | .str s => Lean.Json.mkObj [("str", Lean.toJson s)]
  | .erased => Lean.Json.mkObj [("erased", Lean.toJson true)]
  | .ctor address tag fields => Lean.Json.mkObj [
      ("address", Lean.toJson address.toHex), ("tag", Lean.toJson tag),
      ("fields", Lean.Json.arr (fields.map DataExpr.json).toArray)]

/-- Reproducible checker metadata. This is not a serialized Lean proof; the
certificate is reconstructed from the exact source, config, image and budgets. -/
def SymbolicCertificate.json {source config compiled}
    (certificate : @SymbolicCertificate source config compiled) : Lean.Json := Lean.Json.mkObj [
  ("format", Lean.toJson "compilatrix/ixby-symbolic/1"),
  ("fragment", Lean.toJson "opaque-parameters/1"),
  ("parameters", Lean.toJson source.parameters),
  ("source_fuel", Lean.toJson certificate.sourceFuel),
  ("target_fuel", Lean.toJson certificate.targetFuel),
  ("data_depth", Lean.toJson certificate.dataDepth),
  ("result", certificate.result.json)]

end Compilatrix.Ixby
