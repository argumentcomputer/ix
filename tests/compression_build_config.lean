import lakefile

def main : IO Unit := do
  let features ← cargoFeatures (net := true)
  let ffi ← cargoArgs
  let net ← cargoArgs (net := true)
  let test ← cargoArgs (testFfi := true)
  IO.println <| (Lean.Json.mkObj [
    ("ffi", Lean.toJson ffi),
    ("net", Lean.toJson net),
    ("test", Lean.toJson test),
    ("final_groth16", Lean.toJson ((← compressionFeatures).contains "groth16")),
    ("final_plonk", Lean.toJson ((← compressionFeatures).contains "plonk")),
    ("plonk_cuda", Lean.toJson (features.contains "plonk" && usesCuda features))
  ]).compress
