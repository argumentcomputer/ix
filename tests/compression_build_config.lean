import lakefile

def main : IO Unit := do
  let features ← cargoFeatures
  let ffi ← cargoArgs
  let net ← cargoArgs (net := true)
  let test ← cargoArgs (testFfi := true)
  IO.println <| (Lean.Json.mkObj [
    ("ffi", Lean.toJson ffi),
    ("net", Lean.toJson net),
    ("test", Lean.toJson test),
    ("worker", Lean.toJson (compressionWorkerArgs features)),
    ("terminal_groth16", Lean.toJson ((← compressionFeatures).contains "groth16")),
    ("terminal_plonk", Lean.toJson ((← compressionFeatures).contains "plonk")),
    ("plonk_cuda", Lean.toJson (features.contains "plonk" && usesCuda features))
  ]).compress
