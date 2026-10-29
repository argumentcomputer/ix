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
    ("terminal_plonk", Lean.toJson ((← compressionFeatures).contains "plonk")),
    ("terminal_groth16", Lean.toJson ((← compressionFeatures).contains "groth16")),
    ("groth16_cuda", Lean.toJson (← compressionGroth16Cuda)),
    ("plonk_helper", Lean.toJson (compressionHelperName)),
    ("plonk_cuda", Lean.toJson (← compressionHelperCuda)),
    ("plonk_build", Lean.toJson (compressionHelperArgs "helper-output"))
  ]).compress
