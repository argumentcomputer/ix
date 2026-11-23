import IxCCTests.Array.LirControls
import IxCCTests.Array.NativeControls
import IxCCTests.Array.WireTests

/-! # Combined Array/ByteArray/LimbArray + `.rodata` + DR3/DR4 Wiring Test Driver -/

set_option autoImplicit false

private def parseArgs : List String → System.FilePath × Option String × Bool
  | [] => ("/tmp/ixcc-array-tests", none, false)
  | "--require-ix" :: rest =>
    let (d, ix, _) := parseArgs rest
    (d, ix, true)
  | "--ix" :: p :: rest =>
    let (d, _, req) := parseArgs rest
    (d, some p, req)
  | dir :: rest =>
    let (_, ix, req) := parseArgs rest
    (dir, ix, req)

def main (args : List String) : IO Unit := do
  let (logs, cliIx, requireIx) := parseArgs args
  let nLir ← IxCCTests.Array.LirControls.run logs
  let nNat ← IxCCTests.Array.NativeControls.run logs
  let nWire ← IxCCTests.Array.WireTests.run logs cliIx requireIx
  IO.println s!"ALL ARRAY TESTS PASSED: {nLir} Lir/.rodata/readback + {nNat} native Xeon + {nWire} DR3/DR4 wiring assertions"
