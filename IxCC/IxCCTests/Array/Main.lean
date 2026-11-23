import IxCCTests.Array.LirControls
import IxCCTests.Array.NativeControls

/-! # Combined Array/ByteArray/LimbArray + `.rodata` Test Driver -/

set_option autoImplicit false

def main (args : List String) : IO Unit := do
  let logs : System.FilePath := match args with
    | dir :: _ => dir
    | [] => "/tmp/ixcc-array-tests"
  let nLir ← IxCCTests.Array.LirControls.run logs
  let nNat ← IxCCTests.Array.NativeControls.run logs
  IO.println s!"ALL ARRAY TESTS PASSED: {nLir} Lir/.rodata/readback + {nNat} native Xeon assertions"
