import Tests.FFI

/-! # The FFI suite alone (`lake exe ffi-tests`)

The same suite as `lake test -- ffi`, in an executable of its own, so that
the merge queue's Valgrind job builds and runs the Rust FFI boundary without
the rest of `IxTests`, whose import closure holds the certification's
proofs. -/

def main (args : List String) : IO UInt32 := do
  let valgrind := (← IO.getEnv "IX_VALGRIND") == some "1"
  let cfg : LSpec.Prop.PropertyConfig := if valgrind then { numTests := 8 } else {}
  LSpec.lspecMain (LSpec.describe "ffi" (Tests.FFI.suiteWith cfg valgrind)) args
