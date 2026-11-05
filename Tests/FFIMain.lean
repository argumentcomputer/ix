import Tests.FFI

/-! # The FFI suite alone (`lake exe ffi-tests`)

The same suite as `lake test -- ffi`, in an executable of its own, so that
the merge queue's Valgrind job builds and runs the Rust FFI boundary without
the rest of `IxTests`, whose import closure holds the certification's
proofs. -/

def main (_args : List String) : IO UInt32 :=
  LSpec.lspecIO (.ofList [("ffi", Tests.FFI.suite)]) []
