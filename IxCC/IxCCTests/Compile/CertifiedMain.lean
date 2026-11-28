import IxCCTests.Compile.Certified

/-! Thin root of the `tests-compile-certified` executable (`IxCCTests.Compile.Certified`).
`--child …` is the suite's other process. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--child", closure, target, mode, kind, dir] =>
    IxCCTests.Compile.Certified.child closure target mode kind dir
  | _ => IxCCTests.Compile.Certified.run args
