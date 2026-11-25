import IxCCTests.Compile.Run

/-! Thin root of the `tests-pure-compile` executable (`IxCCTests.Compile.Run`).
`--child …` is the suite's other process (`IxCCTests.Compile.child`). -/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--child", closure, target, mode, kind, stack, region, dir] =>
    IxCCTests.Compile.child closure target mode kind stack region dir
  | _ => IxCCTests.Compile.run args
