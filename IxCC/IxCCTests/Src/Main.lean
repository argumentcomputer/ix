import IxCCTests.Src.Run
import IxCCTests.Src.AutoHints

/-! Root of the `tests-src` executable. -/

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--auto-hints"] => IxCCTests.Src.AutoHints.main
  | [] =>
    let code ← IxCCTests.Src.Run.main args
    if code != 0 then return code
    IxCCTests.Src.AutoHints.main
  | _ => IxCCTests.Src.Run.main args
