import IxCCTests.IxonV3.Run

/-- `tests-ixon-v3` runs the suite. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => return if ← IxCCTests.IxonV3.run then 0 else 1
  | _ =>
    IO.eprintln "usage: tests-ixon-v3"
    return 2
