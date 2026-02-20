import Tests.IxVM

def main (args : List String) : IO UInt32 := do
  LSpec.lspecIO (.ofList [("ixvm", Tests.IxVM.suite)]) args
