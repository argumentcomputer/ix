import Tests.Aiur

def main (args : List String) : IO UInt32 := do
  LSpec.lspecIO (.ofList [("aiur", Tests.Aiur.suite)]) args
