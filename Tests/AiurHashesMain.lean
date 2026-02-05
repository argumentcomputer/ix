import Tests.AiurHashes

def main (args : List String) : IO UInt32 := do
  LSpec.lspecIO (.ofList [("aiur-hashes", Tests.AiurHashes.suite)]) args
