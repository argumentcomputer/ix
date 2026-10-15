import Tests.CompressionCli

def main : IO UInt32 := do
  Tests.CompressionCli.run
  return 0
