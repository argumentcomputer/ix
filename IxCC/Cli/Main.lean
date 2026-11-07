import IxCC.Cli

/-! The `ixcc` executable's root (`IxCC.Cli`). -/

def main (args : List String) : IO UInt32 := IxCC.Cli.main args
