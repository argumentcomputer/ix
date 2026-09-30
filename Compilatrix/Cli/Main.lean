import Compilatrix.Cli

/-! The `compilatrix` executable's root (`Compilatrix.Cli`). -/

def main (args : List String) : IO UInt32 := Compilatrix.Cli.main args
