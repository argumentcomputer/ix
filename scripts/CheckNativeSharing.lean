import Compilatrix.Tools.NativeSharingCheck

def main (args : List String) : IO UInt32 :=
  Compilatrix.Tools.Check.cli "native sharing check failed" (Compilatrix.Tools.NativeSharingCheck.runCheck args)
