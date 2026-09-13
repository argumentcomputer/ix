import Compilatrix.Tools.NativeSharingCheck

def main (args : List String) : IO UInt32 :=
  Compilatrix.Tools.Check.cli "native graph check failed" (Compilatrix.Tools.NativeSharingCheck.runCheck args true)
