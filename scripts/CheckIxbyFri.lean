import CompilatrixTests.Ixby.Fri.Main

def main : IO UInt32 := Compilatrix.Tools.Check.cli "check-ixby-fri" do
  CompilatrixTests.Ixby.Fri.run
