import CompilatrixTests.Ixby.Inline.Main

def main : IO UInt32 := Compilatrix.Tools.Check.cli "check-ixby-inline" do
  CompilatrixTests.Ixby.Inline.run
