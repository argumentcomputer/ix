import CompilatrixTests.Ixby.Native.Main
import CompilatrixTests.Ixby.Inline.Main
import CompilatrixTests.Ixby.Fri.Main

def main : IO UInt32 := Compilatrix.Tools.Check.cli "check-ixby-lean" do
  CompilatrixTests.Ixby.Native.run
  CompilatrixTests.Ixby.Inline.run
  CompilatrixTests.Ixby.Fri.run
