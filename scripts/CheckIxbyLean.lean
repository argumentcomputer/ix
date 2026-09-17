import CompilatrixTests.Ixby.Native.Main

def main : IO UInt32 := Compilatrix.Tools.Check.cli "check-ixby-lean" do
  CompilatrixTests.Ixby.Native.run
