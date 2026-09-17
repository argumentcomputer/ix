import Compilatrix.Ixby.Runtime.Native.Code.Number
import Compilatrix.Ixby.Runtime.Native.Code.Array
import Compilatrix.Ixby.Runtime.Native.Code.Field

namespace Compilatrix.Ixby.Runtime.Native.Code

open Lean Ix.Ixby

def entries : Array Entry := numberEntries ++ arrayEntries ++ fieldEntries

def constructors : Array (Name × CtorDecl) := #[
  (`Ixby.Runtime.Bytes, ⟨⟨1, 0, 0⟩, 2⟩),
  (`Ixby.Runtime.Array, ⟨⟨1, 0, 1⟩, 1⟩),
  (`Ixby.Runtime.WriterBuffer, ⟨⟨1, 0, 2⟩, 1⟩),
  (`List.nil, ⟨⟨1, 0, 3⟩, 0⟩),
  (`List.cons, ⟨⟨1, 0, 4⟩, 2⟩)]

end Compilatrix.Ixby.Runtime.Native.Code
