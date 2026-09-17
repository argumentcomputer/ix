import Compilatrix.Ixby.Runtime.Native.WireCertificate
import Compilatrix.Ixby.Runtime.Native.Values

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby

def writeState (buffer : Value) (byteLimit : Nat) (nodes depth : Value) : Value :=
  .ctor ⟨1, 0, 5⟩ #[buffer, natural byteLimit, nodes, depth]

def pairValue (a b : Value) : Value := .ctor ⟨1, 0, 10⟩ #[a, b]
def unitValue : Value := .ctor ⟨1, 0, 9⟩ #[]
def okValue (value : Value) : Value := .ctor ⟨1, 0, 7⟩ #[value]
def errorValue (value : Value) : Value := .ctor ⟨1, 0, 6⟩ #[value]
def byteLimitError : Value := errorValue (.ctor ⟨1, 0, 8⟩ #[])

def encodeLocals (configId : CtorId) (byteLimit : Nat) (nodes depth writer : Value) : Array Value :=
  #[.ctor configId #[natural byteLimit, nodes, depth], writer, .byteBuilder #[], writerValue #[],
    natural byteLimit, nodes, depth, writeState (writerValue #[]) byteLimit nodes depth]

def encodeSaved (configId : CtorId) (byteLimit : Nat) (nodes depth writer : Value) : Frame :=
  { function := 100, block := 7, locals := encodeLocals configId byteLimit nodes depth writer }

@[simp] theorem error_ok_distinct : ((⟨1, 0, 6⟩ : CtorId) == ⟨1, 0, 7⟩) = false := rfl

/-- The source writer's sequence is represented internally by a builder.
Other state fields keep the same values across a byte write. -/
def WriterRep (bytes : Array UInt8) (byteLimit : Nat) (nodes depth state : Value) : Prop :=
  state = writeState (writerValue bytes) byteLimit nodes depth

theorem writerRep_append_alias (before chunk : Array UInt8) (byteLimit : Nat) (nodes depth : Value) :
    WriterRep before byteLimit nodes depth (writeState (writerValue before) byteLimit nodes depth) ∧
    WriterRep (before ++ chunk) byteLimit nodes depth
      (writeState (writerValue (before ++ chunk)) byteLimit nodes depth) := ⟨rfl, rfl⟩

end Compilatrix.Ixby.Runtime.Native
