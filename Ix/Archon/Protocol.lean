import Ix.Archon.Circuit
import Ix.Archon.Witness
import Ix.Binius.Boundary

namespace Archon

open Binius

private opaque GenericNonempty : NonemptyType
def Proof : Type := GenericNonempty.type
instance : Nonempty Proof := GenericNonempty.property

@[never_extract, extern "c_rs_validate_witness"]
opaque validateWitness : @& Array CircuitModule → @& Array Boundary → @& Witness →
   Except String Unit

/-- **Invalidates** the input `Witness` -/
@[never_extract, extern "c_rs_prove"]
opaque prove : @& Array CircuitModule → @& Array Boundary →
  (logInvRate securitiByts : USize) → Witness → Proof

/-- **Invalidates** the input `Proof` -/
@[never_extract, extern "c_rs_verify"]
opaque verify : @& Array CircuitModule → @& Array Boundary →
  (logInvRate securitiByts : USize) → Proof → Except String Unit

end Archon
