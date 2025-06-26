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
  (logInvRate securityBits : USize) → Witness → Proof

/-- **Invalidates** the input `Proof` -/
@[never_extract, extern "c_rs_verify"]
opaque verify : @& Array CircuitModule → @& Array Boundary →
  (logInvRate securityBits : USize) → Proof → Except String Unit

/--
Serialize an Archon proof as a `ByteArray`.
* The 2 first bytes form an `UInt16` that tells how many modules there are
* Then, chunks of 8 bytes form `UInt64`s that tell the heights for each module
* Finally, the rest of the bytes compose the Binius proof transcript
-/
@[extern "c_rs_proof_to_bytes"]
opaque Proof.toBytes : @& Proof → ByteArray

@[extern "c_rs_proof_of_bytes"]
private opaque Proof.ofBytes' : @& ByteArray → Proof

def Proof.ofBytes (bytes : ByteArray) : Except String Proof :=
  let size := bytes.size
  if _ : 1 < size then -- 2 bytes are needed for the first `u16`
    let b₀ := bytes[0]
    let b₁ := bytes[1]
    let numModules := b₀.toNat + 256 * b₁.toNat
    let numHeightsBytes := numModules * 8 -- 8 bytes (an `u64`) for each module height
    if size < 2 + numHeightsBytes then
      .error "Not enough data to read modules heights"
    else
      .ok $ Proof.ofBytes' bytes
  else
    .error "Not enough data to read the number of modules"

end Archon
