import Ix.Aiur.Bytecode

namespace Aiur

private opaque PoofNonempty : NonemptyType
def Proof : Type := PoofNonempty.type
instance : Nonempty Proof := PoofNonempty.property

namespace Proof

@[extern "c_rs_aiur_proof_to_bytes"]
opaque toBytes : @& Proof → ByteArray

@[extern "c_rs_aiur_proof_of_bytes"]
opaque ofBytes : @& ByteArray → Proof

end Proof

structure FriParameters where
  logBlowup : Nat
  logFinalPolyLen : Nat
  numQueries : Nat
  proofOfWorkBits : Nat

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

namespace AiurSystem

@[extern "c_rs_aiur_system_build"]
opaque build : @&Bytecode.Toplevel → AiurSystem

@[extern "c_rs_aiur_system_prove"]
opaque prove : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& Array G → Array G × Proof

@[extern "c_rs_aiur_system_verify"]
opaque verify : @& AiurSystem → @& FriParameters →
  @& Array G → @& Proof → Except String Unit

end AiurSystem

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur
