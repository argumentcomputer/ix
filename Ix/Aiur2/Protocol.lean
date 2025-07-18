import Ix.Aiur2.Bytecode

namespace Aiur

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

@[extern "c_rs_aiur_system_build"]
opaque AiurSystem.build : @&Bytecode.Toplevel → AiurSystem

structure FriParameters where
  logBlowup : Nat
  logFinalPolyLen : Nat
  numQueries : Nat
  proofOfWorkBits : Nat

structure Claim where
  circuitIdx : Nat
  args : Array G
  deriving Inhabited

private opaque PoofNonempty : NonemptyType
def Proof : Type := PoofNonempty.type
instance : Nonempty Proof := PoofNonempty.property

@[extern "c_rs_aiur_system_prove"]
private opaque AiurSystem.prove : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& Array G → Claim × Proof

@[extern "c_rs_aiur_verify"]
opaque AiurSystem.verify : @& AiurSystem → @& FriParameters → @& Claim → @& Proof →
  Except String Unit

end Aiur
