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

private opaque PoofNonempty : NonemptyType
def Proof : Type := PoofNonempty.type
instance : Nonempty Proof := PoofNonempty.property

@[extern "c_rs_aiur_system_prove"]
opaque AiurSystem.prove : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& Array G → Array G × Proof

@[extern "c_rs_aiur_system_verify"]
opaque AiurSystem.verify : @& AiurSystem → @& FriParameters →
  @& Array G → @& Proof → Except String Unit

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur
