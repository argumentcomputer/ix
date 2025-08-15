import Ix.Aiur.Bytecode
import Std.Data.HashMap

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

structure CommitmentParameters where
  logBlowup : Nat

structure FriParameters where
  logFinalPolyLen : Nat
  numQueries : Nat
  proofOfWorkBits : Nat

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

structure IOKeyInfo where
  idx : Nat
  len : Nat
  deriving BEq

structure IOBuffer where
  data : Array G
  map : Std.HashMap (Array G) IOKeyInfo
  deriving Inhabited

instance : BEq IOBuffer where
  beq x y := x.data == y.data && x.map.toArray == y.map.toArray

namespace AiurSystem

@[extern "c_rs_aiur_system_build"]
opaque build : @&Bytecode.Toplevel → @&CommitmentParameters → AiurSystem

@[extern "c_rs_aiur_system_prove"]
private opaque prove' : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& Array G → (ioData : @& Array G) →
  (ioMap : @& Array (Array G × IOKeyInfo)) →
    Array G × Proof × Array G × Array (Array G × IOKeyInfo)

def prove (system : @& AiurSystem) (friParameters : @& FriParameters)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data
  let ioMap := ioBuffer.map
  let (claim, proof, ioData, ioMap) := prove' system friParameters funIdx args
    ioData ioMap.toArray
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "c_rs_aiur_system_verify"]
opaque verify : @& AiurSystem → @& FriParameters →
  @& Array G → @& Proof → Except String Unit

end AiurSystem

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur
