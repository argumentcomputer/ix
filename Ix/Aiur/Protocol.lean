module
public import Ix.Aiur.Semantics.BytecodeFfi

/-!
AiurSystem, Proof, FRI params, and `buildClaim` — the "prove & verify" FFI surface.

The bytecode-execution FFI that used to live here has moved to
`Ix/Aiur/Bytecode/ExecuteFfi.lean` so that `Bytecode/Eval.lean` can be built
without pulling in the proving backend.
-/

public section

namespace Aiur

private opaque PoofNonempty : NonemptyType
def Proof : Type := PoofNonempty.type
instance : Nonempty Proof := PoofNonempty.property

namespace Proof

@[extern "rs_aiur_proof_to_bytes"]
opaque toBytes : @& Proof → ByteArray

@[extern "rs_aiur_proof_of_bytes"]
opaque ofBytes : @& ByteArray → Proof

end Proof

structure CommitmentParameters where
  logBlowup : Nat
  capHeight : Nat

structure FriParameters where
  logFinalPolyLen : Nat
  maxLogArity : Nat
  numQueries : Nat
  commitProofOfWorkBits : Nat
  queryProofOfWorkBits : Nat

private opaque AiurSystemNonempty : NonemptyType
def AiurSystem : Type := AiurSystemNonempty.type
instance : Nonempty AiurSystem := AiurSystemNonempty.property

namespace AiurSystem

@[extern "rs_aiur_system_build"]
opaque build : @&Bytecode.Toplevel → @&CommitmentParameters → AiurSystem

@[extern "rs_aiur_system_prove"]
private opaque prove' : @& AiurSystem → @& FriParameters →
  @& Bytecode.FunIdx → @& Array G → (ioData : @& Array G) →
  (ioMap : @& Array (Array G × IOKeyInfo)) →
    Array G × Proof × Array G × Array (Array G × IOKeyInfo)

/-- Executes the bytecode function `funIdx` with the given `args` and `ioBuffer`,
then generates a proof of the computation. Returns the claim
(`#[functionChannel, funIdx] ++ args ++ output`), the `Proof`, and the
updated `IOBuffer`. -/
def prove (system : @& AiurSystem) (friParameters : @& FriParameters)
  (funIdx : @& Bytecode.FunIdx) (args : @& Array G) (ioBuffer : IOBuffer) :
    Array G × Proof × IOBuffer :=
  let ioData := ioBuffer.data
  let ioMap := ioBuffer.map
  let (claim, proof, ioData, ioMap) := prove' system friParameters funIdx args
    ioData ioMap.toArray
  let ioMap := ioMap.foldl (fun acc (k, v) => acc.insert k v) ∅
  (claim, proof, ⟨ioData, ioMap⟩)

@[extern "rs_aiur_system_verify"]
opaque verify : @& AiurSystem → @& FriParameters →
  @& Array G → @& Proof → Except String Unit

end AiurSystem

abbrev functionChannel : G := .ofNat 0

def buildClaim (funIdx : Bytecode.FunIdx) (input output : Array G) :=
  #[functionChannel, .ofNat funIdx] ++ input ++ output

end Aiur

end -- public section
