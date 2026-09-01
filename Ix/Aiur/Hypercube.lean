module

public import Ix.Aiur.Protocol

/-!
# The SP1 Hypercube proving backend (KoalaBear)

The FFI surface of `crates/ffi/src/aiur/hypercube.rs`, mirroring the
multi-stark `AiurSystem` at the minimum the pipeline needs: build a system
from a KOALABEAR-PROFILE bytecode toplevel (`IxVM.koalaBearProfile`; the
FFI's checked constant embedding rejects anything Goldilocks-sized) and an
entry function, prove a call, verify a proof blob.

Field values cross the FFI as canonical `u64`s inside `Aiur.G` (every
canonical KoalaBear value is far below the Goldilocks modulus), so
`IOBuffer` and claims reuse the existing types; the Rust side checks
canonicity on ingest.
-/

public section

namespace Aiur

private opaque HypercubeSystemNonempty : NonemptyType
def HypercubeSystem : Type := HypercubeSystemNonempty.type
instance : Nonempty HypercubeSystem := HypercubeSystemNonempty.property

namespace HypercubeSystem

/-- Build the Hypercube machine for `funIdx` (every circuit of the toplevel
is synthesized; the entry fixes the claim layout). -/
@[extern "rs_aiur_hypercube_build"]
opaque build : @& Bytecode.Toplevel → @& Bytecode.FunIdx →
  Except String HypercubeSystem

@[extern "rs_aiur_hypercube_prove"]
private opaque prove' : @& HypercubeSystem → @& Array G →
  (ioData : @& Array (G × Array G)) →
  (ioMap : @& Array ((G × Array G) × IOKeyInfo)) →
    Except String (Array G × ByteArray)

/-- Executes the entry function with `args` and `ioBuffer` and proves the
execution. Returns the claim (`#[functionChannel, funIdx] ++ args ++
output`) and the proof blob (`(vk, proof)` bincoded). -/
def prove (system : @& HypercubeSystem) (args : @& Array G)
    (ioBuffer : IOBuffer) : Except String (Array G × ByteArray) :=
  prove' system args ioBuffer.data.toArray ioBuffer.map.toArray

/-- Verifies a proof blob against the system and the expected claim (checked
as the proof's public-value prefix). -/
@[extern "rs_aiur_hypercube_verify"]
opaque verify : @& HypercubeSystem → @& Array G → @& ByteArray →
  Except String Unit

end HypercubeSystem

end Aiur

end
