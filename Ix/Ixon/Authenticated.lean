import Ix.Address.Admission
import Ix.Ixon.BlockOrder

/-! # The authenticated Ixon entries at BLAKE3

The certified entries take their content hash as a parameter: the kernel
admits no hasher (`Ix.Kernel.Admission.checkBytes`), and the root library's
variants are generic in it too (`Ixon.Projection.checkBytes`,
`Ixon.BlockOrder.checkBytes`). These are the three at the admission hash
`Address.admissionHash`, which is pure BLAKE3 (`Address.blake3Pure`) for
every theorem and executes as the Rust BLAKE3 (`Address.blake3`); that
substitution is the one assumption the authenticated entries add to the
kernel's trust surface (`Ix.Kernel.Audit.assumedSubstitutions`).

An Ixon address is BLAKE3 of exact bytes, with no tag or length prefix: a
record's is BLAKE3 of its complete serialization (`Ixon.serConstant`, the
bytes an `.ixe` stores for it after its length prefix), a projection
record's likewise, and a blob's is BLAKE3 of its payload. This is how the
compiler addresses them (`crates/compile`, `Address::hash` over
`Constant::put`), how the `.ixe` loaders verify them (`Ixon.getEnv`,
`Ixon.getEnvVerifiedLazy`), and how the resource adapter commits them
(`Ix.Resource.Addressed.commit`).

Theorems: `Ixon.Authenticated.Theorems`; audit: `Ixon.Authenticated.Audit`. -/

namespace Ixon.Authenticated

open Ix.Kernel

/-- **The certified Ixon entry at BLAKE3** (`Ix.Kernel.Admission.checkBytes`
at `Address.admissionHash`). -/
def checkBytes (binding : Admission.Binding) (limits : Admission.Limits) (records : Admission.Records)
    (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Admission.Error Ix.Kernel.Env :=
  Admission.checkBytes Address.admissionHash binding limits records blobs hint

/-- The entry with omitted projection records reconstructed, at BLAKE3
(`Ixon.Projection.checkBytes` at `Address.admissionHash`). -/
def checkBytesProjection (binding : Admission.Binding) (maxProjections : Nat)
    (limits : Admission.Limits) (records : Admission.Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except Projection.CheckError Ix.Kernel.Env :=
  Projection.checkBytes Address.admissionHash binding maxProjections limits records blobs hint

/-- The entry with canonical block order, at BLAKE3
(`Ixon.BlockOrder.checkBytes` at `Address.admissionHash`). -/
def checkBytesBlockOrder (binding : Admission.Binding) (maxProjections : Nat)
    (limits : Admission.Limits) (orderLimits : BlockOrder.Limits) (records : Admission.Records)
    (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint := fun _ => none) :
    Except BlockOrder.CheckError Ix.Kernel.Env :=
  BlockOrder.checkBytes Address.admissionHash binding maxProjections limits orderLimits records blobs
    hint

/-- A projection record's address at BLAKE3. -/
def projectionAddress (record : Ixon.Constant) : Address :=
  Projection.address Address.admissionHash record

/-- Projection reconstruction at BLAKE3. -/
def reconstruct (maxProjections : Nat) (constants : Ingress.Constants) :
    Except Projection.Error Ingress.Constants :=
  Projection.reconstruct Address.admissionHash maxProjections constants

end Ixon.Authenticated
