import Ix.Ixon.Authenticated
import Ix.Ixon.BlockOrder.Theorems

/-! # The theorems of the authenticated entries at BLAKE3

The generic entries' theorems hold at every hash; these are the
instantiations at the specification hash `Address.blake3Pure`, which the
admission hash is (`Address.admissionHash_eq`). Each is stated for the
executed function and depends on the standard axioms only. -/

namespace Ixon.Authenticated

open Ix.Kernel
open Ix.Kernel.Reader (defaultPins builtinPrelude builtinNatOpPins)

universe v

/-- An admission-hash address is 32 bytes. -/
theorem admissionHash_width (bytes : ByteArray) : (Address.admissionHash bytes).hash.size = 32 :=
  (Blake3.Pure.hash bytes).property

theorem checkBytes_eq : checkBytes = Admission.checkBytes Address.blake3Pure := rfl

theorem checkBytesProjection_eq : checkBytesProjection = Projection.checkBytes Address.blake3Pure := rfl

theorem checkBytesBlockOrder_eq : checkBytesBlockOrder = BlockOrder.checkBytes Address.blake3Pure := rfl

/-! ## The certified entry -/

/-- **Authentication**: every record and every blob of accepted bytes is
stored under the BLAKE3 hash of its bytes. -/
theorem checkBytes_authentic {limits : Admission.Limits} {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env} (h : checkBytes limits records blobs hint = .ok env) :
    Admission.Authentic Address.blake3Pure records blobs :=
  Admission.checkBytes_authentic h

/-- **Fidelity** at BLAKE3 (`Ix.Kernel.Admission.checkBytes_reading`). -/
theorem checkBytes_reading {limits : Admission.Limits} {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env} (h : checkBytes limits records blobs hint = .ok env) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      Admission.WithinBatch limits records blobs ∧ Admission.UniqueKeys records blobs ∧
      Admission.Authentic Address.blake3Pure records blobs ∧
        ∃ constants, Admission.RecordsRead limits records constants ∧
          Admission.Hashed Address.blake3Pure constants ∧
          Admission.Installed pins pre natPins constants blobs hint env :=
  Admission.checkBytes_reading h

/-- **Model existence** at BLAKE3. -/
theorem checkBytes_has_model (V : Type v) [Ix.Kernel.SetTheory V] {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  Admission.checkBytes_has_model V h

/-- **No proof of `False`** at BLAKE3. -/
theorem checkBytes_no_proof_of_False (V : Type v) [Ix.Kernel.SetTheory V] {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  Admission.checkBytes_no_proof_of_False V h

/-! ## Projection reconstruction -/

/-- **Authentication** with reconstruction: every supplied record and blob
is stored under the BLAKE3 hash of its bytes, and every record the checker
read, supplied or reconstructed, under the BLAKE3 hash of its
serialization. -/
theorem checkBytesProjection_authentic {maxProjections : Nat} {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesProjection maxProjections limits records blobs hint = .ok env) :
    Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ output, Admission.Hashed Address.blake3Pure output ∧
        Admission.checkConstants output blobs hint = .ok env :=
  Projection.checkBytes_authentic h

theorem checkBytesProjection_reading {maxProjections : Nat} {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesProjection maxProjections limits records blobs hint = .ok env) :
    Admission.UniqueKeys records blobs ∧ Admission.Authentic Address.blake3Pure records blobs ∧
    ∃ input output, Admission.RecordsRead limits records input ∧
      Projection.Expanded Address.blake3Pure maxProjections input output ∧
      Admission.Hashed Address.blake3Pure output ∧
      ∃ pins pre natPins, defaultPins = .ok pins ∧
        builtinPrelude = .ok pre ∧ builtinNatOpPins = .ok natPins ∧
        Admission.Installed pins pre natPins output blobs hint env :=
  Projection.checkBytes_reading h

theorem checkBytesProjection_has_model (V : Type v) [Ix.Kernel.SetTheory V] {maxProjections : Nat}
    {limits : Admission.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesProjection maxProjections limits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Projection.checkBytes_has_model V h

theorem checkBytesProjection_no_proof_of_False (V : Type v) [Ix.Kernel.SetTheory V]
    {maxProjections : Nat} {limits : Admission.Limits} {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env} (h : checkBytesProjection maxProjections limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  Projection.checkBytes_no_proof_of_False V h

/-! ## Canonical block order -/

theorem checkBytesBlockOrder_authentic {maxProjections : Nat} {limits : Admission.Limits}
    {orderLimits : BlockOrder.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder maxProjections limits orderLimits records blobs hint = .ok env) :
    Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ output, Admission.Hashed Address.blake3Pure output ∧
        Admission.checkConstants output blobs hint = .ok env :=
  BlockOrder.checkBytes_authentic h

theorem checkBytesBlockOrder_reading {maxProjections : Nat} {limits : Admission.Limits}
    {orderLimits : BlockOrder.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder maxProjections limits orderLimits records blobs hint = .ok env) :
    Admission.UniqueKeys records blobs ∧ Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ input output, Admission.RecordsRead limits records input ∧
      Projection.Expanded Address.blake3Pure maxProjections input output ∧
      BlockOrder.Ordered Address.blake3Pure orderLimits blobs input ∧
      Admission.Hashed Address.blake3Pure output ∧
      ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
        builtinNatOpPins = .ok natPins ∧
        Admission.Installed pins pre natPins output blobs hint env :=
  BlockOrder.checkBytes_reading h

theorem checkBytesBlockOrder_has_model (V : Type v) [Ix.Kernel.SetTheory V] {maxProjections : Nat}
    {limits : Admission.Limits} {orderLimits : BlockOrder.Limits} {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder maxProjections limits orderLimits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  BlockOrder.checkBytes_has_model V h

theorem checkBytesBlockOrder_no_proof_of_False (V : Type v) [Ix.Kernel.SetTheory V]
    {maxProjections : Nat} {limits : Admission.Limits} {orderLimits : BlockOrder.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder maxProjections limits orderLimits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  BlockOrder.checkBytes_no_proof_of_False V h

end Ixon.Authenticated
