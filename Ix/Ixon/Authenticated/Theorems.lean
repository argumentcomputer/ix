import Ix.Ixon.Authenticated
import Ix.Ixon.BlockOrder.Theorems

/-! # The theorems of the authenticated entries at BLAKE3

The generic entries' theorems hold at every hash and every role table;
these are the instantiations at the specification hash `Address.blake3Pure`,
which the admission hash is (`Address.admissionHash_eq`). Each is stated for
the executed function and depends on the standard axioms only. -/

namespace Ixon.Authenticated

open Ix.Kernel
open Ix.Kernel.Reader (preludeFor)

universe v

/-- An admission-hash address is 32 bytes. -/
theorem admissionHash_width (bytes : ByteArray) : (Address.admissionHash bytes).hash.size = 32 :=
  (Blake3.Pure.hash bytes).property

theorem checkBytes_eq : checkBytes = Admission.checkBytes Address.blake3Pure := rfl

theorem checkBytesProjection_eq : checkBytesProjection = Projection.checkBytes Address.blake3Pure := rfl

theorem checkBytesBlockOrder_eq : checkBytesBlockOrder = BlockOrder.checkBytes Address.blake3Pure := rfl

/-! ## The certified entry -/

/-- **Authentication**: every record and every blob of accepted bytes is
stored under the BLAKE3 hash of its bytes, and so is the role table's
section. -/
theorem checkBytes_authentic {binding : Admission.Binding} {limits : Admission.Limits}
    {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env} (h : checkBytes binding limits records blobs hint = .ok env) :
    Admission.Authentic Address.blake3Pure records blobs ∧
      Address.blake3Pure binding.bytes = binding.address :=
  Admission.checkBytes_authentic h

/-- **The role table** at BLAKE3: accepted bytes came with an admitted table,
its section stored under the BLAKE3 hash of its bytes (the binding hash). -/
theorem checkBytes_binding {binding : Admission.Binding} {limits : Admission.Limits}
    {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env} (h : checkBytes binding limits records blobs hint = .ok env) :
    ∃ t, Admission.BindingAdmitted Address.blake3Pure binding t :=
  Admission.checkBytes_binding h

/-- **Fidelity** at BLAKE3 (`Ix.Kernel.Admission.checkBytes_reading`). -/
theorem checkBytes_reading {binding : Admission.Binding} {limits : Admission.Limits}
    {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env} (h : checkBytes binding limits records blobs hint = .ok env) :
    ∃ t pre, Admission.admitBinding Address.blake3Pure binding = .ok t ∧ preludeFor t = .ok pre ∧
      Admission.WithinBatch limits records blobs ∧ Admission.UniqueKeys records blobs ∧
      Admission.Authentic Address.blake3Pure records blobs ∧
        ∃ constants, Admission.BindingAdmitted Address.blake3Pure binding t ∧
          Admission.RecordsRead limits records constants ∧
          Admission.Hashed Address.blake3Pure constants ∧
          Admission.Installed t pre constants blobs hint env :=
  Admission.checkBytes_reading h

/-- **Model existence** at BLAKE3. -/
theorem checkBytes_has_model (V : Type v) [Ix.Kernel.SetTheory V] {binding : Admission.Binding}
    {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes binding limits records blobs hint = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  Admission.checkBytes_has_model V h

/-- **No proof of `False`** at BLAKE3, at `False`'s role key, for every role
table. -/
theorem checkBytes_no_proof_of_False (V : Type v) [Ix.Kernel.SetTheory V]
    {binding : Admission.Binding} {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes binding limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False :=
  Admission.checkBytes_no_proof_of_False V h

/-! ## Projection reconstruction -/

/-- **Authentication** with reconstruction: every supplied record and blob
is stored under the BLAKE3 hash of its bytes, and every record the checker
read, supplied or reconstructed, under the BLAKE3 hash of its
serialization. -/
theorem checkBytesProjection_authentic {binding : Admission.Binding} {maxProjections : Nat}
    {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesProjection binding maxProjections limits records blobs hint = .ok env) :
    Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ output, Admission.Hashed Address.blake3Pure output ∧
        Admission.checkConstantsAt Address.blake3Pure binding output blobs hint = .ok env :=
  Projection.checkBytes_authentic h

theorem checkBytesProjection_reading {binding : Admission.Binding} {maxProjections : Nat}
    {limits : Admission.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesProjection binding maxProjections limits records blobs hint = .ok env) :
    Admission.UniqueKeys records blobs ∧ Admission.Authentic Address.blake3Pure records blobs ∧
    ∃ input output, Admission.RecordsRead limits records input ∧
      Projection.Expanded Address.blake3Pure maxProjections input output ∧
      Admission.Hashed Address.blake3Pure output ∧
      ∃ t pre, Admission.BindingAdmitted Address.blake3Pure binding t ∧ preludeFor t = .ok pre ∧
        Admission.Installed t pre output blobs hint env :=
  Projection.checkBytes_reading h

theorem checkBytesProjection_has_model (V : Type v) [Ix.Kernel.SetTheory V]
    {binding : Admission.Binding} {maxProjections : Nat}
    {limits : Admission.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesProjection binding maxProjections limits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  Projection.checkBytes_has_model V h

theorem checkBytesProjection_no_proof_of_False (V : Type v) [Ix.Kernel.SetTheory V]
    {binding : Admission.Binding} {maxProjections : Nat} {limits : Admission.Limits}
    {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env}
    (h : checkBytesProjection binding maxProjections limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False :=
  Projection.checkBytes_no_proof_of_False V h

/-! ## Canonical block order -/

theorem checkBytesBlockOrder_authentic {binding : Admission.Binding} {maxProjections : Nat}
    {limits : Admission.Limits}
    {orderLimits : BlockOrder.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder binding maxProjections limits orderLimits records blobs hint = .ok env) :
    Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ output, Admission.Hashed Address.blake3Pure output ∧
        Admission.checkConstantsAt Address.blake3Pure binding output blobs hint = .ok env :=
  BlockOrder.checkBytes_authentic h

theorem checkBytesBlockOrder_reading {binding : Admission.Binding} {maxProjections : Nat}
    {limits : Admission.Limits}
    {orderLimits : BlockOrder.Limits} {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder binding maxProjections limits orderLimits records blobs hint = .ok env) :
    Admission.UniqueKeys records blobs ∧ Admission.Authentic Address.blake3Pure records blobs ∧
      ∃ input output, Admission.RecordsRead limits records input ∧
      Projection.Expanded Address.blake3Pure maxProjections input output ∧
      BlockOrder.Ordered Address.blake3Pure orderLimits blobs input ∧
      Admission.Hashed Address.blake3Pure output ∧
      ∃ t pre, Admission.BindingAdmitted Address.blake3Pure binding t ∧ preludeFor t = .ok pre ∧
        Admission.Installed t pre output blobs hint env :=
  BlockOrder.checkBytes_reading h

theorem checkBytesBlockOrder_has_model (V : Type v) [Ix.Kernel.SetTheory V]
    {binding : Admission.Binding} {maxProjections : Nat}
    {limits : Admission.Limits} {orderLimits : BlockOrder.Limits} {records : Admission.Records}
    {blobs : Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder binding maxProjections limits orderLimits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  BlockOrder.checkBytes_has_model V h

theorem checkBytesBlockOrder_no_proof_of_False (V : Type v) [Ix.Kernel.SetTheory V]
    {binding : Admission.Binding} {maxProjections : Nat} {limits : Admission.Limits}
    {orderLimits : BlockOrder.Limits}
    {records : Admission.Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytesBlockOrder binding maxProjections limits orderLimits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False :=
  BlockOrder.checkBytes_no_proof_of_False V h

end Ixon.Authenticated
