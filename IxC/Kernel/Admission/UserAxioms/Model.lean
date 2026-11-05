import IxC.Kernel.Admission.UserAxioms
import IxC.Kernel.Admission.Theorems

/-! # The model of an accept that lists no user axiom

T1 (`checkBytesUnder_strict_of_nil`, `IxC/Kernel/Admission/UserAxioms.lean`)
makes such an accept the certified entry's, and `checkBytesWith_has_model`
gives that one a model. This theorem needs `Ix.Kernel.Admission.Theorems`,
which is not a `module`, so it is not in `UserAxioms.lean`, which is. -/

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

universe u

/-- **Model existence without user axioms**: an accept of the bytes entry under
any policy that lists no user axiom has a model in every set theory. -/
theorem checkBytesUnder_has_model_of_nil (V : Type u) [Ix.Kernel.SetTheory V]
    {policy : Ix.Kernel.Cached.AxiomPolicy}
    {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesUnder policy hash binding pre limits records blobs hint = .ok (env, [])) :
    Nonempty (Ix.Kernel.Model V env) :=
  checkBytesWith_has_model V (checkBytesUnder_strict_of_nil h)

end Ix.Kernel.Admission
