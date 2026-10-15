import IxSetTheoryModel.Carneiro
import IxC.Kernel.Admission.Theorems

/-!
# The certified checker's consistency under Carneiro's hypothesis

The checker's theorems hold in every `Ix.Kernel.SetTheory V`
(`Ix.Kernel.Admission.Theorems`). With the instance on Mathlib's `ZFSet` built
from `ω` inaccessible cardinals (`zfSetTheoryOfCarneiro`), they hold in
a concrete model: every environment the certified Ixon entry accepts, at any
content hash and under any role table, has a model in `ZFSet`, and no
accepted constant has `False`'s role key as its type. The inaccessible cardinals remain a hypothesis.
-/

universe u

namespace IxSetTheoryModel

open Ix.Kernel.Admission (checkBytes)

/-- **Every input the certified Ixon entry accepts has a model in `ZFSet`**,
given `ω` strongly inaccessible cardinals. -/
theorem checkBytes_has_ZFSet_model (h : OmegaInaccessibles.{u}) {hash : ByteArray → Address}
    {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env md}
    (accepted : checkBytes hash binding limits records blobs hint = .ok env) :
    Nonempty (@Ix.Kernel.Model md ZFSet.{u} (zfSetTheoryOfCarneiro h) env) :=
  @Ix.Kernel.Admission.checkBytes_has_model md ZFSet.{u} (zfSetTheoryOfCarneiro h)
    hash binding limits records blobs hint env accepted

/-- **No accepted constant proves `False`**, given `ω` strongly
inaccessible cardinals. -/
theorem checkBytes_no_proof_of_False (h : OmegaInaccessibles.{u}) {hash : ByteArray → Address}
    {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env md}
    (accepted : checkBytes hash binding limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  @Ix.Kernel.Admission.checkBytes_no_proof_of_False md ZFSet.{u} (zfSetTheoryOfCarneiro h)
    hash binding limits records blobs hint env accepted

end IxSetTheoryModel
