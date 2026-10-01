/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import IxSetTheoryModel.Carneiro
import Ix.Ixon.Consistency

/-!
# The certified checker's consistency under Carneiro's hypothesis

The checker's theorems hold in every `Ix.Kernel.SetTheory V`
(`Ix.Ixon.Consistency`). With the instance on Mathlib's `ZFSet` built
from `ω` inaccessible cardinals (`zfSetTheoryOfCarneiro`), they hold in
a concrete model: every environment the certified Ixon entry accepts has a
model in `ZFSet`, and no accepted constant has the pinned `False` as its type.
The inaccessible cardinals remain a hypothesis.
-/

universe u

namespace IxSetTheoryModel

open Ix.Ixon.Admission (checkBytes)

/-- **Every input the certified Ixon entry accepts has a model in `ZFSet`**,
given `ω` strongly inaccessible cardinals. -/
theorem checkBytes_has_ZFSet_model (h : OmegaInaccessibles.{u})
    {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (accepted : checkBytes limits records blobs hint = .ok env) :
    Nonempty (@Ix.Kernel.Model ZFSet.{u} (zfSetTheoryOfCarneiro h) env) :=
  @Ix.Ixon.Admission.checkBytes_has_model ZFSet.{u} (zfSetTheoryOfCarneiro h)
    limits records blobs hint env accepted

/-- **No accepted constant proves the pinned `False`**, given `ω` strongly
inaccessible cardinals. -/
theorem checkBytes_no_proof_of_False (h : OmegaInaccessibles.{u})
    {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (accepted : checkBytes limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  @Ix.Ixon.Admission.checkBytes_no_proof_of_False ZFSet.{u} (zfSetTheoryOfCarneiro h)
    limits records blobs hint env accepted

end IxSetTheoryModel
