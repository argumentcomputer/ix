/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import IxSetTheoryModel.Carneiro
import Ix.Ixon.ConLecheConsistency

/-!
# The certified checker's consistency under Carneiro's hypothesis

The checker's theorems hold in every `ConLeche.SetTheory V`
(`Ix.Ixon.ConLecheAdmission`). With the instance on Mathlib's `ZFSet` built
from `ω` inaccessible cardinals (`conLecheSetTheoryOfCarneiro`), they hold in
a concrete model: every environment the certified Ixon entry accepts has a
model in `ZFSet`, and no accepted constant has the pinned `False` as its type.
The inaccessible cardinals remain a hypothesis.
-/

universe u

namespace IxSetTheoryModel

open Ix.Ixon.ConLecheAdmission (checkBytes)

/-- **Every input the certified Ixon entry accepts has a model in `ZFSet`**,
given `ω` strongly inaccessible cardinals. -/
theorem checkBytes_has_ZFSet_model (h : OmegaInaccessibles.{u})
    {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)}
    {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (accepted : checkBytes limits records blobs hint = .ok env) :
    Nonempty (@ConLeche.Model ZFSet.{u} (conLecheSetTheoryOfCarneiro h) env) :=
  @Ix.Ixon.ConLecheAdmission.checkBytes_has_model ZFSet.{u} (conLecheSetTheoryOfCarneiro h)
    limits records blobs hint env accepted

/-- **No accepted constant proves the pinned `False`**, given `ω` strongly
inaccessible cardinals. -/
theorem checkBytes_no_proof_of_False (h : OmegaInaccessibles.{u})
    {limits : Ix.Ixon.Admission.Limits} {records : Ix.Ixon.Admission.Records}
    {blobs : List (Address × ByteArray)}
    {hint : Ix.Kernel.ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (accepted : checkBytes limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const ConLeche.falseName [] → False :=
  @Ix.Ixon.ConLecheAdmission.checkBytes_no_proof_of_False ZFSet.{u} (conLecheSetTheoryOfCarneiro h)
    limits records blobs hint env accepted

end IxSetTheoryModel
