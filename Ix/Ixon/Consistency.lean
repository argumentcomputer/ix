/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Admission
import Ix.Ixon.ConLecheConsistency

/-! # The public theorems of the certified Ixon API

The contract of `Ix.Ixon.Admission.checkBytes` (roadmap section 2), stated
for the executed function. Each theorem is the con-leche entry's
(`Ix.Ixon.ConLecheConsistency`, where the same statements hold at every pin
table, prelude and Nat-operation pin list) at the committed tables.

* `checkBytes_has_model`: every accepted input has a model in con-leche's
  sense (`ConLeche.Model`) in every set theory (D2 (iii));
  `checkBytes_has_model_values`: one in which every stored definition's
  value denotes the constant (D2 (ii)).
* `checkBytes_no_proof_of_False`: no accepted constant has the pinned
  `False` as its type; `checkBytes_no_False_theorem`: no theorem record of
  accepted bytes has a type that reads as the pinned `False` (D3, con-leche's
  pinned form).
* `checkBytes_reading`: fidelity: the batch limits, key uniqueness
  (`UniqueKeys`), the exact canonical reading of every record, and
  installation of what the records describe.
* `checkBytes_resources`: the byte limits bound the decoded representation.

The set theory is the standing hypothesis; `Models/SetTheory` provides an
instance on Mathlib's `ZFSet` under `ω` inaccessible cardinals. -/

namespace Ix.Ixon.Admission

open Kernel
open Ix.Kernel.ConLecheReader (Pins Prelude defaultPins builtinPrelude builtinNatOpPins definitionReader)
open Ix.Ixon.Verify.Admission (WithinBatch UniqueKeys RecordsRead resourceUnits)

universe u

/-- The certified entry is the con-leche entry at the committed tables. -/
theorem checkBytes_eq (limits : Limits) (records : Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) :
    checkBytes limits records blobs hint = ConLecheAdmission.checkBytes limits records blobs hint := rfl

/-- **Model existence.** Every environment the certified entry accepts has
a model in every set theory. -/
theorem checkBytes_has_model (V : Type u) [ConLeche.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) : Nonempty (ConLeche.Model V env) :=
  ConLecheAdmission.checkBytes_has_model V h

/-- **Model existence with definition values.** The model can be chosen so
that every stored definition's value denotes the constant. -/
theorem checkBytes_has_model_values (V : Type u) [ConLeche.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ M : ConLeche.Model V env, ∀ cv value hint', ConLeche.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, ConLeche.Denotes M.cval env φ ρ value (M.cval cv.name φ) :=
  ConLecheAdmission.checkBytes_has_model_values V h

/-- **No proof of `False`.** No constant of an accepted environment has the
pinned `False` as its type. -/
theorem checkBytes_no_proof_of_False (V : Type u) [ConLeche.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const ConLeche.falseName [] → False :=
  ConLecheAdmission.checkBytes_no_proof_of_False V h

/-- **No accepted theorem of `False`, at the records.** No theorem record of
accepted bytes has a type that reads as the pinned `False`. -/
theorem checkBytes_no_False_theorem (V : Type u) [ConLeche.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) {pins : Pins} {pre : Prelude}
    (hpins : defaultPins = .ok pins) (hpre : builtinPrelude = .ok pre)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (ConLecheAdmission.streamContext pins pre constants blobs hint) owner c d).read
      d.typ = .ok (.const ConLeche.falseName [])) : False :=
  ConLecheAdmission.checkBytes_no_False_theorem V h hpins hpre reading hmem hc hk hty

/-- **Fidelity.** Accepted bytes are within the batch limits, use each
record address and each blob address once, read exactly and canonically,
and the checker installed what the records describe
(`ConLecheAdmission.Installed`). -/
theorem checkBytes_reading {limits : Limits} {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      WithinBatch limits records blobs ∧ UniqueKeys records blobs ∧
        ∃ constants, RecordsRead limits records constants ∧
          ConLecheAdmission.Installed pins pre natPins constants blobs hint env :=
  ConLecheAdmission.checkBytes_reading h

/-- **Resources.** The byte limits bound the whole decoded representation. -/
theorem checkBytes_resources {limits : Limits} {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ constants, RecordsRead limits records constants ∧
      resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes :=
  ConLecheAdmission.checkBytes_resources h

end Ix.Ixon.Admission
