/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.Admission
import Ix.Ixon.KernelConsistency

/-! # The public theorems of the certified Ixon API

The contract of `Ix.Ixon.Admission.checkBytes` (`docs/kernel.md`), stated
for the executed function. Each theorem is the kernel entry's
(`Ix.Ixon.KernelConsistency`, where the same statements hold at every pin
table, prelude and Nat-operation pin list) at the committed tables.

* `checkBytes_has_model`: every accepted input has a model
  (`Ix.Kernel.Model`) in every set theory; `checkBytes_has_model_values`:
  one in which every stored definition's value denotes the constant.
* `checkBytes_no_proof_of_False`: no accepted constant has the pinned
  `False` as its type; `checkBytes_no_False_theorem`: no theorem record of
  accepted bytes has a type that reads as the pinned `False`
  (`Ix.Kernel.falseName`).
* `checkBytes_reading`: fidelity: the batch limits, key uniqueness
  (`UniqueKeys`), the exact canonical reading of every record, and
  installation of what the records describe.
* `checkBytes_resources`: the byte limits bound the decoded representation.

The set theory is the standing hypothesis; `Models/SetTheory` provides an
instance on Mathlib's `ZFSet` under `ω` inaccessible cardinals. -/

namespace Ix.Ixon.Admission

open Kernel
open Ix.Kernel.IxonReader (Pins Prelude defaultPins builtinPrelude builtinNatOpPins definitionReader)
open Ix.Ixon.Verify.Admission (WithinBatch UniqueKeys RecordsRead resourceUnits)

universe u

/-- The certified entry is the kernel entry at the committed tables. -/
theorem checkBytes_eq (limits : Limits) (records : Records) (blobs : Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    checkBytes limits records blobs hint = KernelAdmission.checkBytes limits records blobs hint := rfl

/-- **Model existence.** Every environment the certified entry accepts has
a model in every set theory. -/
theorem checkBytes_has_model (V : Type u) [Ix.Kernel.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) : Nonempty (Ix.Kernel.Model V env) :=
  KernelAdmission.checkBytes_has_model V h

/-- **Model existence with definition values.** The model can be chosen so
that every stored definition's value denotes the constant. -/
theorem checkBytes_has_model_values (V : Type u) [Ix.Kernel.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ∀ cv value hint', Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) :=
  KernelAdmission.checkBytes_has_model_values V h

/-- **No proof of `False`.** No constant of an accepted environment has the
pinned `False` as its type. -/
theorem checkBytes_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const Ix.Kernel.falseName [] → False :=
  KernelAdmission.checkBytes_no_proof_of_False V h

/-- **No accepted theorem of `False`, at the records.** No theorem record of
accepted bytes has a type that reads as the pinned `False`. -/
theorem checkBytes_no_False_theorem (V : Type u) [Ix.Kernel.SetTheory V] {limits : Limits}
    {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) {pins : Pins} {pre : Prelude}
    (hpins : defaultPins = .ok pins) (hpre : builtinPrelude = .ok pre)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (KernelAdmission.streamContext pins pre constants blobs hint) owner c d).read
      d.typ = .ok (.const Ix.Kernel.falseName [])) : False :=
  KernelAdmission.checkBytes_no_False_theorem V h hpins hpre reading hmem hc hk hty

/-- **Fidelity.** Accepted bytes are within the batch limits, use each
record address and each blob address once, read exactly and canonically,
and the checker installed what the records describe
(`KernelAdmission.Installed`). -/
theorem checkBytes_reading {limits : Limits} {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      WithinBatch limits records blobs ∧ UniqueKeys records blobs ∧
        ∃ constants, RecordsRead limits records constants ∧
          KernelAdmission.Installed pins pre natPins constants blobs hint env :=
  KernelAdmission.checkBytes_reading h

/-- **Resources.** The byte limits bound the whole decoded representation. -/
theorem checkBytes_resources {limits : Limits} {records : Records} {blobs : Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ constants, RecordsRead limits records constants ∧
      resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes :=
  KernelAdmission.checkBytes_resources h

end Ix.Ixon.Admission
