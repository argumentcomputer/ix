/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Ixon.ConLecheAdmission
import Ix.Ixon.Verify.Admission
import Ix.Kernel.ConLeche.ReaderSpec
import Ix.Kernel.ConLeche.Installed
import Ix.Kernel.ConLeche.Values
import ConLeche.Verify.Cached.StreamThm
import ConLeche.Verify.Frontend.Prepare

/-! # The public theorems of the con-leche entry (plan v4, L5)

The certified contract of Ix's Ixon checker from L5 on (roadmap section 2,
decisions D2 (iii) and D3): con-leche's verified fold
(`ConLeche.Cached.checkDecls .verified`) behind the Ixon reader, stated for
the executed functions.

* **Model existence** (`checkConstantsWith_has_model`,
  `checkBytesWith_has_model`, `checkBytes_has_model`): every accepted input
  has a model in con-leche's sense (`ConLeche.Model`, which states types)
  in every set theory. This is `ConLeche.model_exists` at the prepared
  declarations; the reader owes nothing.
* **No proof of `False`, in con-leche's pinned form** (D3).
  `checkBytesWith_no_proof_of_False`: no constant of an accepted environment
  has the pinned `False` (`ConLeche.falseName`) as its type.
  `checkBytesWith_no_False_theorem`: no theorem record of an accepted input
  has a type that reads as the pinned `False`; this is
  `ConLeche.no_False_theorem_accepted`
  (`ConLeche/Verify/Cached/StreamThm.lean`) at the reader's reading of the
  record. `checkBytesWith_no_False_reference` is the syntactic case: the
  record's type is a bare reference to the constant the reader names
  `False`.
* **Fidelity** (`Installed`, `checkBytesWith_reading`): no two records and
  no two blobs share an address (`UniqueKeys`), the records are read exactly
  and canonically (`RecordsRead`), the reader's output is a record-by-record reading of them
  (`StreamRead`), the fold accepted exactly that output behind the prelude,
  and the installed environment has exactly the install skeletons it
  declares (`Installed.skels`). Per record
  (`Installed.singleton`): a definition, theorem, opaque, axiom or quotient
  record's declaration carries the record's name, its level-parameter
  names, its type's reading and (for a definition or theorem) its value's
  reading or projection rewrite, is in the array the fold accepted, and is
  installed under that name with its kind.
* **Definition values** (`checkBytesWith_has_model_values`, D2 (ii)): the
  model can be chosen so that every stored definition's value denotes the
  constant, the counterpart of Ix's `Realizes.bodyValue` for definitions
  (`Ix.Kernel.ConLecheFold.checkDecls_model_defn_values`).
* **Resources** (`checkBytesWith_resources`): the byte limits checked
  before decoding bound the whole decoded representation.

Every theorem holds at every pin table, prelude and Nat-operation pin list
(`checkBytesWith`), so none depends on how the pins are generated;
`checkBytes` (the committed tables) inherits them through `checkBytes_with`.
-/

namespace Ix.Ixon.ConLecheAdmission

open Ix.Kernel (ConstRef)
open Ix.Kernel.ConLecheReader
open Ix.Kernel.ConLecheFold (declSkel checkDecls_installs)
open Ix.Ixon.Admission (Limits Records preflight uniqueKeys decodeRecords)
open Ix.Ixon.Verify.Admission (WithinBatch UniqueKeys RecordsRead resourceUnits)

universe u

/-! ## Checking decoded records

`streamContext`, `checkConstantsWith` and `checkConstants` are defined with
the entry (`Ix.Ixon.ConLecheAdmission`). -/

/-- The bytes entry is byte admission (`preflight`, `uniqueKeys`,
`decodeRecords`) followed by the check of the decoded records. -/
theorem checkBytesWith_eq (pins : Pins) (pre : Prelude) (natPins : List ConLeche.NatOpPinSet)
    (limits : Limits) (records : Records) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) :
    checkBytesWith pins pre natPins limits records blobs hint = (do
      (preflight limits records blobs).mapError Error.ofAdmission
      (uniqueKeys records blobs).mapError Error.ofAdmission
      let constants ← (decodeRecords limits records).mapError Error.ofAdmission
      checkConstantsWith pins pre natPins constants blobs hint) := by
  unfold checkBytesWith prepareWith checkConstantsWith
  cases preflight limits records blobs with
  | error e => rfl
  | ok u =>
    cases uniqueKeys records blobs with
    | error e => rfl
    | ok v =>
      cases decodeRecords limits records with
      | error e => rfl
      | ok constants =>
        show (Except.bind (Except.bind (readStream pins pre constants blobs hint) _) _) =
          Except.bind (readStream pins pre constants blobs hint) _
        cases readStream pins pre constants blobs hint <;> rfl

/-- The committed tables load, and the bytes entry is `checkBytesWith` at
them. -/
theorem checkBytes_with {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      checkBytesWith pins pre natPins limits records blobs hint = .ok env := by
  unfold checkBytes at h
  cases hp : defaultPins with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pins =>
    cases hq : builtinPrelude with
    | error e => simp [hp, hq, bind, Except.bind, Except.mapError] at h
    | ok pre =>
      cases hn : builtinNatOpPins with
      | error e => simp [hp, hq, hn, bind, Except.bind, Except.mapError] at h
      | ok natPins =>
        simp only [hp, hq, hn, bind, Except.bind, Except.mapError] at h
        exact ⟨pins, pre, natPins, rfl, rfl, rfl, h⟩

/-- `checkConstants` is `checkConstantsWith` at the committed tables. -/
theorem checkConstants_with {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkConstants constants blobs hint = .ok env) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      checkConstantsWith pins pre natPins constants blobs hint = .ok env := by
  unfold checkConstants at h
  cases hp : defaultPins with
  | error e => simp [hp, bind, Except.bind, Except.mapError] at h
  | ok pins =>
    cases hq : builtinPrelude with
    | error e => simp [hp, hq, bind, Except.bind, Except.mapError] at h
    | ok pre =>
      cases hn : builtinNatOpPins with
      | error e => simp [hp, hq, hn, bind, Except.bind, Except.mapError] at h
      | ok natPins =>
        simp only [hp, hq, hn, bind, Except.bind, Except.mapError] at h
        exact ⟨pins, pre, natPins, rfl, rfl, rfl, h⟩

/-- An accepted reading of decoded records is a record-by-record reading
from the prelude's state. -/
theorem readStream_spec {pins : Pins} {pre : Prelude} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {decls : Array ConLeche.Declaration}
    (h : readStream pins pre constants blobs hint = .ok decls) :
    ∃ st', StreamRead (streamContext pins pre constants blobs hint) pre.state constants st' decls := by
  unfold readStream at h
  dsimp only at h
  split at h
  · rename_i st' out hr
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hs := readRecords_spec hr
    rw [List.toList_toArray] at hs
    exact ⟨st', hs⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- An accepted reading of decoded records has no two records under one
address (the reader's own check, `readRecords_nodup`). -/
theorem readStream_nodup {pins : Pins} {pre : Prelude} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {decls : Array ConLeche.Declaration}
    (h : readStream pins pre constants blobs hint = .ok decls) :
    (constants.map Prod.fst).Nodup := by
  unfold readStream at h
  dsimp only at h
  split at h
  · rename_i st' out hr
    simpa using readRecords_nodup hr
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Fidelity -/

/-- **What an accepted check of decoded records installs**, in the role of
`Ingress.Installed`: the reader's output `decls` is a record-by-record
reading of `constants` (`StreamRead`, each record read by `readRecord`
against the state the records before it left), and the fold accepted
exactly `decls` behind the prelude (`preparePrelude`, which only adds the
prelude's records and moves the stream's own copies of them to the front).
No two of the records share an address (`keys`, the reader's check).
`Installed.skels`: the environment has exactly the install skeletons of
that array. -/
structure Installed (pins : Pins) (pre : Prelude) (natPins : List ConLeche.NatOpPinSet)
    (constants : List (Address × Ixon.Constant)) (blobs : List (Address × ByteArray))
    (hint : ConstRef Address → Option ConLeche.ReducibilityHint) (env : ConLeche.Env) : Prop where
  reading : ∃ decls st', StreamRead (streamContext pins pre constants blobs hint) pre.state constants st' decls ∧
    ConLeche.Cached.checkDecls .verified natPins (ConLeche.Frontend.preparePrelude pre.ix decls) = .ok env
  keys : (constants.map Prod.fst).Nodup

theorem checkConstantsWith_installed {pins : Pins} {pre : Prelude}
    {natPins : List ConLeche.NatOpPinSet} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkConstantsWith pins pre natPins constants blobs hint = .ok env) :
    Installed pins pre natPins constants blobs hint env := by
  unfold checkConstantsWith at h
  cases hr : readStream pins pre constants blobs hint with
  | error e => simp [hr, bind, Except.bind] at h
  | ok decls =>
    simp only [hr, bind, Except.bind] at h
    cases hc : ConLeche.Cached.checkDecls .verified natPins (ConLeche.Frontend.preparePrelude pre.ix decls) with
    | error e => simp [hc, Except.mapError] at h
    | ok env' =>
      simp only [hc, Except.mapError, Except.ok.injEq] at h
      subst h
      obtain ⟨st', hs⟩ := readStream_spec hr
      exact ⟨⟨decls, st', hs, hc⟩, readStream_nodup hr⟩

/-- The installed environment has exactly the install skeletons of the
accepted array (`ConLeche.Cached.checkDecls_skels`): the same constants,
in the same order, with the same names, kinds, constructor arities and
recursor rule constructors. -/
theorem Installed.skels {pins : Pins} {pre : Prelude} {natPins : List ConLeche.NatOpPinSet}
    {constants : List (Address × Ixon.Constant)} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : Installed pins pre natPins constants blobs hint env) :
    ∃ decls st', StreamRead (streamContext pins pre constants blobs hint) pre.state constants st' decls ∧
      ConLeche.Cached.envSkels env =
        ConLeche.Cached.streamSkels (ConLeche.Frontend.preparePrelude pre.ix decls).toList := by
  obtain ⟨decls, st', hs, hc⟩ := h.reading
  exact ⟨decls, st', hs, ConLeche.Cached.checkDecls_skels hc⟩

/-- **Per-record fidelity.** Every definition, theorem, opaque, axiom or
quotient record of an accepted input is read (`SingletonRead`: the record's
name, its level-parameter names, its type's reading, and its value's
reading or projection rewrite), its declaration is in the array the fold
accepted, and the declaration is installed under its name with its kind
(for every declaration but a quotient record's, `sorryAx` and
`Quot.sound`, whose skeletons are the pinned blocks'; `declSkel`). -/
theorem Installed.singleton {pins : Pins} {pre : Prelude} {natPins : List ConLeche.NatOpPinSet}
    {constants : List (Address × Ixon.Constant)} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : Installed pins pre natPins constants blobs hint env) {owner : Address} {c : Ixon.Constant}
    (hmem : (owner, c) ∈ constants) (hs : isSingleton c.info = true) :
    ∃ st decl ds, SingletonRead (streamContext pins pre constants blobs hint) st owner c decl ∧
      decl ∈ ds ∧ ConLeche.Cached.checkDecls .verified natPins ds = .ok env ∧
      ∀ s, declSkel decl = some s → ∃ ci ∈ env.consts, ConLeche.Cached.ciSkel ci = s := by
  obtain ⟨decls, st', hstream, hc⟩ := h.reading
  obtain ⟨st, decl, hread, hd⟩ := hstream.singleton hmem hs
  have hd' := ConLeche.Frontend.mem_preparePrelude (pre := pre.ix) hd
  exact ⟨st, decl, _, hread, hd', hc, fun s hsk => checkDecls_installs hc hd' hsk⟩

/-! ## Model existence and no proof of `False` -/

theorem Installed.has_model (V : Type u) [ConLeche.SetTheory V] {pins : Pins} {pre : Prelude}
    {natPins : List ConLeche.NatOpPinSet} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : Installed pins pre natPins constants blobs hint env) :
    Nonempty (ConLeche.Model V env) := by
  obtain ⟨decls, _, _, hc⟩ := h.reading
  exact ConLeche.model_exists V natPins _ env hc

/-- The model can be chosen so that every stored definition's value denotes
the constant (the counterpart of Ix's `Realizes.bodyValue` for
definitions). -/
theorem Installed.has_model_values (V : Type u) [ConLeche.SetTheory V] {pins : Pins} {pre : Prelude}
    {natPins : List ConLeche.NatOpPinSet} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : Installed pins pre natPins constants blobs hint env) :
    ∃ M : ConLeche.Model V env, ∀ cv value hint', ConLeche.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, ConLeche.Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨decls, _, _, hc⟩ := h.reading
  exact Ix.Kernel.ConLecheFold.checkDecls_model_defn_values V natPins _ env hc

/-- No constant of an accepted environment has the pinned `False` as its
type (con-leche's `no_proof_of_False_cached`). -/
theorem Installed.no_proof_of_False (V : Type u) [ConLeche.SetTheory V] {pins : Pins} {pre : Prelude}
    {natPins : List ConLeche.NatOpPinSet} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : Installed pins pre natPins constants blobs hint env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const ConLeche.falseName [] → False := by
  obtain ⟨decls, _, _, hc⟩ := h.reading
  exact ConLeche.Cached.no_proof_of_False_cached V rfl hc

/-- No theorem record of an accepted input has a type that reads as the
pinned `False`: con-leche's `no_False_theorem_accepted` at the record's
reading. -/
theorem Installed.no_False_theorem (V : Type u) [ConLeche.SetTheory V] {pins : Pins} {pre : Prelude}
    {natPins : List ConLeche.NatOpPinSet} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : Installed pins pre natPins constants blobs hint env)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (streamContext pins pre constants blobs hint) owner c d).read d.typ =
      .ok (.const ConLeche.falseName [])) : False := by
  obtain ⟨decls, st', hstream, hcheck⟩ := h.reading
  obtain ⟨st, decl, hread, hd⟩ := hstream.singleton hmem (by simp [isSingleton, hc])
  cases hread with
  | defn info type _ kind =>
    rw [hc] at info
    cases info
    rw [hty] at type
    cases type
    rw [hk] at kind
    cases kind
    exact ConLeche.no_False_theorem_accepted V _ _ _ (ConLeche.Frontend.mem_preparePrelude hd) rfl
      env hcheck
  | axio info => rw [hc] at info; cases info
  | quot info => rw [hc] at info; cases info

/-! ## The bytes entry -/

/-- **The reading of accepted bytes** (fidelity): within the batch limits,
with no two records and no two blobs under one address (`UniqueKeys`), the
records read exactly and canonically as `constants` (`RecordsRead`, unique
by `RecordsRead.deterministic`), and the check of those records installed
what they describe (`Installed`). -/
theorem checkBytesWith_reading {pins : Pins} {pre : Prelude} {natPins : List ConLeche.NatOpPinSet}
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    WithinBatch limits records blobs ∧ UniqueKeys records blobs ∧
      ∃ constants, RecordsRead limits records constants ∧
        Installed pins pre natPins constants blobs hint env := by
  rw [checkBytesWith_eq] at h
  cases hf : preflight limits records blobs with
  | error e => simp [hf, Except.mapError, bind, Except.bind] at h
  | ok u =>
    cases hu : uniqueKeys records blobs with
    | error e => simp [hf, hu, Except.mapError, bind, Except.bind] at h
    | ok v =>
      cases hd : decodeRecords limits records with
      | error e => simp [hf, hu, hd, Except.mapError, bind, Except.bind] at h
      | ok constants =>
        simp only [hf, hu, hd, Except.mapError, bind, Except.bind] at h
        exact ⟨(Ix.Ixon.Verify.Admission.preflight_ok_iff _ _ _).mp hf,
          (Ix.Ixon.Verify.Admission.uniqueKeys_ok_iff _ _).mp hu, constants,
          (Ix.Ixon.Verify.Admission.decodeRecords_ok_iff _ _ _).mp hd, checkConstantsWith_installed h⟩

/-- The byte limits bound the whole decoded representation, including
expanded universes, while retaining the exact reading and installation. -/
theorem checkBytesWith_resources {pins : Pins} {pre : Prelude} {natPins : List ConLeche.NatOpPinSet}
    {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    ∃ constants, RecordsRead limits records constants ∧
      Installed pins pre natPins constants blobs hint env ∧
      resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes := by
  obtain ⟨within, _, constants, reading, installed⟩ := checkBytesWith_reading h
  have resources := reading.resourceUnits_le
  obtain ⟨recordCount, _, totalBytes⟩ := within
  have countProduct := Nat.mul_le_mul_right limits.maxRecordUnivNodes recordCount
  exact ⟨constants, reading, installed, by omega⟩

theorem checkBytesWith_has_model_values (V : Type u) [ConLeche.SetTheory V] {pins : Pins}
    {pre : Prelude} {natPins : List ConLeche.NatOpPinSet} {limits : Limits} {records : Records}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    ∃ M : ConLeche.Model V env, ∀ cv value hint', ConLeche.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, ConLeche.Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨_, _, _, _, installed⟩ := checkBytesWith_reading h
  exact installed.has_model_values V

theorem checkBytesWith_no_proof_of_False (V : Type u) [ConLeche.SetTheory V] {pins : Pins}
    {pre : Prelude} {natPins : List ConLeche.NatOpPinSet} {limits : Limits} {records : Records}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const ConLeche.falseName [] → False := by
  obtain ⟨_, _, _, _, installed⟩ := checkBytesWith_reading h
  exact installed.no_proof_of_False V

/-- **No accepted theorem of `False`, at the records** (D3, con-leche's
pinned form): no theorem record of accepted bytes has a type that reads as
the pinned `False`. -/
theorem checkBytesWith_no_False_theorem (V : Type u) [ConLeche.SetTheory V] {pins : Pins}
    {pre : Prelude} {natPins : List ConLeche.NatOpPinSet} {limits : Limits} {records : Records}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (streamContext pins pre constants blobs hint) owner c d).read d.typ =
      .ok (.const ConLeche.falseName [])) : False := by
  obtain ⟨_, _, constants', reading', installed⟩ := checkBytesWith_reading h
  obtain rfl := reading.deterministic reading'
  exact installed.no_False_theorem V hmem hc hk hty

/-- The syntactic case: a theorem record whose type is a bare reference
(no universe arguments) to the constant the reader names `False` is never
accepted. Under the committed pin table that is Init's `False` block
(`Ctx.nameOf_of_pin`). -/
theorem checkBytesWith_no_False_reference (V : Type u) [ConLeche.SetTheory V] {pins : Pins}
    {pre : Prelude} {natPins : List ConLeche.NatOpPinSet} {limits : Limits} {records : Records}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkBytesWith pins pre natPins limits records blobs hint = .ok env)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    {i : UInt64} {a : Address} {r : ConstRef Address}
    (hty : d.typ = .ref i #[]) (href : c.refs[i.toNat]? = some a)
    (hres : resolve (streamContext pins pre constants blobs hint).store a = some r)
    (hfalse : (streamContext pins pre constants blobs hint).nameOf r = ConLeche.falseName) : False := by
  refine checkBytesWith_no_False_theorem V h reading hmem hc hk ?_
  rw [hty, ← hfalse]
  exact MemberReader.read_ref (by simpa [definitionReader] using href)
    (by simpa [definitionReader] using hres)

/-! ## The committed tables -/

/-- The reading of bytes accepted under the committed tables. -/
theorem checkBytes_reading {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ pins pre natPins, defaultPins = .ok pins ∧ builtinPrelude = .ok pre ∧
      builtinNatOpPins = .ok natPins ∧
      WithinBatch limits records blobs ∧ UniqueKeys records blobs ∧
        ∃ constants, RecordsRead limits records constants ∧
          Installed pins pre natPins constants blobs hint env := by
  obtain ⟨pins, pre, natPins, hp, hq, hn, hw⟩ := checkBytes_with h
  exact ⟨pins, pre, natPins, hp, hq, hn, checkBytesWith_reading hw⟩

theorem checkBytes_resources {limits : Limits} {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ constants, RecordsRead limits records constants ∧
      resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes := by
  obtain ⟨_, _, _, _, _, _, hw⟩ := checkBytes_with h
  obtain ⟨constants, reading, _, bound⟩ := checkBytesWith_resources hw
  exact ⟨constants, reading, bound⟩

theorem checkBytes_has_model_values (V : Type u) [ConLeche.SetTheory V] {limits : Limits}
    {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∃ M : ConLeche.Model V env, ∀ cv value hint', ConLeche.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, ConLeche.Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨_, _, _, _, _, _, hw⟩ := checkBytes_with h
  exact checkBytesWith_has_model_values V hw

theorem checkBytes_no_proof_of_False (V : Type u) [ConLeche.SetTheory V] {limits : Limits}
    {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const ConLeche.falseName [] → False := by
  obtain ⟨_, _, _, _, _, _, hw⟩ := checkBytes_with h
  exact checkBytesWith_no_proof_of_False V hw

theorem checkBytes_no_False_theorem (V : Type u) [ConLeche.SetTheory V] {limits : Limits}
    {records : Records} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkBytes limits records blobs hint = .ok env) {pins : Pins} {pre : Prelude}
    (hpins : defaultPins = .ok pins) (hpre : builtinPrelude = .ok pre)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (streamContext pins pre constants blobs hint) owner c d).read d.typ =
      .ok (.const ConLeche.falseName [])) : False := by
  obtain ⟨pins', pre', _, hp, hq, _, hw⟩ := checkBytes_with h
  rw [hpins] at hp; cases hp
  rw [hpre] at hq; cases hq
  exact checkBytesWith_no_False_theorem V hw reading hmem hc hk hty

/-! ## Decoded records -/

theorem checkConstantsWith_has_model (V : Type u) [ConLeche.SetTheory V] {pins : Pins}
    {pre : Prelude} {natPins : List ConLeche.NatOpPinSet} {constants : List (Address × Ixon.Constant)}
    {blobs : List (Address × ByteArray)} {hint : ConstRef Address → Option ConLeche.ReducibilityHint}
    {env : ConLeche.Env} (h : checkConstantsWith pins pre natPins constants blobs hint = .ok env) :
    Nonempty (ConLeche.Model V env) :=
  (checkConstantsWith_installed h).has_model V

theorem checkConstants_has_model (V : Type u) [ConLeche.SetTheory V]
    {constants : List (Address × Ixon.Constant)} {blobs : List (Address × ByteArray)}
    {hint : ConstRef Address → Option ConLeche.ReducibilityHint} {env : ConLeche.Env}
    (h : checkConstants constants blobs hint = .ok env) : Nonempty (ConLeche.Model V env) := by
  obtain ⟨_, _, _, _, _, _, hw⟩ := checkConstants_with h
  exact checkConstantsWith_has_model V hw

end Ix.Ixon.ConLecheAdmission
