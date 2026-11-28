import IxCK.Kernel.Admission
import IxCK.Kernel.Admission.Bytes.Theorems
import IxCK.Kernel.Ixon.ReaderSpec
import IxCK.Kernel.Ixon.Installed
import IxCK.Kernel.Ixon.Values
import IxCK.Kernel.Verify.Cached.StreamThm
import IxCK.Kernel.Verify.Cached.StreamConsts
import IxCK.Kernel.Verify.Frontend.Prepare
import IxCK.Kernel.MainTheorem

/-! # The public theorems of the certified Ixon entry

The certified contract of Ix's Ixon checker (`docs/kernel.md`):
`Ix.Kernel.Admission.checkBytes`, the verified fold
(`Ix.Kernel.Cached.checkDecls .verified`) behind the Ixon reader, under a
role table, stated for the executed functions.

* **Model existence** (`checkConstantsWith_has_model`,
  `checkBytesWith_has_model`, `checkBytes_has_model`): every accepted input
  has a model (`Ix.Kernel.Model`, which states types)
  in every set theory. This is `Ix.Kernel.model_exists` at the prepared
  declarations and the table's evidence; the reader owes nothing.
* **No proof of `False`**, stated at the role key `roleKey .false`
  independently of the table.
  `checkBytesWith_no_proof_of_False`: no constant of an accepted environment
  has `False`'s role key as its type. `checkBytesWith_no_False_theorem`: no
  theorem record of an accepted input has a type that reads as it; this is
  `Ix.Kernel.no_False_theorem_accepted`
  (`IxCK/Kernel/Verify/Cached/StreamThm.lean`) at the reader's reading of the
  record. `checkBytesWith_no_False_reference` is the syntactic case: the
  record's type is a bare reference to the constant the reader names
  `False`.
* **Authentication** (`checkBytesWith_authentic`, `checkBytes_authentic`):
  every record and every blob of an accepted input is stored under `hash`
  of its supplied bytes (`Authentic`), so every decoded record under `hash`
  of its canonical encoding (`Hashed`, in `checkBytesWith_reading`); and the
  role table's section is stored under `hash` of its bytes, which are the
  canonical encoding of a well-formed table (`BindingAdmitted`).
* **The role table** (`admitBinding_ok_iff`, `checkBytesWith_binding`): the
  entry refuses a table whose section is not authentic, not canonical or not
  well formed (`RoleTable.check`).
* **Fidelity** (`Installed`, `checkBytesWith_reading`): no two records and
  no two blobs share an address (`UniqueKeys`), the records are read exactly
  and canonically (`RecordsRead`), the reader's output is a record-by-record
  reading of them (`StreamRead`) under the table's bindings, the fold
  accepted exactly that output behind the prelude at the table's evidence
  resolved against the reading (`evidenceOf`), and the installed environment
  has exactly the install skeletons it declares (`Installed.skels`). Per
  record (`Installed.singleton`): a definition, theorem, opaque, axiom or
  quotient record's declaration carries the record's name, its
  level-parameter names, its type's reading and (for a definition or theorem)
  its value's reading or projection rewrite, is in the array the fold
  accepted, and is installed under that name with its kind.
* **Definition values** (`checkBytesWith_has_model_values`): the model can
  be chosen so that every stored definition's value denotes the constant
  (`Ix.Kernel.Cached.checkDecls_model_defn_values`).
* **Resources** (`checkBytesWith_resources`): the byte limits checked
  before decoding bound the whole decoded representation.

Every theorem holds at every content hash `hash`, every role table and
every prelude (`checkBytesWith`), so none depends on which hash executes or
on how the table and its evidence were generated; `checkBytes` (the committed
prelude read under the admitted table) inherits them through
`checkBytes_with`. The set theory is the standing hypothesis;
`Models/SetTheory` provides an instance on Mathlib's `ZFSet` under `ω`
inaccessible cardinals.
-/

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Ix.Kernel.Cached (declSkel checkDecls_installs)

universe u

/-! ## The role table -/

/-- **An admitted role table**: its section is stored under `hash` of its
bytes, the bytes are the canonical encoding of `t` (`RoleTable.toBytes`, in
the format's domain), and `t` is well formed (`RoleTable.check`). -/
structure BindingAdmitted (hash : ByteArray → Address) (b : Binding)
    (t : Ix.Kernel.RoleTable) : Prop where
  authentic : hash b.bytes = b.address
  canonical : t.wireWF = true ∧ t.toBytes = b.bytes
  wellFormed : t.check = .ok ()

/-- **The role table's admission, exactly**: it admits `t` iff the section is
authentic, canonical and well formed. -/
theorem admitBinding_ok_iff (hash : ByteArray → Address) (b : Binding)
    (t : Ix.Kernel.RoleTable) : admitBinding hash b = .ok t ↔ BindingAdmitted hash b t := by
  unfold admitBinding
  by_cases ha : hash b.bytes = b.address
  · simp only [ha, decide_true, ite_true]
    cases hd : Ix.Kernel.RoleTable.ofBytes b.bytes with
    | none =>
      simp only [throw, throwThe, MonadExceptOf.throw]
      constructor
      · intro h; cases h
      · rintro ⟨-, hcan, -⟩
        rw [(Ix.Kernel.RoleTable.ofBytes_eq_some_iff _ _).mpr hcan] at hd
        cases hd
    | some t' =>
      cases hc : t'.check with
      | error e =>
        simp only [hc, Except.mapError, bind, Except.bind]
        constructor
        · intro h; cases h
        · rintro ⟨-, hcan, hwf⟩
          rw [(Ix.Kernel.RoleTable.ofBytes_eq_some_iff _ _).mpr hcan] at hd
          cases hd
          rw [hc] at hwf; cases hwf
      | ok v =>
        simp only [hc, Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl
          exact ⟨ha, (Ix.Kernel.RoleTable.ofBytes_eq_some_iff _ _).mp hd, by cases v; exact hc⟩
        · rintro ⟨-, hcan, -⟩
          rw [(Ix.Kernel.RoleTable.ofBytes_eq_some_iff _ _).mpr hcan] at hd
          exact (Option.some.inj hd).symm
  · simp only [ha, decide_false, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    constructor
    · intro h; cases h
    · rintro ⟨ha', -, -⟩; exact absurd ha' ha

/-! ## Model existence

`checkBytesWith_checkDecls`, `checkBytesWith_has_model` and
`checkBytes_has_model` live here, beside the other theorems, so that the
entry (`Ix.Kernel.Admission`) holds definitions only and its import
closure does not reach the main theorem (`Ix.Kernel.MainTheorem`). -/

/-- Every accept of the entry, at any hash, role table and prelude, is an
accept of the verified fold on the prepared declarations, at the evidence
the reader resolved and the entry's fold configuration (`limits.fold`). -/
theorem checkBytesWith_checkDecls {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    ∃ ev decls, prepareWith hash binding pre limits records blobs hint = .ok (ev, decls) ∧
      Ix.Kernel.Cached.checkDecls .verified ev decls limits.fold = .ok env := by
  unfold checkBytesWith at h
  cases hp : prepareWith hash binding pre limits records blobs hint with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    obtain ⟨ev, decls⟩ := p
    simp only [hp, bind, Except.bind] at h
    cases hc : Ix.Kernel.Cached.checkDecls .verified ev decls limits.fold with
    | error e => simp [hc, Except.mapError] at h
    | ok env' =>
      simp only [hc, Except.mapError, Except.ok.injEq] at h
      exact ⟨ev, decls, rfl, h ▸ hc⟩

/-- **Model existence for the Ixon entry** (any hash, role table and
prelude). -/
theorem checkBytesWith_has_model (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
    {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨ev, decls, _, hc⟩ := checkBytesWith_checkDecls h
  exact Ix.Kernel.model_exists_cfg V ev decls limits.fold env hc

/-- `checkBytesUsing` is `checkBytesWith` at the prelude its source gives the
admitted table. -/
theorem checkBytesUsing_with {prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon)}
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesUsing prelude hash binding limits records blobs hint = .ok env) :
    ∃ t pre, admitBinding hash binding = .ok t ∧ prelude t = .ok pre ∧
      checkBytesWith hash binding pre limits records blobs hint = .ok env := by
  unfold checkBytesUsing at h
  cases ht : admitBinding hash binding with
  | error e => simp [ht, bind, Except.bind, Except.mapError] at h
  | ok t =>
    cases hq : prelude t with
    | error e => simp [ht, hq, bind, Except.bind, Except.mapError] at h
    | ok pre =>
      simp only [ht, hq, bind, Except.bind, Except.mapError] at h
      exact ⟨t, pre, rfl, hq, h⟩

/-- The entry is `checkBytesWith` at the committed prelude read under the
admitted table. -/
theorem checkBytes_with {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    ∃ t pre, admitBinding hash binding = .ok t ∧ preludeFor t = .ok pre ∧
      checkBytesWith hash binding pre limits records blobs hint = .ok env :=
  checkBytesUsing_with h

/-- **Model existence for the Ixon entry**: every environment `checkBytes`
accepts, at any hash and any role table, has a model in every set theory. -/
theorem checkBytes_has_model (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
    {binding : Binding} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨_, _, _, _, hw⟩ := checkBytes_with h
  exact checkBytesWith_has_model V hw

/-! ## Checking decoded records

`streamContext`, `checkConstantsWith` and `checkConstants` are defined with
the entry (`Ix.Kernel.Admission`). -/

/-- The bytes entry is byte admission (`preflight`, `uniqueKeys`,
`authenticate`), the role table's admission (`admitBinding`), decoding
within the depth limit (`decodeWithin`), and then the check of the decoded
records under the admitted table and fold settings (`limits.fold`). -/
theorem checkBytesWith_eq (hash : ByteArray → Address) (binding : Binding) (pre : Prelude .anon)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    checkBytesWith hash binding pre limits records blobs hint = (do
      (preflight limits records blobs).mapError Error.ofBytes
      (uniqueKeys records blobs).mapError Error.ofBytes
      (authenticate hash records blobs).mapError Error.ofBytes
      let t ← (admitBinding hash binding).mapError .binding
      let constants ← (decodeWithin limits records).mapError Error.ofBytes
      checkConstantsWith hash t pre constants blobs hint limits.fold) := by
  unfold checkBytesWith prepareWith checkConstantsWith
  cases preflight limits records blobs with
  | error e => rfl
  | ok u =>
    cases uniqueKeys records blobs with
    | error e => rfl
    | ok v =>
      cases authenticate hash records blobs with
      | error e => rfl
      | ok w =>
        cases admitBinding hash binding with
        | error e => rfl
        | ok t =>
          cases decodeWithin limits records with
          | error e => rfl
          | ok constants =>
            show (Except.bind (Except.bind (readStream hash t pre constants blobs hint) _) _) =
              Except.bind (readStream hash t pre constants blobs hint) _
            cases readStream hash t pre constants blobs hint <;> rfl

/-- `checkConstantsUsing` is `checkConstantsWith` at the prelude its source
gives the table. -/
theorem checkConstantsUsing_with {hash : ByteArray → Address} {prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon)}
    {t : Ix.Kernel.RoleTable} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {cfg : Ix.Kernel.Cached.FoldConfig} {env : Ix.Kernel.Env .anon}
    (h : checkConstantsUsing prelude hash t constants blobs hint cfg = .ok env) :
    ∃ pre, prelude t = .ok pre ∧ checkConstantsWith hash t pre constants blobs hint cfg = .ok env := by
  unfold checkConstantsUsing at h
  cases hq : prelude t with
  | error e => simp [hq, bind, Except.bind, Except.mapError] at h
  | ok pre =>
    simp only [hq, bind, Except.bind, Except.mapError] at h
    exact ⟨pre, rfl, h⟩

/-- `checkConstants` is `checkConstantsWith` at the committed prelude read
under the table. -/
theorem checkConstants_with {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {cfg : Ix.Kernel.Cached.FoldConfig} {env : Ix.Kernel.Env .anon}
    (h : checkConstants hash t constants blobs hint cfg = .ok env) :
    ∃ pre, preludeFor t = .ok pre ∧ checkConstantsWith hash t pre constants blobs hint cfg = .ok env :=
  checkConstantsUsing_with h

/-- An accepted reading of decoded records is a record-by-record reading
from the prelude's state, the evidence is the table's, resolved against
the reading's final state, and that state keeps the prelude's entries
(`State.keepsPrelude`). -/
theorem readStream_spec {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {ev : Ix.Kernel.Evidences .anon} {decls : Array (Ix.Kernel.Declaration .anon)}
    (h : readStream hash t pre constants blobs hint = .ok (ev, decls)) :
    ∃ st', StreamRead (streamContext hash t pre constants blobs hint) pre.state constants st' decls ∧
      ev = evidenceOf (streamContext hash t pre constants blobs hint) st' t ∧
      State.keepsPrelude pre.state st' = true := by
  unfold readStream at h
  dsimp only at h
  split at h
  · rename_i st' out hr
    split at h
    · rename_i hk
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs := readRecords_spec hr
      rw [List.toList_toArray] at hs
      exact ⟨st', hs, rfl, hk⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- An accepted reading of decoded records has no two records under one
address (the reader's own check, `readRecords_nodup`). -/
theorem readStream_nodup {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {ev : Ix.Kernel.Evidences .anon} {decls : Array (Ix.Kernel.Declaration .anon)}
    (h : readStream hash t pre constants blobs hint = .ok (ev, decls)) :
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
reading of `constants` under the role table `t` (`StreamRead`, each record
read by `readRecord` against the state the records before it left), and the
fold accepted exactly `decls` behind the prelude (`preparePrelude`, which
only adds the prelude's records and moves the stream's own copies of them to
the front), at the table's evidence resolved against that reading
(`evidenceOf`). No two of the records share an address (`keys`, the reader's
check). `Installed.skels`: the environment has exactly the install skeletons
of that array. -/
structure Installed (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable) (pre : Prelude .anon)
    (constants : List (Address × Ixon.Constant)) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) (env : Ix.Kernel.Env .anon) : Prop where
  reading : ∃ decls st' cfg, StreamRead (streamContext hash t pre constants blobs hint) pre.state constants st' decls ∧
    Ix.Kernel.Cached.checkDecls .verified (evidenceOf (streamContext hash t pre constants blobs hint) st' t)
      (Ix.Kernel.Frontend.preparePrelude pre.ix decls) cfg = .ok env
  keys : (constants.map Prod.fst).Nodup

theorem checkConstantsWith_installed {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {cfg : Ix.Kernel.Cached.FoldConfig} {env : Ix.Kernel.Env .anon}
    (h : checkConstantsWith hash t pre constants blobs hint cfg = .ok env) :
    Installed hash t pre constants blobs hint env := by
  unfold checkConstantsWith at h
  cases hr : readStream hash t pre constants blobs hint with
  | error e => simp [hr, bind, Except.bind] at h
  | ok p =>
    obtain ⟨ev, decls⟩ := p
    simp only [hr, bind, Except.bind] at h
    cases hc : Ix.Kernel.Cached.checkDecls .verified ev (Ix.Kernel.Frontend.preparePrelude pre.ix decls) cfg with
    | error e => simp [hc, Except.mapError] at h
    | ok env' =>
      simp only [hc, Except.mapError, Except.ok.injEq] at h
      subst h
      obtain ⟨st', hs, rfl, -⟩ := readStream_spec hr
      exact ⟨⟨decls, st', cfg, hs, hc⟩, readStream_nodup hr⟩

/-- The installed environment has exactly the install skeletons of the
accepted array (`Ix.Kernel.Cached.checkDecls_skels`): the same constants,
in the same order, with the same names, kinds, constructor arities and
recursor rule constructors. -/
theorem Installed.skels {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : Installed hash t pre constants blobs hint env) :
    ∃ decls st', StreamRead (streamContext hash t pre constants blobs hint) pre.state constants st' decls ∧
      Ix.Kernel.Cached.envSkels env =
        Ix.Kernel.Cached.streamSkels (Ix.Kernel.Frontend.preparePrelude pre.ix decls).toList := by
  obtain ⟨decls, st', _, hs, hc⟩ := h.reading
  exact ⟨decls, st', hs, Ix.Kernel.Cached.checkDecls_skels hc⟩

/-- **Per-record fidelity.** Every definition, theorem, opaque, axiom or
quotient record of an accepted input is read (`SingletonRead`: the record's
name, its level-parameter names, its type's reading, and its value's
reading or projection rewrite), its declaration is in the array the fold
accepted, and the declaration is installed under its name with its kind
(for every declaration but a quotient record's, `sorryAx`, `Quot.sound`, and
the five inert compiler-trust declarations (`§7.10`); `declSkel`). -/
theorem Installed.singleton {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : Installed hash t pre constants blobs hint env) {owner : Address} {c : Ixon.Constant}
    (hmem : (owner, c) ∈ constants) (hs : isSingleton c.info = true) :
    ∃ st decl ev ds cfg, SingletonRead (streamContext hash t pre constants blobs hint) st owner c decl ∧
      decl ∈ ds ∧ Ix.Kernel.Cached.checkDecls .verified ev ds cfg = .ok env ∧
      ∀ s, declSkel decl = some s → ∃ ci ∈ env.consts, Ix.Kernel.Cached.ciSkel ci = s := by
  obtain ⟨decls, st', cfg, hstream, hc⟩ := h.reading
  obtain ⟨st, decl, hread, hd⟩ := hstream.singleton hmem hs
  have hd' := Ix.Kernel.Frontend.mem_preparePrelude (pre := pre.ix) hd
  exact ⟨st, decl, _, _, cfg, hread, hd', hc, fun s hsk => Ix.Kernel.Cached.checkDecls_installs_cfg hc hd' hsk⟩

/-- **Per-record type fidelity**: every singleton record
(definition, theorem, opaque, axiom or quotient) of an accepted input is read
(`SingletonRead`), and whenever its declaration declares a constant
(`Declaration.Declares`: definitions, theorems, non-inert opaques, and
installed axioms), the returned environment stores that constant under its own
name, with its own level parameters, and with the annotation of its declared
type (`AnnotOf`: every `let` ζ-reduced and binder prop-ness written). The
`[Ix.Kernel.SetTheory V]` premise is inherited from `Cached.checkDecls_consts_cfg`
(the cached-to-pure simulation needs `EnvWF` from the model). -/
theorem Installed.consts (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : Installed hash t pre constants blobs hint env) {owner : Address} {c : Ixon.Constant}
    (hmem : (owner, c) ∈ constants) (hs : isSingleton c.info = true) :
    ∃ st decl, SingletonRead (streamContext hash t pre constants blobs hint) st owner c decl ∧
      ∀ cv, Ix.Kernel.Cached.Declaration.Declares decl cv →
        ∃ ci, env.find? cv.name = some ci ∧
          ci.toConstantVal.levelParams = cv.levelParams ∧
          Ix.Kernel.AnnotOf cv.type ci.toConstantVal.type := by
  obtain ⟨st, decl, ev, ds, cfg, hread, hd, hc, -⟩ := h.singleton hmem hs
  exact ⟨st, decl, hread, fun cv hcv => Ix.Kernel.Cached.checkDecls_consts_cfg V hc hd hcv⟩

/-! ## Model existence and no proof of `False` -/

theorem Installed.has_model (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : Installed hash t pre constants blobs hint env) :
    Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨decls, _, cfg, _, hc⟩ := h.reading
  exact Ix.Kernel.model_exists_cfg V _ _ cfg env hc

/-- The model can be chosen so that every stored definition's value denotes
the constant (the counterpart of Ix's `Realizes.bodyValue` for
definitions). -/
theorem Installed.has_model_values (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : Installed hash t pre constants blobs hint env) :
    ∃ M : Ix.Kernel.Model V env, ∀ cv value hint', Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨decls, _, cfg, _, hc⟩ := h.reading
  exact Ix.Kernel.Cached.checkDecls_model_defn_values_cfg V _ _ cfg env hc

/-- No constant of an accepted environment has `False`'s role key as its
type (`Ix.Kernel.Cached.no_proof_of_False_cached_cfg`); the statement does not
depend on the table. -/
theorem Installed.no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : Installed hash t pre constants blobs hint env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨decls, _, _, _, hc⟩ := h.reading
  exact Ix.Kernel.Cached.no_proof_of_False_cached_cfg V rfl hc

/-- No theorem record of an accepted input has a type that reads as
`False`'s role key: `Ix.Kernel.no_False_theorem_accepted_cfg` at the record's
reading. -/
theorem Installed.no_False_theorem (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : Installed hash t pre constants blobs hint env)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (streamContext hash t pre constants blobs hint) owner c d).read d.typ =
      .ok (.const (Ix.Kernel.roleKey .false) [])) : False := by
  obtain ⟨decls, st', cfg, hstream, hcheck⟩ := h.reading
  obtain ⟨st, decl, hread, hd⟩ := hstream.singleton hmem (by simp [isSingleton, hc])
  cases hread with
  | defn info _ type _ kind =>
    rw [hc] at info
    cases info
    rw [hty] at type
    cases type
    rw [hk] at kind
    cases kind
    exact Ix.Kernel.no_False_theorem_accepted_cfg V _ _ _ (Ix.Kernel.Frontend.mem_preparePrelude hd) rfl
      cfg env hcheck
  | axio info => rw [hc] at info; cases info
  | quot info => rw [hc] at info; cases info

/-! ## The bytes entry -/

/-- **The reading of accepted bytes** (fidelity): within the batch limits,
with no two records and no two blobs under one address (`UniqueKeys`), every
record and blob under `hash` of its bytes (`Authentic`), the role table's
section admitted (`BindingAdmitted`: authentic, canonical, well formed), the
records read exactly and canonically as `constants` (`RecordsRead`, unique
by `RecordsRead.deterministic`), each under `hash` of its canonical encoding
(`Hashed`), and the check of those records under the table installed what
they describe (`Installed`). -/
theorem checkBytesWith_reading {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    WithinBatch limits records blobs ∧ UniqueKeys records blobs ∧ Authentic hash records blobs ∧
      ∃ t constants, BindingAdmitted hash binding t ∧ RecordsRead limits records constants ∧
        Hashed hash constants ∧ Installed hash t pre constants blobs hint env := by
  rw [checkBytesWith_eq] at h
  cases hf : preflight limits records blobs with
  | error e => simp [hf, Except.mapError, bind, Except.bind] at h
  | ok u =>
    cases hu : uniqueKeys records blobs with
    | error e => simp [hf, hu, Except.mapError, bind, Except.bind] at h
    | ok v =>
      cases ha : authenticate hash records blobs with
      | error e => simp [hf, hu, ha, Except.mapError, bind, Except.bind] at h
      | ok w =>
        cases hb : admitBinding hash binding with
        | error e => simp [hf, hu, ha, hb, Except.mapError, bind, Except.bind] at h
        | ok t =>
          cases hd : decodeWithin limits records with
          | error e => simp [hf, hu, ha, hb, hd, Except.mapError, bind, Except.bind] at h
          | ok constants =>
            simp only [hf, hu, ha, hb, hd, Except.mapError, bind, Except.bind] at h
            have authentic := (Ix.Kernel.Admission.authenticate_ok_iff _ _ _).mp ha
            have reading := (Ix.Kernel.Admission.decodeRecords_ok_iff _ _ _).mp
              (decodeWithin_decodeRecords hd)
            exact ⟨(Ix.Kernel.Admission.preflight_ok_iff _ _ _).mp hf,
              (Ix.Kernel.Admission.uniqueKeys_ok_iff _ _).mp hu, authentic, t, constants,
              (admitBinding_ok_iff _ _ _).mp hb, reading, reading.hashed authentic.1,
              checkConstantsWith_installed h⟩

/-- **The role table**: accepted bytes came with an admitted table — its
section stored under `hash` of its bytes, the canonical encoding of a
well-formed table. -/
theorem checkBytesWith_binding {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    ∃ t, BindingAdmitted hash binding t := by
  obtain ⟨_, _, _, t, _, hb, _⟩ := checkBytesWith_reading h
  exact ⟨t, hb⟩

/-- **Authentication**: every record and every blob of accepted bytes is
stored under `hash` of its supplied bytes, and so is the role table's
section. -/
theorem checkBytesWith_authentic {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    Authentic hash records blobs ∧ hash binding.bytes = binding.address := by
  obtain ⟨_, _, ha, _, _, hb, _⟩ := checkBytesWith_reading h
  exact ⟨ha, hb.authentic⟩

/-- The byte limits bound the whole decoded representation, including
expanded universes, while retaining the exact reading and installation. -/
theorem checkBytesWith_resources {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    ∃ t constants, RecordsRead limits records constants ∧
      Installed hash t pre constants blobs hint env ∧
      resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes := by
  obtain ⟨within, _, _, t, constants, _, reading, _, installed⟩ := checkBytesWith_reading h
  have resources := reading.resourceUnits_le
  obtain ⟨recordCount, _, totalBytes⟩ := within
  have countProduct := Nat.mul_le_mul_right limits.maxRecordUnivNodes recordCount
  exact ⟨t, constants, reading, installed, by omega⟩

theorem checkBytesWith_has_model_values (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding}
    {pre : Prelude .anon} {limits : Limits} {records : Records}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ∀ cv value hint', Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨_, _, _, _, _, _, _, _, installed⟩ := checkBytesWith_reading h
  exact installed.has_model_values V

/-- **No proof of `False`**, at `False`'s role key, for every role table. -/
theorem checkBytesWith_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding}
    {pre : Prelude .anon} {limits : Limits} {records : Records}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : checkBytesWith hash binding pre limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, _, _, _, _, _, _, installed⟩ := checkBytesWith_reading h
  exact installed.no_proof_of_False V

/-- **No accepted theorem of `False`, at the records**: no theorem record of
accepted bytes has a type that reads as `False`'s role key. -/
theorem checkBytesWith_no_False_theorem (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding}
    {pre : Prelude .anon} {limits : Limits} {records : Records}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : checkBytesWith hash binding pre limits records blobs hint = .ok env)
    {t : Ix.Kernel.RoleTable} (ht : admitBinding hash binding = .ok t)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (streamContext hash t pre constants blobs hint) owner c d).read d.typ =
      .ok (.const (Ix.Kernel.roleKey .false) [])) : False := by
  rw [checkBytesWith_eq] at h
  cases hf : preflight limits records blobs with
  | error e => simp [hf, Except.mapError, bind, Except.bind] at h
  | ok u =>
    cases hu : uniqueKeys records blobs with
    | error e => simp [hf, hu, Except.mapError, bind, Except.bind] at h
    | ok v =>
      cases ha : authenticate hash records blobs with
      | error e => simp [hf, hu, ha, Except.mapError, bind, Except.bind] at h
      | ok w =>
        cases hd : decodeWithin limits records with
        | error e => simp [hf, hu, ha, ht, hd, Except.mapError, bind, Except.bind] at h
        | ok constants' =>
          simp only [hf, hu, ha, ht, hd, Except.mapError, bind, Except.bind] at h
          have reading' := (Ix.Kernel.Admission.decodeRecords_ok_iff _ _ _).mp
            (decodeWithin_decodeRecords hd)
          obtain rfl := reading.deterministic reading'
          exact (checkConstantsWith_installed h).no_False_theorem V hmem hc hk hty

/-- The syntactic case: a theorem record whose type is a bare reference
(no universe arguments) to the constant the reader keys as `False` is never
accepted. Under a table that binds `False` the reader keys the address of its
constant so (`Ctx.keyAt_eq_ok`). -/
theorem checkBytesWith_no_False_reference (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding}
    {pre : Prelude .anon} {limits : Limits} {records : Records}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : checkBytesWith hash binding pre limits records blobs hint = .ok env)
    {t : Ix.Kernel.RoleTable} (ht : admitBinding hash binding = .ok t)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    {i : UInt64} {a : Address}
    (hty : d.typ = .ref i #[]) (href : c.refs[i.toNat]? = some a)
    (hfalse : (streamContext hash t pre constants blobs hint).keyAt a = .ok (Ix.Kernel.roleKey .false)) :
    False := by
  refine checkBytesWith_no_False_theorem V h ht reading hmem hc hk ?_
  rw [hty]
  exact MemberReader.read_ref (by simpa [definitionReader] using href)
    (by simpa [definitionReader] using hfalse)

/-- **Per-record type fidelity at `checkBytesWith`**:
for every singleton record (definition, theorem, opaque, axiom or quotient) of
accepted bytes (`RecordsRead`), its reading (`SingletonRead`) produces a
declaration whose declared constant (for definitions, theorems, non-inert
opaques and installed axioms) is stored in `env` under its own name, with its
own level parameters, and with the annotation (`AnnotOf`) of its declared type.
Under `[Ix.Kernel.SetTheory V]` (`Cached.checkDecls_consts_cfg` needs `EnvWF`
from the model). -/
theorem checkBytesWith_consts (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesWith hash binding pre limits records blobs hint = .ok env)
    {t : Ix.Kernel.RoleTable} (ht : admitBinding hash binding = .ok t)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant}
    (hmem : (owner, c) ∈ constants) (hs : isSingleton c.info = true) :
    ∃ st decl, SingletonRead (streamContext hash t pre constants blobs hint) st owner c decl ∧
      ∀ cv, Ix.Kernel.Cached.Declaration.Declares decl cv →
        ∃ ci, env.find? cv.name = some ci ∧
          ci.toConstantVal.levelParams = cv.levelParams ∧
          Ix.Kernel.AnnotOf cv.type ci.toConstantVal.type := by
  obtain ⟨_, _, _, t', constants', hb, reading', _, installed⟩ := checkBytesWith_reading h
  have ht' : t' = t := by
    rw [(admitBinding_ok_iff _ _ _).mpr hb] at ht
    exact Except.ok.inj ht
  subst ht'
  obtain rfl := reading.deterministic reading'
  exact installed.consts V hmem hs

/-! ## The entry -/

/-- **Fidelity.** Accepted bytes are within the batch limits, use each
record address and each blob address once, are stored under `hash` of their
bytes, come with an admitted role table, read exactly and canonically, and
the checker installed what the records describe (`Installed`), behind the
committed prelude read under the table. -/
theorem checkBytes_reading {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    ∃ t pre, admitBinding hash binding = .ok t ∧ preludeFor t = .ok pre ∧
      WithinBatch limits records blobs ∧ UniqueKeys records blobs ∧ Authentic hash records blobs ∧
        ∃ constants, BindingAdmitted hash binding t ∧ RecordsRead limits records constants ∧
          Hashed hash constants ∧ Installed hash t pre constants blobs hint env := by
  obtain ⟨t, pre, ht, hq, hw⟩ := checkBytes_with h
  obtain ⟨hwithin, huniq, hauth, t', constants, hb, hread, hhash, hinst⟩ := checkBytesWith_reading hw
  have ht' : t' = t := by
    rw [(admitBinding_ok_iff _ _ _).mpr hb] at ht
    exact Except.ok.inj ht
  subst ht'
  exact ⟨t', pre, (admitBinding_ok_iff _ _ _).mpr hb, hq, hwithin, huniq, hauth, constants, hb,
    hread, hhash, hinst⟩

/-- **Authentication.** Every record and every blob of accepted bytes is
stored under `hash` of its supplied bytes, and so is the role table's
section. -/
theorem checkBytes_authentic {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    Authentic hash records blobs ∧ hash binding.bytes = binding.address := by
  obtain ⟨_, _, _, _, hw⟩ := checkBytes_with h
  exact checkBytesWith_authentic hw

/-- **The role table.** Accepted bytes came with an admitted role table. -/
theorem checkBytes_binding {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    ∃ t, BindingAdmitted hash binding t := by
  obtain ⟨_, _, _, _, hw⟩ := checkBytes_with h
  exact checkBytesWith_binding hw

/-- **Resources.** The byte limits bound the whole decoded representation. -/
theorem checkBytes_resources {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    ∃ constants, RecordsRead limits records constants ∧
      resourceUnits constants ≤ 2 * limits.maxTotalBytes + limits.maxRecords * limits.maxRecordUnivNodes := by
  obtain ⟨_, _, _, _, hw⟩ := checkBytes_with h
  obtain ⟨_, constants, reading, _, bound⟩ := checkBytesWith_resources hw
  exact ⟨constants, reading, bound⟩

/-- **Model existence with definition values.** The model can be chosen so
that every stored definition's value denotes the constant. -/
theorem checkBytes_has_model_values (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ∀ cv value hint', Ix.Kernel.ConstantInfo.defnInfo cv value hint' ∈ env.consts →
      ∀ φ ρ, Ix.Kernel.Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨_, _, _, _, hw⟩ := checkBytes_with h
  exact checkBytesWith_has_model_values V hw

/-- **No proof of `False`**, for every hash and every role table: no constant
of an accepted environment has `False`'s role key as its type. -/
theorem checkBytes_no_proof_of_False (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env) :
    ∀ ci ∈ env.consts, ci.toConstantVal.type = .const (Ix.Kernel.roleKey .false) [] → False := by
  obtain ⟨_, _, _, _, hw⟩ := checkBytes_with h
  exact checkBytesWith_no_proof_of_False V hw

/-- **No accepted theorem of `False`, at the records.** No theorem record of
accepted bytes has a type that reads as `False`'s role key. -/
theorem checkBytes_no_False_theorem (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env)
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    (ht : admitBinding hash binding = .ok t) (hpre : preludeFor t = .ok pre)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant} {d : Ixon.Definition}
    (hmem : (owner, c) ∈ constants) (hc : c.info = .defn d) (hk : d.kind = .thm)
    (hty : (definitionReader (streamContext hash t pre constants blobs hint) owner c d).read d.typ =
      .ok (.const (Ix.Kernel.roleKey .false) [])) : False := by
  obtain ⟨t', pre', ht', hq, hw⟩ := checkBytes_with h
  rw [ht] at ht'; cases ht'
  rw [hpre] at hq; cases hq
  exact checkBytesWith_no_False_theorem V hw ht reading hmem hc hk hty

/-- **Per-record type fidelity at `checkBytes`**:
every singleton record (definition, theorem, opaque, axiom or quotient) of
accepted bytes reads (`SingletonRead`) to a declaration whose declared constant
(for definitions, theorems, non-inert opaques and installed axioms) is stored
in `env` under its own name, with its own level parameters, and with the
annotation (`AnnotOf`) of its declared type. Under `[Ix.Kernel.SetTheory V]`
(`Cached.checkDecls_consts_cfg` needs `EnvWF` from the model). -/
theorem checkBytes_consts (V : Type u) [Ix.Kernel.SetTheory V]
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytes hash binding limits records blobs hint = .ok env)
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    (ht : admitBinding hash binding = .ok t) (hpre : preludeFor t = .ok pre)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant}
    (hmem : (owner, c) ∈ constants) (hs : isSingleton c.info = true) :
    ∃ st decl, SingletonRead (streamContext hash t pre constants blobs hint) st owner c decl ∧
      ∀ cv, Ix.Kernel.Cached.Declaration.Declares decl cv →
        ∃ ci, env.find? cv.name = some ci ∧
          ci.toConstantVal.levelParams = cv.levelParams ∧
          Ix.Kernel.AnnotOf cv.type ci.toConstantVal.type := by
  obtain ⟨t', pre', ht', hq, hw⟩ := checkBytes_with h
  rw [ht] at ht'; cases ht'
  rw [hpre] at hq; cases hq
  exact checkBytesWith_consts V hw ht reading hmem hs

/-! ## Decoded records -/

theorem checkConstantsWith_has_model (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {cfg : Ix.Kernel.Cached.FoldConfig} {env : Ix.Kernel.Env .anon}
    (h : checkConstantsWith hash t pre constants blobs hint cfg = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  (checkConstantsWith_installed h).has_model V

theorem checkConstants_has_model (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {cfg : Ix.Kernel.Cached.FoldConfig} {env : Ix.Kernel.Env .anon}
    (h : checkConstants hash t constants blobs hint cfg = .ok env) : Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨_, _, hw⟩ := checkConstants_with h
  exact checkConstantsWith_has_model V hw

end Ix.Kernel.Admission

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

universe w

/-- `checkConstantsAt` admits the table and then checks the records behind
the prelude read under it. -/
theorem checkConstantsAt_with {hash : ByteArray → Address} {binding : Binding}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {cfg : Ix.Kernel.Cached.FoldConfig} {env : Ix.Kernel.Env .anon}
    (h : checkConstantsAt hash binding constants blobs hint cfg = .ok env) :
    ∃ t pre, BindingAdmitted hash binding t ∧ preludeFor t = .ok pre ∧
      checkConstantsWith hash t pre constants blobs hint cfg = .ok env := by
  unfold checkConstantsAt at h
  cases ht : admitBinding hash binding with
  | error e => simp [ht, bind, Except.bind, Except.mapError] at h
  | ok t =>
    simp only [ht, bind, Except.bind, Except.mapError] at h
    obtain ⟨pre, hq, hw⟩ := checkConstants_with h
    exact ⟨t, pre, (admitBinding_ok_iff _ _ _).mp ht, hq, hw⟩

theorem checkConstantsAt_has_model (V : Type w) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
    {binding : Binding} {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {cfg : Ix.Kernel.Cached.FoldConfig} {env : Ix.Kernel.Env .anon}
    (h : checkConstantsAt hash binding constants blobs hint cfg = .ok env) :
    Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨_, _, _, _, hw⟩ := checkConstantsAt_with h
  exact checkConstantsWith_has_model V hw

end Ix.Kernel.Admission

/-! ## The strict admission

`admitStrict` and `checkBytesStrict` (`Ix.Kernel.Admission`) only refuse: an
accept of `checkBytesStrict` is an accept of `checkBytes`
(`checkBytesStrict_checkBytes`), so every theorem above holds of it, and in
addition its table binds the pinned roles where the committed default table
does and its records are within the universe-parameter bound
(`checkBytesStrict_strict`). -/

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader

universe v

set_option linter.unusedSimpArgs false in
/-- An accepted universe-parameter admission: every record is within the
bound. -/
theorem admitLevels_ok {constants : List (Address × Ixon.Constant)}
    (h : admitLevels constants = .ok ()) :
    ∀ e ∈ constants, levelCount e.2.info ≤ maxRecordLevelParams := by
  unfold admitLevels at h
  by_cases hall : constants.all levelsWithin = true
  · intro e he
    have := List.all_eq_true.mp hall e he
    simpa [levelsWithin] using this
  · simp only [hall, Bool.false_eq_true, ↓reduceIte] at h
    split at h <;> simp [throw, throwThe, MonadExceptOf.throw] at h

set_option linter.unusedSimpArgs false in
/-- An accepted pinned-role admission under `committed`: the table binds every
pinned role where the committed default table does, or not at all. -/
theorem admitPinnedRoles_committed {t : Ix.Kernel.RoleTable}
    (h : admitPinnedRoles .committed t = .ok ()) :
    ∃ d, defaultTable = .ok d ∧ t.PinnedTo d := by
  unfold admitPinnedRoles at h
  cases hd : (defaultTable : Except String Ix.Kernel.RoleTable) with
  | error e =>
    rw [hd] at h
    simp [Except.mapError, bind, Except.bind] at h
  | ok d =>
    refine ⟨d, rfl, ?_⟩
    cases hu : t.unpinned? d with
    | none => exact (Ix.Kernel.RoleTable.unpinned?_eq_none_iff t d).mp hu
    | some r =>
      rw [hd] at h
      simp [Except.mapError, bind, Except.bind, hu, throw, throwThe, MonadExceptOf.throw] at h

set_option linter.unusedSimpArgs false in
/-- An accepted pinned-role admission under `trustAnchors`: the table binds
`True` and `True.intro` (`Role.trustAnchorsPinned`) where the committed default
table does, or not at all. -/
theorem admitPinnedRoles_trustAnchors {t : Ix.Kernel.RoleTable}
    (h : admitPinnedRoles .trustAnchors t = .ok ()) :
    ∃ d, defaultTable = .ok d ∧ t.PinnedRoles Ix.Kernel.Role.trustAnchorsPinned d := by
  unfold admitPinnedRoles at h
  cases hd : (defaultTable : Except String Ix.Kernel.RoleTable) with
  | error e =>
    rw [hd] at h
    simp [Except.mapError, bind, Except.bind] at h
  | ok d =>
    refine ⟨d, rfl, ?_⟩
    cases hu : t.unpinnedIn? Ix.Kernel.Role.trustAnchorsPinned d with
    | none => exact (Ix.Kernel.RoleTable.unpinnedIn?_eq_none_iff Ix.Kernel.Role.trustAnchorsPinned t d).mp hu
    | some r =>
      rw [hd] at h
      simp [Except.mapError, bind, Except.bind, hu, throw, throwThe, MonadExceptOf.throw] at h

set_option linter.unusedSimpArgs false in
/-- An accepted strict admission: the records are within the universe-parameter
bound, and the pinned roles' admission accepted. -/
theorem admitStrict_ok {pins : RolePins} {t : Ix.Kernel.RoleTable}
    {constants : List (Address × Ixon.Constant)} (h : admitStrict pins t constants = .ok ()) :
    (∀ e ∈ constants, levelCount e.2.info ≤ maxRecordLevelParams) ∧
      admitPinnedRoles pins t = .ok () := by
  unfold admitStrict at h
  cases hl : admitLevels constants with
  | error e => simp [hl, bind, Except.bind] at h
  | ok u =>
    simp only [hl, bind, Except.bind] at h
    exact ⟨admitLevels_ok hl, h⟩

set_option linter.unusedSimpArgs false in
/-- **An accept of the strict entry is an accept of `checkBytes`.** -/
theorem checkBytesStrict_checkBytes {pins : RolePins} {hash : ByteArray → Address}
    {binding : Binding} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesStrict pins hash binding limits records blobs hint = .ok env) :
    checkBytes hash binding limits records blobs hint = .ok env := by
  unfold checkBytesStrict at h
  cases hp : preflight limits records blobs with
  | error e => simp [hp, Except.mapError, bind, Except.bind] at h
  | ok u =>
    cases ht : admitBinding hash binding with
    | error e => simp [hp, ht, Except.mapError, bind, Except.bind] at h
    | ok t =>
      cases hd : decodeWithin limits records with
      | error e => simp [hp, ht, hd, Except.mapError, bind, Except.bind] at h
      | ok constants =>
        cases hs : admitStrict pins t constants with
        | error e => simp [hp, ht, hd, hs, Except.mapError, bind, Except.bind] at h
        | ok v => simpa [hp, ht, hd, hs, Except.mapError, bind, Except.bind] using h

set_option linter.unusedSimpArgs false in
/-- **What the strict entry adds**: an accept admits the table `t`, reads the
records canonically as `constants` within the universe-parameter bound, and,
under `committed`, `t` binds every pinned role where the committed default
table does (`RoleTable.PinnedTo`). -/
theorem checkBytesStrict_strict {pins : RolePins} {hash : ByteArray → Address}
    {binding : Binding} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesStrict pins hash binding limits records blobs hint = .ok env) :
    ∃ t constants, BindingAdmitted hash binding t ∧ RecordsRead limits records constants ∧
      (∀ e ∈ constants, levelCount e.2.info ≤ maxRecordLevelParams) ∧
      (pins = .committed → ∃ d, defaultTable = .ok d ∧ t.PinnedTo d) := by
  unfold checkBytesStrict at h
  cases hp : preflight limits records blobs with
  | error e => simp [hp, Except.mapError, bind, Except.bind] at h
  | ok u =>
    cases ht : admitBinding hash binding with
    | error e => simp [hp, ht, Except.mapError, bind, Except.bind] at h
    | ok t =>
      cases hd : decodeWithin limits records with
      | error e => simp [hp, ht, hd, Except.mapError, bind, Except.bind] at h
      | ok constants =>
        cases hs : admitStrict pins t constants with
        | error e => simp [hp, ht, hd, hs, Except.mapError, bind, Except.bind] at h
        | ok v =>
          obtain ⟨hl, hpin⟩ := admitStrict_ok hs
          refine ⟨t, constants, (admitBinding_ok_iff _ _ _).mp ht,
            (decodeRecords_ok_iff _ _ _).mp (decodeWithin_decodeRecords hd), hl, ?_⟩
          rintro rfl
          exact admitPinnedRoles_committed hpin

/-- **Model existence for the strict entry**, through `checkBytes`. -/
theorem checkBytesStrict_has_model (V : Type v) [Ix.Kernel.SetTheory V] {pins : RolePins}
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits} {records : Records}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon}
    (h : checkBytesStrict pins hash binding limits records blobs hint = .ok env) :
    Nonempty (Ix.Kernel.Model V env) :=
  checkBytes_has_model V (checkBytesStrict_checkBytes h)

set_option linter.unusedSimpArgs false in
/-- **What `checkBytesStrict .trustAnchors` adds**: an accept admits the table
`t`, reads the records canonically as `constants` within the universe-parameter
bound, and keeps `True` and `True.intro` pinned to the committed default table
(`RoleTable.PinnedRoles Role.trustAnchorsPinned`) while allowing custom
literal-support bindings. -/
theorem checkBytesStrict_trustAnchors {hash : ByteArray → Address}
    {binding : Binding} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesStrict .trustAnchors hash binding limits records blobs hint = .ok env) :
    ∃ t constants, BindingAdmitted hash binding t ∧ RecordsRead limits records constants ∧
      (∀ e ∈ constants, levelCount e.2.info ≤ maxRecordLevelParams) ∧
      ∃ d, defaultTable = .ok d ∧ t.PinnedRoles Ix.Kernel.Role.trustAnchorsPinned d := by
  unfold checkBytesStrict at h
  cases hp : preflight limits records blobs with
  | error e => simp [hp, Except.mapError, bind, Except.bind] at h
  | ok u =>
    cases ht : admitBinding hash binding with
    | error e => simp [hp, ht, Except.mapError, bind, Except.bind] at h
    | ok t =>
      cases hd : decodeWithin limits records with
      | error e => simp [hp, ht, hd, Except.mapError, bind, Except.bind] at h
      | ok constants =>
        cases hs : admitStrict .trustAnchors t constants with
        | error e => simp [hp, ht, hd, hs, Except.mapError, bind, Except.bind] at h
        | ok v =>
          obtain ⟨hl, hpin⟩ := admitStrict_ok hs
          exact ⟨t, constants, (admitBinding_ok_iff _ _ _).mp ht,
            (decodeRecords_ok_iff _ _ _).mp (decodeWithin_decodeRecords hd), hl,
            admitPinnedRoles_trustAnchors hpin⟩

/-- **Per-record type fidelity for the strict entry**, through `checkBytes`. -/
theorem checkBytesStrict_consts (V : Type v) [Ix.Kernel.SetTheory V] {pins : RolePins}
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits} {records : Records}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon}
    (h : checkBytesStrict pins hash binding limits records blobs hint = .ok env)
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    (ht : admitBinding hash binding = .ok t) (hpre : preludeFor t = .ok pre)
    {constants : List (Address × Ixon.Constant)} (reading : RecordsRead limits records constants)
    {owner : Address} {c : Ixon.Constant}
    (hmem : (owner, c) ∈ constants) (hs : isSingleton c.info = true) :
    ∃ st decl, SingletonRead (streamContext hash t pre constants blobs hint) st owner c decl ∧
      ∀ cv, Ix.Kernel.Cached.Declaration.Declares decl cv →
        ∃ ci, env.find? cv.name = some ci ∧
          ci.toConstantVal.levelParams = cv.levelParams ∧
          Ix.Kernel.AnnotOf cv.type ci.toConstantVal.type :=
  checkBytes_consts V (checkBytesStrict_checkBytes h) ht hpre reading hmem hs

end Ix.Kernel.Admission
