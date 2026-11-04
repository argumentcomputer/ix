import IxC.Kernel.Admission.Tier
import IxC.Kernel.Admission.Theorems
import IxC.Kernel.Verify.Tier

/-! # The theorems of the tiered Ixon entry

* `checkConstantsTiered_ok`: an accept is `checkConstantsWith`'s accept of
  the partition's logical records, so **every theorem about
  `checkConstantsWith` applies to the logical environment as stated**
  (model existence, no proof of `False`, the reading); the logical
  environment is well formed and no tier constant resolves in it (the
  fence); and every tier constant is typed in its scope
  (`Ix.Kernel.Tier.TypedIn`), over the tier reader's declarations.
* `checkBytesTiered_ok`: an accept authenticates every record and blob
  (`Authentic`), admits the role table, reads the committed prelude under it
  and decodes the records, then is `checkConstantsTiered`'s accept.
* `checkBytesTiered_has_model`: the logical environment has a model in every
  set theory, at every hash and role table.

Every statement holds at every content hash `hash`. -/

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Ix.Kernel.Tier (TierDecl TierConst TypedIn)

universe u

/-- An accept of `checkConstantsWith` is an accept of the verified fold. -/
theorem checkConstantsWith_checkDecls {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} (h : checkConstantsWith hash t pre constants blobs hint = .ok env) :
    ∃ ev decls, Ix.Kernel.Cached.checkDecls .verified ev decls = .ok env := by
  unfold checkConstantsWith at h
  cases hr : readStream hash t pre constants blobs hint with
  | error e => simp [hr, bind, Except.bind] at h
  | ok p =>
    obtain ⟨ev, decls⟩ := p
    simp only [hr, bind, Except.bind] at h
    cases hc : Ix.Kernel.Cached.checkDecls .verified ev
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) with
    | error e => simp [hc, Except.mapError] at h
    | ok env' =>
      simp only [hc, Except.mapError, Except.ok.injEq] at h
      exact ⟨ev, _, h ▸ hc⟩

/-- **The tiered entry over decoded records**: the logical part is
`checkConstantsWith`'s accept of the partition's logical records, the
logical environment is well formed and misses every tier constant, and
every tier constant is typed in its scope over the tier reader's
declarations. -/
theorem checkConstantsTiered_ok (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
    {t : Ix.Kernel.RoleTable} {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} {ts : List (TierConst .anon)}
    (h : checkConstantsTiered hash t pre constants blobs hint = .ok (env, ts)) :
    checkConstantsWith hash t pre (partitionTier constants).1 blobs hint = .ok env ∧
      Ix.Kernel.EnvWF env ∧ (∀ c ∈ ts, env.find? c.cv.name = none) ∧
      Ix.Kernel.EnvWF (env.extendOpaque ts) ∧
      ∃ tds, readTier (streamContext hash t pre constants blobs hint) (partitionTier constants).2 = .ok tds ∧
        ∀ c ∈ ts, TypedIn env (tds.toList.map (·.2)) ts c := by
  unfold checkConstantsTiered at h
  generalize hp : partitionTier constants = p at h
  obtain ⟨logical, tier⟩ := p
  cases hf : fenceOf logical tier with
  | some x => simp [hf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | none =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h
    cases hc : checkConstantsWith hash t pre logical blobs hint with
    | error e => simp [hc, Except.mapError] at h
    | ok env' =>
      simp only [hc, Except.mapError] at h
      cases hr : readTier (streamContext hash t pre constants blobs hint) tier with
      | error e => simp [hr] at h
      | ok tds =>
        simp only [hr] at h
        cases ht : Ix.Kernel.Tier.checkTierC (Ix.Kernel.mkFEnv env') (tds.toList.map (·.2)) with
        | error e => simp [ht, throw, throwThe, MonadExceptOf.throw] at h
        | ok r =>
          obtain ⟨fe', ts'⟩ := r
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ev, decls, hdecls⟩ := checkConstantsWith_checkDecls hc
          obtain ⟨hwf, hfresh, hwfT, htyped⟩ := Ix.Kernel.Tier.checkDecls_checkTierC V hdecls ht
          refine ⟨?_, hwf, hfresh, hwfT, tds, ?_, htyped⟩
          · first | rfl | exact hc | (rw [hp]; exact hc)
          · first | rfl | exact hr | (rw [hp]; exact hr)

/-- **The tiered Ixon entry**: the byte stage authenticated every record and
blob, the role table admitted, the committed prelude read under it, the
records decoded, and the decoded records' tiered check accepted. -/
theorem checkBytesTieredUsing_ok {prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon)}
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} {ts : List (TierConst .anon)}
    (h : checkBytesTieredUsing prelude hash binding limits records blobs hint = .ok (env, ts)) :
    Authentic hash records blobs ∧ ∃ t pre constants,
      admitBinding hash binding = .ok t ∧ prelude t = .ok pre ∧
      decodeRecords limits records = .ok constants ∧
      checkConstantsTiered hash t pre constants blobs hint = .ok (env, ts) := by
  unfold checkBytesTieredUsing at h
  cases h1 : preflight limits records blobs with
  | error e => simp [h1, bind, Except.bind, Except.mapError] at h
  | ok u1 =>
  cases h2 : uniqueKeys records blobs with
  | error e => simp [h1, h2, bind, Except.bind, Except.mapError] at h
  | ok u2 =>
  cases h3 : authenticate hash records blobs with
  | error e => simp [h1, h2, h3, bind, Except.bind, Except.mapError] at h
  | ok u3 =>
  cases h4 : admitBinding hash binding with
  | error e => simp [h1, h2, h3, h4, bind, Except.bind, Except.mapError] at h
  | ok t =>
  cases h5 : prelude t with
  | error e => simp [h1, h2, h3, h4, h5, bind, Except.bind, Except.mapError] at h
  | ok pre =>
  cases h6 : decodeRecords limits records with
  | error e => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind, Except.mapError] at h
  | ok constants =>
  simp only [h1, h2, h3, h4, h5, h6, bind, Except.bind, Except.mapError] at h
  cases u3
  exact ⟨(authenticate_ok_iff hash records blobs).mp h3, t, pre, constants, rfl,
    by first | rfl | exact h5, by first | rfl | exact h6, h⟩

/-- **The tiered Ixon entry**, behind the committed prelude: `checkBytesTieredUsing_ok`
at `preludeFor`. -/
theorem checkBytesTiered_ok {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} {ts : List (TierConst .anon)}
    (h : checkBytesTiered hash binding limits records blobs hint = .ok (env, ts)) :
    Authentic hash records blobs ∧ ∃ t pre constants,
      admitBinding hash binding = .ok t ∧ preludeFor t = .ok pre ∧
      decodeRecords limits records = .ok constants ∧
      checkConstantsTiered hash t pre constants blobs hint = .ok (env, ts) :=
  checkBytesTieredUsing_ok h

/-- **Model existence for the tiered entry's logical part**: the logical
environment of every accept, at any hash and any role table, has a model in
every set theory. -/
theorem checkBytesTiered_has_model (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
    {binding : Binding} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} {ts : List (TierConst .anon)}
    (h : checkBytesTiered hash binding limits records blobs hint = .ok (env, ts)) :
    Nonempty (Ix.Kernel.Model V env) := by
  obtain ⟨-, t, pre, constants, -, -, -, hc⟩ := checkBytesTiered_ok h
  exact checkConstantsWith_has_model V (checkConstantsTiered_ok V hc).1

/-- **The tier over the tiered entry**: the logical environment is well
formed and misses every tier constant, and every tier constant is typed in
its scope over the tier reader's declarations. -/
theorem checkBytesTiered_typed (V : Type u) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
    {binding : Binding} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} {ts : List (TierConst .anon)}
    (h : checkBytesTiered hash binding limits records blobs hint = .ok (env, ts)) :
    Ix.Kernel.EnvWF env ∧ (∀ c ∈ ts, env.find? c.cv.name = none) ∧
      ∃ tds : List (TierDecl .anon), ∀ c ∈ ts, TypedIn env tds ts c := by
  obtain ⟨-, t, pre, constants, -, -, -, hc⟩ := checkBytesTiered_ok h
  obtain ⟨-, hwf, hfresh, -, tds, -, htyped⟩ := checkConstantsTiered_ok V hc
  exact ⟨hwf, hfresh, _, htyped⟩

end Ix.Kernel.Admission
