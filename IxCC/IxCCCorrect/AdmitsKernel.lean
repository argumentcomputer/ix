import IxCCCorrect.Tiers
import IxCK.Kernel.Admission.TierTheorems

/-!
# `Admits` from IxCK's acceptance (`IxCCCorrect.AdmitsKernel`), discharge lemma A

`AdmitsChecked` is `Admits` as it stood before the owner-approved restatement: IxCK's full
checker accepts the decoded environment (`Src.KernelFront.accept`). `admits_of_accept`: it gives
the new `Admits` at the acceptance's reading (`EnvReading.ofAccepted`). Two steps:

* **the reading** (`readEnv_of_accept`): `accept` runs `readEnv`'s steps on the same inputs before
  it type checks (`acceptPrepared`: the decode, then the tiered entry, whose reading part is
  `readCore` and whose fold's install half is `installDecls`), so `readEnv` returns the environment
  `accept` installed and the reader's keys `accept`'s context gives;
* **the model** (`accepted_hasModel`): IxCK's model-existence theorem for the tiered entry's logical
  part (`checkConstantsTiered_ok`, `checkConstantsWith_has_model`), as `accepted_has_model`.
-/

set_option autoImplicit false

namespace IxCC.Correct

open IxCC.Grounding (KEnv KKey)

universe u

/-- **`Admits` before the owner-approved restatement**: IxCK's full checker accepts the committed
environment at the claim's limits, with result `acc`, and the reader keys the target. -/
def AdmitsChecked (claim : Claim) (envBytes : ByteArray) (acc : Src.KernelFront.Accepted) : Prop :=
  ∃ env, Ixon.V3.decodeAnonymousEnv envBytes = .ok env ∧
    env.root = claim.env ∧
    env.bindingAddress = some claim.roleTable ∧
    Src.KernelFront.accept env claim.kernelLimits = .ok acc ∧
    keyOf acc claim.target ≠ none

/-- Phase A of an accepting fold is accepting, with the same environment. -/
theorem installDecls_of_checkDecls {ev : Ix.Kernel.Evidences .anon}
    {ds : Array (Ix.Kernel.Declaration .anon)} {cfg : Ix.Kernel.Cached.FoldConfig} {env : KEnv}
    (h : Ix.Kernel.Cached.checkDecls .verified ev ds cfg = .ok env) :
    installDecls ev ds cfg = .ok env := by
  unfold Ix.Kernel.Cached.checkDecls at h
  unfold installDecls
  cases hf : (ds.foldlM (Ix.Kernel.Cached.annotDeclStep .verified ev)
      (0, Ix.Kernel.mkFEnv Ix.Kernel.Env.empty, #[])) { core := cfg.core } with
  | error e => simp [hf, bind, Except.bind] at h
  | ok r =>
    obtain ⟨p, s⟩ := r
    simp only [hf, bind, Except.bind] at h ⊢
    split at h
    · cases h
    · split at h
      · cases h
      · exact h

/-- **The tiered entry's reading part**: an accepting tiered entry's reading part (`readCore`)
returns the environment it installed. -/
theorem readCore_of_tiered
    {prelude : Ix.Kernel.RoleTable → Except String (Ix.Kernel.Reader.Prelude .anon)}
    {hash : ByteArray → _root_.Address} {binding : Ix.Kernel.Admission.Binding}
    {limits : Ix.Kernel.Admission.Limits} {records : Ix.Kernel.Admission.Records}
    {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : Ix.Kernel.ConstRef _root_.Address → Option Ix.Kernel.ReducibilityHint}
    {env : KEnv} {ts : List (Ix.Kernel.Tier.TierConst .anon)}
    (h : Ix.Kernel.Admission.checkBytesTieredUsing prelude hash binding limits records blobs hint =
      .ok (env, ts)) :
    readCore prelude hash binding limits records blobs hint = .ok env := by
  unfold Ix.Kernel.Admission.checkBytesTieredUsing at h
  unfold readCore
  cases h1 : Ix.Kernel.Admission.preflight limits records blobs with
  | error e => simp [h1, bind, Except.bind, Except.mapError] at h
  | ok u1 =>
  cases h2 : Ix.Kernel.Admission.uniqueKeys records blobs with
  | error e => simp [h1, h2, bind, Except.bind, Except.mapError] at h
  | ok u2 =>
  cases h3 : Ix.Kernel.Admission.authenticate hash records blobs with
  | error e => simp [h1, h2, h3, bind, Except.bind, Except.mapError] at h
  | ok u3 =>
  cases h4 : Ix.Kernel.Admission.admitBinding hash binding with
  | error e => simp [h1, h2, h3, h4, bind, Except.bind, Except.mapError] at h
  | ok t =>
  cases h5 : prelude t with
  | error e => simp [h1, h2, h3, h4, h5, bind, Except.bind, Except.mapError] at h
  | ok pre =>
  cases h6 : Ix.Kernel.Admission.decodeWithin limits records with
  | error e => simp [h1, h2, h3, h4, h5, h6, bind, Except.bind, Except.mapError] at h
  | ok constants =>
  simp only [h1, h2, h3, h4, h5, h6, bind, Except.bind, Except.mapError] at h ⊢
  -- the tiered check: its logical part accepted
  have hcw : Ix.Kernel.Admission.checkConstantsWith hash t pre
      (Ix.Kernel.Admission.partitionTier constants).1 blobs hint limits.fold = .ok env := by
    unfold Ix.Kernel.Admission.checkConstantsTiered at h
    generalize hp : Ix.Kernel.Admission.partitionTier constants = q at h
    obtain ⟨logical, tier⟩ := q
    cases hf : Ix.Kernel.Admission.fenceOf logical tier with
    | some x => simp [hf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    | none =>
      simp only [hf, bind, Except.bind, pure, Except.pure] at h
      cases hc : Ix.Kernel.Admission.checkConstantsWith hash t pre logical blobs hint
          limits.fold with
      | error e => simp [hc, Except.mapError] at h
      | ok env' =>
        simp only [hc, Except.mapError] at h
        cases hr : Ix.Kernel.Admission.readTier
            (Ix.Kernel.Admission.streamContext hash t pre constants blobs hint) tier with
        | error e => simp [hr] at h
        | ok tds =>
          simp only [hr] at h
          cases ht : Ix.Kernel.Tier.checkTierC (Ix.Kernel.mkFEnv env') (tds.toList.map (·.2))
              limits.fold.core with
          | error e => simp [ht, throw, throwThe, MonadExceptOf.throw] at h
          | ok r =>
            obtain ⟨fe', ts'⟩ := r
            simp only [ht, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
  -- its reader and its fold
  unfold Ix.Kernel.Admission.checkConstantsWith at hcw
  cases hr : Ix.Kernel.Admission.readStream hash t pre
      (Ix.Kernel.Admission.partitionTier constants).1 blobs hint with
  | error e => simp [hr, bind, Except.bind] at hcw
  | ok q =>
    obtain ⟨ev, decls⟩ := q
    simp only [hr, bind, Except.bind] at hcw ⊢
    cases hd : Ix.Kernel.Cached.checkDecls .verified ev
        (Ix.Kernel.Frontend.preparePrelude pre.ix decls) limits.fold with
    | error e => simp [hd, Except.mapError] at hcw
    | ok env' =>
      simp only [hd, Except.mapError, Except.ok.injEq] at hcw
      subst hcw
      simp [installDecls_of_checkDecls hd]

/-- **The reading of an acceptance's prepared inputs** is the acceptance's reading. -/
theorem readPrepared_of_acceptPrepared {env : Ixon.V3.Env} {limits : Ix.Kernel.Admission.Limits}
    {p : Src.KernelFront.Prepared}
    {q : { a : Src.KernelFront.Accepted // Src.KernelFront.AcceptedFrom env limits a }}
    (hq : Src.KernelFront.acceptPrepared env limits p = .ok q) :
    readPrepared env limits p = .ok (EnvReading.ofAccepted q.val) := by
  unfold Src.KernelFront.acceptPrepared at hq
  split at hq
  · simp [throw, throwThe, MonadExceptOf.throw] at hq
  · split at hq
    · split at hq
      · split at hq
        · try simp only at hq
          split at hq <;> simp [throw, throwThe, MonadExceptOf.throw] at hq
        · rename_i constants hd
          try simp only at hq
          split at hq
          · simp [throw, throwThe, MonadExceptOf.throw] at hq
          · rename_i kenv tier ha
            try simp only at hq
            split at hq
            · simp [throw, throwThe, MonadExceptOf.throw] at hq
            · try simp only at hq
              split at hq
              · simp [throw, throwThe, MonadExceptOf.throw] at hq
              · simp only [pure, Except.pure, Except.ok.injEq] at hq
                subst hq
                unfold readPrepared
                simp only [hd, readCore_of_tiered ha, bind, Except.bind, Except.mapError, pure,
                  Except.pure]
                simp only [EnvReading.ofAccepted, keyOf_eq]
                rfl
      · simp [throw, throwThe, MonadExceptOf.throw] at hq
    · simp [throw, throwThe, MonadExceptOf.throw] at hq

/-- **IxCK's acceptance is a reading**: `readEnv` returns the environment `accept` installed and
the reader's keys of `accept`'s context. -/
theorem readEnv_of_accept {env : Ixon.V3.Env} {limits : Ix.Kernel.Admission.Limits}
    {acc : Src.KernelFront.Accepted} (h : Src.KernelFront.accept env limits = .ok acc) :
    readEnv env limits = .ok (EnvReading.ofAccepted acc) := by
  unfold Src.KernelFront.accept at h
  unfold readEnv
  cases hp : Src.KernelFront.prepare env limits with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    simp only [hp, bind, Except.bind] at h ⊢
    cases hq : Src.KernelFront.acceptPrepared env limits p with
    | error e => simp [hq] at h
    | ok q =>
      simp only [hq, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact readPrepared_of_acceptPrepared hq

/-- **The environment IxCK installed has a model in every set theory** (the kernel's
model-existence theorem for the tiered entry's logical part, which every `Accepted` carries). -/
theorem acceptedEnv_model (V : Type u) [Ix.Kernel.SetTheory V] (acc : Src.KernelFront.Accepted) :
    Nonempty (Ix.Kernel.Model V acc.env) := by
  obtain ⟨-, t, pre, constants, -, -, -, hc⟩ :=
    Ix.Kernel.Admission.checkBytesTieredUsing_ok acc.accepted
  exact Ix.Kernel.Admission.checkConstantsWith_has_model V
    (Ix.Kernel.Admission.checkConstantsTiered_ok V hc).1

/-- `acceptedEnv_model`, as `HasModel`. -/
theorem accepted_hasModel (acc : Src.KernelFront.Accepted) : HasModel.{u} acc.env :=
  fun V _ => acceptedEnv_model V acc

/-- **Discharge lemma A**: IxCK's acceptance of the committed environment (`Admits` as it stood)
gives the new `Admits` at the acceptance's reading. -/
theorem admits_of_accept {claim : Claim} {envBytes : ByteArray} {acc : Src.KernelFront.Accepted}
    (h : AdmitsChecked claim envBytes acc) : Admits.{u} claim envBytes acc := by
  obtain ⟨env, hdec, hroot, hbind, hacc, hkey⟩ := h
  refine ⟨env, hdec, hroot, hbind, readEnv_of_accept hacc, ?_, ?_⟩
  · intro V _
    exact acceptedEnv_model V acc
  · exact hkey

end IxCC.Correct
