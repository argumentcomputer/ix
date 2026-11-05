module

public import IxC.Kernel.Admission.Tier

/-! # The theorems of the entries that admit user axioms

The entries under an axiom policy (`checkConstantsUnder`, `checkBytesUnder`,
`checkConstantsTieredUnder`, `checkBytesTieredUsingUnder`;
`IxC/Kernel/Admission.lean`, `IxC/Kernel/Admission/Tier.lean`) return the
environment together with the user axioms the accept is conditional on. The
user-axiom entries (`checkBytesWithUserAxioms`, `checkConstantsWithUserAxioms`,
`checkConstantsTieredWithUserAxioms`, `checkBytesTieredUsingWithUserAxioms`)
are their environments at `allowUser`.

* **At `strict` they are the certified entries** (`checkConstantsUnder_strict`,
  `checkBytesUnder_strict`, `checkConstantsTieredUnder_strict`,
  `checkBytesTieredUsingUnder_strict`), so every theorem of
  `Ix.Kernel.Admission.Theorems` and `.TierTheorems` is a theorem about them.
* **T1: an accept with no user axioms is the certified entry's accept**
  (`checkConstantsUnder_strict_of_nil`, `checkBytesUnder_strict_of_nil`,
  `checkConstantsTieredUnder_strict_of_nil`,
  `checkBytesTieredUsingUnder_strict_of_nil`), at every policy: over records
  that declare no user axiom the fold is `checkDecls`
  (`Cached.checkDeclsUnder_eq_checkDecls`). In particular such an accept has a
  model (`checkBytesUnder_has_model_of_nil`, `UserAxioms/Model.lean`), and a
  receipt of the user-axiom entry whose list is empty is a receipt of the
  certified entry (`Ix.RoleBinding.Artifact.ReceiptConditional.toReceipt`,
  `TierReceiptConditional.toTierReceipt`).
* An accept of a user-axiom entry is exactly an accept under `allowUser` with
  some list (`checkBytesWithUserAxioms_ok_iff`, ...).

This file is a `module`, so that a host's compiled code can build the certified
entry's receipt from an accept that lists no user axiom (a `module` imports
only modules). It imports no theorem module: the theorem that needs one, the
model of such an accept, is `UserAxioms/Model.lean`.

Every statement holds at every content hash `hash`. An accept that lists user
axioms is conditional on them; no model is claimed for it here. -/

public section

namespace Ix.Kernel.Admission

open Ix.Kernel (ConstRef)
open Ix.Kernel.Reader
open Ix.Kernel.Tier (TierConst)

/-- The environment of an accept that also returns a list. -/
theorem map_fst_ok_iff {ε α β : Type} {x : Except ε (α × β)} {a : α} :
    Prod.fst <$> x = .ok a ↔ ∃ b, x = .ok (a, b) := by
  cases x with
  | error e => exact ⟨fun h => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
  | ok p =>
    obtain ⟨a', b⟩ := p
    constructor
    · intro h
      have : a' = a := Except.ok.inj h
      subst this
      exact ⟨b, rfl⟩
    · rintro ⟨b', h⟩
      have : (a', b) = (a, b') := Except.ok.inj h
      cases this
      rfl

/-! ## Over decoded records -/

/-- **At `strict`, the fold over decoded records is `checkConstantsWith`.** -/
theorem checkConstantsUnder_strict (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable)
    (pre : Prelude .anon) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs) (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Prod.fst <$> checkConstantsUnder .strict hash t pre constants blobs hint =
      checkConstantsWith hash t pre constants blobs hint := by
  unfold checkConstantsUnder checkConstantsWith
  cases hr : readStream hash t pre constants blobs hint with
  | error e => rfl
  | ok p =>
    obtain ⟨ev, decls⟩ := p
    simp only [admitAxiomPolicy, bind, Except.bind, Ix.Kernel.Cached.checkDeclsUnder_strict]
    cases Ix.Kernel.Cached.checkDecls .verified ev (Ix.Kernel.Frontend.preparePrelude pre.ix decls) <;> rfl

/-- **T1 over decoded records**: an accept under any policy that lists no user
axiom is `checkConstantsWith`'s accept, with the same environment. -/
theorem checkConstantsUnder_strict_of_nil {policy : Ix.Kernel.Cached.AxiomPolicy}
    {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkConstantsUnder policy hash t pre constants blobs hint = .ok (env, [])) :
    checkConstantsWith hash t pre constants blobs hint = .ok env := by
  unfold checkConstantsUnder at h
  unfold checkConstantsWith
  cases hp : admitAxiomPolicy policy t with
  | error e => simp [hp, bind, Except.bind] at h
  | ok u =>
    cases hr : readStream hash t pre constants blobs hint with
    | error e => simp [hp, hr, bind, Except.bind] at h
    | ok p =>
      obtain ⟨ev, decls⟩ := p
      simp only [hp, hr, bind, Except.bind] at h
      simp only [bind, Except.bind]
      cases hc : Ix.Kernel.Cached.checkDeclsUnder .verified policy ev
          (Ix.Kernel.Frontend.preparePrelude pre.ix decls) with
      | error e => simp [hc, Except.mapError] at h
      | ok env' =>
        simp only [hc, Except.mapError, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, hnil⟩ := h
        rw [← Ix.Kernel.Cached.checkDeclsUnder_eq_checkDecls .verified policy ev _ hnil, hc]
        rfl

/-- An accept of `checkConstantsWithUserAxioms` is an accept under `allowUser`. -/
theorem checkConstantsWithUserAxioms_ok_iff {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable}
    {pre : Prelude .anon} {constants : List (Address × Ixon.Constant)}
    {blobs : Ix.Kernel.Ingress.Blobs} {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Kernel.Env .anon} :
    checkConstantsWithUserAxioms hash t pre constants blobs hint = .ok env ↔
      ∃ axs, checkConstantsUnder .allowUser hash t pre constants blobs hint = .ok (env, axs) :=
  map_fst_ok_iff

/-! ## Over record bytes -/

/-- **At `strict`, the bytes entry is `checkBytesWith`.** -/
theorem checkBytesUnder_strict (hash : ByteArray → Address) (binding : Binding) (pre : Prelude .anon)
    (limits : Limits) (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Prod.fst <$> checkBytesUnder .strict hash binding pre limits records blobs hint =
      checkBytesWith hash binding pre limits records blobs hint := by
  unfold checkBytesUnder checkBytesWith prepareWith
  cases preflight limits records blobs with
  | error e => rfl
  | ok _ =>
    cases uniqueKeys records blobs with
    | error e => rfl
    | ok _ =>
      cases authenticate hash records blobs with
      | error e => rfl
      | ok _ =>
        cases admitBinding hash binding with
        | error e => rfl
        | ok t =>
          cases decodeRecords limits records with
          | error e => rfl
          | ok constants =>
            refine (checkConstantsUnder_strict hash t pre constants blobs hint).trans ?_
            unfold checkConstantsWith
            show Except.bind (readStream hash t pre constants blobs hint) _ =
              Except.bind (Except.bind (readStream hash t pre constants blobs hint) _) _
            cases readStream hash t pre constants blobs hint <;> rfl

/-- **T1 over record bytes**: an accept of the bytes entry under any policy that
lists no user axiom is `checkBytesWith`'s accept, with the same environment. -/
theorem checkBytesUnder_strict_of_nil {policy : Ix.Kernel.Cached.AxiomPolicy}
    {hash : ByteArray → Address} {binding : Binding} {pre : Prelude .anon}
    {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon}
    (h : checkBytesUnder policy hash binding pre limits records blobs hint = .ok (env, [])) :
    checkBytesWith hash binding pre limits records blobs hint = .ok env := by
  unfold checkBytesWith prepareWith
  unfold checkBytesUnder at h
  cases h1 : preflight limits records blobs with
  | error e => simp [h1, bind, Except.bind, Except.mapError] at h
  | ok _ =>
    cases h2 : uniqueKeys records blobs with
    | error e => simp [h1, h2, bind, Except.bind, Except.mapError] at h
    | ok _ =>
      cases h3 : authenticate hash records blobs with
      | error e => simp [h1, h2, h3, bind, Except.bind, Except.mapError] at h
      | ok _ =>
        cases h4 : admitBinding hash binding with
        | error e => simp [h1, h2, h3, h4, bind, Except.bind, Except.mapError] at h
        | ok t =>
          cases h5 : decodeRecords limits records with
          | error e => simp [h1, h2, h3, h4, h5, bind, Except.bind, Except.mapError] at h
          | ok constants =>
            simp only [h1, h2, h3, h4, h5, bind, Except.bind, Except.mapError] at h
            refine Eq.trans ?_ (checkConstantsUnder_strict_of_nil h)
            unfold checkConstantsWith
            show Except.bind (Except.bind (readStream hash t pre constants blobs hint) _) _ =
              Except.bind (readStream hash t pre constants blobs hint) _
            cases readStream hash t pre constants blobs hint <;> rfl

/-- An accept of `checkBytesWithUserAxioms` is an accept under `allowUser`. -/
theorem checkBytesWithUserAxioms_ok_iff {hash : ByteArray → Address} {binding : Binding}
    {pre : Prelude .anon} {limits : Limits} {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env .anon} :
    checkBytesWithUserAxioms hash binding pre limits records blobs hint = .ok env ↔
      ∃ axs, checkBytesUnder .allowUser hash binding pre limits records blobs hint = .ok (env, axs) :=
  map_fst_ok_iff

/-! ## The tiered entries -/

/-- A bind whose first action accepts. -/
theorem bind_ok {ε α β : Type} {m : Except ε α} {k : α → Except ε β} {r : β}
    (h : (m >>= k) = .ok r) : ∃ a, m = .ok a ∧ k a = .ok r := by
  cases m with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- A bind after an accepting action is its continuation. -/
theorem bind_of_ok {ε α β : Type} {m : Except ε α} {a : α} (h : m = .ok a) (k : α → Except ε β) :
    (m >>= k) = k a := by
  rw [h]
  rfl

/-- A map through a bind, continuation by continuation. -/
theorem map_bind_eq {ε α β γ : Type} (f : β → γ) (m : Except ε α) {k₁ : α → Except ε β}
    {k₂ : α → Except ε γ} (h : ∀ a, f <$> k₁ a = k₂ a) : f <$> (m >>= k₁) = m >>= k₂ := by
  cases m with
  | error e => rfl
  | ok a => exact h a

/-- **At `strict`, the tiered entry over decoded records is
`checkConstantsTiered`.** -/
theorem checkConstantsTieredUnder_strict (hash : ByteArray → Address) (t : Ix.Kernel.RoleTable)
    (pre : Prelude .anon) (constants : List (Address × Ixon.Constant))
    (blobs : Ix.Kernel.Ingress.Blobs) (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Prod.fst <$> checkConstantsTieredUnder .strict hash t pre constants blobs hint =
      checkConstantsTiered hash t pre constants blobs hint := by
  unfold checkConstantsTieredUnder checkConstantsTiered
  generalize partitionTier constants = p
  obtain ⟨logical, tier⟩ := p
  dsimp only
  cases fenceOf logical tier with
  | some x =>
    obtain ⟨a, r⟩ := x
    rfl
  | none =>
    simp only [bind, Except.bind, pure, Except.pure]
    rw [← checkConstantsUnder_strict hash t pre logical blobs hint]
    cases checkConstantsUnder .strict hash t pre logical blobs hint with
    | error e => rfl
    | ok q =>
      obtain ⟨env, axs⟩ := q
      simp only [Except.mapError, Functor.map, Except.map]
      cases readTier (streamContext hash t pre constants blobs hint) tier with
      | error e => rfl
      | ok tds =>
        try simp only []
        cases Ix.Kernel.Tier.checkTierC (Ix.Kernel.mkFEnv env) (tds.toList.map (·.2)) with
        | ok r => obtain ⟨_, ts⟩ := r; rfl
        | error r => obtain ⟨e, k⟩ := r; rfl

/-- **T1 for the tiered entry over decoded records**: an accept under any policy
that lists no user axiom is `checkConstantsTiered`'s accept. -/
theorem checkConstantsTieredUnder_strict_of_nil {policy : Ix.Kernel.Cached.AxiomPolicy}
    {hash : ByteArray → Address} {t : Ix.Kernel.RoleTable} {pre : Prelude .anon}
    {constants : List (Address × Ixon.Constant)} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {r : Ix.Kernel.Env .anon × List (TierConst .anon)}
    (h : checkConstantsTieredUnder policy hash t pre constants blobs hint = .ok (r, [])) :
    checkConstantsTiered hash t pre constants blobs hint = .ok r := by
  unfold checkConstantsTieredUnder at h
  unfold checkConstantsTiered
  generalize partitionTier constants = p at h ⊢
  obtain ⟨logical, tier⟩ := p
  cases hf : fenceOf logical tier with
  | some x => simp [hf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | none =>
    simp only [hf, bind, Except.bind, pure, Except.pure] at h ⊢
    cases hc : checkConstantsUnder policy hash t pre logical blobs hint with
    | error e => simp [hc, Except.mapError] at h
    | ok q =>
      obtain ⟨env, axs⟩ := q
      simp only [hc, Except.mapError] at h
      cases hr : readTier (streamContext hash t pre constants blobs hint) tier with
      | error e => simp [hr] at h
      | ok tds =>
        simp only [hr] at h
        cases ht : Ix.Kernel.Tier.checkTierC (Ix.Kernel.mkFEnv env) (tds.toList.map (·.2)) with
        | error e => simp [ht, throw, throwThe, MonadExceptOf.throw] at h
        | ok q' =>
          obtain ⟨fe', ts'⟩ := q'
          simp only [ht, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hw := checkConstantsUnder_strict_of_nil hc
          simp only [hw, Except.mapError, ht]

/-- **At `strict`, the tiered Ixon entry is `checkBytesTieredUsing`.** -/
theorem checkBytesTieredUsingUnder_strict (prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon))
    (hash : ByteArray → Address) (binding : Binding) (limits : Limits)
    (records : Records) (blobs : Ix.Kernel.Ingress.Blobs)
    (hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint) :
    Prod.fst <$> checkBytesTieredUsingUnder .strict prelude hash binding limits records blobs hint =
      checkBytesTieredUsing prelude hash binding limits records blobs hint := by
  unfold checkBytesTieredUsingUnder checkBytesTieredUsing
  refine map_bind_eq _ _ fun _ => ?_
  refine map_bind_eq _ _ fun _ => ?_
  refine map_bind_eq _ _ fun _ => ?_
  refine map_bind_eq _ _ fun t => ?_
  refine map_bind_eq _ _ fun pre => ?_
  refine map_bind_eq _ _ fun constants => ?_
  exact checkConstantsTieredUnder_strict hash t pre constants blobs hint

/-- **T1 for the tiered Ixon entry**: an accept under any policy that lists no
user axiom is `checkBytesTieredUsing`'s accept. -/
theorem checkBytesTieredUsingUnder_strict_of_nil {policy : Ix.Kernel.Cached.AxiomPolicy}
    {prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon)}
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {r : Ix.Kernel.Env .anon × List (TierConst .anon)}
    (h : checkBytesTieredUsingUnder policy prelude hash binding limits records blobs hint = .ok (r, [])) :
    checkBytesTieredUsing prelude hash binding limits records blobs hint = .ok r := by
  unfold checkBytesTieredUsingUnder at h
  unfold checkBytesTieredUsing
  obtain ⟨_, h1, h⟩ := bind_ok h
  obtain ⟨_, h2, h⟩ := bind_ok h
  obtain ⟨_, h3, h⟩ := bind_ok h
  obtain ⟨t, h4, h⟩ := bind_ok h
  obtain ⟨pre, h5, h⟩ := bind_ok h
  obtain ⟨constants, h6, h⟩ := bind_ok h
  simp only [bind_of_ok h1, bind_of_ok h2, bind_of_ok h3, bind_of_ok h4, bind_of_ok h5,
    bind_of_ok h6]
  exact checkConstantsTieredUnder_strict_of_nil h

/-- An accept of `checkBytesTieredUsingWithUserAxioms` is an accept under
`allowUser`. -/
theorem checkBytesTieredUsingWithUserAxioms_ok_iff
    {prelude : Ix.Kernel.RoleTable → Except String (Prelude .anon)}
    {hash : ByteArray → Address} {binding : Binding} {limits : Limits}
    {records : Records} {blobs : Ix.Kernel.Ingress.Blobs}
    {hint : ConstRef Address → Option Ix.Kernel.ReducibilityHint}
    {r : Ix.Kernel.Env .anon × List (TierConst .anon)} :
    checkBytesTieredUsingWithUserAxioms prelude hash binding limits records blobs hint = .ok r ↔
      ∃ axs, checkBytesTieredUsingUnder .allowUser prelude hash binding limits records blobs hint =
        .ok (r, axs) :=
  map_fst_ok_iff

end Ix.Kernel.Admission

end
