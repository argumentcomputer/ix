module

public import ConLeche.Verify.EnvPreds

public section

/-!
# Sibs

Per-clause preservation (`.cons`) lemmas for extending an environment by
one fresh constant, at the two clauses that are statements about the
environment alone: `BasisBlocks` and `RecCtorsStored`, with the head
obligation (`SibFinds`) they consume.

The valuation-carrying clauses of the same cons are preserved one tier
up, in `ConLeche/Model/Install.lean`, which builds the extended core out
of the prefix's fields and these two model-free lemmas.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

/-- The sibling-availability data `BasisBlocks` preservation needs when
extending by one (fresh) constant: if the constant is a recursor-kind
record, the members of its block are already stored. -/
def SibFinds (env : Env) (c₀ : ConstantInfo) : Prop :=
  ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
    (c₀.name = eqName.str "rec" →
      env.find? eqName = some eqA ∧ env.find? eqReflName = some eqReflA) ∧
    (c₀.name = natName.str "rec" →
      env.find? natName = some natA ∧
      env.find? natZeroName = some natZeroA ∧
      env.find? natSuccName = some natSuccA) ∧
    (c₀.name = punitName.str "rec" →
      env.find? punitName = some punitA ∧
      env.find? punitUnitName = some punitUnitA)

theorem BasisBlocks.cons {env : Env} {c₀ : ConstantInfo}
    (hb : BasisBlocks env) (hfind' : env.find? c₀.name = none)
    (hsib : SibFinds env c₀) :
    BasisBlocks (⟨c₀ :: env.consts⟩ : Env) := by
  have keep : ∀ {s : Name} {X : ConstantInfo}, env.find? s = some X →
      Env.find? ⟨c₀ :: env.consts⟩ s = some X := by
    intro s X hs
    rw [Env.find?_cons_of_isSome hfind' (by rw [hs]; rfl)]
    exact hs
  refine ⟨?_, ?_, ?_⟩
  · intro cv mI rP rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨hs, -, -⟩ := hsib cv mI rP rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.1 cv mI rP rules h
      exact ⟨keep h1, keep h2⟩
  · intro cv mI rP rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, hs, -⟩ := hsib cv mI rP rules heq
      obtain ⟨h1, h2, h3⟩ := hs hn
      exact ⟨keep h1, keep h2, keep h3⟩
    · next hn =>
      obtain ⟨h1, h2, h3⟩ := hb.right.left cv mI rP rules h
      exact ⟨keep h1, keep h2, keep h3⟩
  · intro cv mI rP rules h
    rw [Env.find?_cons] at h
    split at h
    · next hn =>
      obtain heq := (Option.some.inj h)
      obtain ⟨-, -, hs⟩ := hsib cv mI rP rules heq
      obtain ⟨h1, h2⟩ := hs hn
      exact ⟨keep h1, keep h2⟩
    · next hn =>
      obtain ⟨h1, h2⟩ := hb.right.right cv mI rP rules h
      exact ⟨keep h1, keep h2⟩

/-- `RecCtorsStored` is preserved by a fresh extension, given the
stored-constructor facts for the new member (vacuous unless it is a
recursor). -/
theorem RecCtorsStored.cons {env : Env} {c₀ : ConstantInfo}
    (hold : RecCtorsStored env) (hfresh : env.find? c₀.name = none)
    (hnew : ∀ cvR mI rP rules, c₀ = .recInfo cvR mI rP rules →
      ∀ r ∈ rules,
        (∃ cvj cnP cnF,
          env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → recRuleKOf env.find? r.ctor = true) ∧
        (r.eta = true → recRuleEtaOf env.find? c₀.name r.ctor = true)) :
    RecCtorsStored (⟨c₀ :: env.consts⟩ : Env) := by
  have hkeep : ∀ (m : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env.find? m = some ci → (⟨c₀ :: env.consts⟩ : Env).find? m = some ci := by
    intro m ci _ hf
    rw [Env.find?_cons_of_isSome hfresh (by rw [hf]; rfl)]
    exact hf
  intro n cv mI rP rules hfp r hr
  rw [Env.find?_cons] at hfp
  split at hfp
  · next hn =>
    obtain hceq := Option.some.inj hfp
    obtain ⟨⟨cvj, cnP, cnF, hf⟩, hk, he⟩ := hnew _ _ _ _ hceq r hr
    exact ⟨⟨cvj, cnP, cnF, hkeep _ _
        (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) hf⟩,
      fun hb => recRuleKOf_mono hkeep (hk hb),
      fun hb => recRuleEtaOf_mono hkeep (hn ▸ he hb)⟩
  · next hn =>
    obtain ⟨⟨cvj, cnP, cnF, hf⟩, hk, he⟩ := hold n cv mI rP rules hfp r hr
    exact ⟨⟨cvj, cnP, cnF, hkeep _ _
        (fun _ _ _ _ hh => ConstantInfo.noConfusion hh) hf⟩,
      fun hb => recRuleKOf_mono hkeep (hk hb),
      fun hb => recRuleEtaOf_mono hkeep (he hb)⟩

end ConLeche
