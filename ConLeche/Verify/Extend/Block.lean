module

public import ConLeche.Verify.Denote.Rename
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Extend.Inversions

public section

/-!
# The modeled block's fold invariant and member valuation

Relocated verbatim from `ConLeche/TTVerify/DeclIndMember.lean` (task
#148, T5): `BlockInstalledTT` (the group-local public↔`_model`
identification — model stored, level parameters agree, renamed type
equal up to display names, valuation aliased), its three preservation
lemmas, and `cvalAlias` (a modeled member's valuation is its `_model`
companion's).  All V-free and lane-shared: both the TT lane's
`checkIndMemberTT` fold and the [set] lane's `declIndS` fold consume
them; the namespace stays `ConLeche.Verify` so no call site moves.
-/

namespace ConLeche.Verify

open ConLeche.Term

/-! ## The block fold invariant -/

/-- The fold invariant of `checkModeled`: every installed block member
has its `_model` companion stored (as a definition with the same level
parameters), its checked type is the companion's under the block
renaming (up to display names), and it is *valued* by the companion.
Transpose of `BlockInstalled`; the group-local public↔`_model`
identification, discarded at the block's end. -/
@[expose] def BlockInstalledTT (blockNames : List Name) (env' : Env)
    (cval : TConstVal) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci, env'.find? n = some ci →
    ∃ cvm mval hmcvm,
      env'.find? (n.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      ((ci.toConstantVal.type.renameConsts (fun n' =>
        if blockNames.contains n' then n'.str "_model" else n'))
        == cvm.type) = true ∧
      ∀ ψ : Name → Nat, cval n ψ = cval (n.str "_model") ψ

/-- Installing one member valued by its model preserves the fold
invariant.  Transpose of `BlockInstalled.step`. -/
theorem BlockInstalledTT.step {blockNames : List Name} {env' : Env}
    {cval cval₁ : TConstVal} {ci₁ : ConstantInfo} {cvm : ConstantVal}
    {mval : Expr} {hmcvm : ReducibilityHint}
    (hI : BlockInstalledTT blockNames env' cval)
    (hms : ci₁.name.isModelSuffix = false)
    (hfm : env'.find? (ci₁.name.str "_model") =
      some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci₁.toConstantVal.levelParams)
    (hren : ((ci₁.toConstantVal.type.renameConsts (fun n' =>
      if blockNames.contains n' then n'.str "_model" else n'))
      == cvm.type) = true)
    (hval₁ : ∀ ψ, cval₁ ci₁.name ψ = cval (ci₁.name.str "_model") ψ)
    (hpres₁ : ∀ n ψ, n ≠ ci₁.name → cval₁ n ψ = cval n ψ) :
    BlockInstalledTT blockNames ⟨ci₁ :: env'.consts⟩ cval₁ := by
  intro n hbn ci₂ hf₂
  rw [Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    obtain rfl := Option.some.inj hf₂
    obtain rfl : ci₁.name = n := hh
    refine ⟨cvm, mval, hmcvm, ?_, hlps, hren, ?_⟩
    · rw [Env.find?_cons,
        if_neg (fun h => Name.str_ne ci₁.name "_model" h.symm)]
      exact hfm
    · intro ψ
      rw [hval₁ ψ, hpres₁ _ ψ (Name.str_ne ci₁.name "_model")]
  · next hh =>
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hI n hbn ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, hren₂, ?_⟩
    · rw [Env.find?_cons, if_neg (show ¬ci₁.name = n.str "_model" from
        fun h => Name.str_model_ne hms h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁ _ ψ (fun h => hh h.symm),
        hpres₁ _ ψ (fun h => Name.str_model_ne hms h),
        hv₂ ψ]

/-- Prepending a fresh non-member constant preserves the fold
invariant (the projection-family phase's installs).  Transpose of
`BlockInstalled.fresh_cons`. -/
theorem BlockInstalledTT.fresh_cons {blockNames : List Name} {env' : Env}
    {cval cval₁ : TConstVal} {c₀ : ConstantInfo}
    (hI : BlockInstalledTT blockNames env' cval)
    (hnotb : blockNames.contains c₀.name = false)
    (hfresh : env'.find? c₀.name = none)
    (hpres : ∀ n ψ, n ≠ c₀.name → cval₁ n ψ = cval n ψ) :
    BlockInstalledTT blockNames ⟨c₀ :: env'.consts⟩ cval₁ := by
  intro n hbn ci₂ hf₂
  rw [Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    exfalso
    rw [← hh] at hbn
    rw [hbn] at hnotb
    exact nomatch hnotb
  · next hh =>
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hI n hbn ci₂ hf₂
    have hnne : n ≠ c₀.name := fun h => hh h.symm
    have hmne : n.str "_model" ≠ c₀.name := by
      intro h
      rw [← h] at hfresh
      rw [hfresh] at hfm₂
      exact nomatch hfm₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, hren₂, ?_⟩
    · rw [Env.find?_cons, if_neg (fun h => hmne h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres _ ψ hnne, hpres _ ψ hmne, hv₂ ψ]

/-- The semantically pruned block renaming is `RenameOkT` at any
environment/valuation carrying the block invariant.  Transpose of
`BlockInstalled.renameOk`. -/
theorem BlockInstalledTT.renameOkT {blockNames : List Name} {env₁ : Env}
    {cval₁ : TConstVal}
    (hI : BlockInstalledTT blockNames env₁ cval₁) :
    RenameOkT cval₁ env₁ (fun n => if (env₁.find? n).isSome = true then
      (if blockNames.contains n then n.str "_model" else n) else n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n ci₂ hf₂
    have hsome : (env₁.find? n).isSome = true := by rw [hf₂]; rfl
    simp only [hsome, if_true]
    by_cases hc : blockNames.contains n = true
    · rw [if_pos hc]
      obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, -, -⟩ := hI n hc ci₂ hf₂
      exact ⟨.defnInfo cvm₂ mval₂ hm₂, hfm₂, hlps₂⟩
    · rw [if_neg hc]
      exact ⟨ci₂, hf₂, rfl⟩
  · intro n hf₂
    simp [hf₂]
  · intro n ψ
    cases hf₂ : env₁.find? n with
    | none => simp [hf₂]
    | some ci₂ =>
      have hsome : (env₁.find? n).isSome = true := by rw [hf₂]; rfl
      simp only [hsome, if_true]
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        obtain ⟨cvm₂, mval₂, -, -, -, -, hv₂⟩ := hI n hc ci₂ hf₂
        exact (hv₂ ψ).symm
      · rw [if_neg hc]

/-! ## The member's valuation -/

/-- Value one name by another's valuation — the modeled member's
valuation is its `_model` companion's. -/
def cvalAlias (cval : TConstVal) (n mn : Name) : TConstVal := fun c ψ =>
  if c = n then cval mn ψ else cval c ψ


end ConLeche.Verify
