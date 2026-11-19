import IxVMRefinement.FamilyAlias.Facts

/-! # A member's record from the family check's facts

The first part of the passage from `FamilyCheckFacts` (`FamilyAlias/Facts.lean`) to IxC's renamed
record over the family package: one member of the family (a type, a constructor or a recursor
before its rules) against its model.

* `constsResolve_of_renamed`: a term whose renaming resolves in `env` resolves in any environment
  that stores what `env` stores and every key the renaming sends to a stored key.
* `renameConsts_block_alias`: on a term that resolves in an environment storing no alias key, the
  block renaming followed by the alias renaming is the renaming to the advice.
* `memberValRunJ_of_facts`: IxC's member record (`MemberValRunJ`: the member's front door and its
  alias at the model key) at an environment `env'` that extends the prefix and stores the
  member's alias, from the member's facts.

What the member's record needs beyond its facts is listed in the last statement's hypotheses:
the prefix stores well-formed constants (the model's own type gives the member's level
parameters), the name is fresh in `env'` and is no reserved, projection-function or model key,
the annotated type resolves in `env'`, and the two renamings compose to the renaming to the
advice on it. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  EnvExt EnvWF auxKey hasFvar_renameConsts)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false

/-! ## Resolution and the two renamings -/

/-- **Resolution passes back along a renaming**: if the renamed term resolves in `env`, the
term resolves in an environment that stores what `env` stores and every key the renaming sends
to a key `env` stores. -/
theorem constsResolve_of_renamed {env E : Env .anon} {g : KKey → KKey}
    (hE : ∀ k, (env.find? (g k)).isSome = true → (E.find? k).isSome = true)
    (hmono : ∀ k, (env.find? k).isSome = true → (E.find? k).isSome = true) :
    ∀ e : KExpr, (e.renameConsts g).constsResolve env = true → e.constsResolve E = true := by
  intro e
  induction e with
  | bvar _ | sort _ => intro _; rfl
  | lit _ => intro h; exact Ix.Kernel.Expr.constsResolve_le hmono h
  | fvar _ _ ih => intro h; exact ih h
  | const n _ => intro h; exact hE n h
  | app _ _ ihf iha =>
    intro h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1, ihb h.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj _ _ _ ihe =>
    intro h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hmono _ h.1, ihe h.2⟩

/-- **The block renaming followed by the alias renaming is the renaming to the advice**, on a
term that resolves in an environment `E` at whose stored keys the two agree: `h` sends the model
key of a member to the member's model and fixes every other key `E` stores. -/
theorem renameConsts_block_alias {E : Env .anon} {g h : KKey → KKey} {bn : List KKey}
    (hmem : ∀ k, bn.contains k = true → h (auxKey k .model) = g k)
    (hout : ∀ k, bn.contains k = false → (E.find? k).isSome = true → h k = k ∧ g k = k)
    {e : KExpr} (hres : e.constsResolve E = true) :
    (e.renameConsts (blockRen bn)).renameConsts h = e.renameConsts g :=
  renameConsts_comp_eq_of_constsResolve
    (fun k hk => by
      show h (if bn.contains k then auxKey k .model else k) = g k
      cases hb : bn.contains k with
      | true => exact hmem k hb
      | false =>
        obtain ⟨h1, h2⟩ := hout k hb hk
        show h k = g k
        rw [h1, h2]) hres

/-! ## One member -/

/-- **A member's record from its facts.** `env` is the prefix, which stores the member's model;
`env'` is the environment the member is stored in: it extends the prefix, `h` moves stored
aliases only in it, and it stores the member's alias at the model key, a definition at the
member's level parameters whose type is the member's annotated type under the block renaming. -/
theorem memberValRunJ_of_facts {env env' : Env .anon} {g h : KKey → KKey} {bn : List KKey}
    {ci : ConstantInfo .anon} {tyA : KExpr}
    (hF : MemberFacts env g ci tyA) (hwf : EnvWF env)
    (hext : EnvExt env env') (hA : AliasEnv env' h)
    (hfresh : env'.find? ci.toConstantVal.name = none)
    (hres : Ix.Kernel.reservedBasisNames.contains ci.toConstantVal.name = false)
    (hprj : ci.toConstantVal.name.isProjFnShape = false)
    (hsuf : ci.toConstantVal.name.isModelSuffix = false)
    (hcomp : (tyA.renameConsts (blockRen bn)).renameConsts h = tyA.renameConsts g)
    (hresolve : tyA.constsResolve env' = true)
    (halias : ∃ (mval : KExpr) (hint : ReducibilityHint),
      env'.find? (auxKey ci.toConstantVal.name .model) = some (.defnInfo
        ⟨auxKey ci.toConstantVal.name .model, ci.toConstantVal.levelParams,
          tyA.renameConsts (blockRen bn)⟩ mval hint)) :
    MemberValRunJ (renameJ (blockRen bn) (famJ h)) env' bn ci.toConstantVal
      ⟨ci.toConstantVal.name, ci.toConstantVal.levelParams, tyA⟩ := by
  obtain ⟨hperm, hclosed, hbnd, hann, hlv, ⟨cvm, mval₀, hint₀, hfm, hlm, htm⟩,
    ⟨stype, u, hinf, hsort⟩⟩ := hF
  obtain ⟨mval, hint, hal⟩ := halias
  -- the annotation, and what it keeps of the declared type
  have hannot : Annot 0 ci.toConstantVal.type tyA := annot_of_annotates hann hclosed hbnd 0
  obtain ⟨hclA, hbA⟩ := (judgeFrames_posRulesJ env).annot_syntax hannot hclosed hbnd
  -- the front door's typing, on the renamed type
  have hclR : (tyA.renameConsts (blockRen bn)).hasFvar = false :=
    (hasFvar_renameConsts (blockRen bn) tyA).trans hclA
  have hi : posRulesJ.infer env' 0 (tyA.renameConsts g) stype :=
    posRulesJ_infer_weaken hext hinf
  rw [← hcomp] at hi
  have hinf' : (renameJ (blockRen bn) (famJ h)).infer env' 0 tyA stype :=
    Or.inr ⟨hclA, hA, LeavesFixed.of_closed hclR, hi⟩
  have hsort' : (renameJ (blockRen bn) (famJ h)).sort env' 0 stype u :=
    posRulesJ_sort_weaken hext hsort
  have hcv : ConstantValRunJ (renameJ (blockRen bn) (famJ h)) env' ci.toConstantVal tyA :=
    ⟨by rw [hfresh]; rfl, hres, hprj, levelParam_nodup_of_perm_range hperm, hbnd, hclosed,
      hannot, hlv, hresolve, stype, u, hinf', hsort'⟩
  exact ⟨tyA, hcv, rfl, hsuf, _, mval, hint, hal, rfl, beq_self_eq_true _⟩

end IxVM.Refinement.Decl.FamilyAlias
