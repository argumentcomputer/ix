import IxVMRefinement.FamilyAlias.MemberStep

/-! # The members' model aliases, from the family check's facts

The alias group of a family step holds, for each member of the family, a definition at the
member's model key: its type is the member's annotated type under the block renaming, its value
the member's advice model at the member's own level parameters. This module builds those
aliases from the family as read, its annotated types and the renaming to the advice, and shows
they are an alias group over the prefix.

* `renameConsts_comp`, `renameConsts_congr_mentions`, `constsResolve_transfer`: renamings
  compose; two renamings agree on a term whose named keys they agree on; resolution of a
  renamed term passes to another renaming and environment, key by key, for the keys the term
  names.
* `modelAlias`, `modelAliases`, `modelTable`: the aliases, newest first, and their table.
* `AliasesReady`: what each alias needs of the aliases installed before it: its key is fresh,
  the prefix's constants are still found, its type resolves, and the block renaming followed by
  the earlier aliases' renaming is the renaming to the advice on the member's annotated type.
* `aliasGroup_modelAliases`: from the members' facts and `AliasesReady`, the aliases extend an
  alias group to an alias group.

`AliasesReady` is a condition on names only (which keys the prefix and the earlier aliases
store, which members a type names); it follows from the facts' scope field and the freshness of
the family's names. That derivation is not in this module. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  EnvExt EnvWF auxKey hasFvar_renameConsts)
open Ix.Kernel.Rules (Annot Red DefEq Infer)

set_option linter.unusedVariables false

/-! ## Renamings and the keys a term names -/

/-- Renamings compose. -/
theorem renameConsts_comp (f h : KKey → KKey) :
    ∀ e : KExpr, (e.renameConsts f).renameConsts h = e.renameConsts (fun k => h (f k)) := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ | const _ _ => rfl
  | fvar _ _ ih => simp only [Expr.renameConsts, ih]
  | app _ _ ihf iha => simp only [Expr.renameConsts, ihf, iha]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb => simp only [Expr.renameConsts, iht, ihb]
  | letE _ _ _ _ iht ihv ihb => simp only [Expr.renameConsts, iht, ihv, ihb]
  | proj _ _ _ ihe => simp only [Expr.renameConsts, ihe]

/-- Two renamings agree on a term whose named keys they agree on. -/
theorem renameConsts_congr_mentions {f g : KKey → KKey} :
    ∀ e : KExpr, (∀ k, e.mentionsConst k = true → f k = g k) →
      e.renameConsts f = e.renameConsts g := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ => intro _; rfl
  | const n _ =>
    intro h
    have hn : f n = g n := h n (by simp [Expr.mentionsConst])
    simp only [Expr.renameConsts, hn]
  | fvar _ _ ih =>
    intro h
    simp only [Expr.renameConsts, ih (fun k hk => h k (by simpa [Expr.mentionsConst] using hk))]
  | app _ _ ihf iha =>
    intro h
    simp only [Expr.renameConsts,
      ihf (fun k hk => h k (by simp [Expr.mentionsConst, hk])),
      iha (fun k hk => h k (by simp [Expr.mentionsConst, hk]))]
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro h
    simp only [Expr.renameConsts,
      iht (fun k hk => h k (by simp [Expr.mentionsConst, hk])),
      ihb (fun k hk => h k (by simp [Expr.mentionsConst, hk]))]
  | letE _ _ _ _ iht ihv ihb =>
    intro h
    simp only [Expr.renameConsts,
      iht (fun k hk => h k (by simp [Expr.mentionsConst, hk])),
      ihv (fun k hk => h k (by simp [Expr.mentionsConst, hk])),
      ihb (fun k hk => h k (by simp [Expr.mentionsConst, hk]))]
  | proj _ _ _ ihe =>
    intro h
    simp only [Expr.renameConsts, ihe (fun k hk => h k (by simp [Expr.mentionsConst, hk]))]

/-- **Resolution passes from one renaming and environment to another**, key by key for the keys
the term names: where `env` stores `g k`, `E` stores `f k`; and `E` stores what `env` stores. -/
theorem constsResolve_transfer {env E : Env .anon} {g f : KKey → KKey}
    (hmono : ∀ k, (env.find? k).isSome = true → (E.find? k).isSome = true) :
    ∀ e : KExpr,
      (∀ k, e.mentionsConst k = true → (env.find? (g k)).isSome = true →
        (E.find? (f k)).isSome = true) →
      (e.renameConsts g).constsResolve env = true →
      (e.renameConsts f).constsResolve E = true := by
  intro e
  induction e with
  | bvar _ | sort _ => intro _ _; rfl
  | lit _ => intro _ h; exact Ix.Kernel.Expr.constsResolve_le hmono h
  | const n _ => intro hk h; exact hk n (by simp [Expr.mentionsConst]) h
  | fvar _ _ ih =>
    intro hk h
    exact ih (fun k hm => hk k (by simpa [Expr.mentionsConst] using hm)) h
  | app _ _ ihf iha =>
    intro hk h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨ihf (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.1,
      iha (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.2⟩
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro hk h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨iht (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.1,
      ihb (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.2⟩
  | letE _ _ _ _ iht ihv ihb =>
    intro hk h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.1.1,
      ihv (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.1.2⟩,
      ihb (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.2⟩
  | proj _ _ _ ihe =>
    intro hk h
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h ⊢
    exact ⟨hmono _ h.1, ihe (fun k hm => hk k (by simp [Expr.mentionsConst, hm])) h.2⟩

/-! ## The aliases -/

/-- **The model alias of a member**: the definition at the member's model key, at the member's
level parameters, of the member's annotated type under the block renaming, by the member's
advice model. -/
def modelAlias (g : KKey → KKey) (bn : List KKey) (ci : ConstantInfo .anon) (tyA : KExpr) :
    ConstantInfo .anon :=
  .defnInfo
    ⟨auxKey ci.toConstantVal.name .model, ci.toConstantVal.levelParams,
      tyA.renameConsts (blockRen bn)⟩
    (.const (g ci.toConstantVal.name) (ci.toConstantVal.levelParams.map .param)) .abbrev

/-- The model aliases of the listed members, installed in the list's order onto `as` (the result
is newest first). -/
def modelAliases (g : KKey → KKey) (bn : List KKey) :
    List (ConstantInfo .anon) → List KExpr → List (ConstantInfo .anon) →
    List (ConstantInfo .anon)
  | ci :: rest, tyA :: tys, as => modelAliases g bn rest tys (modelAlias g bn ci tyA :: as)
  | _, _, as => as

/-- The table of the model aliases: each model key with the member's model, onto `tbl`. -/
def modelTable (g : KKey → KKey) :
    List (ConstantInfo .anon) → List KExpr → List (KKey × KKey) → List (KKey × KKey)
  | ci :: rest, _ :: tys, tbl =>
    modelTable g rest tys
      ((auxKey ci.toConstantVal.name .model, g ci.toConstantVal.name) :: tbl)
  | _, _, tbl => tbl

/-- **What each model alias needs of the aliases installed before it** (`as`, with table
`tbl`): its key is fresh, the prefix's constants are still found, its type resolves, and on the
member's annotated type the block renaming followed by the earlier aliases' renaming is the
renaming to the advice. -/
def AliasesReady (env : Env .anon) (g : KKey → KKey) (bn : List KKey) :
    List (ConstantInfo .anon) → List KExpr → List (ConstantInfo .anon) → List (KKey × KKey) →
    Prop
  | ci :: rest, tyA :: tys, as, tbl =>
    (⟨as ++ env.consts⟩ : Env .anon).find? (auxKey ci.toConstantVal.name .model) = none ∧
    (∀ (k : KKey) (c : ConstantInfo .anon), env.find? k = some c →
      (⟨as ++ env.consts⟩ : Env .anon).find? k = some c) ∧
    (tyA.renameConsts (blockRen bn)).constsResolve (⟨as ++ env.consts⟩ : Env .anon) = true ∧
    (tyA.renameConsts (blockRen bn)).renameConsts (aliasMap tbl) = tyA.renameConsts g ∧
    AliasesReady env g bn rest tys (modelAlias g bn ci tyA :: as)
      ((auxKey ci.toConstantVal.name .model, g ci.toConstantVal.name) :: tbl)
  | _, _, _, _ => True

/-- **The members' model aliases extend an alias group to an alias group**, from the members'
facts and `AliasesReady`. -/
theorem aliasGroup_modelAliases {env : Env .anon} {g : KKey → KKey} {bn : List KKey}
    (hwf : EnvWF env) :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (as : List (ConstantInfo .anon))
      (tbl : List (KKey × KKey)),
      AliasGroup env (aliasMap tbl) as →
      MembersFacts env g ms tys →
      AliasesReady env g bn ms tys as tbl →
      AliasGroup env (aliasMap (modelTable g ms tys tbl)) (modelAliases g bn ms tys as)
  | [], [], _, _, hg, _, _ => hg
  | [], _ :: _, _, _, hg, _, _ => hg
  | _ :: _, [], _, _, hg, _, _ => hg
  | ci :: rest, tyA :: tys, as, tbl, hg, hm, hr => by
    obtain ⟨hF, hrestF⟩ := hm
    obtain ⟨hfresh, hfind, hres, hcomp, hready⟩ := hr
    obtain ⟨hperm, hclosed, hbnd, hann, hlv, ⟨cvm, mval₀, hint₀, hfm, hlm, htm⟩, -⟩ := hF
    have hannot : Annot 0 ci.toConstantVal.type tyA := annot_of_annotates hann hclosed hbnd 0
    obtain ⟨hclA, hbA⟩ := (judgeFrames_posRulesJ env).annot_syntax hannot hclosed hbnd
    have hty : ExprLvEq
        (posOf ci.toConstantVal.levelParams
          ((tyA.renameConsts (blockRen bn)).renameConsts (aliasMap tbl)))
        (posOf (ConstantInfo.defnInfo cvm mval₀ hint₀ : ConstantInfo .anon).toConstantVal.levelParams
          (ConstantInfo.defnInfo cvm mval₀ hint₀ : ConstantInfo .anon).toConstantVal.type) := by
      rw [hcomp]
      exact htm
    have hstep : AliasGroup env
        (aliasMap ((auxKey ci.toConstantVal.name .model, g ci.toConstantVal.name) :: tbl))
        (modelAlias g bn ci tyA :: as) :=
      AliasGroup.cons hg hperm hfresh (ne_projTableName_auxKey_model _)
        (hfind _ _ hfm) hlm
        ((hasFvar_renameConsts (blockRen bn) tyA).trans hclA)
        ((allLevelParamsDefined_renameConsts (blockRen bn) _ tyA).trans hlv)
        hres
        ((looseBVarsBounded_renameConsts (blockRen bn) 0 tyA).trans hbA)
        hty (ite_eq_left rfl) (fun x hx => ite_eq_right hx)
    exact aliasGroup_modelAliases hwf rest tys _ _ hstep hrestF hready

end IxVM.Refinement.Decl.FamilyAlias
