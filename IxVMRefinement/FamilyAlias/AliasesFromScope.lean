import IxVMRefinement.FamilyAlias.ModelAliases

/-! # The members' model aliases are admissible, from the scope of the members' types

`AliasesReady` (`FamilyAlias/ModelAliases.lean`) is what each member's model alias needs of the
aliases installed before it. This module derives it from the members' facts, the scope of their
annotated types (`typesScopedB`: a type names, of the family's members, only earlier ones) and
the names: the family's names are distinct, the renaming to the advice moves members only, and
the prefix stores no model key of a member.

* `stored_of_mentions`: a key a term names is stored where the renamed term resolves, itself
  or renamed.
* `AliasStage`: what the aliases installed so far give: the prefix's constants are still found,
  each installed alias is stored and sent to its member's model, and a key the prefix stores is
  not moved.
* `aliasesReady_of_scope`: the derivation, by the family's order.

With `aliasGroup_modelAliases` this gives the alias group of the members' aliases from the
family check's facts and the names alone. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  EnvExt EnvWF auxKey Derived)

set_option linter.unusedVariables false

/-- **A key a term names is stored where the renamed term resolves**: renamed, where it is named
as a constant; as it is, where it is named as a projection's structure. -/
theorem stored_of_mentions {env : Env .anon} {g : KKey → KKey} {k : KKey} :
    ∀ e : KExpr, (e.renameConsts g).constsResolve env = true → e.mentionsConst k = true →
      (env.find? (g k)).isSome = true ∨ (env.find? k).isSome = true := by
  intro e
  induction e with
  | bvar _ | sort _ | lit _ =>
    intro _ hm
    exact absurd hm (by simp [Expr.mentionsConst])
  | const n _ =>
    intro h hm
    have hn : n = k := by simpa [Expr.mentionsConst] using hm
    subst hn
    exact Or.inl h
  | fvar _ _ ih =>
    intro h hm
    exact ih h (by simpa [Expr.mentionsConst] using hm)
  | app _ _ ihf iha =>
    intro h hm
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact ihf h.1 hm
    · exact iha h.2 hm
  | lam _ _ _ iht ihb | forallE _ _ _ iht ihb =>
    intro h hm
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · exact iht h.1 hm
    · exact ihb h.2 hm
  | letE _ _ _ _ iht ihv ihb =>
    intro h hm
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with (hm | hm) | hm
    · exact iht h.1.1 hm
    · exact ihv h.1.2 hm
    · exact ihb h.2 hm
  | proj s _ _ ihe =>
    intro h hm
    simp only [Expr.renameConsts, Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.mentionsConst, Bool.or_eq_true] at hm
    rcases hm with hm | hm
    · have hs : s = k := by simpa using hm
      subst hs
      exact Or.inr h.1
    · exact ihe h.2 hm

/-- **What the aliases installed so far give**, for the members `done` whose aliases are
`as` with table `tbl`: the prefix's constants are still found; each alias is stored and its key
is sent to the member's model; a key the prefix stores is not moved. -/
structure AliasStage (env : Env .anon) (g : KKey → KKey) (done : List KKey)
    (as : List (ConstantInfo .anon)) (tbl : List (KKey × KKey)) : Prop where
  find : ∀ (k : KKey) (c : ConstantInfo .anon), env.find? k = some c →
    (⟨as ++ env.consts⟩ : Env .anon).find? k = some c
  stored : ∀ k ∈ done,
    ((⟨as ++ env.consts⟩ : Env .anon).find? (auxKey k .model)).isSome = true
  target : ∀ k ∈ done, aliasMap tbl (auxKey k .model) = g k
  fixed : ∀ k, (env.find? k).isSome = true → aliasMap tbl k = k

/-- Before any alias is installed. -/
theorem AliasStage.start (env : Env .anon) (g : KKey → KKey) : AliasStage env g [] [] [] where
  find := fun _ _ hc => hc
  stored := fun _ hk => nomatch hk
  target := fun _ hk => nomatch hk
  fixed := fun _ _ => rfl

theorem auxKey_model_ne {k m : KKey} (h : k ≠ m) : auxKey k .model ≠ auxKey m .model :=
  fun heq => h (Key.aux.inj (heq : Key.aux k Derived.model = Key.aux m Derived.model)).1

/-- **The members' model aliases are admissible** (`AliasesReady`), from the members' facts, the
scope of their annotated types and the names. `done` are the members whose aliases are
installed; `ms` those still to come. -/
theorem aliasesReady_of_scope {env : Env .anon} {g : KKey → KKey} {bn : List KKey}
    (hwf : EnvWF env)
    (hout : ∀ k, bn.contains k = false → g k = k)
    (hnew : ∀ k, bn.contains k = true → env.find? (auxKey k .model) = none) :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (done : List KKey)
      (as : List (ConstantInfo .anon)) (tbl : List (KKey × KKey)),
      MembersFacts env g ms tys →
      typesScopedB (ms.map (·.name)) tys = true →
      (ms.map (·.name)).Nodup →
      (∀ k, bn.contains k = true → k ∈ done ∨ k ∈ ms.map (·.name)) →
      (∀ k ∈ ms.map (·.name), bn.contains k = true) →
      (∀ k ∈ done, k ∉ ms.map (·.name)) →
      AliasStage env g done as tbl →
      (∀ k ∈ ms.map (·.name),
        (⟨as ++ env.consts⟩ : Env .anon).find? (auxKey k .model) = none) →
      AliasesReady env g bn ms tys as tbl
  | [], [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | ci :: rest, tyA :: tys, done, as, tbl, hm, hsc, hnd, hS, hbn, hD, hst, hJ => by
    obtain ⟨hF, hrestF⟩ := hm
    obtain ⟨hperm, hclosed, hbnd, hann, ⟨cvm, mval₀, hint₀, hfm, hlm, htm⟩, hmt⟩ := hF
    have hsc0 : ((ci.name :: rest.map (·.name)).all (fun k => !tyA.mentionsConst k) &&
        typesScopedB (rest.map (·.name)) tys) = true := hsc
    simp only [Bool.and_eq_true] at hsc0
    obtain ⟨hsc1, hsc2⟩ := hsc0
    obtain ⟨hhead, hndrest⟩ := List.nodup_cons.mp hnd
    -- a member a type names is one whose alias is installed
    have hdone : ∀ k, tyA.mentionsConst k = true → bn.contains k = true → k ∈ done := by
      intro k hmk hb
      rcases hS k hb with hd | hin
      · exact hd
      · have hno := List.all_eq_true.mp hsc1 k hin
        simp [hmk] at hno
    -- the renamed type resolves in the prefix: it is the stored model's type
    have hcw := hwf _ (List.mem_of_find?_eq_some hfm)
    have hmres : (tyA.renameConsts g).constsResolve env = true := by
      have h1 : cvm.type.constsResolve env = true := hcw.2.2.1
      rw [htm, constsResolve_posOf] at h1
      exact h1
    have hmono : ∀ k, (env.find? k).isSome = true →
        ((⟨as ++ env.consts⟩ : Env .anon).find? k).isSome = true := by
      intro k hk
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hk
      rw [hst.find k c hc]
      rfl
    have hres : (tyA.renameConsts (blockRen bn)).constsResolve
        (⟨as ++ env.consts⟩ : Env .anon) = true :=
      constsResolve_transfer hmono tyA (fun k hmk hgk => by
        cases hb : bn.contains k with
        | true =>
          have hk : blockRen bn k = auxKey k .model := ite_eq_left hb
          rw [hk]
          exact hst.stored k (hdone k hmk hb)
        | false =>
          have hk : blockRen bn k = k := ite_eq_right (by rw [hb]; exact Bool.false_ne_true)
          rw [hk]
          rw [hout k hb] at hgk
          exact hmono k hgk) hmres
    have hcomp : (tyA.renameConsts (blockRen bn)).renameConsts (aliasMap tbl) =
        tyA.renameConsts g := by
      rw [renameConsts_comp]
      exact renameConsts_congr_mentions tyA (fun k hmk => by
        show aliasMap tbl (blockRen bn k) = g k
        cases hb : bn.contains k with
        | true =>
          have hk : blockRen bn k = auxKey k .model := ite_eq_left hb
          rw [hk]
          exact hst.target k (hdone k hmk hb)
        | false =>
          have hk : blockRen bn k = k := ite_eq_right (by rw [hb]; exact Bool.false_ne_true)
          rw [hk, hout k hb]
          rcases stored_of_mentions tyA hmres hmk with hs | hs
          · rw [hout k hb] at hs
            exact hst.fixed k hs
          · exact hst.fixed k hs)
    -- the stage after this member's alias
    have hfr : (⟨as ++ env.consts⟩ : Env .anon).find? (modelAlias g bn ci tyA).name = none :=
      hJ ci.name List.mem_cons_self
    have hbci : bn.contains ci.name = true := hbn ci.name List.mem_cons_self
    have hst' : AliasStage env g (ci.name :: done) (modelAlias g bn ci tyA :: as)
        ((auxKey ci.toConstantVal.name .model, g ci.toConstantVal.name) :: tbl) :=
      { find := fun k c hc => Ix.Kernel.Env.find?_cons_of_fresh hfr (hst.find k c hc)
        stored := fun k hk => by
          rcases List.mem_cons.mp hk with hk | hk
          · subst hk
            have hself := Ix.Kernel.Env.find?_cons_self (modelAlias g bn ci tyA)
              (⟨as ++ env.consts⟩ : Env .anon)
            exact Option.isSome_iff_exists.mpr ⟨_, hself⟩
          · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hst.stored k hk)
            exact Option.isSome_iff_exists.mpr
              ⟨c, Ix.Kernel.Env.find?_cons_of_fresh hfr hc⟩
        target := fun k hk => by
          rcases List.mem_cons.mp hk with hk | hk
          · subst hk
            exact ite_eq_left rfl
          · have hne : k ≠ ci.name := fun heq =>
              hD k hk (by rw [heq]; exact List.mem_cons_self)
            exact (ite_eq_right (auxKey_model_ne hne)).trans (hst.target k hk)
        fixed := fun k hk => by
          have hne : ¬ k = auxKey ci.name .model := fun heq => by
            have hk' := hk
            rw [heq, hnew ci.name hbci] at hk'
            exact absurd hk' (by simp)
          exact (ite_eq_right hne).trans (hst.fixed k hk) }
    have hJ' : ∀ k ∈ rest.map (·.name),
        (⟨modelAlias g bn ci tyA :: as ++ env.consts⟩ : Env .anon).find? (auxKey k .model)
          = none := by
      intro k hk
      have hne : (modelAlias g bn ci tyA).name ≠ auxKey k .model :=
        auxKey_model_ne (fun heq => by
          subst heq
          exact hhead hk)
      exact (Ix.Kernel.EnvExt.find?_cons_ne (env := (⟨as ++ env.consts⟩ : Env .anon)) hne).trans
        (hJ k (List.mem_cons_of_mem _ hk))
    have hS' : ∀ k, bn.contains k = true → k ∈ ci.name :: done ∨ k ∈ rest.map (·.name) := by
      intro k hb
      rcases hS k hb with hd | hin
      · exact Or.inl (List.mem_cons_of_mem _ hd)
      · rcases List.mem_cons.mp hin with hk | hk
        · subst hk
          exact Or.inl List.mem_cons_self
        · exact Or.inr hk
    have hD' : ∀ k ∈ ci.name :: done, k ∉ rest.map (·.name) := by
      intro k hk hin
      rcases List.mem_cons.mp hk with hk | hk
      · subst hk
        exact hhead hin
      · exact hD k hk (List.mem_cons_of_mem _ hin)
    exact ⟨hJ ci.name List.mem_cons_self, hst.find, hres, hcomp,
      aliasesReady_of_scope hwf hout hnew rest tys (ci.name :: done) _ _ hrestF hsc2 hndrest
        hS' (fun k hk => hbn k (List.mem_cons_of_mem _ hk)) hD' hst' hJ'⟩

end IxVM.Refinement.Decl.FamilyAlias
