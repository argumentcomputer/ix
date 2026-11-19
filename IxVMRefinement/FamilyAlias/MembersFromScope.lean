import IxVMRefinement.FamilyAlias.RecursorsProvisioned
import IxVMRefinement.FamilyAlias.AliasesFromScope

/-! # The members of a family are admissible, from the scope of their types

`MembersReady` (`FamilyAlias/MembersRun.lean`) is what each member of a family needs of the
environment it is stored in. This module derives it from the members' facts, the scope of their
annotated types (`typesScopedB`: a type names, of the family's members, only earlier ones) and
the names, at any environment that stores what the prefix stores, the members stored so far and
every member's model alias.

* `constsResolve_of_renamed_mentions`: resolution passes back along a renaming, key by key for
  the keys the term names.
* `membersReady_of_scope`: the derivation, by the family's order.
* `MembersReady.split`, `MembersFacts.split`, `MembersFacts.length_eq`: the conditions of a
  family listed as its types and constructors followed by its recursors are those of the two
  parts, the second at the environment the first leaves.
* `storeMembers_find_keep`, `storeMembers_find`: what the environment after the members finds:
  a constant found before under another name, and each member as the record stores it.

The renaming of the aliases enters through three facts only: it sends a member's model key to
the member's model, it fixes every key the prefix stores, and the renaming to the advice moves
members only. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel.Model
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam ReducibilityHint
  EnvExt EnvWF auxKey Derived)

set_option linter.unusedVariables false

/-! ## Resolution along a renaming, key by key -/

/-- **Resolution passes back along a renaming, key by key**: if the renamed term resolves in
`env`, the term resolves in an environment `E` that stores what `env` stores and, for each key
the term names, the key itself where `env` stores its renaming. -/
theorem constsResolve_of_renamed_mentions {env E : Env .anon} {g : KKey → KKey}
    (hmono : ∀ k, (env.find? k).isSome = true → (E.find? k).isSome = true) :
    ∀ e : KExpr,
      (∀ k, e.mentionsConst k = true → (env.find? (g k)).isSome = true →
        (E.find? k).isSome = true) →
      (e.renameConsts g).constsResolve env = true → e.constsResolve E = true := by
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

/-- **The renamed annotated type of a member resolves in the prefix**: it is, at positions, the
type of the member's stored model. -/
theorem MemberFacts.renamed_resolves {env : Env .anon} {g : KKey → KKey}
    {ci : ConstantInfo .anon} {tyA : KExpr} (hF : MemberFacts env g ci tyA) (hwf : EnvWF env) :
    (tyA.renameConsts g).constsResolve env = true := by
  obtain ⟨cvm, mval₀, hint₀, hfm, hlm, htm⟩ := hF.model
  have hcw := hwf _ (List.mem_of_find?_eq_some hfm)
  have h1 : (posOf cvm.levelParams cvm.type).constsResolve env = true := by
    rw [constsResolve_posOf]; exact hcw.2.2.1
  rw [← exprLvEq_constsResolve env htm, constsResolve_posOf] at h1
  exact h1

/-! ## The derivation -/

/-- **The members of a family are admissible** (`MembersReady`), from the members' facts, the
scope of their annotated types and the names. `done` are the members already stored in `envK`;
`ms` those still to come. `envK` stores what the prefix stores, each member of `done`, no member
of `ms`, and the model alias of each member of `ms`. -/
theorem membersReady_of_scope {env : Env .anon} {g h : KKey → KKey} {bn : List KKey}
    (hwf : EnvWF env)
    (hout : ∀ k, bn.contains k = false → g k = k)
    (htarget : ∀ k, bn.contains k = true → h (auxKey k .model) = g k)
    (hfixed : ∀ k, (env.find? k).isSome = true → h k = k) :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (done : List KKey) (envK : Env .anon),
      MembersFacts env g ms tys →
      typesScopedB (ms.map (·.name)) tys = true →
      (ms.map (·.name)).Nodup →
      (∀ k, bn.contains k = true → k ∈ done ∨ k ∈ ms.map (·.name)) →
      (∀ ci ∈ ms, isBaseKey ci.name = true ∧
        Ix.Kernel.reservedBasisNames.contains ci.name = false) →
      (∀ k, (env.find? k).isSome = true → (envK.find? k).isSome = true) →
      (∀ k ∈ done, (envK.find? k).isSome = true) →
      (∀ k ∈ ms.map (·.name), envK.find? k = none) →
      (∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr), ms[i]? = some ci →
        tys[i]? = some tyA →
        envK.find? (auxKey ci.name .model) = some (modelAlias g bn ci tyA)) →
      MembersReady g h bn envK ms tys
  | [], [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | ci :: rest, tyA :: tys, done, envK, hm, hsc, hnd, hS, hnm, hmono, hstored, hJ, hal => by
    obtain ⟨hF, hrestF⟩ := hm
    have hmres : (tyA.renameConsts g).constsResolve env = true := hF.renamed_resolves hwf
    have hsc0 : ((ci.name :: rest.map (·.name)).all (fun k => !tyA.mentionsConst k) &&
        typesScopedB (rest.map (·.name)) tys) = true := hsc
    simp only [Bool.and_eq_true] at hsc0
    obtain ⟨hsc1, hsc2⟩ := hsc0
    obtain ⟨hhead, hndrest⟩ := List.nodup_cons.mp hnd
    -- a member a type names is one that is stored
    have hdone : ∀ k, tyA.mentionsConst k = true → bn.contains k = true → k ∈ done := by
      intro k hmk hb
      rcases hS k hb with hd | hin
      · exact hd
      · have hno := List.all_eq_true.mp hsc1 k hin
        simp [hmk] at hno
    obtain ⟨hbase, hresv⟩ := hnm ci List.mem_cons_self
    have hfreshK : envK.find? ci.name = none := hJ ci.name List.mem_cons_self
    -- the two renamings compose to the renaming to the advice
    have hcomp : (tyA.renameConsts (blockRen bn)).renameConsts h = tyA.renameConsts g := by
      rw [renameConsts_comp]
      exact renameConsts_congr_mentions tyA (fun k hmk => by
        show h (blockRen bn k) = g k
        cases hb : bn.contains k with
        | true =>
          have hk : blockRen bn k = auxKey k .model := ite_eq_left hb
          rw [hk]
          exact htarget k hb
        | false =>
          have hk : blockRen bn k = k := ite_eq_right (by rw [hb]; exact Bool.false_ne_true)
          rw [hk, hout k hb]
          rcases stored_of_mentions tyA hmres hmk with hs | hs
          · rw [hout k hb] at hs
            exact hfixed k hs
          · exact hfixed k hs)
    -- the type resolves: a member it names is stored, any other key the prefix stores
    have hresolve : tyA.constsResolve envK = true :=
      constsResolve_of_renamed_mentions hmono tyA (fun k hmk hgk => by
        cases hb : bn.contains k with
        | true => exact hstored k (hdone k hmk hb)
        | false =>
          rw [hout k hb] at hgk
          exact hmono k hgk) hmres
    have halias : envK.find? (auxKey ci.name .model) = some (modelAlias g bn ci tyA) :=
      hal 0 ci tyA rfl rfl
    -- the environment after this member
    have hfresh' : envK.find? (storedMember ci tyA).name = none := by
      rw [storedMember_name]
      exact hfreshK
    have hkeep : ∀ (k : KKey) (c : ConstantInfo .anon), envK.find? k = some c →
        (⟨storedMember ci tyA :: envK.consts⟩ : Env .anon).find? k = some c :=
      fun k c hc => Ix.Kernel.Env.find?_cons_of_fresh hfresh' hc
    have hself : ((⟨storedMember ci tyA :: envK.consts⟩ : Env .anon).find? ci.name).isSome
        = true := by
      have h1 := Ix.Kernel.Env.find?_cons_self (storedMember ci tyA) envK
      rw [storedMember_name] at h1
      rw [h1]
      rfl
    have hmono' : ∀ k, (env.find? k).isSome = true →
        ((⟨storedMember ci tyA :: envK.consts⟩ : Env .anon).find? k).isSome = true := by
      intro k hk
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hmono k hk)
      rw [hkeep k c hc]
      rfl
    have hstored' : ∀ k ∈ ci.name :: done,
        ((⟨storedMember ci tyA :: envK.consts⟩ : Env .anon).find? k).isSome = true := by
      intro k hk
      rcases List.mem_cons.mp hk with hk | hk
      · rw [hk]
        exact hself
      · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (hstored k hk)
        rw [hkeep k c hc]
        rfl
    have hJ' : ∀ k ∈ rest.map (·.name),
        (⟨storedMember ci tyA :: envK.consts⟩ : Env .anon).find? k = none := by
      intro k hk
      have hne : (storedMember ci tyA).name ≠ k := by
        rw [storedMember_name]
        intro heq
        rw [← heq] at hk
        exact hhead hk
      exact (Ix.Kernel.EnvExt.find?_cons_ne (env := envK) hne).trans
        (hJ k (List.mem_cons_of_mem _ hk))
    have hS' : ∀ k, bn.contains k = true → k ∈ ci.name :: done ∨ k ∈ rest.map (·.name) := by
      intro k hb
      rcases hS k hb with hd | hin
      · exact Or.inl (List.mem_cons_of_mem _ hd)
      · rcases List.mem_cons.mp hin with hk | hk
        · rw [hk]
          exact Or.inl List.mem_cons_self
        · exact Or.inr hk
    have hrest : MembersReady g h bn ⟨storedMember ci tyA :: envK.consts⟩ rest tys :=
      membersReady_of_scope hwf hout htarget hfixed rest tys (ci.name :: done) _ hrestF hsc2
        hndrest hS' (fun c hc => hnm c (List.mem_cons_of_mem _ hc)) hmono' hstored' hJ'
        (fun i c t hc ht => hkeep _ _ (hal (i + 1) c t hc ht))
    exact ⟨hfreshK, hresv, isProjFnShape_of_isBaseKey hbase, isModelSuffix_of_isBaseKey hbase,
      fun T => ne_projTableName_of_isBaseKey hbase, hcomp, hresolve, ⟨_, _, halias⟩, hrest⟩

/-! ## A family as its types and constructors followed by its recursors -/

/-- The members' facts list one annotated type for each member. -/
theorem MembersFacts.length_eq {env : Env .anon} {g : KKey → KKey} :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr), MembersFacts env g ms tys →
      ms.length = tys.length
  | [], [], _ => rfl
  | [], _ :: _, hm => nomatch hm
  | _ :: _, [], hm => nomatch hm
  | _ :: rest, _ :: tys, hm => by
    obtain ⟨-, hrest⟩ := hm
    have hl := MembersFacts.length_eq rest tys hrest
    simp [hl]

/-- The members' facts of two lists in a row are those of each. -/
theorem MembersFacts.split {env : Env .anon} {g : KKey → KKey} :
    ∀ (ms₁ : List (ConstantInfo .anon)) (tys₁ : List KExpr) (ms₂ : List (ConstantInfo .anon))
      (tys₂ : List KExpr), ms₁.length = tys₁.length →
      MembersFacts env g (ms₁ ++ ms₂) (tys₁ ++ tys₂) →
      MembersFacts env g ms₁ tys₁ ∧ MembersFacts env g ms₂ tys₂
  | [], [], _, _, _, hm => ⟨trivial, hm⟩
  | [], _ :: _, _, _, hl, _ => absurd hl (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, _, hl, _ => absurd hl (Nat.succ_ne_zero _)
  | ci :: rest, tyA :: tys, ms₂, tys₂, hl, hm => by
    have hm' : MembersFacts env g (ci :: (rest ++ ms₂)) (tyA :: (tys ++ tys₂)) := hm
    obtain ⟨hF, hrest⟩ := hm'
    obtain ⟨ha, hb⟩ := MembersFacts.split rest tys ms₂ tys₂ (by simpa using hl) hrest
    exact ⟨⟨hF, ha⟩, hb⟩

/-- **The conditions of two lists of members in a row** are those of the first, and those of
the second at the environment the first leaves. -/
theorem MembersReady.split {g h : KKey → KKey} {bn : List KKey} :
    ∀ (ms₁ : List (ConstantInfo .anon)) (tys₁ : List KExpr) (ms₂ : List (ConstantInfo .anon))
      (tys₂ : List KExpr) (env' : Env .anon), ms₁.length = tys₁.length →
      MembersReady g h bn env' (ms₁ ++ ms₂) (tys₁ ++ tys₂) →
      MembersReady g h bn env' ms₁ tys₁ ∧
        MembersReady g h bn (storeMembers env' ms₁ tys₁) ms₂ tys₂
  | [], [], _, _, _, _, hr => ⟨trivial, hr⟩
  | [], _ :: _, _, _, _, hl, _ => absurd hl (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, _, _, hl, _ => absurd hl (Nat.succ_ne_zero _)
  | ci :: rest, tyA :: tys, ms₂, tys₂, env', hl, hr => by
    have hr' : MembersReady g h bn env' (ci :: (rest ++ ms₂)) (tyA :: (tys ++ tys₂)) := hr
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hrest⟩ := hr'
    obtain ⟨ha, hb⟩ := MembersReady.split rest tys ms₂ tys₂ _ (by simpa using hl) hrest
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, ha⟩, hb⟩

/-! ## What the environment after the members finds -/

/-- A constant found under a name that is no listed member's is found after the members are
stored. -/
theorem storeMembers_find_keep :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (env' : Env .anon) (k : KKey)
      (c : ConstantInfo .anon), env'.find? k = some c → k ∉ ms.map (·.name) →
      (storeMembers env' ms tys).find? k = some c
  | [], _, _, _, _, hf, _ => hf
  | _ :: _, [], _, _, _, hf, _ => hf
  | ci :: rest, tyA :: tys, env', k, c, hf, hk => by
    have hne : (storedMember ci tyA).name ≠ k := by
      rw [storedMember_name]
      intro heq
      exact hk (by rw [← heq]; exact List.mem_cons_self)
    have hf' : (⟨storedMember ci tyA :: env'.consts⟩ : Env .anon).find? k = some c :=
      (Ix.Kernel.EnvExt.find?_cons_ne (env := env') hne).trans hf
    exact storeMembers_find_keep rest tys _ k c hf'
      (fun hin => hk (List.mem_cons_of_mem _ hin))

/-- **Each member is found as the record stores it** after the members are stored, where their
names are distinct. -/
theorem storeMembers_find :
    ∀ (ms : List (ConstantInfo .anon)) (tys : List KExpr) (env' : Env .anon),
      (ms.map (·.name)).Nodup →
      ∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr), ms[i]? = some ci →
        tys[i]? = some tyA →
        (storeMembers env' ms tys).find? ci.name = some (storedMember ci tyA)
  | [], _, _, _, _, _, _, hc, _ => by simp at hc
  | _ :: _, [], _, _, _, _, _, _, ht => by simp at ht
  | c₀ :: rest, t₀ :: tys, env', hnd, 0, ci, tyA, hc, ht => by
    obtain ⟨hhead, -⟩ := List.nodup_cons.mp hnd
    have hc' : c₀ = ci := Option.some.inj hc
    have ht' : t₀ = tyA := Option.some.inj ht
    subst hc'
    subst ht'
    have h1 := Ix.Kernel.Env.find?_cons_self (storedMember c₀ t₀) env'
    rw [storedMember_name] at h1
    exact storeMembers_find_keep rest tys _ _ _ h1 hhead
  | c₀ :: rest, t₀ :: tys, env', hnd, i + 1, ci, tyA, hc, ht =>
    storeMembers_find rest tys ⟨storedMember c₀ t₀ :: env'.consts⟩ (List.nodup_cons.mp hnd).2 i
      ci tyA hc ht

end IxVM.Refinement.Decl.FamilyAlias
