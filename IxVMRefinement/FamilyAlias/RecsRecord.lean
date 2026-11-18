import IxVMRefinement.FamilyAlias.RuleRecordOf

/-! # The recursors of a family, installed with their rules

IxC's renamed record installs each recursor of a family with its checked rules over the
environment `envSelf` where the recursors are stored without rules (`IndRecsFoldRenRunJ`). This
module gives that fold from the rules' facts with their aliases (`RecsAliased`):

* `RuleRecordEnv`: what the rules' records need of the family and of the environments, as one
  condition (`iotaRuleRenRunJ_of_aliased`'s hypotheses that are not about a rule);
* `iotaRulesRenRunJ_of_aliased`: the rules of one recursor, each stored as declared;
* `indRecsFoldRenRunJ_of_aliased`: the recursors, each found after the fold as a recursor that
  stores its reading (`StoredAs`), every other key left as it was.

`AliasGroup.aliasEnv` and `AliasGroup.envExt` read off an alias group that the environment with
the aliases stores the aliases its renaming moves, and extends the prefix. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam EnvWF EnvExt
  auxKey)
open Ix.Kernel.Rules (Annot)

set_option linter.unusedVariables false

/-! ## An alias group, without a model -/

/-- The renaming of an alias group moves stored aliases only. -/
theorem AliasGroup.aliasEnv {env : Env .anon} {h : KKey → KKey} {as : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) : AliasEnv ⟨as ++ env.consts⟩ h := by
  induction hg with
  | nil hid => exact fun k hk => absurd (hid k) hk
  | cons _ hperm hfresh _ hsrc hlps _ _ _ _ _ hk' hrest ih =>
    exact aliasEnv_cons ih hperm hfresh hsrc hlps hk' hrest

/-- The environment with an alias group extends the prefix. -/
theorem AliasGroup.envExt {env : Env .anon} {h : KKey → KKey} {as : List (ConstantInfo .anon)}
    (hg : AliasGroup env h as) : EnvExt env ⟨as ++ env.consts⟩ := by
  induction hg with
  | nil _ => exact EnvExt.refl env
  | cons _ _ hfresh hnpt _ _ _ _ _ _ _ _ _ ih =>
    exact ih.trans (envExt_cons_fresh hfresh hnpt)

/-! ## What the rules' records need -/

/-- **What the rules' records need of the family and of the environments** (the hypotheses of
`iotaRuleRenRunJ_of_aliased` that are not about a rule). `env` is the prefix, `E` the prefix with
the aliases, `envM` the environment after the types and constructors, `envSelf` the one after
the recursors without rules. -/
structure RuleRecordEnv (env E envM envSelf : Env .anon) (g h : KKey → KKey)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) (bn : List KKey) : Prop where
  wf : EnvWF env
  store : Ix.Kernel.Open.StoreInv env
  out : ∀ k, bn.contains k = false → g k = k
  moves : ∀ k, bn.contains k = true → g k ≠ k
  target : ∀ k, bn.contains k = true → h (auxKey k .model) = g k
  fixes : ∀ k, (env.find? k).isSome = true → h k = k
  members : ∀ ci ∈ blk, bn.contains ci.name = true
  ctor : ∀ k cvj cnP cnF, RuleCtor env blk tys k cvj cnP cnF →
    envM.find? k = some (.ctorInfo cvj cnP cnF) ∧
      (cvj.type.renameConsts g).constsResolve env = true
  iotaFound : ∀ k j c, E.find? (iotaKey k j) = some c → envM.find? (iotaKey k j) = some c
  ext : EnvExt env envSelf
  aliasEnv : AliasEnv envSelf h
  stored : ∀ k, (env.find? (g k)).isSome = true → (envSelf.find? k).isSome = true

/-! ## The rules of a recursor -/

/-- **The rules of a recursor**, from their facts with their aliases, each stored as declared. -/
theorem iotaRulesRenRunJ_of_aliased {env E envM envSelf : Env .anon} {g h : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr} {bn : List KKey} {recKey : KKey}
    {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    (hR : RuleRecordEnv env E envM envSelf g h blk tys bn)
    (hperm : lps.Perm (List.range lps.length)) (hrecbn : bn.contains recKey = true)
    (htyF : tyA.hasFvar = false) (htyB : tyA.looseBVarsBounded 0 = true)
    (htyL : tyA.allLevelParamsDefined lps = true)
    (htyR : (tyA.renameConsts g).constsResolve env = true) :
    ∀ (rules : List (RecRule .anon)) (rhss : List KExpr) (thms : List KKey) (j : Nat),
      RulesAliased env E g blk tys bn recKey lps tyA mI rP j rules rhss thms →
      ∃ rules', IotaRulesRenRunJ (famJ h) envM envSelf (blockRen bn) recKey lps tyA mI rP j
          rules rules' ∧ List.Forall₂ IxVM.Consistency.RuleStored rules' rules ∧
          List.Forall₂ (fun (r' : RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss
  | [], [], [], _, _ => ⟨[], rfl, List.Forall₂.nil, List.Forall₂.nil⟩
  | [], [], _ :: _, _, ha => nomatch ha
  | [], _ :: _, _, _, ha => nomatch ha
  | _ :: _, [], _, _, ha => nomatch ha
  | _ :: _, _ :: _, [], _, ha => nomatch ha
  | r :: rs, rhsA :: rhss, thm :: thms, j, ha => by
    obtain ⟨hr, hrest⟩ := ha
    have hiota : envM.find? (iotaKey recKey j) = E.find? (iotaKey recKey j) := by
      obtain ⟨_, _, _, _, _, _, _, _, hfind⟩ := hr
      exact (hR.iotaFound _ _ _ hfind).trans hfind.symm
    obtain ⟨r', hrec, hst, hrhs⟩ := iotaRuleRenRunJ_of_aliased hr hR.wf hR.store hperm hR.out hR.moves
      hR.target hR.fixes hrecbn hR.members htyF htyB htyL htyR (hR.ctor r.ctor) hiota hR.ext
      hR.aliasEnv hR.stored
    obtain ⟨rest', hrecs, hsts, hrhss⟩ := iotaRulesRenRunJ_of_aliased hR hperm hrecbn htyF htyB htyL
      htyR rs rhss thms (j + 1) hrest
    exact ⟨r' :: rest', ⟨r', rest', hrec, hrecs, rfl⟩, List.Forall₂.cons hst hsts,
      List.Forall₂.cons hrhs hrhss⟩

/-! ## The recursors of a family -/

theorem RecsAliased.cons_inv {env E : Env .anon} {g : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr} {bn : List KKey}
    {tysR : List KExpr} {rhsss : List (List KExpr)} {thss : List (List KKey)}
    {c : ConstantInfo .anon} {rest : List (ConstantInfo .anon)}
    (h : RecsAliased env E g blk tys bn (c :: rest) tysR rhsss thss) :
    ∃ cv mI rP rules tyA tysR' rhss rhsss' ths thss',
      c = .recInfo cv mI rP rules ∧ tysR = tyA :: tysR' ∧ rhsss = rhss :: rhsss' ∧
      thss = ths :: thss' ∧
      RulesAliased env E g blk tys bn cv.name cv.levelParams tyA mI rP 0 rules rhss ths ∧
      RecsAliased env E g blk tys bn rest tysR' rhsss' thss' := by
  cases c <;> cases tysR <;> cases rhsss <;> cases thss <;>
    first
      | exact False.elim h
      | (obtain ⟨h1, h2⟩ := h
         exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, h1, h2⟩)

/-- **A member's annotated type is closed, bounded and in its level parameters.** -/
theorem MemberFacts.annotated_scope {env : Env .anon} {g : KKey → KKey}
    {ci : ConstantInfo .anon} {tyA : KExpr} (hF : MemberFacts env g ci tyA) (hwf : EnvWF env) :
    tyA.hasFvar = false ∧ tyA.looseBVarsBounded 0 = true ∧
      tyA.allLevelParamsDefined ci.toConstantVal.levelParams = true := by
  have hann : Annot 0 ci.toConstantVal.type tyA :=
    annot_of_annotates hF.annotated hF.closed hF.bounded 0
  obtain ⟨htyF, htyB⟩ := (judgeFrames_posRulesJ env).annot_syntax hann hF.closed hF.bounded
  obtain ⟨cvm, mval₀, hint₀, hfm, hlm, htm⟩ := hF.model
  have hcw := hwf _ (List.mem_of_find?_eq_some hfm)
  have h1 : cvm.type.allLevelParamsDefined cvm.levelParams = true := hcw.2.1
  rw [htm, hlm] at h1
  have h2 := allLevelParamsDefined_of_posOf_perm hF.perm h1
  rw [allLevelParamsDefined_renameConsts] at h2
  exact ⟨htyF, htyB, h2⟩

/-- **The recursors of a family, installed with their rules**, from the rules' facts with their
aliases: each recursor is found after the fold as a recursor that stores its reading, and every
other key is found as before. -/
theorem indRecsFoldRenRunJ_of_aliased {env E envM envSelf : Env .anon} {g h : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr} {bn : List KKey}
    (hR : RuleRecordEnv env E envM envSelf g h blk tys bn) :
    ∀ (recs : List (ConstantInfo .anon)) (tysR : List KExpr) (rhsss : List (List KExpr))
      (thss : List (List KKey)) (acc : Env .anon),
      RecsAliased env E g blk tys bn recs tysR rhsss thss → MembersFacts env g recs tysR →
      (∀ ci ∈ recs, bn.contains ci.name = true) → (recs.map (·.name)).Nodup →
      ∃ out, IndRecsFoldRenRunJ (famJ h) bn envM envSelf acc (provisioned recs tysR) out ∧
        (∀ k, k ∉ recs.map (·.name) → out.find? k = acc.find? k) ∧
        (∀ ci ∈ recs, ∃ c, out.find? ci.name = some c ∧ IxVM.Consistency.StoredAs c ci) ∧
        (∀ (i : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon))
          (tyA : KExpr) (rhss : List KExpr),
          recs[i]? = some (.recInfo cv mI rP rules) → tysR[i]? = some tyA → rhsss[i]? = some rhss →
          ∃ rules' : List (RecRule .anon),
            out.find? cv.name = some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') ∧
            List.Forall₂ IxVM.Consistency.RuleStored rules' rules ∧
            List.Forall₂ (fun (r' : RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss) := by
  intro recs
  induction recs with
  | nil =>
    intro tysR rhsss thss acc ha _ _ _
    have hnil : tysR = [] := by
      cases tysR with
      | nil => rfl
      | cons _ _ => cases rhsss <;> cases thss <;> exact False.elim ha
    subst hnil
    exact ⟨acc, rfl, fun _ _ => rfl, (fun _ hci => nomatch hci),
      fun i _ _ _ _ _ _ hi => by simp at hi⟩
  | cons c rest ih =>
    intro tysR rhsss thss acc ha hmf hbn hnd
    obtain ⟨cv, mI, rP, rules, tyA, tysR', rhss, rhsss', ths, thss', rfl, rfl, rfl, rfl, hra,
      hrest⟩ := RecsAliased.cons_inv ha
    obtain ⟨hMF, hmfrest⟩ := hmf
    obtain ⟨hhead, hndrest⟩ := List.nodup_cons.mp hnd
    obtain ⟨htyF, htyB, htyL⟩ := hMF.annotated_scope hR.wf
    obtain ⟨rules', hrules, hst, hrhs⟩ := iotaRulesRenRunJ_of_aliased hR hMF.perm
      (hbn _ List.mem_cons_self) htyF htyB htyL (hMF.renamed_resolves hR.wf) rules rhss ths 0 hra
    obtain ⟨out, hfold, hkeep, hstored, hstoredF⟩ := ih tysR' rhsss' thss'
      ⟨.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules' :: acc.consts⟩ hrest hmfrest
      (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci)) hndrest
    refine ⟨out, ⟨rules', hrules, hfold⟩, ?_, ?_, ?_⟩
    · intro k hk
      have hk1 : k ∉ rest.map (·.name) := fun h => hk (List.mem_cons_of_mem _ h)
      have hne : (ConstantInfo.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules' :
          ConstantInfo .anon).name ≠ k := fun h => hk (by rw [← h]; exact List.mem_cons_self)
      exact (hkeep k hk1).trans (EnvExt.find?_cons_ne (env := acc) hne)
    · intro ci hci
      rcases List.mem_cons.mp hci with rfl | hci
      · refine ⟨_, (hkeep _ hhead).trans (Ix.Kernel.Env.find?_cons_self _ acc), ?_⟩
        exact ⟨⟨rfl, rfl, hMF.annotated⟩, rfl, rfl, hst⟩
      · exact hstored ci hci
    · intro i cv' mI' rP' rls' tyA' rhss'' hi hti hri
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi hti hri
        injection hi with e1 e2 e3 e4
        subst e1 e2 e3 e4 hti hri
        exact ⟨rules', (hkeep _ hhead).trans (Ix.Kernel.Env.find?_cons_self _ acc), hst, hrhs⟩
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi hti hri
        exact hstoredF i cv' mI' rP' rls' tyA' rhss'' hi hti hri

end IxVM.Refinement.Decl.FamilyAlias
