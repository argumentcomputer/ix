import IxVMRefinement.FamilyAlias.RuleAliases

/-! # The aliases of a family's rules, as an extension of an alias group

`aliasGroup_ruleAlias` (`FamilyAlias/RuleAliases.lean`) installs one rule's alias. This module
iterates it over the rules of a recursor (`aliasGroup_rules`) and over the recursors of a
family (`aliasGroup_recs`), in the order the family check walks them.

What an extension leaves in place is stated with it, since the next alias and the record read
it: the renaming and the lookups are unchanged at every key that is no `iota` key of the
recursors walked; each new alias sits at such a key; and each rule's facts are kept together
with the rule's alias as the final environment finds it (`RuleAliased`, `RulesAliased`,
`RecsAliased`), at the data the alias was built from. -/

namespace IxVM.Refinement.Decl.FamilyAlias

open IxVM.Refinement.Core
open Ix.Kernel.Semantics
open Ix.Kernel (Env Expr Key Level ConstantInfo ConstantVal RecRule LevelParam EnvWF Derived
  auxKey)

set_option linter.unusedVariables false

/-! ## A rule with its alias -/

/-- **A rule's facts, with its alias found in `E`** at the data of the facts. -/
def RuleAliased (env E : Env .anon) (g : KKey → KKey) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) (bn : List KKey) (recKey : KKey) (lps : List LevelParam) (tyA : KExpr)
    (mI rP j : Nat) (r : RecRule .anon) (rhsA : KExpr) (thm : KKey) : Prop :=
  ∃ cvj cnP cnF lvls pins cvt vt,
    RuleWitness env g blk tys recKey lps tyA mI rP r rhsA thm cvj cnP cnF lvls pins cvt vt ∧
    E.find? (iotaKey recKey j) =
      some (ruleAlias bn recKey lps j r.ctor lvls cnF pins thm cvt.type)

/-- The rules of one recursor with their aliases, from index `j` on. -/
def RulesAliased (env E : Env .anon) (g : KKey → KKey) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) (bn : List KKey) (recKey : KKey) (lps : List LevelParam) (tyA : KExpr)
    (mI rP : Nat) : Nat → List (RecRule .anon) → List KExpr → List KKey → Prop
  | _, [], [], [] => True
  | j, r :: rs, rhsA :: rhss, thm :: thms =>
    RuleAliased env E g blk tys bn recKey lps tyA mI rP j r rhsA thm ∧
      RulesAliased env E g blk tys bn recKey lps tyA mI rP (j + 1) rs rhss thms
  | _, _, _, _ => False

/-- The recursors' rules with their aliases. -/
def RecsAliased (env E : Env .anon) (g : KKey → KKey) (blk : List (ConstantInfo .anon))
    (tys : List KExpr) (bn : List KKey) :
    List (ConstantInfo .anon) → List KExpr → List (List KExpr) → List (List KKey) → Prop
  | [], [], [], [] => True
  | .recInfo cv mI rP rules :: rest, tyA :: tysR, rhss :: rhsss, ths :: thss =>
    RulesAliased env E g blk tys bn cv.name cv.levelParams tyA mI rP 0 rules rhss ths ∧
      RecsAliased env E g blk tys bn rest tysR rhsss thss
  | _, _, _, _ => False

/-- The rules' aliases are read at the recursor's `iota` keys only. -/
theorem RulesAliased.congr {env E E' : Env .anon} {g : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr} {bn : List KKey} {recKey : KKey}
    {lps : List LevelParam} {tyA : KExpr} {mI rP : Nat}
    (hE : ∀ j, E'.find? (iotaKey recKey j) = E.find? (iotaKey recKey j)) :
    ∀ (j : Nat) (rules : List (RecRule .anon)) (rhss : List KExpr) (thms : List KKey),
      RulesAliased env E g blk tys bn recKey lps tyA mI rP j rules rhss thms →
      RulesAliased env E' g blk tys bn recKey lps tyA mI rP j rules rhss thms
  | _, [], [], [], _ => trivial
  | _, [], [], _ :: _, h => nomatch h
  | _, [], _ :: _, _, h => nomatch h
  | _, _ :: _, [], _, h => nomatch h
  | _, _ :: _, _ :: _, [], h => nomatch h
  | j, r :: rs, rhsA :: rhss, thm :: thms, h => by
    obtain ⟨⟨cvj, cnP, cnF, lvls, pins, cvt, vt, hw, hf⟩, hrest⟩ := h
    exact ⟨⟨cvj, cnP, cnF, lvls, pins, cvt, vt, hw, (hE j).trans hf⟩,
      RulesAliased.congr hE (j + 1) rs rhss thms hrest⟩

/-! ## The rules of one recursor -/

/-- **The aliases of a recursor's rules extend an alias group**, from the rules' facts.
`recKey` is the recursor (a member), `tyA` its annotated type, whose renaming to the advice
resolves in the prefix. The `iota` keys of the recursor from `j` on are fresh. -/
theorem aliasGroup_rules {env : Env .anon} {g : KKey → KKey} {blk : List (ConstantInfo .anon)}
    {tys : List KExpr} {bn : List KKey} {recKey : KKey} {lps : List LevelParam} {tyA : KExpr}
    {mI rP : Nat} (hwf : EnvWF env) (hperm : lps.Perm (List.range lps.length))
    (hout : ∀ k, bn.contains k = false → g k = k)
    (hrecbn : bn.contains recKey = true)
    (hblk : ∀ ci ∈ blk, bn.contains ci.name = true)
    (htyres : (tyA.renameConsts g).constsResolve env = true) :
    ∀ (rules : List (RecRule .anon)) (rhss : List KExpr) (thms : List KKey) (j : Nat)
      (as : List (ConstantInfo .anon)) (tbl : List (KKey × KKey)),
      RulesFacts env g blk tys recKey lps tyA mI rP rules rhss thms →
      AliasGroup env (aliasMap tbl) as →
      (∀ k, bn.contains k = true → aliasMap tbl (auxKey k .model) = g k) →
      (∀ j', j ≤ j' → (⟨as ++ env.consts⟩ : Env .anon).find? (iotaKey recKey j') = none) →
      ∃ (as' : List (ConstantInfo .anon)) (tbl' : List (KKey × KKey)),
        AliasGroup env (aliasMap tbl') as' ∧
        (∀ k, (∀ j', j ≤ j' → k ≠ iotaKey recKey j') → aliasMap tbl' k = aliasMap tbl k) ∧
        (∀ k, (∀ j', j ≤ j' → k ≠ iotaKey recKey j') →
          (⟨as' ++ env.consts⟩ : Env .anon).find? k =
            (⟨as ++ env.consts⟩ : Env .anon).find? k) ∧
        (∀ a ∈ as', a ∈ as ∨ ∃ j', a.name = iotaKey recKey j') ∧
        RulesAliased env ⟨as' ++ env.consts⟩ g blk tys bn recKey lps tyA mI rP j rules rhss thms
  | [], [], [], _, as, tbl, _, hg, _, _ =>
    ⟨as, tbl, hg, fun _ _ => rfl, fun _ _ => rfl, fun _ ha => Or.inl ha, trivial⟩
  | [], [], _ :: _, _, _, _, hf, _, _, _ => nomatch hf
  | [], _ :: _, _, _, _, _, hf, _, _, _ => nomatch hf
  | _ :: _, [], _, _, _, _, hf, _, _, _ => nomatch hf
  | _ :: _, _ :: _, [], _, _, _, hf, _, _, _ => nomatch hf
  | r :: rs, rhsA :: rhss, thm :: thms, j, as, tbl, hf, hg, htarget, hfresh => by
    obtain ⟨hF, hrestF⟩ := hf
    obtain ⟨cvj, cnP, cnF, lvls, pins, cvt, vt, hw⟩ := hF.witness
    have hg1 := aliasGroup_ruleAlias hw hwf hperm hg (hfresh j (Nat.le_refl j)) hout htarget
      hrecbn hblk (pins_renamed_resolve hw.major htyres)
    have htarget1 : ∀ k, bn.contains k = true →
        aliasMap ((iotaKey recKey j, thm) :: tbl) (auxKey k .model) = g k :=
      fun k hk =>
        (ite_eq_right (fun heq => iotaKey_ne_model recKey j k heq.symm)).trans (htarget k hk)
    have hname : ∀ j', j ≠ j' →
        (ruleAlias bn recKey lps j r.ctor lvls cnF pins thm cvt.type).name ≠ iotaKey recKey j' :=
      fun j' hjj heq => hjj (iotaKey_inj heq).2
    have hfresh1 : ∀ j', j + 1 ≤ j' →
        (⟨(ruleAlias bn recKey lps j r.ctor lvls cnF pins thm cvt.type :: as) ++ env.consts⟩ :
          Env .anon).find? (iotaKey recKey j') = none :=
      fun j' hj' =>
        (Ix.Kernel.EnvExt.find?_cons_ne (env := (⟨as ++ env.consts⟩ : Env .anon))
          (hname j' (by omega))).trans (hfresh j' (by omega))
    obtain ⟨as', tbl', hg', hmap, hfind, hnames, hrest⟩ :=
      aliasGroup_rules hwf hperm hout hrecbn hblk htyres rs rhss thms (j + 1) _ _ hrestF hg1
        htarget1 hfresh1
    refine ⟨as', tbl', hg', ?_, ?_, ?_, ⟨⟨cvj, cnP, cnF, lvls, pins, cvt, vt, hw, ?_⟩, hrest⟩⟩
    · intro k hk
      have h1 := hmap k (fun j' hj' => hk j' (by omega))
      have h2 : aliasMap ((iotaKey recKey j, thm) :: tbl) k = aliasMap tbl k :=
        ite_eq_right (hk j (Nat.le_refl j))
      exact h1.trans h2
    · intro k hk
      have h1 := hfind k (fun j' hj' => hk j' (by omega))
      have hne : (ruleAlias bn recKey lps j r.ctor lvls cnF pins thm cvt.type).name ≠ k :=
        fun heq => hk j (Nat.le_refl j) heq.symm
      exact h1.trans
        (Ix.Kernel.EnvExt.find?_cons_ne (env := (⟨as ++ env.consts⟩ : Env .anon)) hne)
    · intro a ha
      rcases hnames a ha with h1 | ⟨j', hj'⟩
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact Or.inr ⟨j, rfl⟩
        · exact Or.inl h1
      · exact Or.inr ⟨j', hj'⟩
    · have h1 := hfind (iotaKey recKey j)
        (fun j' hj' heq => absurd (iotaKey_inj heq).2 (by omega))
      exact h1.trans (Ix.Kernel.Env.find?_cons_self _ (⟨as ++ env.consts⟩ : Env .anon))

/-! ## The recursors of a family -/

theorem RecsFacts.nil_inv {env : Env .anon} {g : KKey → KKey} {blk : List (ConstantInfo .anon)}
    {tys tysR : List KExpr} {rhsss : List (List KExpr)} {thss : List (List KKey)}
    (h : RecsFacts env g blk tys [] tysR rhsss thss) : tysR = [] ∧ rhsss = [] ∧ thss = [] := by
  cases tysR <;> cases rhsss <;> cases thss <;>
    first
      | exact ⟨rfl, rfl, rfl⟩
      | exact False.elim h

theorem RecsFacts.cons_inv {env : Env .anon} {g : KKey → KKey} {blk : List (ConstantInfo .anon)}
    {tys tysR : List KExpr} {rhsss : List (List KExpr)} {thss : List (List KKey)}
    {c : ConstantInfo .anon} {rest : List (ConstantInfo .anon)}
    (h : RecsFacts env g blk tys (c :: rest) tysR rhsss thss) :
    ∃ cv mI rP rules tyA tysR' rhss rhsss' ths thss',
      c = .recInfo cv mI rP rules ∧ tysR = tyA :: tysR' ∧ rhsss = rhss :: rhsss' ∧
      thss = ths :: thss' ∧
      RulesFacts env g blk tys cv.name cv.levelParams tyA mI rP rules rhss ths ∧
      RecsFacts env g blk tys rest tysR' rhsss' thss' := by
  cases c <;> cases tysR <;> cases rhsss <;> cases thss <;>
    first
      | exact False.elim h
      | (obtain ⟨h1, h2⟩ := h
         exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, h1, h2⟩)

/-- **The aliases of a family's rules extend an alias group**, from the recursors' facts.
The recursors are members with distinct names; every `iota` key of theirs is fresh. -/
theorem aliasGroup_recs {env : Env .anon} {g : KKey → KKey} {blk : List (ConstantInfo .anon)}
    {tys : List KExpr} {bn : List KKey} (hwf : EnvWF env)
    (hout : ∀ k, bn.contains k = false → g k = k)
    (hblk : ∀ ci ∈ blk, bn.contains ci.name = true) :
    ∀ (recs : List (ConstantInfo .anon)) (tysR : List KExpr) (rhsss : List (List KExpr))
      (thss : List (List KKey)) (as : List (ConstantInfo .anon)) (tbl : List (KKey × KKey)),
      RecsFacts env g blk tys recs tysR rhsss thss → MembersFacts env g recs tysR →
      (∀ ci ∈ recs, bn.contains ci.name = true) → (recs.map (·.name)).Nodup →
      AliasGroup env (aliasMap tbl) as →
      (∀ k, bn.contains k = true → aliasMap tbl (auxKey k .model) = g k) →
      (∀ ci ∈ recs, ∀ j,
        (⟨as ++ env.consts⟩ : Env .anon).find? (iotaKey ci.name j) = none) →
      ∃ (as' : List (ConstantInfo .anon)) (tbl' : List (KKey × KKey)),
        AliasGroup env (aliasMap tbl') as' ∧
        (∀ k, (∀ ci ∈ recs, ∀ j, k ≠ iotaKey ci.name j) → aliasMap tbl' k = aliasMap tbl k) ∧
        (∀ k, (∀ ci ∈ recs, ∀ j, k ≠ iotaKey ci.name j) →
          (⟨as' ++ env.consts⟩ : Env .anon).find? k =
            (⟨as ++ env.consts⟩ : Env .anon).find? k) ∧
        (∀ a ∈ as', a ∈ as ∨ ∃ ci ∈ recs, ∃ j, a.name = iotaKey ci.name j) ∧
        RecsAliased env ⟨as' ++ env.consts⟩ g blk tys bn recs tysR rhsss thss := by
  intro recs
  induction recs with
  | nil =>
    intro tysR rhsss thss as tbl hf _ _ _ hg _ _
    obtain ⟨rfl, rfl, rfl⟩ := RecsFacts.nil_inv hf
    exact ⟨as, tbl, hg, fun _ _ => rfl, fun _ _ => rfl, fun _ ha => Or.inl ha, trivial⟩
  | cons c rest ih =>
    intro tysR rhsss thss as tbl hf hmf hbn hnd hg htarget hfresh
    obtain ⟨cv, mI, rP, rules, tyA, tysR', rhss, rhsss', ths, thss', rfl, rfl, rfl, rfl, hrf,
      hrestF⟩ := RecsFacts.cons_inv hf
    obtain ⟨hMF, hmfrest⟩ := hmf
    obtain ⟨hhead, hndrest⟩ := List.nodup_cons.mp hnd
    have hcvbn : bn.contains cv.name = true := hbn _ List.mem_cons_self
    obtain ⟨as₁, tbl₁, hg₁, hmap₁, hfind₁, hnames₁, hrules₁⟩ :=
      aliasGroup_rules hwf hMF.perm hout hcvbn hblk (hMF.renamed_resolves hwf) rules rhss ths 0
        as tbl hrf hg htarget (fun j' _ => hfresh _ List.mem_cons_self j')
    -- another recursor's `iota` keys are not this one's
    have hother : ∀ ci ∈ rest, ∀ j j', iotaKey ci.name j ≠ iotaKey cv.name j' := by
      intro ci hci j j' heq
      have h1 : ci.name = cv.name := (iotaKey_inj heq).1
      have h2 : cv.name ∈ rest.map (·.name) := by
        rw [← h1]
        exact List.mem_map.mpr ⟨ci, hci, rfl⟩
      exact hhead h2
    obtain ⟨as₂, tbl₂, hg₂, hmap₂, hfind₂, hnames₂, hrecs₂⟩ :=
      ih tysR' rhsss' thss' as₁ tbl₁ hrestF hmfrest
        (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci)) hndrest hg₁
        (fun k hk =>
          (hmap₁ (auxKey k .model)
            (fun j' _ heq => iotaKey_ne_model cv.name j' k heq.symm)).trans (htarget k hk))
        (fun ci hci j =>
          (hfind₁ (iotaKey ci.name j) (fun j' _ => hother ci hci j j')).trans
            (hfresh ci (List.mem_cons_of_mem _ hci) j))
    refine ⟨as₂, tbl₂, hg₂, ?_, ?_, ?_, ⟨?_, hrecs₂⟩⟩
    · intro k hk
      exact (hmap₂ k (fun ci hci j => hk ci (List.mem_cons_of_mem _ hci) j)).trans
        (hmap₁ k (fun j' _ => hk _ List.mem_cons_self j'))
    · intro k hk
      exact (hfind₂ k (fun ci hci j => hk ci (List.mem_cons_of_mem _ hci) j)).trans
        (hfind₁ k (fun j' _ => hk _ List.mem_cons_self j'))
    · intro a ha
      rcases hnames₂ a ha with h1 | ⟨ci, hci, j, hj⟩
      · rcases hnames₁ a h1 with h2 | ⟨j, hj⟩
        · exact Or.inl h2
        · exact Or.inr ⟨_, List.mem_cons_self, j, hj⟩
      · exact Or.inr ⟨ci, List.mem_cons_of_mem _ hci, j, hj⟩
    · exact RulesAliased.congr
        (fun j => hfind₂ (iotaKey cv.name j)
          (fun ci hci j' heq => hother ci hci j' j heq.symm)) 0 rules rhss ths hrules₁

end IxVM.Refinement.Decl.FamilyAlias
