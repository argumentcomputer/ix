module

public import IxC.Kernel.Semantics.Inductives.DeclNativeRecLateExtJ
public import IxC.Kernel.Model.StoreRecShape
public import IxC.Kernel.Model.JudgeRules

public section

/-!
# A recursor for a stored native family: the store facts, model-free

The late recursor's step (`DeclNativeRecLateRunJ`) conses one recursor with its generated rules
at an environment that stores the family. It keeps every store fact the declaration steps keep
(`Model/StoreFold.lean`, `Model/StoreCompanions.lean`, `Model/StoreRecShape.lean`):

* `StoreInv` (`storeInv_declNativeRecLateRunJ`): the recursor's cons is well formed, and each
  generated rule is canonical, at a stored constructor, its two rescue bits the store's verdict;
* the new recursor's `RecAt` facts (`nativeRecLate_recShape_new`) and K facts
  (`nativeRecLate_recK_new`): its major premise is the generated one, each rule is at one of the
  family's constructors, and a K rule is the only rule, since the family's capability record is
  its own (`nativeCaps`) and grants K only to a one-constructor family;
* the step stores a recursor and nothing else (`nativeRecLate_newSat`), so it stores no
  theorem, no η family and no table.

The proofs are the recursor-cons part of the native route's (`storeInv_declNativeRunJ`,
`native_recShape_new`, `native_recK_new`), with the family's lookups read off the relation
(`NativeFamStored`) instead of the install's front. `storeFacts_declNativeRecLateRunJ` collects
the six facts at the derivation package.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel (Env Key Expr ConstantInfo ConstantVal RecRule NativeParts)

/-- **The late recursor's step stores a recursor.** -/
theorem nativeRecLate_newSat {J : Judgements md} {env env₂ : Env md} {fam : NativeFam md}
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    {Q : ConstantInfo md → Prop} (hQ : ∀ cv a b rs, Q (.recInfo cv a b rs))
    (h : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) : NewSat env env₂ Q := by
  obtain ⟨_, _, _, _, _, -, -, -, -, -, -, -, -, -, rfl⟩ := h
  exact NewSat.cons (hQ _ _ _ _)

/-- **The late recursor's step keeps the store invariant**: the recursor's cons is well formed
(`NativeRecJ.recWF`), and each generated rule is canonical at its stored constructor, whose
residual is the family, with its two rescue bits the store's verdict. -/
theorem storeInv_declNativeRecLateRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {fam : NativeFam md} {cvR : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} (h : StoreInv env)
    (hrun : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) : StoreInv env₂ := by
  obtain ⟨_, _, pR, cvRa, rhss, hpR, -, -, -, -, hst, -, -, hRec, rfl⟩ := hrun
  obtain ⟨hfT, hctor, hlenA, hk⟩ := hst.atRec hpR
  have hplAll := hRec.plain ⟨fam.cvS, _, hfT⟩ hk hlenA fun c hc =>
    let ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    (hctor j c hj).2.1
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  have hfreshR : env.find? cvRa.name = none := by rw [hnR]; exact hfR
  refine ⟨hRec.recWF h.wf (hfr _).annot_syntax,
    Ix.Kernel.RecCtorsStored.cons h.rec_ctors hfreshR ?_,
    Ix.Kernel.Verify.ProjOkT.cons h.proj_ok hfreshR (fun _ heq => nomatch heq)⟩
  intro cvR' mI' rP' rules' heq r hr
  injection heq with h1 h2 h3 hrules
  subst h1 h2 h3 hrules
  obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
  obtain ⟨hfC, -, cbs, es, hres, -⟩ := hctor j cA hj
  have hpl : Expr.recRulePlain cvRa.type pR.majorIdx pR.rulePrefix pR.nP cA.1.levelParams = true :=
    List.all_eq_true.mp hplAll cA (List.mem_of_getElem? hj)
  exact ⟨Ix.Kernel.RuleCtorOk.of_plain hfC (by simp [Ix.Kernel.recRuleBits, hpl]) hpl
      (Ix.Kernel.Expr.ctorTeleOk_of hres (by rw [Ix.Kernel.Expr.getAppFn_mkAppN]; rfl)),
    fun hb => hb, fun hb => hb⟩

/-- **The late recursor's `RecAt` facts**: its major premise is the generated one, the family
applied to the parameter and index variables (`NativeRecJ.majorOf`); each rule is at one of the
family's stored constructors, whose type ends in the family, with the family's parameter count;
the rules are one per constructor; the η bits are the verdict at the environment the recursor
is consed to, which the cons keeps. -/
theorem nativeRecLate_recShape_new {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {fam : NativeFam md} {cvR : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} (h : StoreInv env)
    (hrun : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) :
    ∀ n cv mI' rP' rules', env₂.find? n = some (.recInfo cv mI' rP' rules') →
      env.find? n = none → RecAt env₂ n cv mI' rP' rules' := by
  obtain ⟨_, _, pR, cvRa, rhss, hpR, -, -, -, -, hst, -, -, hRec, henv⟩ := hrun
  obtain ⟨hfT, hctor, hlenA, hk⟩ := hst.atRec hpR
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  have hfreshR : env.find? cvRa.name = none := by rw [hnR]; exact hfR
  have hkeep : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x →
      env₂.find? k = some x := by
    intro k x hk'
    rw [henv]
    exact Ix.Kernel.Env.find?_cons_of_fresh hfreshR hk'
  obtain ⟨bs₀, B₀, m₀, hmaj⟩ := hRec.majorOf ⟨fam.cvS, _, hfT⟩ hk hlenA
  have hmr : pR.majorIdx - pR.rulePrefix = pR.nIdx :=
    Nat.add_sub_cancel_left pR.rulePrefix pR.nIdx
  intro n cv mI' rP' rules' hf hn0
  rw [henv, Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · next hnm =>
    have hn : cvRa.name = n := hnm
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
    -- each rule: one of the family's constructors, at the family's parameter count
    have hrule : ∀ r ∈ Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix
        cvRa.type fam.ctorsA rhss, ∃ (j : Nat) (cA : ConstantVal md × Nat),
          fam.ctorsA[j]? = some cA ∧ r.ctor = cA.1.name ∧ r.ctorParams = pR.nP := by
      intro r hr
      obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
      exact ⟨j, cA, hj, rfl, rfl⟩
    refine ⟨fun r hr => ?_, fun _ r hr _ => ?_, fun _ r hr cvj a b hc bs D B m hs T us hD => ?_,
      fun _ r hrs _ => ?_⟩
    · -- the η bit
      obtain ⟨j, cA, hj, hctorEq, -⟩ := hrule r hr
      obtain ⟨hfC, -, -⟩ := hctor j cA hj
      rw [(Ix.Kernel.sumRules_bits hr).2, ← hn]
      refine recRuleEtaOf_ext (cvj := cA.1) (a := pR.nP) (b := cA.2) hkeep
        (by rw [hctorEq]; exact hfC) (fun T us heq => .inl ?_)
      have hres : cA.1.type.constsResolve env = true :=
        (h.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfC)).2.2.1
      have h2 := constsResolve_getAppFn (constsResolve_piResult hres)
      rw [heq] at h2
      simpa [Ix.Kernel.Expr.constsResolve] using h2
    · -- the major premise's index arguments
      obtain ⟨_, _, -, -, hcp⟩ := hrule r hr
      refine ⟨bs₀, _, B₀, m₀, hmaj, ?_⟩
      rw [hcp, hmr]
      exact structFamI_args_drop
    · -- the constructor's family
      obtain ⟨j, cA, hj, hctorEq, -⟩ := hrule r hr
      obtain ⟨hfC, -, cbs, es, hres, -⟩ := hctor j cA hj
      have hc' := hkeep hfC
      rw [← hctorEq, hc] at hc'
      obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hc')
      rw [hmaj] at hs
      simp only [Option.some.injEq, Prod.mk.injEq, Expr.forallE.injEq] at hs
      obtain ⟨-, rfl, -, -⟩ := hs
      rw [structFamI_getAppFn] at hD
      injection hD with hT _
      subst hT
      exact ⟨_, family_of_residual hres⟩
    · -- one rule: one constructor, so the prefix is the parameters, a motive and a minor
      have hr : r ∈ Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix
          cvRa.type fam.ctorsA rhss := by rw [hrs]; exact List.mem_singleton_self r
      obtain ⟨_, _, -, -, hcp⟩ := hrule r hr
      obtain ⟨-, -, -, hlenR, -⟩ := NativeRecJ.facts (hfr _).annot_syntax hRec
      have hl := sumRules_length_of (find? := env.find?) (recName := cvRa.name) (nP := pR.nP)
        (mI := pR.majorIdx) (rP := pR.rulePrefix) (recTy := cvRa.type)
        (by rw [hlenR, Ix.Kernel.nativeCtors4_length hk])
      rw [hrs, List.length_singleton, hlenA] at hl
      rw [hcp]
      show pR.nP + 2 = pR.nP + 1 + pR.ctors.length
      omega
  · rw [hn0] at hf
    exact nomatch hf

/-- **The late recursor's K facts**: its rules' K bits are the verdict at the step's end, and a
rule with the K bit is the only one: the family is stored at its own capability record, which
grants K only to a one-constructor family. -/
theorem nativeRecLate_recK_new {J : Judgements md} (_hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {fam : NativeFam md} {cvR : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} (h : StoreInv env)
    (hrun : DeclNativeRecLateRunJ J env fam cvR mI rP rules env₂) :
    ∀ n cv mI' rP' rules', env₂.find? n = some (.recInfo cv mI' rP' rules') →
      env.find? n = none →
      (∀ r ∈ rules', r.k = Ix.Kernel.recRuleKOf env₂.find? r.ctor) ∧
      (∀ r ∈ rules', r.k = true → rules' = [r]) := by
  obtain ⟨_, _, pR, cvRa, rhss, hpR, -, -, -, -, hst, -, -, hRec, henv⟩ := hrun
  obtain ⟨hfT, hctor, -, -⟩ := hst.atRec hpR
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  have hfreshR : env.find? cvRa.name = none := by rw [hnR]; exact hfR
  -- lookups of the environment survive the recursor's cons
  have hkeep : ∀ {k : Key md} {x : ConstantInfo md}, env.find? k = some x →
      env₂.find? k = some x := by
    intro k x hk'
    rw [henv]
    exact Ix.Kernel.Env.find?_cons_of_fresh hfreshR hk'
  intro n cv mI' rP' rules' hf hn0
  rw [henv, Ix.Kernel.Env.find?_cons] at hf
  split at hf
  · obtain ⟨-, -, -, hrules⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
    subst hrules
    -- each rule: the constructor's verdict at the environment the recursor is consed to
    have hrule : ∀ r ∈ Ix.Kernel.sumRules env.find? cvRa.name pR.nP pR.majorIdx pR.rulePrefix
        cvRa.type fam.ctorsA rhss, ∃ (j : Nat) (cA : ConstantVal md × Nat),
          fam.ctorsA[j]? = some cA ∧ r.ctor = cA.1.name ∧
          r.k = Ix.Kernel.recRuleKOf env.find? r.ctor := by
      intro r hr
      obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
      exact ⟨j, cA, hj, rfl, (Ix.Kernel.sumRules_bits hr).1⟩
    refine ⟨fun r hr => ?_, fun r hr hk => ?_⟩
    · obtain ⟨j, cA, hj, hctorEq, hk⟩ := hrule r hr
      obtain ⟨hfC, -, -⟩ := hctor j cA hj
      rw [hk]
      refine recRuleKOf_ext (cvj := cA.1) (a := pR.nP) (b := cA.2) hkeep
        (by rw [hctorEq]; exact hfC) (fun T us heq => .inl ?_)
      have hres : cA.1.type.constsResolve env = true :=
        (h.wf _ (Ix.Kernel.Semantics.Env.find?_mem hfC)).2.2.1
      have h2 := constsResolve_getAppFn (constsResolve_piResult hres)
      rw [heq] at h2
      simpa [Ix.Kernel.Expr.constsResolve] using h2
    · obtain ⟨j, cA, hj, hctorEq, hk'⟩ := hrule r hr
      obtain ⟨hfC, -, cbs, es, hres, -⟩ := hctor j cA hj
      rw [hk] at hk'
      obtain ⟨cvj, cnP, T, us, cvT, caps, hcj, hhead, hfT', hK⟩ :=
        Ix.Kernel.recRuleKOf_inv hk'.symm
      rw [hctorEq, hfC] at hcj
      obtain ⟨rfl, -, -⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hcj)
      rw [family_of_residual hres] at hhead
      injection hhead with hTe _
      subst hTe
      -- the family's capability record is the summary's own
      rw [hfT] at hfT'
      obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfT')
      obtain ⟨c, hc⟩ := nativeCapsAt_ruleK hK
      have hlen : fam.ctorsA.length ≤ 1 := by
        rw [hst.lenA]
        have hc' : fam.p.ctors = [c] := hc
        simp [hc']
      exact eq_singleton_of_length_le_one (Nat.le_trans sumRules_length_le hlen) hr
  · rw [hn0] at hf
    exact nomatch hf

/-- **The late recursor's step keeps the six store facts**, at the derivation package: the store
invariant, the recursors' shape and K facts (the new recursor's from the two lemmas above), the
typed theorems, the η towers and the tables' bodies (the step stores none of them). -/
theorem storeFacts_declNativeRecLateRunJ {env env₂ : Env md} {fam : NativeFam md}
    {cvR : ConstantVal md} {mI rP : Nat} {rules : List (RecRule md)}
    (hrun : DeclNativeRecLateRunJ rulesJ env fam cvR mI rP rules env₂)
    (hS : StoreInv env) (hR : RecShape env) (hK : RecK env) (hT : ThmTyped env)
    (hE : EtaTowers env) (hB : TableBodies env) :
    StoreInv env₂ ∧ RecShape env₂ ∧ RecK env₂ ∧ ThmTyped env₂ ∧ EtaTowers env₂ ∧
      TableBodies env₂ := by
  have hext := declNativeRecLateRunJ_envExt hrun
  refine ⟨storeInv_declNativeRecLateRunJ judgeFrames_rulesJ hS hrun,
    recShape_step hS hR hext.find (nativeRecLate_recShape_new judgeFrames_rulesJ hS hrun),
    recK_step hS hK hext.find (fun n cv mI' rP' rules' hf hn => ?_),
    thmTyped_step_noThm hext hT
      (nativeRecLate_newSat (fun _ _ _ _ _ _ h => nomatch h) hrun),
    etaTowers_step_noEta hext hE
      (nativeRecLate_newSat (fun _ _ _ _ _ _ h => nomatch h) hrun),
    tableBodies_step_noProj hext.find hB
      (nativeRecLate_newSat (fun _ _ _ _ _ h => nomatch h) hrun)⟩
  obtain ⟨h1, h2⟩ := nativeRecLate_recK_new judgeFrames_rulesJ hS hrun n cv mI' rP' rules' hf hn
  exact ⟨h1, fun _ => h2⟩

end Ix.Kernel.Model
