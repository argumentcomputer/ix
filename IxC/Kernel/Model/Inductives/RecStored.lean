module

public import IxC.Kernel.Model.Inductives.WrapModel
public import IxC.Kernel.Model.Inductives.NativeJudge
public import IxC.Kernel.Semantics.Inductives.DeclNativeJ
import IxC.Kernel.Verify.Inductives.SumRec
import IxC.Kernel.Verify.Inductives.StructRec
import IxC.Kernel.Verify.InstSpine
import IxC.Kernel.Verify.EnvWF

public section

/-!
# The declared recursor, stored

The recursor stage's record (`NativeRecRunJ`) gives the model of the environment storing the
generated recursor (`stageFixRecJ`). At the record's declared form (`RecStoredJ`) the block stores
the checked declared recursor instead, with its rules; `recStoredStep` gives the model storing it,
with the same leaf, from `recDeclaredStep`, discharging that step's premises from the record:

* the declared type is accepted by the package (`ConstantValCheckJ`), so it reads, and a read
  term has no `let`; the stored rules carry none (a premise of the declared form);
* both types are recursor types (`piToBvar_structRecTyR`, moved along `WrapRel`), so a recursor
  stored at a literal-support name leaves the guards unchanged;
* each stored rule is the generated rule at its constructor with its right-hand side replaced
  (`sumRules` at the same constructors), and the generated type fires every rule (a premise of the
  declared form), so the generated laws are the ones to transport.
-/

namespace Ix.Kernel.Model
open Ix.Kernel.Semantics
open Ix.Kernel.SetModel
open Ix.Kernel.Term Ix.Kernel.Verify SetTheory
open Ix.Kernel.Semantics (AnnotTerm)
open Ix.Kernel (CheckMode Env Expr Key Level ConstantInfo ConstantVal RecRule NativeParts)

universe w

variable {V : Type w} [SetTheory V]

theorem forall₂_getElem? {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : Forall₂ R l₁ l₂) :
    ∀ {j : Nat} {b : β}, l₂[j]? = some b → ∃ a, l₁[j]? = some a ∧ R a b := by
  induction h with
  | nil => intro j b hb; simp at hb
  | @cons a b' _ _ hab _ ih =>
    intro j b hb
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
      subst hb
      exact ⟨a, rfl, hab⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hb ⊢
      exact ih hb

/-- The rule `sumRules` builds at a constructor and a right-hand side at the same position. -/
theorem sumRules_mem_of_getElem? {find? : Key md → Option (ConstantInfo md)} {recName : Key md}
    {nP mI rP : Nat} {recTy : Expr md} :
    ∀ {cs : List (ConstantVal md × Nat)} {rhss : List (Expr md)} {j : Nat}
      {c : ConstantVal md × Nat} {rhs : Expr md},
      cs[j]? = some c → rhss[j]? = some rhs →
      Ix.Kernel.recRuleBits find? recName
        { ctor := c.1.name, nfields := c.2, ctorParams := nP,
          fire := if Expr.recRulePlain recTy mI rP nP c.1.levelParams then .plain else .inert,
          rhs := rhs, paramsBlind := true }
        ∈ Ix.Kernel.sumRules find? recName nP mI rP recTy cs rhss
  | _ :: _, _ :: _, 0, _, _, hc, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr
    subst hc hr
    simp only [Ix.Kernel.sumRules]
    exact List.mem_cons_self
  | _ :: _, _ :: _, _ + 1, _, _, hc, hr => by
    simp only [List.getElem?_cons_succ] at hc hr
    simp only [Ix.Kernel.sumRules]
    exact List.mem_cons_of_mem _ (sumRules_mem_of_getElem? hc hr)
  | [], _, _, _, _, hc, _ => by simp at hc
  | _ :: _, [], _, _, _, _, hr => by simp at hr

/-- **The declared recursor, stored**: from the model storing the generated recursor (leaf `A`),
the model storing the checked declared recursor and its rules, with the same leaf. -/
theorem recStoredStep {μ : CheckMode} {J : Judgements md} {E : Env md} (mpC : EnvModelM V μ E)
    (hfr : JudgeFrames J E) (hJ : JudgeSound J mpC.base2)
    {p : NativeParts md} {cvTa cvRg cvRa : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    {rhsG rhss : List (Expr md)}
    (hRecG : NativeRecRunJ J E p cvTa ctorsA cvRg rhsG)
    (hdecl : ∃ cvRi : ConstantVal md,
      ConstantValCheckJ J E p.cvR cvRi ∧
      cvRa = ⟨p.cvR.name, p.cvR.levelParams, cvRi.type⟩ ∧
      WrapRel E.find? cvRg.type cvRi.type ∧
      Forall₂ (WrapRel E.find?) rhsG rhss ∧
      (∀ r ∈ rhss, letFree r = true) ∧
      Forall₂ (J.annot ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: E.consts⟩ 0) p.rhss
        rhss ∧
      letFree cvRi.type = true)
    (hplG : ctorsA.all (fun c => Expr.recRulePlain cvRg.type p.majorIdx p.rulePrefix p.nP
      c.1.levelParams) = true)
    (hplAll : ctorsA.all (fun c => Expr.recRulePlain cvRa.type p.majorIdx p.rulePrefix p.nP
      c.1.levelParams) = true)
    (hctor : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      E.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) ∧
        Expr.ctorTeleOk cA.1.type (p.nP + cA.2) = true)
    (mpg : EnvModelM V μ ⟨.recInfo cvRg p.majorIdx p.rulePrefix
      (Ix.Kernel.sumRules E.find? cvRg.name p.nP p.majorIdx p.rulePrefix cvRg.type ctorsA rhsG)
        :: E.consts⟩)
    {A : (LevelParam → Nat) → AnnotTerm}
    (hac : mpg.base2.acval = acvalWith mpC.base2.acval cvRg.name A) :
    ∃ mpd : EnvModelM V μ ⟨.recInfo cvRa p.majorIdx p.rulePrefix
      (Ix.Kernel.sumRules E.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: E.consts⟩,
      mpd.base2.acval = acvalWith mpC.base2.acval cvRa.name A := by
  have hstored : NativeRecJ J E p cvTa ctorsA cvRa rhss := ⟨cvRg, rhsG, hRecG, Or.inr hdecl⟩
  obtain ⟨cvRi, hccv, hcvRa, hW, hWr, hlf, -, -⟩ := hdecl
  obtain ⟨-, -, cvRi₀, recTy, sty, u, hccv₀, hgenR, -, -, -, hfvR, -, -, -, -, hcvRg⟩ := id hRecG
  have hcvRg : cvRg = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ := hcvRg
  obtain ⟨hnG, hlG, hfreshP, -⟩ := hRecG.recursor
  have hfresh : E.find? cvRg.name = none := by rw [hnG]; exact hfreshP
  have hname : cvRa.name = cvRg.name := by rw [hcvRa, hnG]
  have hlps : cvRa.levelParams = cvRg.levelParams := by rw [hcvRa, hlG]
  have hnres : Ix.Kernel.reservedBasisNames.contains cvRg.name = false := by
    obtain ⟨_, ⟨-, hres, -⟩, -⟩ := hccv₀
    rw [hnG]; exact hres
  -- the declared type reads, so it has no `let`
  obtain ⟨htf, -, -, htb⟩ := ConstantValCheckJ.typeWF hfr hccv
  have hlfT : letFree cvRa.type = true := by
    obtain ⟨type', ⟨-, -, -, -, -, -, -, -, -, sty', u', hinf, -⟩, rfl⟩ := hccv
    obtain ⟨ea, hea⟩ := hJ.accepted (fun _ => 0) hinf (Expr.WScoped.of_not_hasFvar htf) htb
      (fun l hl => absurd hl (fun h' => by
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf] at h'
        exact nomatch h'))
    rw [hcvRa]
    exact letFree_of_denoteMeta _ _ (Nat.lt_succ_self _) 0 ea hea
  have hWd : WrapRel E.find? cvRg.type cvRa.type := by rw [hcvRa]; exact hW
  -- both types are recursor types
  have hpiG : PiToBvar (p.nP + 1 + (Ix.Kernel.nativeCtors4 ctorsA p.kinds).length + p.nIdx + 1)
      cvRg.type := by rw [hcvRg]; exact piToBvar_structRecTyR hgenR
  -- the generated environment's lookups extend the checked one's
  have hfind : ∀ w ci, E.find? w = some ci →
      (⟨.recInfo cvRg p.majorIdx p.rulePrefix
        (Ix.Kernel.sumRules E.find? cvRg.name p.nP p.majorIdx p.rulePrefix cvRg.type ctorsA rhsG)
          :: E.consts⟩ : Env md).find? w = some ci :=
    fun w ci h => Ix.Kernel.Env.find?_cons_of_fresh
      (c := .recInfo cvRg p.majorIdx p.rulePrefix _) hfresh h
  have hhead : ConsHead E (.recInfo cvRa p.majorIdx p.rulePrefix
      (Ix.Kernel.sumRules E.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)) A :=
    ConsHead.ofFresh (hstored.recWF mpC.base2.wf hfr.annot_syntax)
      (fun ψ => by
        have h := mpg.base2.cval_closedL cvRg.name ψ
        rw [hac, acvalWith_self] at h
        exact h)
      (by show Ix.Kernel.reservedBasisNames.contains cvRa.name = false; rw [hname]; exact hnres)
      (fun _ h => nomatch h)
      (by
        intro cvR' mI' rP' rules heq r hr
        injection heq with h1 h2 h3 hrules
        subst h1 h2 h3 hrules
        obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
        obtain ⟨hf, hct⟩ := hctor j cA hj
        have hpl : Expr.recRulePlain cvRa.type p.majorIdx p.rulePrefix p.nP cA.1.levelParams = true :=
          List.all_eq_true.mp hplAll cA (List.mem_of_getElem? hj)
        exact ⟨Ix.Kernel.RuleCtorOk.of_plain hf (by simp [Ix.Kernel.recRuleBits, hpl]) hpl hct,
          fun hb => hb, fun hb => hb⟩)
  obtain ⟨mpd, hmpd⟩ := recDeclaredStep mpC mpg hac hname hlps hfresh hnres hhead
    ⟨_, by omega, hpiG⟩ ⟨_, by omega, WrapT.piToBvar hpiG (hWd.toWrapT hlfT)⟩
    (fun ψ ta hta => wrapRel_read hfind mpg.defn_reads hWd hlfT hta)
    (fun rl hrl _ => by
      obtain ⟨j, cA, rhsD, hj, hrj, rfl⟩ := Ix.Kernel.sumRules_getElem? hrl
      obtain ⟨rhsGj, hgj, hWj⟩ := forall₂_getElem? hWr hrj
      have hpl : Expr.recRulePlain cvRa.type p.majorIdx p.rulePrefix p.nP cA.1.levelParams = true :=
        List.all_eq_true.mp hplAll cA (List.mem_of_getElem? hj)
      have hplg : Expr.recRulePlain cvRg.type p.majorIdx p.rulePrefix p.nP cA.1.levelParams
          = true :=
        List.all_eq_true.mp hplG cA (List.mem_of_getElem? hj)
      refine ⟨Ix.Kernel.recRuleBits E.find? cvRg.name
          { ctor := cA.1.name, nfields := cA.2, ctorParams := p.nP, fire := .plain,
            rhs := rhsGj, paramsBlind := true }, rhsGj, ?_, ?_, rfl, ?_, ?_⟩
      · rw [hname]
        rw [if_pos hpl]
        rfl
      · have h := sumRules_mem_of_getElem? (find? := E.find?) (recName := cvRg.name) (nP := p.nP)
          (mI := p.majorIdx) (rP := p.rulePrefix) (recTy := cvRg.type) hj hgj
        rw [if_pos hplg] at h
        exact h
      · intro ψ ta hta
        obtain ⟨pre, dom, body, bm, _D, hs, -, -⟩ := Ix.Kernel.recRulePlain_shapeT hplg
        have hiss : (cvRg.type.stripPis (p.majorIdx + 1)).isSome = true := by
          rw [Ix.Kernel.stripPis_append _ hs
            (show (Expr.forallE dom body bm).stripPis 1 = some ([(dom, bm)], body) from rfl)]
          rfl
        exact Rules.piChain_of_stripPis (p.majorIdx + 1) hiss hta
      · intro ψ ra hra
        exact wrapRel_read hfind mpg.defn_reads hWj (hlf rhsD (List.mem_of_getElem? hrj)) hra)
  exact ⟨mpd, by rw [hmpd, hac, hname]⟩

end Ix.Kernel.Model
