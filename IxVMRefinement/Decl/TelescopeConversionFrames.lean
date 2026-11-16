import IxVMRefinement.Decl.TelescopeConversionPins
import IxVMRefinement.Decl.NativeNormalizationFrames

/-! # Dependent telescope frames from checked conversion

The conversion's actual domain comparison identifies the next admissible values. Its
opened-body comparison is retained at whichever original opener the derivation used.
The semantic context follows that choice, so conversion is never transported by replacing
free-variable type annotations syntactically.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term Ix.Kernel.Verify
open Ix.Kernel.Model.Rules (Frame Graded)

universe u

/-- A checked conversion of two syntactic telescope prefixes identifies their dependent
contexts and the interpretation of their residual readings. -/
theorem converted_telescope_frames {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {count depth : Nat} {left right : Expr md}
    (converted : Ix.Kernel.Rules.DefEq env depth left right)
    (leftShape : (left.stripPis count).isSome = true)
    (rightShape : (right.stripPis count).isSome = true)
    (leftFrame : Frame depth left) (rightFrame : Frame depth right)
    {φ : LevelParam → Nat} {context : List AnnotTerm} {leftReading rightReading : AnnotTerm}
    (leftContextOk : CtxOk model.base2 φ depth context left)
    (rightContextOk : CtxOk model.base2 φ depth context right)
    (leftRead : denoteMeta model.base2.acval env φ depth left = some leftReading)
    (rightRead : denoteMeta model.base2.acval env φ depth right = some rightReading)
    (leftGraded : Graded V context leftReading) (rightGraded : Graded V context rightReading)
    {leftContext rightContext : List AnnotTerm} {leftResidual rightResidual : AnnotTerm}
    (leftTele : PiTeleAV count leftReading leftContext leftResidual)
    (rightTele : PiTeleAV count rightReading rightContext rightResidual) :
    (∀ ρ : Nat → V, Sat V (leftContext ++ context) ρ ↔ Sat V (rightContext ++ context) ρ) ∧
      ∀ ρ : Nat → V, Sat V (leftContext ++ context) ρ →
        interp V ρ leftResidual = interp V ρ rightResidual := by
  induction count generalizing depth left right context leftReading rightReading
      leftContext rightContext leftResidual rightResidual with
  | zero =>
    cases leftTele
    cases rightTele
    exact ⟨fun _ => Iff.rfl, Ix.Kernel.Model.Rules.defeq_sound
      (fun ψ => Ix.Kernel.Model.Rules.RulesInputs.ofSem model ψ) converted
      leftFrame rightFrame leftContextOk rightContextOk leftRead rightRead leftGraded rightGraded⟩
  | succ count ih =>
    cases left with
    | forallE leftDomain leftBody leftMeta =>
      cases right with
      | forallE rightDomain rightBody rightMeta =>
        simp only [Expr.stripPis, Option.isSome_map] at leftShape rightShape
        obtain ⟨leftDomainRead, leftBodyRead, readLD, readLB, rfl⟩ := denoteMeta_forallE_inv leftRead
        obtain ⟨rightDomainRead, rightBodyRead, readRD, readRB, rfl⟩ := denoteMeta_forallE_inv rightRead
        obtain ⟨gradeLD, gradeLB⟩ := Ix.Kernel.Model.Rules.Graded.pi leftGraded
        obtain ⟨gradeRD, gradeRB⟩ := Ix.Kernel.Model.Rules.Graded.pi rightGraded
        obtain ⟨domainConverted, _, bodies⟩ := forall_conversion_components converted
        have domainEqual := Ix.Kernel.Model.Rules.defeq_sound
          (fun ψ => Ix.Kernel.Model.Rules.RulesInputs.ofSem model ψ) domainConverted
          leftFrame.forallE_ty rightFrame.forallE_ty leftContextOk.forallE_ty rightContextOk.forallE_ty
          readLD readRD gradeLD gradeRD
        cases leftTele with
        | @cons _ _ _ _ _ _ leftTail leftRest =>
          cases rightTele with
          | @cons _ _ _ _ _ _ rightTail rightRest =>
            have restFrames :
                (∀ ρ : Nat → V, Sat V (leftTail ++ leftDomainRead :: context) ρ ↔
                  Sat V (rightTail ++ leftDomainRead :: context) ρ) ∧
                ∀ ρ : Nat → V, Sat V (leftTail ++ leftDomainRead :: context) ρ →
                  interp V ρ leftResidual = interp V ρ rightResidual := by
              rcases bodies with openedLeft | openedRight
              · exact ih openedLeft
                  (Expr.stripPis_instantiate1_isSome (v := .fvar depth leftDomain) count 0 leftShape)
                  (Expr.stripPis_instantiate1_isSome (v := .fvar depth leftDomain) count 0 rightShape)
                  (leftFrame.forallE_open leftFrame.forallE_ty)
                  (rightFrame.forallE_open leftFrame.forallE_ty)
                  (CtxOk.open leftContextOk.forallE_body leftContextOk.forallE_ty readLD gradeLD)
                  (CtxOk.open rightContextOk.forallE_body leftContextOk.forallE_ty readLD gradeLD)
                  readLB (Ix.Kernel.Model.Rules.denoteMeta_open_rename (ty' := leftDomain) readRB)
                  gradeLB (Ix.Kernel.Model.Rules.Graded.head_congr domainEqual gradeRB) leftRest rightRest
              · exact ih openedRight
                  (Expr.stripPis_instantiate1_isSome (v := .fvar depth rightDomain) count 0 leftShape)
                  (Expr.stripPis_instantiate1_isSome (v := .fvar depth rightDomain) count 0 rightShape)
                  (leftFrame.forallE_open rightFrame.forallE_ty)
                  (rightFrame.forallE_open rightFrame.forallE_ty)
                  (CtxOk.openCongC leftContextOk.forallE_body rightContextOk.forallE_ty readRD gradeRD domainEqual)
                  (CtxOk.openCongC rightContextOk.forallE_body rightContextOk.forallE_ty readRD gradeRD domainEqual)
                  (Ix.Kernel.Model.Rules.denoteMeta_open_rename (ty' := rightDomain) readLB) readRB
                  gradeLB (Ix.Kernel.Model.Rules.Graded.head_congr domainEqual gradeRB) leftRest rightRest
            have heads : ∀ ρ : Nat → V,
                Sat V (leftDomainRead :: context) ρ ↔ Sat V (rightDomainRead :: context) ρ :=
              fun _ => ⟨Sat.head_congr domainEqual,
                Sat.head_congr (fun σ h => (domainEqual σ h).symm)⟩
            constructor
            · intro ρ
              simpa only [List.append_assoc, List.singleton_append] using
                (restFrames.1 ρ).trans (sat_append_congr heads rightTail ρ)
            · simpa only [List.append_assoc, List.singleton_append] using restFrames.2
      | _ => cases rightShape
    | _ => cases leftShape

/-- For closed telescope prefixes, the actual conversion transfers their fitting value spines. -/
theorem converted_telescope_spines {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {count : Nat} {left right : Expr md}
    (converted : Ix.Kernel.Rules.DefEq env 0 left right)
    (leftShape : (left.stripPis count).isSome = true)
    (rightShape : (right.stripPis count).isSome = true)
    (leftFrame : Frame 0 left) (rightFrame : Frame 0 right)
    {φ : LevelParam → Nat} {leftReading rightReading : AnnotTerm}
    (leftContextOk : CtxOk model.base2 φ 0 [] left)
    (rightContextOk : CtxOk model.base2 φ 0 [] right)
    (leftRead : denoteMeta model.base2.acval env φ 0 left = some leftReading)
    (rightRead : denoteMeta model.base2.acval env φ 0 right = some rightReading)
    (leftGraded : Graded V [] leftReading) (rightGraded : Graded V [] rightReading)
    {leftContext rightContext : List AnnotTerm} {leftResidual rightResidual : AnnotTerm}
    (leftTele : PiTeleAV count leftReading leftContext leftResidual)
    (rightTele : PiTeleAV count rightReading rightContext rightResidual)
    (ρ : Nat → V) (values : List V) (length : values.length = count) :
    SpineFit ρ leftContext.reverse values ↔ SpineFit ρ rightContext.reverse values := by
  have same := (converted_telescope_frames model converted leftShape rightShape leftFrame rightFrame
    leftContextOk rightContextOk leftRead rightRead leftGraded rightGraded leftTele rightTele).1
  apply spineFit_iff_of_sat_iff
  · simp only [List.length_reverse, leftTele.length, rightTele.length]
  · intro σ
    simpa only [List.reverse_reverse, List.append_nil] using same σ
  · simpa only [List.length_reverse, leftTele.length] using length

end IxVM.Refinement.Decl
