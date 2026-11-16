import IxVMRefinement.Decl.NativeNormalizationFrame
import IxC.Kernel.Model.Inductives.StructStageCtor

/-! # Dependent frames of the actual normalized field telescope

Domain interpretation equality is retained binder by binder in the original context.
It constructs equality of the satisfying valuations of the two opened telescopes, and
therefore transfers fitting argument spines without requiring equal free-variable types.
The statement concerns the telescope before the separate final annotation pass.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term Ix.Kernel.Verify
open Ix.Kernel.Model.Rules (Frame Graded)

universe u

/-- A telescope correspondence with every domain comparison in its actual earlier frame. -/
inductive TelescopeFrames (V : Type u) [SetTheory V] :
    List AnnotTerm → Nat → AnnotTerm → AnnotTerm → Prop
  | nil (context : List AnnotTerm) (body : AnnotTerm) : TelescopeFrames V context 0 body body
  | pi {context : List AnnotTerm} {count leftLevel leftBit rightLevel rightBit : Nat}
      {leftDomain rightDomain leftBody rightBody : AnnotTerm}
      (domain : ∀ ρ : Nat → V, Sat V context ρ →
        interp V ρ leftDomain = interp V ρ rightDomain)
      (body : TelescopeFrames V (leftDomain :: context) count leftBody rightBody) :
      TelescopeFrames V context (count + 1) (.pi leftLevel leftBit leftDomain leftBody)
        (.pi rightLevel rightBit rightDomain rightBody)

private theorem sat_append_congr {V : Type u} [SetTheory V]
    {left right : List AnnotTerm}
    (same : ∀ ρ : Nat → V, Sat V left ρ ↔ Sat V right ρ) :
    ∀ front ρ, Sat V (front ++ left) ρ ↔ Sat V (front ++ right) ρ := by
  intro front
  induction front with
  | nil => exact same
  | cons head front ih =>
    intro ρ
    constructor
    · intro satisfied
      obtain ⟨member, tail⟩ := Sat_cons_inv satisfied
      have result := Sat_cons V ((ih _).mp tail) member
      rwa [cons_eta] at result
    · intro satisfied
      obtain ⟨member, tail⟩ := Sat_cons_inv satisfied
      have result := Sat_cons V ((ih _).mpr tail) member
      rwa [cons_eta] at result

/-- The two complete dependent contexts have the same satisfying valuations and residual reading. -/
theorem TelescopeFrames.contexts {V : Type u} [SetTheory V]
    {context : List AnnotTerm} {count : Nat} {left right : AnnotTerm}
    (related : TelescopeFrames V context count left right)
    {leftContext rightContext : List AnnotTerm} {leftResidual rightResidual : AnnotTerm}
    (leftTele : PiTeleAV count left leftContext leftResidual)
    (rightTele : PiTeleAV count right rightContext rightResidual) :
    leftResidual = rightResidual ∧
      ∀ ρ : Nat → V, Sat V (leftContext ++ context) ρ ↔ Sat V (rightContext ++ context) ρ := by
  induction related generalizing leftContext rightContext leftResidual rightResidual with
  | nil =>
    cases leftTele
    cases rightTele
    exact ⟨rfl, fun _ => Iff.rfl⟩
  | @pi context count ll lb rl rb leftDomain rightDomain leftBody rightBody domain body ih =>
    cases leftTele with
    | @cons _ _ _ _ _ _ leftTail leftRest =>
      cases rightTele with
      | @cons _ _ _ _ _ _ rightTail rightRest =>
        obtain ⟨residualEq, contextEq⟩ := ih leftRest rightRest
        have headEq : ∀ ρ : Nat → V,
            Sat V (leftDomain :: context) ρ ↔ Sat V (rightDomain :: context) ρ := by
          intro ρ
          exact ⟨Sat.head_congr domain, Sat.head_congr (fun σ h => (domain σ h).symm)⟩
        refine ⟨residualEq, fun ρ => ?_⟩
        simpa only [List.append_assoc, List.singleton_append] using
          (contextEq ρ).trans (sat_append_congr headEq rightTail ρ)

/-- At a closed telescope the corresponding domain lists fit exactly the same argument spines. -/
theorem TelescopeFrames.spines {V : Type u} [SetTheory V] {count : Nat} {left right : AnnotTerm}
    (related : TelescopeFrames V [] count left right)
    {leftContext rightContext : List AnnotTerm} {leftResidual rightResidual : AnnotTerm}
    (leftTele : PiTeleAV count left leftContext leftResidual)
    (rightTele : PiTeleAV count right rightContext rightResidual)
    (ρ : Nat → V) (values : List V) (length : values.length = count) :
    SpineFit ρ leftContext.reverse values ↔ SpineFit ρ rightContext.reverse values := by
  have contextEq := (related.contexts leftTele rightTele).2
  apply spineFit_iff_of_sat_iff
  · simp only [List.length_reverse, leftTele.length, rightTele.length]
  · intro σ
    simpa only [List.reverse_reverse, List.append_nil] using contextEq σ
  · simpa only [List.length_reverse, leftTele.length] using length

/-- The actual field normalizer constructs its dependent frame correspondence before reannotation. -/
theorem normFieldDoms_frames {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {fuel count depth : Nat} {T : Key md} {e residual : Expr md}
    {binders : List (Expr md × BinderMeta)}
    (run : normFieldDoms (fueledOps .verified fuel) env T depth count e = .ok (binders, residual))
    (frame : Frame depth e) {φ : LevelParam → Nat} {context : List AnnotTerm} {reading : AnnotTerm}
    (aligned : CtxOk model.base2 φ depth context e)
    (read : denoteMeta model.base2.acval env φ depth e = some reading)
    (graded : Graded V context reading) :
    ∃ output, denoteMeta model.base2.acval env φ depth (closeTelescope binders depth residual) = some output ∧
      TelescopeFrames V context count reading output := by
  induction count generalizing depth e binders residual context reading with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨reading, read, .nil context reading⟩
  | succ count ih =>
    cases e with
    | forallE dom body bm =>
      simp only [normFieldDoms] at run
      obtain ⟨dom', normalized, rest⟩ := exceptBind_ok run
      obtain ⟨pair, recursive, result⟩ := exceptBind_ok rest
      obtain ⟨tailBinders, tailResidual⟩ := pair
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj result)
      obtain ⟨domainReading, bodyReading, domainRead, bodyRead, rfl⟩ := denoteMeta_forallE_inv read
      obtain ⟨domainGraded, bodyGraded⟩ := Ix.Kernel.Model.Rules.Graded.pi graded
      obtain ⟨domainOutput, domainOutputRead, _, domainEqual⟩ :=
        normPosDom_semantics model normalized frame.forallE_ty aligned.forallE_ty domainRead domainGraded
      have openFrame := frame.forallE_open frame.forallE_ty
      have openContext := CtxOk.open aligned.forallE_body aligned.forallE_ty domainRead domainGraded
      obtain ⟨bodyOutput, outputRead, related⟩ := ih recursive openFrame openContext bodyRead bodyGraded
      obtain ⟨_, _, outputBounded, outputLeaves, _⟩ :=
        normFieldDoms_reclose model.base2.wf recursive openFrame.1 openFrame.2.1
      have scopes : Expr.WScoped depth dom ∧ Expr.WScoped depth body := by
        simpa only [Expr.WScoped] using frame.1
      have roundTrip := normalization_reclose_from_leaves scopes.1 scopes.2 outputBounded outputLeaves
      have sameOpenerRead : denoteMeta model.base2.acval env φ (depth + 1)
          (((closeTelescope tailBinders (depth + 1) tailResidual).abstract1 depth).instantiate1
            (.fvar depth dom)) = some bodyOutput := by
        rw [roundTrip]
        exact outputRead
      have newOpenerRead := Ix.Kernel.Model.Rules.denoteMeta_open_rename (ty' := dom') sameOpenerRead
      refine ⟨.pi 0 (pwBit φ bm.pw) domainOutput bodyOutput, ?_, .pi domainEqual related⟩
      simp only [closeTelescope]
      rw [denoteMeta_forallE, domainOutputRead, newOpenerRead]
      rfl
    | _ => cases run

end IxVM.Refinement.Decl
