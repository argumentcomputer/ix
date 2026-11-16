import IxVMRefinement.Decl.NativeNormalization
import IxC.Kernel.Model.Inductives.StructRows
import IxC.Kernel.Model.Rules.DefEqSoundKit

/-! # Semantic frames for actual positivity normalization

The real weak-head reductions provide readable, graded outputs. Recursion under a binder
uses its original opener and preserves its metadata; interpretation equality transports
its codomain validity as well as ordinary grading. This statement is before reannotation.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term Ix.Kernel.Verify
open Ix.Kernel.Model.Rules (Frame Graded)

universe u

private theorem graded_pi_replace_body {V : Type u} [SetTheory V]
    {context : List AnnotTerm} {level bit : Nat} {domain body replacement : AnnotTerm}
    (original : Graded V context (.pi level bit domain body))
    (changed : Graded V (domain :: context) replacement)
    (same : ∀ ρ : Nat → V, Sat V (domain :: context) ρ →
      interp V ρ body = interp V ρ replacement) :
    Graded V context (.pi level bit domain replacement) := by
  intro ρ satisfied
  have old := original ρ satisfied
  simp only [WellDenotedV, WellDenoted_pi, AnnotValid_pi] at old ⊢
  refine ⟨⟨old.1.1, fun x hx => (changed _ (Sat_cons V satisfied hx)).1⟩,
    old.2.1, (fun x hx => (changed _ (Sat_cons V satisfied hx)).2), ?_⟩
  intro zero x member
  rw [← same (cons x ρ) (Sat_cons V satisfied member)]
  exact old.2.2.2 zero x member

/-- Actual positivity normalization preserves the reading and grading in its checked input frame. -/
theorem normPosDom_semantics {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {fuel steps depth : Nat} {T : Key md} {e out : Expr md}
    (run : normPosDom (fueledOps .verified fuel) env T depth steps e = .ok out)
    (frame : Frame depth e) {φ : LevelParam → Nat} {context : List AnnotTerm} {reading : AnnotTerm}
    (aligned : CtxOk model.base2 φ depth context e)
    (read : denoteMeta model.base2.acval env φ depth e = some reading)
    (graded : Graded V context reading) :
    ∃ output, denoteMeta model.base2.acval env φ depth out = some output ∧
      Graded V context output ∧
      ∀ ρ : Nat → V, Sat V context ρ → interp V ρ reading = interp V ρ output := by
  induction steps generalizing depth e out context reading with
  | zero => cases run
  | succ steps ih =>
    simp only [normPosDom] at run
    split at run
    · have same := Except.ok.inj run
      subst out
      exact ⟨reading, read, graded, fun _ _ => rfl⟩
    · obtain ⟨w, reduced, rest⟩ := exceptBind_ok run
      change whnf .verified env fuel depth e = .ok w at reduced
      have semantic := Ix.Kernel.Model.Rules.red_sound
        (fun ψ => Ix.Kernel.Model.Rules.RulesInputs.ofSem model ψ)
        (Ix.Kernel.Rules.whnf_bridge reduced)
      obtain ⟨wFrame, wLeaves, wReading, wRead, wGraded, wEqual⟩ := semantic frame aligned read graded
      have wContext := aligned.of_subset wLeaves
      split at rest
      · have same := Except.ok.inj rest
        subst out
        exact ⟨wReading, wRead, wGraded, wEqual⟩
      · cases w with
        | forallE dom body bm =>
          dsimp only at rest
          split at rest
          · cases rest
          · obtain ⟨bodyOut, recursive, result⟩ := exceptBind_ok rest
            have same := Except.ok.inj result
            subst out
            obtain ⟨domainReading, bodyReading, domainRead, bodyRead, rfl⟩ := denoteMeta_forallE_inv wRead
            obtain ⟨domainGraded, bodyGraded⟩ := Ix.Kernel.Model.Rules.Graded.pi wGraded
            have openFrame := wFrame.forallE_open wFrame.forallE_ty
            have openContext := CtxOk.open wContext.forallE_body wContext.forallE_ty domainRead domainGraded
            obtain ⟨bodyOutput, outputRead, outputGraded, outputEqual⟩ :=
              ih recursive openFrame openContext bodyRead bodyGraded
            obtain ⟨_, outputBounded, outputLeaves, _⟩ :=
              normPosDom_sound model.base2.wf recursive openFrame.1 openFrame.2.1
            have scopes : Expr.WScoped depth dom ∧ Expr.WScoped depth body := wFrame.1
            have leafCondition : Expr.LeafCond depth dom (body.instantiate1 (.fvar depth dom)) := by
              intro leaf present sameIndex
              rcases Expr.fvarLeaves_instantiate1 body 0 present with inBody | inVar
              · have lt := Expr.fvarLeaves_lt_of_wscoped scopes.2 leaf inBody
                omega
              · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
                rcases inVar with rfl | inDom
                · rfl
                · have lt := Expr.fvarLeaves_lt_of_wscoped scopes.1 leaf inDom
                  omega
            have consistent := Expr.fvarConsistent_of_leafCond bodyOut
              (fun leaf present => leafCondition leaf (outputLeaves leaf present))
            have roundTrip := abstract1_instantiate1 bodyOut 0 consistent outputBounded
            refine ⟨.pi 0 (pwBit φ bm.pw) domainReading bodyOutput, ?_,
              graded_pi_replace_body wGraded outputGraded outputEqual, ?_⟩
            · rw [denoteMeta_forallE, domainRead, roundTrip, outputRead]
              rfl
            · intro ρ satisfied
              exact (wEqual ρ satisfied).trans
                (deqStep_piCong rfl (fun x member => outputEqual (cons x ρ) (Sat_cons V satisfied member)))
        | _ =>
          have same := Except.ok.inj rest
          subst out
          exact ⟨wReading, wRead, wGraded, wEqual⟩

end IxVM.Refinement.Decl
