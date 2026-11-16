import IxVMRefinement.Decl.NativeRecloseConversion
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

private theorem reclose_from_leaves {md : Mode} {depth : Nat} {dom body output : Expr md}
    (domainScope : Expr.WScoped depth dom) (bodyScope : Expr.WScoped depth body)
    (bounded : output.looseBVarsBounded 0 = true)
    (leaves : ∀ leaf ∈ output.fvarLeaves, leaf ∈ (body.instantiate1 (.fvar depth dom)).fvarLeaves) :
    (output.abstract1 depth).instantiate1 (.fvar depth dom) = output := by
  have leafCondition : Expr.LeafCond depth dom (body.instantiate1 (.fvar depth dom)) := by
    intro leaf present sameIndex
    rcases Expr.fvarLeaves_instantiate1 body 0 present with inBody | inVar
    · have lt := Expr.fvarLeaves_lt_of_wscoped bodyScope leaf inBody
      omega
    · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
      rcases inVar with rfl | inDom
      · rfl
      · have lt := Expr.fvarLeaves_lt_of_wscoped domainScope leaf inDom
        omega
  have consistent := Expr.fvarConsistent_of_leafCond output
    (fun leaf present => leafCondition leaf (leaves leaf present))
  exact abstract1_instantiate1 output 0 consistent bounded


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
      have semantic := Ix.Kernel.Model.Rules.red_sound (φ := φ)
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
            have scopes : Expr.WScoped depth dom ∧ Expr.WScoped depth body := by
              simpa only [Expr.WScoped] using wFrame.1
            have roundTrip := reclose_from_leaves scopes.1 scopes.2 outputBounded outputLeaves
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

private theorem graded_pi_replace_domain {V : Type u} [SetTheory V]
    {context : List AnnotTerm} {level bit : Nat} {domain replacement body : AnnotTerm}
    (original : Graded V context (.pi level bit domain body))
    (changed : Graded V context replacement)
    (same : ∀ ρ : Nat → V, Sat V context ρ → interp V ρ domain = interp V ρ replacement) :
    Graded V context (.pi level bit replacement body) := by
  intro ρ satisfied
  have old := original ρ satisfied
  have newDomain := changed ρ satisfied
  have equal := same ρ satisfied
  simp only [WellDenotedV, WellDenoted_pi, AnnotValid_pi] at old newDomain ⊢
  rw [← equal]
  exact ⟨⟨newDomain.1, old.1.2⟩, newDomain.2, old.2.2⟩

/-- The actual field walk constructs the reading and grading of its reclosed telescope,
while interpreting it in the original parameter/field context. -/
theorem normFieldDoms_semantics {V : Type u} [SetTheory V] {md : Mode} {env : Env md}
    (model : EnvModelM V .verified env) {fuel count depth : Nat} {T : Key md} {e residual : Expr md}
    {binders : List (Expr md × BinderMeta)}
    (run : normFieldDoms (fueledOps .verified fuel) env T depth count e = .ok (binders, residual))
    (frame : Frame depth e) {φ : LevelParam → Nat} {context : List AnnotTerm} {reading : AnnotTerm}
    (aligned : CtxOk model.base2 φ depth context e)
    (read : denoteMeta model.base2.acval env φ depth e = some reading)
    (graded : Graded V context reading) :
    ∃ output, denoteMeta model.base2.acval env φ depth (closeTelescope binders depth residual) = some output ∧
      Graded V context output ∧
      ∀ ρ : Nat → V, Sat V context ρ → interp V ρ reading = interp V ρ output := by
  induction count generalizing depth e binders residual context reading with
  | zero =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨reading, read, graded, fun _ _ => rfl⟩
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
      obtain ⟨domainOutput, domainOutputRead, domainOutputGraded, domainEqual⟩ :=
        normPosDom_semantics model normalized frame.forallE_ty aligned.forallE_ty domainRead domainGraded
      have openFrame := frame.forallE_open frame.forallE_ty
      have openContext := CtxOk.open aligned.forallE_body aligned.forallE_ty domainRead domainGraded
      obtain ⟨bodyOutput, outputRead, outputGraded, outputEqual⟩ :=
        ih recursive openFrame openContext bodyRead bodyGraded
      obtain ⟨_, _, outputBounded, outputLeaves, _⟩ :=
        normFieldDoms_reclose model.base2.wf recursive openFrame.1 openFrame.2.1
      have scopes : Expr.WScoped depth dom ∧ Expr.WScoped depth body := by
        simpa only [Expr.WScoped] using frame.1
      have roundTrip := reclose_from_leaves scopes.1 scopes.2 outputBounded outputLeaves
      have sameOpenerRead : denoteMeta model.base2.acval env φ (depth + 1)
          (((closeTelescope tailBinders (depth + 1) tailResidual).abstract1 depth).instantiate1
            (.fvar depth dom)) = some bodyOutput := by
        rw [roundTrip]
        exact outputRead
      have newOpenerRead := Ix.Kernel.Model.Rules.denoteMeta_open_rename (ty' := dom') sameOpenerRead
      refine ⟨.pi 0 (pwBit φ bm.pw) domainOutput bodyOutput, ?_, ?_, ?_⟩
      · simp only [closeTelescope]
        rw [denoteMeta_forallE, domainOutputRead, newOpenerRead]
        rfl
      · exact graded_pi_replace_domain (graded_pi_replace_body graded outputGraded outputEqual)
          domainOutputGraded domainEqual
      · intro ρ satisfied
        exact deqStep_piCong (domainEqual ρ satisfied)
          (fun x member => outputEqual (cons x ρ) (Sat_cons V satisfied member))
    | _ => cases run

end IxVM.Refinement.Decl
