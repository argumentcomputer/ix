import IxVMRefinement.Decl.NativeNormalization

/-! # Conversion of the actual reclosed constructor field telescope

The field normalizer opens each body with its original domain. Reverse forall congruence
uses that same domain on the right, so its actual conversion derivations compose through
reclosing without changing free-variable annotations or appealing to conversion transitivity.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel

/-- Reclosing the actual normalized fields gives a conversion back to the initial telescope. -/
theorem normFieldDoms_reclose {md : Mode} {env : Env md} (wellFormed : EnvWF env)
    {fuel d count : Nat} {T : Key md} {e residual : Expr md}
    {binders : List (Expr md × BinderMeta)}
    (run : normFieldDoms (fueledOps .verified fuel) env T d count e = .ok (binders, residual))
    (scope : Expr.WScoped d e) (bounded : e.looseBVarsBounded 0 = true) :
    binders.length = count ∧
      Expr.WScoped d (closeTelescope binders d residual) ∧
      (closeTelescope binders d residual).looseBVarsBounded 0 = true ∧
      (∀ leaf ∈ (closeTelescope binders d residual).fvarLeaves, leaf ∈ e.fvarLeaves) ∧
      Rules.DefEq env d (closeTelescope binders d residual) e := by
  induction count generalizing d e binders residual with
  | zero =>
    have same := Except.ok.inj run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨rfl, scope, bounded, fun _ present => present, .refl⟩
  | succ count ih =>
    cases e with
    | forallE dom body bm =>
      simp only [normFieldDoms] at run
      obtain ⟨dom', normalized, rest⟩ := exceptBind_ok run
      obtain ⟨pair, recRun, result⟩ := exceptBind_ok rest
      obtain ⟨tailBinders, tailResidual⟩ := pair
      have same := Except.ok.inj result
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      simp only [Expr.WScoped] at scope
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
      obtain ⟨domainScope, domainBounded, domainLeaves, domainEq⟩ :=
        normPosDom_sound wellFormed normalized scope.1 bounded.1
      obtain ⟨length, tailScope, tailBounded, tailLeaves, tailEq⟩ := ih recRun
        (scope.1.instantiate1 0 scope.2) (looseBVarsBounded_instantiate1 _ 0 bounded.2)
      have leafCondition : Expr.LeafCond d dom (body.instantiate1 (.fvar d dom)) := by
        intro leaf present sameIndex
        rcases Expr.fvarLeaves_instantiate1 body 0 present with inBody | inVar
        · have lt := Expr.fvarLeaves_lt_of_wscoped scope.2 leaf inBody
          omega
        · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
          rcases inVar with rfl | inDom
          · rfl
          · have lt := Expr.fvarLeaves_lt_of_wscoped scope.1 leaf inDom
            omega
      have consistent := Expr.fvarConsistent_of_leafCond
        (closeTelescope tailBinders (d + 1) tailResidual)
        (fun leaf present => leafCondition leaf (tailLeaves leaf present))
      have roundTrip := abstract1_instantiate1 _ 0 consistent tailBounded
      refine ⟨by simp only [List.length_cons, length], ?_, ?_, ?_, ?_⟩
      · simp only [closeTelescope, Expr.WScoped]
        exact ⟨domainScope, WScoped.abstract1 0 tailScope⟩
      · simp only [closeTelescope, Expr.looseBVarsBounded, Bool.and_eq_true]
        exact ⟨domainBounded, looseBVarsBounded_abstract1 _ 0 tailBounded⟩
      · intro leaf present
        simp only [closeTelescope, Expr.fvarLeaves, List.mem_append] at present ⊢
        rcases present with inDomain | inBody
        · exact Or.inl (domainLeaves leaf inDomain)
        · obtain ⟨inOutput, notFresh⟩ := Expr.fvarLeaves_abstract1_ne _ 0 tailScope leaf inBody
          rcases Expr.fvarLeaves_instantiate1 body 0 (tailLeaves leaf inOutput) with inRaw | inVar
          · exact Or.inr inRaw
          · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
            rcases inVar with same | inDomain
            · subst leaf
              exact (notFresh rfl).elim
            · exact Or.inl inDomain
      · apply Rules.DefEq.forallE (.symm domainEq) _ rfl
        rw [roundTrip]
        exact tailEq
    | _ => cases run

end IxVM.Refinement.Decl
