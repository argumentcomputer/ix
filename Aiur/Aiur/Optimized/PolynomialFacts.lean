import Aiur.Optimized.Basic

namespace Aiur.Optimized.Polynomial

variable {F : Type}

theorem beq_eq [BEq F] [LawfulBEq F] (left right : Polynomial F) :
    (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Scalar.Circuit.instBEqArithExpr.beq]

variable [Field F] [DecidableEq F]

omit [DecidableEq F] in
@[simp] theorem denote_subst (expr : Polynomial F) (replacement : Witness → Polynomial F)
    (assignment : Witness → F) :
    (expr.subst replacement).denote assignment =
      expr.denote (fun id => (replacement id).denote assignment) := by
  induction expr <;> simp_all [subst, Scalar.Circuit.ArithExpr.denote]

omit [DecidableEq F] in
theorem denote_congr (expr : Polynomial F) {left right : Witness → F}
    (agree : ∀ id ∈ expr.vars, left id = right id) : expr.denote left = expr.denote right := by
  induction expr <;> simp_all [vars, Scalar.Circuit.ArithExpr.denote]

@[simp] theorem denote_simplify (expr : Polynomial F) (assignment : Witness → F) :
    expr.simplify.denote assignment = expr.denote assignment := by
  change Scalar.Circuit.ArithExpr.denote assignment expr.simplify =
    Scalar.Circuit.ArithExpr.denote assignment expr
  induction expr with
  | const value => rfl
  | var id => rfl
  | add a b ha hb =>
      simp only [simplify, Scalar.Circuit.ArithExpr.denote]
      rw [← ha, ← hb]
      cases simplify a <;> cases simplify b <;>
        simp [Scalar.Circuit.ArithExpr.denote] <;> split <;>
        simp_all [Scalar.Circuit.ArithExpr.denote]
  | sub a b ha hb =>
      simp only [simplify, Scalar.Circuit.ArithExpr.denote]
      rw [← ha, ← hb]
      split
      · rename_i same
        have same := (beq_eq _ _).mp same
        simp [Scalar.Circuit.ArithExpr.denote, same]
      · cases simplify a <;> cases simplify b <;>
          simp [Scalar.Circuit.ArithExpr.denote] <;> split <;>
          simp_all [Scalar.Circuit.ArithExpr.denote]
  | mul a b ha hb =>
      simp only [simplify, Scalar.Circuit.ArithExpr.denote]
      rw [← ha, ← hb]
      cases simplify a <;> cases simplify b <;>
        simp [Scalar.Circuit.ArithExpr.denote] <;> split <;>
        (try simp_all [Scalar.Circuit.ArithExpr.denote]) <;> split <;>
        simp_all [Scalar.Circuit.ArithExpr.denote]

omit [DecidableEq F] in
/-- Naming a total polynomial is an existential conservative extension. The
guard permits an arbitrary witness in an inactive scope. -/
theorem materialize_iff (enable value : F) (property : F → Prop) :
    (∃ witness, enable * (witness - value) = 0 ∧ (enable ≠ 0 → property witness)) ↔
      (enable ≠ 0 → property value) := by
  constructor
  · rintro ⟨witness, equation, required⟩ active
    have equal : witness = value := sub_eq_zero.mp ((mul_eq_zero.mp equation).resolve_left active)
    simpa only [equal] using required active
  · intro required
    exact ⟨value, by simp, required⟩

omit [DecidableEq F] in
/-- Inverse witnesses stay guarded: no obligation is imposed by an inactive
division, even if its denominator is zero. -/
theorem inverse_iff (enable denominator : F) :
    (∃ inverse, enable * (denominator * inverse - 1) = 0) ↔
      (enable = 0 ∨ denominator ≠ 0) := by
  constructor
  · rintro ⟨inverse, valid⟩
    rcases mul_eq_zero.mp valid with inactive | equation
    · exact Or.inl inactive
    · right
      intro zero
      simp [zero] at equation
  · rintro (inactive | nonzero)
    · exact ⟨0, by simp [inactive]⟩
    · exact ⟨denominator⁻¹, by simp [nonzero]⟩

omit [DecidableEq F] in
/-- A nonrecursive selector definition has an extension for every assignment
to the remaining columns. Substitution evaluates in precisely that extension. -/
theorem alias_extension (definition expr : Polynomial F) (id : Witness)
    (nonrecursive : id ∉ definition.vars) (assignment : Witness → F) :
    let extended := Function.update assignment id (definition.denote assignment)
    extended id = definition.denote extended ∧
      (expr.subst (fun other => if other = id then definition else .var other)).denote assignment =
        expr.denote extended := by
  dsimp only
  have unchanged : definition.denote assignment =
      definition.denote (Function.update assignment id (definition.denote assignment)) := by
    apply denote_congr
    intro other member
    have different : other ≠ id := by rintro rfl; exact nonrecursive member
    simp [Function.update_of_ne different]
  constructor
  · simpa only [Function.update_self] using unchanged
  · rw [denote_subst]
    congr 1
    funext other
    by_cases same : other = id <;>
      simp [same, Function.update, Scalar.Circuit.ArithExpr.denote]

omit [DecidableEq F] in
/-- Projection needs the defining equation. Dropping an unconstrained selector
and substituting an arbitrary expression would not justify this equality. -/
theorem alias_projection (definition expr : Polynomial F) (id : Witness) (assignment : Witness → F)
    (defined : assignment id = definition.denote assignment) :
    (expr.subst (fun other => if other = id then definition else .var other)).denote assignment =
      expr.denote assignment := by
  rw [denote_subst]
  apply denote_congr
  intro other _
  by_cases same : other = id <;> simp [same, defined, Scalar.Circuit.ArithExpr.denote]

end Aiur.Optimized.Polynomial
