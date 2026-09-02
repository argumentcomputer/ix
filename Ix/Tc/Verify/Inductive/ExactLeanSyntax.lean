import Ix.Tc.Verify.Inductive.CandidateSyntax

/-!
# Exact executable comparison for Lean kernel syntax

Lean's kernel `Level` and `Expr` values expose fast Boolean equality but do
not provide the proof-producing decidable equality needed to certify a
native-evaluated checker result.  The E2c constructor bridge needs exactly
that implication: a finite computation may observe an expression, but the
public proof must recover structural equality without importing reflected
implementation equations.

The checkers below cover the metadata-free kernel syntax used by inductive
validation.  Metadata nodes deliberately return `false`: their `KVMap`
payload is irrelevant to this fragment and admitting it would require a
separate exact metadata relation.  Every successful comparison is proved to
imply ordinary Lean equality.
-/

namespace Ix.Tc.ExactLeanSyntax

/-- Structural equality for universe levels, ignoring their cached `data`
field and comparing metavariable identifiers through their names. -/
def levelCheck : Lean.Level → Lean.Level → Bool
  | .zero, .zero => true
  | .succ left, .succ right => levelCheck left right
  | .max left₁ left₂, .max right₁ right₂ =>
      levelCheck left₁ right₁ && levelCheck left₂ right₂
  | .imax left₁ left₂, .imax right₁ right₂ =>
      levelCheck left₁ right₁ && levelCheck left₂ right₂
  | .param left, .param right => decide (left = right)
  | .mvar left, .mvar right => decide (left.name = right.name)
  | _, _ => false

/-- Pointwise structural equality for universe argument lists. -/
def levelsCheck : List Lean.Level → List Lean.Level → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      levelCheck left right && levelsCheck lefts rights
  | _, _ => false

/-- Exact comparison for binder annotations. -/
def binderInfoCheck : Lean.BinderInfo → Lean.BinderInfo → Bool
  | .default, .default => true
  | .implicit, .implicit => true
  | .strictImplicit, .strictImplicit => true
  | .instImplicit, .instImplicit => true
  | _, _ => false

/-- Exact comparison for literal payloads. -/
def literalCheck : Lean.Literal → Lean.Literal → Bool
  | .natVal left, .natVal right => decide (left = right)
  | .strVal left, .strVal right => decide (left = right)
  | _, _ => false

/-- Structural equality for the metadata-free Lean expression fragment.

All fields which contribute to kernel expression equality are compared,
including binder names and annotations.  Metavariable nodes are supported so
the checker remains useful for exact failure diagnostics, although E2c's
successful constructor candidates contain none. -/
def exprCheck : Lean.Expr → Lean.Expr → Bool
  | .bvar left, .bvar right => decide (left = right)
  | .fvar left, .fvar right => decide (left.name = right.name)
  | .mvar left, .mvar right => decide (left.name = right.name)
  | .sort left, .sort right => levelCheck left right
  | .const leftName leftLevels, .const rightName rightLevels =>
      decide (leftName = rightName) && levelsCheck leftLevels rightLevels
  | .app leftFn leftArg, .app rightFn rightArg =>
      exprCheck leftFn rightFn && exprCheck leftArg rightArg
  | .lam leftName leftType leftBody leftInfo,
      .lam rightName rightType rightBody rightInfo =>
      decide (leftName = rightName) &&
        binderInfoCheck leftInfo rightInfo &&
        exprCheck leftType rightType && exprCheck leftBody rightBody
  | .forallE leftName leftType leftBody leftInfo,
      .forallE rightName rightType rightBody rightInfo =>
      decide (leftName = rightName) &&
        binderInfoCheck leftInfo rightInfo &&
        exprCheck leftType rightType && exprCheck leftBody rightBody
  | .letE leftName leftType leftValue leftBody leftNondep,
      .letE rightName rightType rightValue rightBody rightNondep =>
      decide (leftName = rightName) && decide (leftNondep = rightNondep) &&
        exprCheck leftType rightType && exprCheck leftValue rightValue &&
        exprCheck leftBody rightBody
  | .lit left, .lit right => literalCheck left right
  | .proj leftName leftIndex leftStruct,
      .proj rightName rightIndex rightStruct =>
      decide (leftName = rightName) && decide (leftIndex = rightIndex) &&
        exprCheck leftStruct rightStruct
  | .mdata .., _ => false
  | _, .mdata .. => false
  | _, _ => false

theorem level_eq_of_check {left right : Lean.Level}
    (success : levelCheck left right = true) : left = right := by
  induction left generalizing right with
  | zero =>
      cases right <;> simp_all [levelCheck]
  | succ left ih =>
      cases right <;> simp_all [levelCheck]
      exact ih success
  | max left₁ left₂ ih₁ ih₂ =>
      cases right <;> simp_all [levelCheck, Bool.and_eq_true]
      exact ⟨ih₁ success.1, ih₂ success.2⟩
  | imax left₁ left₂ ih₁ ih₂ =>
      cases right <;> simp_all [levelCheck, Bool.and_eq_true]
      exact ⟨ih₁ success.1, ih₂ success.2⟩
  | param left =>
      cases right <;> simp_all [levelCheck]
  | mvar left =>
      cases left with
      | mk leftName =>
        cases right <;> simp_all [levelCheck]

theorem levels_eq_of_check {left right : List Lean.Level}
    (success : levelsCheck left right = true) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right <;> simp_all [levelsCheck]
  | cons level levels ih =>
      cases right with
      | nil => simp_all [levelsCheck]
      | cons other others =>
          simp only [levelsCheck, Bool.and_eq_true] at success
          rw [level_eq_of_check success.1, ih success.2]

theorem binderInfo_eq_of_check {left right : Lean.BinderInfo}
    (success : binderInfoCheck left right = true) : left = right := by
  cases left <;> cases right <;> simp_all [binderInfoCheck]

theorem literal_eq_of_check {left right : Lean.Literal}
    (success : literalCheck left right = true) : left = right := by
  cases left <;> cases right <;> simp_all [literalCheck]

theorem expr_eq_of_check {left right : Lean.Expr}
    (success : exprCheck left right = true) : left = right := by
  induction left generalizing right with
  | bvar left =>
      cases right <;> simp_all [exprCheck]
  | fvar left =>
      cases left with
      | mk leftName =>
        cases right <;> simp_all [exprCheck]
  | mvar left =>
      cases left with
      | mk leftName =>
        cases right <;> simp_all [exprCheck]
  | sort left =>
      cases right <;> simp_all [exprCheck]
      exact level_eq_of_check success
  | const leftName leftLevels =>
      cases right <;>
        simp_all [exprCheck, Bool.and_eq_true]
      exact levels_eq_of_check success.2
  | app leftFn leftArg ihFn ihArg =>
      cases right <;>
        simp_all [exprCheck, Bool.and_eq_true]
      exact ⟨ihFn success.1, ihArg success.2⟩
  | lam leftName leftType leftBody leftInfo ihType ihBody =>
      cases right <;>
        simp_all [exprCheck, Bool.and_eq_true]
      exact ⟨ihType success.1.2, ihBody success.2,
        binderInfo_eq_of_check success.1.1.2⟩
  | forallE leftName leftType leftBody leftInfo ihType ihBody =>
      cases right <;>
        simp_all [exprCheck, Bool.and_eq_true]
      exact ⟨ihType success.1.2, ihBody success.2,
        binderInfo_eq_of_check success.1.1.2⟩
  | letE leftName leftType leftValue leftBody leftNondep
      ihType ihValue ihBody =>
      cases right <;>
        simp_all [exprCheck, Bool.and_eq_true]
      exact ⟨ihType success.1.1.2, ihValue success.1.2,
        ihBody success.2⟩
  | lit left =>
      cases right <;> simp_all [exprCheck]
      exact literal_eq_of_check success
  | mdata data expression ih =>
      cases right <;> simp_all [exprCheck]
  | proj leftName leftIndex leftStruct ih =>
      cases right <;>
        simp_all [exprCheck, Bool.and_eq_true]
      exact ih success.2

/-- Compare the successful expression payload of an exception result. -/
def exceptExprCheck (outcome : Except ε Lean.Expr)
    (expected : Lean.Expr) : Bool :=
  match outcome with
  | .ok actual => exprCheck actual expected
  | .error _ => false

/-- Recover the exact successful result from a finite native observation. -/
theorem exceptExpr_eq_ok_of_check {outcome : Except ε Lean.Expr}
    {expected : Lean.Expr}
    (success : exceptExprCheck outcome expected = true) :
    outcome = .ok expected := by
  cases outcome with
  | error error => simp [exceptExprCheck] at success
  | ok actual =>
      simp only [exceptExprCheck] at success
      rw [expr_eq_of_check success]

/-- Compare a Boolean exception result without requiring equality on its
error type. -/
def exceptBoolCheck (outcome : Except ε Bool) (expected : Bool) : Bool :=
  match outcome with
  | .ok actual => decide (actual = expected)
  | .error _ => false

theorem exceptBool_eq_ok_of_check {outcome : Except ε Bool}
    {expected : Bool}
    (success : exceptBoolCheck outcome expected = true) :
    outcome = .ok expected := by
  cases outcome <;> simp_all [exceptBoolCheck]

end Ix.Tc.ExactLeanSyntax
