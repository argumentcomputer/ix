import Aiur.Circuit.WitnessBasic

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

theorem equalIndicator_complete [Field F] [DecidableEq F]
    {difference test : ArithExpr F} {before after : BuildState F}
    (compiled : equalIndicator difference before = .ok (test, after))
    {calls : CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (bounded : difference.inBounds before.nextVar = true) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      test.inBounds after.nextVar = true := by
  simp [equalIndicator, StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
  obtain ⟨rfl, rfl⟩ := compiled
  let equal : F := if difference.denote initial = 0 then 1 else 0
  let assignment := Function.update (Function.update initial before.nextVar equal)
    (before.nextVar + 1) (difference.denote initial)⁻¹
  have agree : ∀ id < before.nextVar, assignment id = initial id := by
    intro id bound
    simp [assignment, Function.update_of_ne (by omega : id ≠ before.nextVar + 1),
      Function.update_of_ne (by omega : id ≠ before.nextVar)]
  have dEq : difference.denote assignment = difference.denote initial :=
    Scalar.Circuit.ArithExpr.denote_eq_of_agree agree bounded
  have eEq : assignment before.nextVar = equal := by simp [assignment]
  have uEq : assignment (before.nextVar + 1) = (difference.denote initial)⁻¹ := by simp [assignment]
  have equations := equality_indicator_complete (difference.denote initial)
  have grown := layout.grow (by omega : before.nextVar ≤ before.nextVar + 1 + 1)
  have db := Scalar.Circuit.ArithExpr.inBounds_mono
    (by omega : before.nextVar ≤ before.nextVar + 1 + 1) bounded
  have lo : before.nextVar < before.nextVar + 1 + 1 := by omega
  have hi : before.nextVar + 1 < before.nextVar + 1 + 1 := by omega
  have firstBound : (ArithExpr.mul (.var before.nextVar)
      (.sub (.var before.nextVar) (.const (1 : F)))).inBounds (before.nextVar + 1 + 1) = true := by
    simp [Scalar.Circuit.ArithExpr.inBounds, lo]
  have secondBound : (ArithExpr.mul difference (.var before.nextVar)).inBounds
      (before.nextVar + 1 + 1) = true := by
    simp [Scalar.Circuit.ArithExpr.inBounds, lo, db]
  have thirdBound : (ArithExpr.sub (.mul difference (.var (before.nextVar + 1)))
      (.sub (.const 1) (.var before.nextVar))).inBounds (before.nextVar + 1 + 1) = true := by
    simp [Scalar.Circuit.ArithExpr.inBounds, lo, hi, db]
  have grownValid : ({ before with nextVar := before.nextVar + 1 + 1 } : BuildState F).Valid rom calls assignment :=
    ⟨(valid.of_agree layout agree).constraints, (valid.of_agree layout agree).calls, (valid.of_agree layout agree).memory⟩
  have firstZero : (ArithExpr.mul (.var before.nextVar)
      (.sub (.var before.nextVar) (.const (1 : F)))).denote assignment = 0 := by
    simpa only [ArithExpr.denote, Scalar.Circuit.ArithExpr.denote, eEq, equal] using equations.1
  have secondZero : (ArithExpr.mul difference (.var before.nextVar)).denote assignment = 0 := by
    change difference.denote assignment * assignment before.nextVar = 0
    simpa only [dEq, eEq, equal] using equations.2.1
  have thirdZero : (ArithExpr.sub (.mul difference (.var (before.nextVar + 1)))
      (.sub (.const 1) (.var before.nextVar))).denote assignment = 0 := by
    change difference.denote assignment * assignment (before.nextVar + 1) - (1 - assignment before.nextVar) = 0
    simpa only [dEq, uEq, eEq, equal] using equations.2.2
  exact ⟨assignment, ⟨by dsimp; omega, agree,
    ((grown.constrain firstBound).constrain secondBound).constrain thirdBound,
    ((grownValid.constrain firstZero).constrain secondZero).constrain thirdZero⟩,
    by simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using lo⟩


end Aiur.Circuit.Compiler
