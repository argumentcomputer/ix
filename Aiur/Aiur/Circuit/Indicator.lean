import Aiur.Circuit.BuildFacts
import Aiur.Circuit.PatternFacts

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

theorem equalIndicator_sound [Field F] [DecidableEq F]
    {difference test : ArithExpr F} {before after : BuildState F}
    (compiled : equalIndicator difference before = .ok (test, after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧
      test.denote assignment = if difference.denote assignment = 0 then 1 else 0 := by
  simp [equalIndicator, StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
  obtain ⟨rfl, rfl⟩ := compiled
  refine ⟨valid.of_subset (fun _ member => by simp [member]) (fun _ member => member) (fun _ member => member), ?_⟩
  apply equality_indicator_sound
  · exact valid.constraints (.mul difference (.var before.nextVar)) (by simp)
  · exact valid.constraints
      (.sub (.mul difference (.var (before.nextVar + 1)))
        (.sub (.const 1) (.var before.nextVar))) (by simp)

end Aiur.Circuit.Compiler
