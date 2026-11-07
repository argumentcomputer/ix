import IxCC.Aiur.CounterAnalysis.Calls
import IxCC.Aiur.CounterAnalysis.Replay

namespace IxCC.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode

/-- One accepted abstract step preserves its meaning for every successful
concrete step, including arbitrary values supplied through the answer tape. -/
theorem stepOp_sound {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore abstractAfter : UnitCounter.State} {before after : OracleEval.State} {op : Op}
    (bound : candidate.mode = .input → candidate.column < inputs.size)
    (sound : Invariant self candidate inputs abstractBefore before)
    (checked : UnitCounter.stepOp self candidate abstractBefore op = some abstractAfter)
    (effect : Effect op before after) : Invariant self candidate inputs abstractAfter after := by
  obtain ⟨outputs, values, outputFact, callFact⟩ := effect
  cases op
  case const value =>
    simp only [UnitCounter.stepOp] at checked
    cases checked
    change outputs = [value] at outputFact
    subst outputs
    apply sound.push _ value (by intro expression known; cases known; exact denotes_constant _ _) values callFact
  case add left right =>
    simp only [UnitCounter.stepOp] at checked
    cases checked
    obtain ⟨a, b, leftRead, rightRead, rfl⟩ := outputFact
    exact sound.push _ _ (add_sound _ _ _ _ _ (sound.registers.get leftRead) (sound.registers.get rightRead)) values callFact
  case sub left right =>
    simp only [UnitCounter.stepOp] at checked
    cases checked
    obtain ⟨a, b, leftRead, rightRead, rfl⟩ := outputFact
    exact sound.push _ _ (sub_sound _ _ _ _ _ (sound.registers.get leftRead) (sound.registers.get rightRead)) values callFact
  case mul left right =>
    simp only [UnitCounter.stepOp] at checked
    cases checked
    obtain ⟨a, b, leftRead, rightRead, rfl⟩ := outputFact
    exact sound.push _ _ (mul_sound _ _ _ _ _ (sound.registers.get leftRead) (sound.registers.get rightRead)) values callFact
  case call function indices count unconstrained =>
    cases unconstrained with
    | true =>
      simp only [UnitCounter.stepOp] at checked
      cases checked
      exact sound.unknown outputs count outputFact values callFact
    | false =>
      obtain ⟨arguments, reads, newCall⟩ := callFact
      simp only [UnitCounter.stepOp] at checked
      by_cases selfCall : function = self
      · subst function
        simp only [BEq.rfl, ↓reduceIte] at checked
        cases mode : candidate.mode with
        | input =>
          simp only [mode] at checked
          cases selected : indices[candidate.column]? with
          | none => rw [selected] at checked; cases checked
          | some argument =>
            rw [selected] at checked
            simp only [bind, Option.bind] at checked
            split at checked
            next bad => cases checked
            next good =>
              cases checked
              have known : (abstractBefore.values[argument]?).getD none =
                  some ⟨some candidate.column, candidate.step⟩ := (optional_affine_beq_eq _ _).mp (by simpa [bne] using good)
              exact sound.inputCall mode (bound mode) indices arguments outputs count argument selected known reads outputFact values newCall
        | output =>
          simp only [mode] at checked
          split at checked
          next bad => cases checked
          next good =>
            cases checked
            have conditions : abstractBefore.recursiveOutput = none ∧ candidate.column < count := by
              simpa using good
            exact sound.outputCall mode conditions.1 arguments outputs count conditions.2 outputFact values newCall
      · simp only [beq_iff_eq, selfCall, ↓reduceIte] at checked
        cases checked
        exact sound.nonselfCall function arguments outputs count selfCall outputFact values newCall
  all_goals
    simp only [UnitCounter.stepOp] at checked
    cases checked
    exact sound.unknown outputs _ outputFact values callFact

theorem evalOp_invariant {self : Nat} {candidate : UnitCounter.Certificate} {inputs : Array G}
    {abstractBefore abstractAfter : UnitCounter.State} {before after : OracleEval.State} {op : Op}
    {toplevel : Toplevel} {maxValues : Nat}
    (bound : candidate.mode = .input → candidate.column < inputs.size)
    (sound : Invariant self candidate inputs abstractBefore before)
    (checked : UnitCounter.stepOp self candidate abstractBefore op = some abstractAfter)
    (success : OracleEval.evalOp toplevel maxValues op before = .ok after) :
    Invariant self candidate inputs abstractAfter after :=
  stepOp_sound bound sound checked (evalOp_effect success)

end IxCC.Aiur.CounterAnalysis
