import IxCC.Aiur.CounterAnalysis.Body
import IxCC.Aiur.CounterAnalysis.Loops

namespace IxCC.Aiur.CounterAnalysis

open _root_.Aiur (G)
open _root_.Aiur.Bytecode

structure Found (functionIndex : Nat) (function : Function) (candidate : UnitCounter.Certificate) : Prop where
  checked : UnitCounter.check 256 functionIndex candidate (initialState function.layout.inputSize) function.body = true
  unit : candidate.step = 1 ∨ candidate.step = (0 : G) - 1
  inputColumn : candidate.mode = .input → candidate.column < function.layout.inputSize

private abbrev SearchState := Option (Option UnitCounter.Certificate) × Unit

private def AnswerValid (self : Nat) (function : Function) (answer : SearchState) : Prop :=
  ∀ candidate, answer.1 = some (some candidate) → Found self function candidate

private theorem empty_valid (self : Nat) (function : Function) : AnswerValid self function (none, ()) := by
  intro candidate impossible
  cases impossible

private def bubble (answer : SearchState) : ForInStep SearchState :=
  match answer.1 with
  | some result => .done (some result, ())
  | none => .yield (none, ())

private theorem bubble_value (answer : SearchState) : stepValue (bubble answer) = answer := by
  rcases answer with ⟨answer, token⟩
  cases token
  cases answer <;> rfl

private def choice (self : Nat) (function : Function) (mode : UnitCounter.Mode) (column : Nat) (step : G) :
    Id (ForInStep SearchState) :=
  let candidate : UnitCounter.Certificate := { mode, column, step }
  if UnitCounter.check 256 self candidate (initialState function.layout.inputSize) function.body then
    pure (.done (some (some candidate), ()))
  else pure (.yield (none, ()))

private def directions (self : Nat) (function : Function) (mode : UnitCounter.Mode) (column : Nat) : Id SearchState :=
  forIn [(1 : G), (0 : G) - 1] (none, ()) fun step _ => choice self function mode column step

private def columns (self : Nat) (function : Function) (mode : UnitCounter.Mode) : Id SearchState :=
  let count := match mode with
    | .input => function.layout.inputSize
    | .output => (UnitCounter.resultSize? 256 function.body).getD 0
  forIn [:count] (none, ()) fun column _ => pure (bubble (directions self function mode column))

private def modes (self : Nat) (function : Function) : Id SearchState :=
  forIn [UnitCounter.Mode.input, UnitCounter.Mode.output] (none, ()) fun mode _ =>
    pure (bubble (columns self function mode))

/-- These proof-local names merely expose the three existing loops. The
connection to the pinned implementation is definitional equality. -/
private theorem find_eq (self : Nat) (function : Function) :
    UnitCounter.find? self function = (modes self function).1.getD none := by
  unfold UnitCounter.find? modes columns directions choice bubble initialState
  simp only [Id.run, bind, pure, Option.getD]
  unfold Break.runK.match_1 bubble.match_1 columns.match_1 UnitCounter.stepOp.match_1 Option.getD.match_1
  rfl

private theorem choice_valid (self : Nat) (function : Function) (mode : UnitCounter.Mode) (column : Nat) (step : G)
    (unit : step = 1 ∨ step = (0 : G) - 1)
    (bound : mode = .input → column < function.layout.inputSize) :
    AnswerValid self function (stepValue (choice self function mode column step)) := by
  dsimp only [choice]
  split
  next checked =>
    intro candidate equal
    cases equal
    exact ⟨checked, unit, bound⟩
  next => exact empty_valid _ _

private theorem directions_valid (self : Nat) (function : Function) (mode : UnitCounter.Mode) (column : Nat)
    (bound : mode = .input → column < function.layout.inputSize) :
    AnswerValid self function (directions self function mode column) := by
  apply forIn_invariant _ _ _ (AnswerValid self function) (empty_valid _ _)
  intro step member _ _
  exact choice_valid self function mode column step (by simpa using member) bound

private theorem columns_valid (self : Nat) (function : Function) (mode : UnitCounter.Mode) :
    AnswerValid self function (columns self function mode) := by
  apply forIn_range_invariant _ _ _ (AnswerValid self function) (empty_valid _ _)
  intro column bound _ _
  change AnswerValid self function (stepValue (bubble (directions self function mode column)))
  rw [bubble_value]
  apply directions_valid
  intro input
  subst mode
  exact bound

private theorem modes_valid (self : Nat) (function : Function) : AnswerValid self function (modes self function) := by
  apply forIn_invariant _ _ _ (AnswerValid self function) (empty_valid _ _)
  intro mode _ _ _
  change AnswerValid self function (stepValue (bubble (columns self function mode)))
  rw [bubble_value]
  exact columns_valid _ _ _

/-- Every result of the actual pinned search passed its checker, uses a unit
step, and selects an existing input column when it is an input counter. -/
theorem find_spec {self : Nat} {function : Function} {candidate : UnitCounter.Certificate}
    (found : UnitCounter.find? self function = some candidate) : Found self function candidate := by
  rw [find_eq] at found
  have valid := modes_valid self function
  cases answer : (modes self function).1 with
  | none => simp [answer] at found
  | some result =>
    simp only [answer, Option.getD_some] at found
    subst result
    exact valid candidate answer

end IxCC.Aiur.CounterAnalysis
