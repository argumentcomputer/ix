import Aiur.Tuple.Correctness
import Aiur.Tuple.Circuit.LocalWitness
import Aiur.Tuple.Semantics.CallTypes

namespace Aiur.Tuple

private theorem compiled_typechecked [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F} (compiled : Circuit.compile program = .ok system) :
    typecheck program = .ok () := by
  cases checked : typecheck program with
  | error error => simp [Circuit.compile, checked] at compiled; cases compiled
  | ok finished => cases finished; rfl

/-- Compiled call premises carry the function's declared structural result type. -/
theorem circuit_calls_typed [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F} (compiled : Circuit.compile program = .ok system) :
    CallsTyped program (Circuit.CircuitEvaluates system) := by
  intro name args result derives fn found
  obtain ⟨tree⟩ := derives
  cases tree with
  | node chip row lookup valid children =>
      obtain ⟨source, sourceFound, lowered⟩ := Circuit.compile_find_chip compiled lookup
      have names : chip.name = row.chip := by simpa using List.find?_some lookup
      change program.findFunction? chip.name = some fn at found
      rw [names] at found
      have same : fn = source := Option.some.inj (found.symm.trans sourceFound)
      subst fn
      simpa only [Circuit.Chip.receive, Value.type_map] using (Circuit.Compiler.lowerFunction_interface lowered).2.2

/-- Every finite source evaluation produces a closed derivation of the compiled tuple chips. -/
theorem evaluation_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F} (evaluated : EvalCall program name args result) :
    Circuit.CircuitEvaluates system name args result := by
  induction evaluated using EvalCall.rec
    (motive_1 := fun locals expr value _ => EvalExprWith (Circuit.CircuitEvaluates system) locals expr value)
    (motive_2 := fun locals exprs values _ => EvalArgsWith (Circuit.CircuitEvaluates system) locals exprs values) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | tuple _ ih => exact .tuple ih
  | project _ projected ih => exact .project ih projected
  | letValue _ matched _ inputIH bodyIH => exact .letValue inputIH matched bodyIH
  | neg _ operation ih => exact .neg ih operation
  | binary _ _ operation leftIH rightIH => exact .binary leftIH rightIH operation
  | call _ _ argsIH calleeIH => exact .call argsIH calleeIH
  | matchValue _ selected _ inputIH bodyIH => exact .matchValue inputIH selected bodyIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH
  | intro prepared _ bodyIH =>
      obtain ⟨fn, lookup, types, rfl, rfl⟩ := prepareCall_spec prepared
      obtain ⟨chip, found, lowered⟩ := Circuit.compile_find_function compiled lookup
      have checked := typecheck_function (compiled_typechecked compiled) (List.mem_of_find?_eq_some lookup)
      obtain ⟨row, rowName, valid, receive, premises⟩ := Circuit.Compiler.lowerFunction_complete
        lowered (circuit_calls_typed compiled) checked types bodyIH
      have name := Circuit.findFunction_name lookup
      have rowLookup : system.findChip? row.chip = some chip := by rw [rowName, name]; exact found
      obtain ⟨children⟩ := Circuit.derivations_nonempty_iff.mpr premises
      have tree := Circuit.Derivation.node chip row rowLookup valid children
      rw [receive, name] at tree
      exact ⟨tree⟩

/-- Successful compilation preserves and reflects evaluation, including arbitrary nested tuples. -/
theorem compiler_correct [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F} :
    EvalCall program name args result ↔ Circuit.CircuitEvaluates system name args result :=
  ⟨evaluation_complete compiled, compiler_sound compiled⟩

end Aiur.Tuple
