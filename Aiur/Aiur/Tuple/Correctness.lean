import Aiur.Tuple.Circuit.LocalCorrectness
import Aiur.Tuple.Circuit.Derivation
import Aiur.Tuple.Semantics.CallFacts

namespace Aiur.Tuple

/-- Every closed derivation of a compiled tuple program has a finite source evaluation. -/
theorem derivation_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {message : Circuit.Message F}
    (derivation : Circuit.Derivation system message) :
    EvalCall program message.channel message.args message.result := by
  induction derivation using Circuit.Derivation.rec
    (motive_2 := fun messages _ =>
      ∀ message ∈ messages, EvalCall program message.channel message.args message.result) with
  | node chip row lookup valid _ childrenIH =>
      obtain ⟨fn, found, lowered⟩ := Circuit.compile_find_chip compiled lookup
      have interface := Circuit.Compiler.lowerFunction_interface lowered
      have body := Circuit.Compiler.lowerFunction_sound lowered valid childrenIH
      have types : fn.params.map Prod.snd = (chip.receive row).args.map Value.type := by
        simpa only [Circuit.Chip.receive, List.map_map, Function.comp_def, Value.type_map]
          using interface.2.1.symm
      apply EvalCall.intro (prepareCall_of_types (fn := fn) ?_ types) body.toEvalExpr
      change program.findFunction? chip.name = some fn
      rw [interface.1, Circuit.findFunction_name found]
      exact found
  | nil => simp_all
  | cons _ _ headIH tailIH =>
      rename_i message member
      rcases List.mem_cons.mp member with same | member
      · subst message; exact headIH
      · exact tailIH message member

/-- Soundness for the current compiler, including nested tuples and ordered patterns. -/
theorem compiler_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List (Value F)} {result : Value F}
    (derives : Circuit.CircuitEvaluates system name args result) :
    EvalCall program name args result := by
  obtain ⟨tree⟩ := derives
  exact derivation_sound compiled tree

end Aiur.Tuple
