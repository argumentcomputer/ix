import Aiur.Scalar.Semantics
import Aiur.Scalar.Circuit.Compile
import Aiur.Scalar.Circuit.Derivation
import Aiur.Scalar.Circuit.LocalCorrectness

namespace Aiur.Scalar

/-- Every successful source evaluation has a closed derivation in the chip system. -/
def CompilationComplete [Field F] [DecidableEq F] (program : Program F)
    (system : Circuit.System F) : Prop :=
  ∀ name args result, EvalCall program name args result →
    Circuit.CircuitEvaluates system name args result

/-- Every closed chip derivation corresponds to a successful source evaluation. -/
def CompilationSound [Field F] [DecidableEq F] (program : Program F)
    (system : Circuit.System F) : Prop :=
  ∀ name args result, Circuit.CircuitEvaluates system name args result →
    EvalCall program name args result

/-- The target equivalence, independent of any fuel bound or flat witness representation. -/
def CompilationCorrect [Field F] [DecidableEq F] (program : Program F)
    (system : Circuit.System F) : Prop :=
  ∀ name args result, EvalCall program name args result ↔
    Circuit.CircuitEvaluates system name args result

theorem compilationCorrect_iff [Field F] [DecidableEq F]
    (program : Program F) (system : Circuit.System F) :
    CompilationCorrect program system ↔
      CompilationComplete program system ∧ CompilationSound program system := by
  constructor
  · intro correct
    exact ⟨fun name args result => (correct name args result).mp,
      fun name args result => (correct name args result).mpr⟩
  · rintro ⟨complete, sound⟩ name args result
    exact ⟨complete name args result, sound name args result⟩

/-- The compiler's correctness specification, with both directions quantified over all calls. -/
def CompilerCorrect (F : Type) [Field F] [DecidableEq F] : Prop :=
  ∀ (program : Program F) (system : Circuit.System F),
    Circuit.compile program = .ok system → CompilationCorrect program system

/-- Induction over a closed circuit tree reduces soundness to one compiled body. -/
theorem derivation_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) {message : Circuit.Message F}
    (derivation : Circuit.Derivation system message) :
    EvalCall program message.channel message.args message.result := by
  induction derivation using Circuit.Derivation.rec
    (motive_2 := fun messages _ =>
      ∀ message ∈ messages, EvalCall program message.channel message.args message.result) with
  | node chip row lookup valid _ childrenIH =>
      obtain ⟨defn, found, lowered⟩ := Circuit.compile_find_chip compiled lookup
      have interface := Circuit.Compiler.lowerFunction_interface lowered
      have name := Circuit.findFunction_name found
      have body := Circuit.Compiler.lowerFunction_sound lowered valid childrenIH
      apply EvalCall.intro (defn := defn)
      · change program.findFunction? chip.name = some defn
        rw [interface.1, name]
        exact found
      · rw [← interface.2.1]
        exact valid.receive_arity.symm
      · exact body.toEvalExpr
  | nil => simp_all
  | cons _ _ headIH tailIH =>
      rename_i message member
      rcases List.mem_cons.mp member with same | member
      · subst message; exact headIH
      · exact tailIH message member

/-- Every closed derivation of a successfully compiled program has a source evaluation. -/
theorem compiler_sound [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system) : CompilationSound program system := by
  rintro name args result ⟨derivation⟩
  exact derivation_sound compiled derivation

/-- Induction over source evaluation reduces completeness to one compiled body. -/
theorem evaluation_complete [Field F] [DecidableEq F]
    {program : Program F} {system : Circuit.System F}
    (compiled : Circuit.compile program = .ok system)
    {name : String} {args : List F} {result : F} (evaluates : EvalCall program name args result) :
    Circuit.CircuitEvaluates system name args result := by
  induction evaluates using EvalCall.rec
    (motive_1 := fun locals expr value _ =>
      EvalExprWith (Circuit.CircuitEvaluates system) locals expr value)
    (motive_2 := fun locals exprs values _ =>
      EvalArgsWith (Circuit.CircuitEvaluates system) locals exprs values) with
  | literal => exact .literal
  | var lookup => exact .var lookup
  | neg _ ih => exact .neg ih
  | add _ _ leftIH rightIH => exact .add leftIH rightIH
  | sub _ _ leftIH rightIH => exact .sub leftIH rightIH
  | mul _ _ leftIH rightIH => exact .mul leftIH rightIH
  | div _ _ nonzero leftIH rightIH => exact .div leftIH rightIH nonzero
  | call _ _ argumentsIH calleeIH => exact .call argumentsIH calleeIH
  | matchValue _ selected _ scrutineeIH branchIH => exact .matchValue scrutineeIH selected branchIH
  | nil => exact .nil
  | cons _ _ headIH tailIH => exact .cons headIH tailIH
  | intro lookup arity _ bodyIH =>
      obtain ⟨chip, found, lowered⟩ := Circuit.compile_find_function compiled lookup
      obtain ⟨row, rowName, valid, receive, premises⟩ :=
        Circuit.Compiler.lowerFunction_complete lowered arity bodyIH
      have name := Circuit.findFunction_name lookup
      have rowLookup : system.findChip? row.chip = some chip := by
        rw [rowName, name]
        exact found
      obtain ⟨children⟩ := Circuit.derivations_nonempty_iff.mpr premises
      have tree := Circuit.Derivation.node chip row rowLookup valid children
      rw [receive, name] at tree
      exact ⟨tree⟩

/-- Successful compilation preserves and reflects evaluation as finite closed chip derivations. -/
theorem compiler_correct [Field F] [DecidableEq F] : CompilerCorrect F := by
  intro program system compiled name args result
  constructor
  · exact evaluation_complete compiled
  · exact compiler_sound compiled name args result

end Aiur.Scalar
