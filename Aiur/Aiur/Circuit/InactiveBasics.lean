import Aiur.Circuit.ValidationWitness
import Aiur.Circuit.ValueWitness
import Aiur.Circuit.SelectorWitness
import Aiur.Circuit.PatternWitness

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

theorem freshValue_zero_complete [Field F] {decls : Declarations} {type : Ty} {vars : WireValue Var}
    {before after : BuildState F} (compiled : freshValue decls type before = .ok (vars, after))
    {calls : CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Bounded (F := F) after.nextVar (vars.map ArithExpr.var) := by
  obtain ⟨typeLayout, expanded, _⟩ := freshValue_eq compiled
  obtain ⟨assignment, ext, bound, _⟩ := freshValue_complete compiled layout valid
    (zeroValue decls type) rfl (zeroValue_sized expanded)
  exact ⟨assignment, ext, bound⟩

theorem validateValue_inactive [Field F] [DecidableEq F] {decls : Declarations}
    {enable : ArithExpr F} {wire : Symbolic F} {before after : BuildState F}
    (compiled : validateValue decls enable wire before = .ok ((), after))
    {calls : CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (enableBound : enable.inBounds before.nextVar = true) (bounded : Bounded before.nextVar wire)
    (zero : enable.denote initial = 0) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  simp only [validateValue] at compiled
  obtain ⟨type, middle, expanded, run⟩ := bind_ok.mp compiled
  obtain ⟨_, rfl⟩ := getLayout_eq expanded
  exact validate_complete run layout valid enableBound bounded (Or.inl zero)

theorem validateValues_inactive [Field F] [DecidableEq F] {decls : Declarations}
    {enable : ArithExpr F} {wires : List (Symbolic F)} {before after : BuildState F}
    (compiled : validateValues decls enable wires before = .ok ((), after))
    {calls : CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (enableBound : enable.inBounds before.nextVar = true)
    (bounded : ∀ wire ∈ wires, Bounded before.nextVar wire) (zero : enable.denote initial = 0) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  induction wires generalizing before initial with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_ok.mp compiled
      exact ⟨initial, .refl layout valid⟩
  | cons wire wires ih =>
      simp only [validateValues] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨a, headExt⟩ := validateValue_inactive headRun layout valid enableBound (bounded _ (by simp)) zero
      obtain ⟨b, tailExt⟩ := ih tailRun headExt.layout headExt.valid (headExt.bound enableBound)
        (fun w h => (bounded w (by simp [h])).mono headExt.increase)
        ((headExt.polynomial enableBound).trans zero)
      exact ⟨b, headExt.trans tailExt⟩

end Aiur.Circuit.Compiler
