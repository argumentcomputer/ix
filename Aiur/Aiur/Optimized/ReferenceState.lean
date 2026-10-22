import Aiur.Optimized.StateSemantics
import Aiur.Circuit.ValueWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

/-- Forget allocation roles, while retaining logical witness indices and all
guarded obligations. This reuses the reference compiler's witness extension
lemmas; it does not assume the two expression compilers are equivalent. -/
def State.toReference (state : State F) : Circuit.Compiler.BuildState F where
  nextVar := state.roles.size
  constraints := state.equations.map fun equation => .mul (state.activation equation.scope) equation.polynomial
  sends := state.calls.map fun call => ⟨call.channel, call.args, call.result, state.activation call.scope⟩
  memory := state.cells.map fun cell => ⟨cell.address, cell.value, state.activation cell.scope⟩

theorem State.valid_iff_reference (state : State F) (rom : WireROM F) (calls : Circuit.CallRelation F)
    (assignment : Witness → F) : state.Valid rom calls assignment ↔ state.toReference.Valid rom calls assignment := by
  have equations : Circuit.Satisfies state.toReference.constraints.toList assignment ↔
      ∀ equation ∈ state.equations.toList,
        (state.activation equation.scope).denote assignment * equation.polynomial.denote assignment = 0 := by
    simp only [State.toReference, Circuit.Satisfies, Scalar.Circuit.Satisfies, Array.toList_map, List.forall_mem_map,
      Scalar.Circuit.ArithExpr.denote]
  constructor
  · rintro ⟨localEquations, localCalls, localCells⟩
    refine ⟨equations.mpr localEquations, ?_, ?_⟩
    · simpa only [State.toReference, Array.toList_map, List.forall_mem_map, Call.message] using localCalls
    · simpa only [State.toReference, Array.toList_map, List.forall_mem_map, Circuit.MemoryLookup.Valid] using localCells
  · intro valid
    refine ⟨equations.mp valid.constraints, ?_, ?_⟩
    · simpa only [State.toReference, Array.toList_map, List.forall_mem_map, Call.message] using valid.calls
    · simpa only [State.toReference, Array.toList_map, List.forall_mem_map, Circuit.MemoryLookup.Valid] using valid.memory

theorem fresh_reference {role : Role} {id : Witness} {before after : State F}
    (compiled : fresh role before = .ok (id, after)) :
    Circuit.Compiler.fresh before.toReference = .ok (id, after.toReference) := by
  obtain ⟨rfl, rfl⟩ := fresh_eq compiled
  simp only [Circuit.Compiler.fresh_apply, State.toReference, State.activation, Array.size_push]

theorem equation_reference {scope : ScopeId} {polynomial : Polynomial F} {before after : State F}
    (compiled : equation scope polynomial before = .ok ((), after)) :
    Circuit.Compiler.constrain (.mul (before.activation scope) polynomial) before.toReference =
      .ok ((), after.toReference) := by
  obtain rfl := equation_eq compiled
  simp only [Circuit.Compiler.constrain_apply, State.toReference, State.activation, Array.map_push]

theorem freshList_reference {α : Type} {items : List α} {role : Role} {ids : List Witness}
    {before after : State F}
    (compiled : (items.mapM (fun _ => fresh role)) before = .ok (ids, after)) :
    Circuit.Compiler.freshWords items.length before.toReference = .ok (ids, after.toReference) := by
  induction items generalizing ids before with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
      simp [Circuit.Compiler.freshWords_apply]
  | cons item items ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨id, middle, headRun, tailBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp tailBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨rfl, rfl⟩ := fresh_eq headRun
      have reference := ih tailRun
      simp only [Circuit.Compiler.freshWords_apply, Except.ok.injEq, Prod.mk.injEq] at reference ⊢
      obtain ⟨rfl, stateEq⟩ := reference
      rw [← stateEq]
      simp [State.toReference, State.activation, List.range'_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem freshValue_reference {decls : Declarations} {role : Role} {type : Ty} {value : WireValue Witness}
    {before after : State F}
    (compiled : freshValue decls role type before = .ok (value, after)) :
    Circuit.Compiler.freshValue decls type before.toReference = .ok (value, after.toReference) := by
  simp only [freshValue] at compiled
  obtain ⟨layout, middle, expanded, rest⟩ := bind_ok.mp compiled
  obtain ⟨expansion, stateEq⟩ := getLayout_eq expanded
  subst middle
  obtain ⟨words, last, wordsRun, finished⟩ := bind_ok.mp rest
  obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
  have reference := freshList_reference wordsRun
  simp only [List.length_range] at reference
  simpa [Circuit.Compiler.freshValue, Circuit.Compiler.getLayout, expansion, Except.mapError,
    StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] using reference

abbrev Extension (rom : WireROM F) (calls : Circuit.CallRelation F) (before after : State F)
    (initial assignment : Witness → F) : Prop :=
  Circuit.Compiler.Extension rom calls before.toReference after.toReference initial assignment

theorem Extension.validAssignment {rom : WireROM F} {calls : Circuit.CallRelation F} {before after : State F}
    {initial assignment : Witness → F} (extension : Extension rom calls before after initial assignment) :
    after.Valid rom calls assignment :=
  (after.valid_iff_reference rom calls assignment).mpr (Circuit.Compiler.Extension.valid extension)

theorem fresh_complete {role : Role} {id : Witness} {before after : State F}
    (compiled : fresh role before = .ok (id, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial) (value : F) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      id < after.roles.size ∧ assignment id = value :=
  Circuit.Compiler.fresh_complete (fresh_reference compiled) layout
    ((before.valid_iff_reference rom calls initial).mp valid) value

theorem equation_complete {scope : ScopeId} {polynomial : Polynomial F} {before after : State F}
    (compiled : equation scope polynomial before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls assignment)
    (bounded : (Polynomial.mul (before.activation scope) polynomial).inBounds before.roles.size = true)
    (zero : (before.activation scope).denote assignment * polynomial.denote assignment = 0) :
    Extension rom calls before after assignment assignment :=
  Circuit.Compiler.constrain_complete (equation_reference compiled) layout
    ((before.valid_iff_reference rom calls assignment).mp valid) bounded zero

theorem freshValue_complete {decls : Declarations} {role : Role} {type : Ty} {vars : WireValue Witness}
    {before after : State F} (compiled : freshValue decls role type before = .ok (vars, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (value : WireValue F) (shape : value.type = type) (sized : value.Sized decls) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Circuit.Compiler.Bounded (F := F) after.roles.size (vars.map Polynomial.var) ∧ vars.map assignment = value :=
  Circuit.Compiler.freshValue_complete (freshValue_reference compiled) layout
    ((before.valid_iff_reference rom calls initial).mp valid) value shape sized

end Aiur.Optimized.Compiler
