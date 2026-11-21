import Aiur.Optimized.ValidationWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

/-- Construction context for a disabled source expression. Unconditional
selector equations are still witnessed; ordinary payload obligations vanish. -/
structure InactiveContext (rom : WireROM F) (calls : Circuit.CallRelation F)
    (scope : ScopeId) (state : State F) (assignment : Witness → F) : Prop where
  layout : state.toReference.WellFormed
  scopeLayout : state.Scoped
  valid : state.Valid rom calls assignment
  scopeValid : scope < state.scopes.size
  inactive : (state.activation scope).denote assignment = 0

namespace InactiveContext

variable {rom : WireROM F} {calls : Circuit.CallRelation F} {scope : ScopeId}
  {before after : State F} {initial assignment : Witness → F}

theorem advance (context : InactiveContext rom calls scope before initial)
    (structurePreserved : before.Extends after ∧ after.Scoped)
    (extension : Extension rom calls before after initial assignment) :
    InactiveContext rom calls scope after assignment :=
  ⟨extension.layout, structurePreserved.2, extension.validAssignment,
    structurePreserved.1.scopeValid context.scopeValid,
    (extension.activation structurePreserved.1 context.scopeLayout context.scopeValid).trans context.inactive⟩

theorem refl (context : InactiveContext rom calls scope before initial) :
    Extension rom calls before before initial initial :=
  .refl context.layout ((before.valid_iff_reference rom calls initial).mp context.valid)

theorem afterLower (context : InactiveContext rom calls scope before initial)
    {program : Program F} {function : String} {locals : Locals F} {expr : Expr F}
    {target : Option (WireValue Witness)} {value : Symbolic F}
    (compiled : lower program function locals scope expr target before = .ok (value, after))
    (extension : Extension rom calls before after initial assignment) :
    InactiveContext rom calls scope after assignment :=
  context.advance (lower_scoped compiled context.scopeLayout context.scopeValid) extension

theorem afterArgs (context : InactiveContext rom calls scope before initial)
    {program : Program F} {function : String} {locals : Locals F} {args : List (Expr F)}
    {values : List (Symbolic F)}
    (compiled : lowerArgs program function locals scope args before = .ok (values, after))
    (extension : Extension rom calls before after initial assignment) :
    InactiveContext rom calls scope after assignment :=
  context.advance (lowerArgs_scoped compiled context.scopeLayout context.scopeValid) extension

theorem destination (context : InactiveContext rom calls scope before initial)
    {decls : Declarations} {type : Ty} {target : Option (WireValue Witness)} {vars : WireValue Witness}
    (compiled : destination decls scope type target before = .ok (vars, after))
    (targetBound : ∀ candidate, target = some candidate →
      Circuit.Compiler.Bounded (F := F) before.roles.size (candidate.map Polynomial.var)) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      InactiveContext rom calls scope after assignment ∧
      Circuit.Compiler.Bounded (F := F) after.roles.size (vars.map Polynomial.var) := by
  obtain ⟨a, extension, bounded⟩ := destination_inactive compiled context.layout context.valid targetBound
  exact ⟨a, extension, context.advance
    ⟨destination_extends compiled, destination_scoped compiled context.scopeLayout⟩ extension, bounded⟩

theorem validate (context : InactiveContext rom calls scope before initial)
    {decls : Declarations} {value : Symbolic F}
    (compiled : validateValue decls scope value before = .ok ((), after))
    (bounded : Circuit.Compiler.Bounded before.roles.size value) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      InactiveContext rom calls scope after assignment := by
  obtain ⟨a, extension⟩ := validateValue_inactive compiled context.layout context.scopeLayout
    context.valid context.scopeValid bounded context.inactive
  exact ⟨a, extension, context.advance
    (validateValue_scoped compiled context.scopeLayout context.scopeValid) extension⟩

theorem equations (context : InactiveContext rom calls scope before initial)
    {conditions : List (Polynomial F)}
    (compiled : (do for condition in conditions do equation scope condition : Build F Unit)
      before = .ok ((), after))
    (bounded : ∀ condition ∈ conditions, condition.inBounds before.roles.size = true) :
    Extension rom calls before after initial initial ∧ InactiveContext rom calls scope after initial := by
  have extension := equations_complete compiled context.layout context.valid
    (context.scopeLayout.activation_bound scope) bounded (Or.inl context.inactive)
  exact ⟨extension, context.advance
    ⟨equations_grow compiled, equations_scoped compiled context.scopeLayout context.scopeValid⟩ extension⟩

theorem equal (context : InactiveContext rom calls scope before initial)
    {left right : Symbolic F} (compiled : equalValue scope left right before = .ok ((), after))
    (leftBound : Circuit.Compiler.Bounded before.roles.size left)
    (rightBound : Circuit.Compiler.Bounded before.roles.size right) :
    Extension rom calls before after initial initial ∧ InactiveContext rom calls scope after initial := by
  have extension := equalValue_complete compiled context.layout context.valid
    (context.scopeLayout.activation_bound scope) leftBound rightBound (Or.inl context.inactive)
  exact ⟨extension, context.advance (equalValue_structural compiled context.scopeLayout context.scopeValid) extension⟩

theorem equation (context : InactiveContext rom calls scope before initial)
    {polynomial : Polynomial F} (compiled : equation scope polynomial before = .ok ((), after))
    (bounded : polynomial.inBounds before.roles.size = true) :
    Extension rom calls before after initial initial ∧ InactiveContext rom calls scope after initial := by
  have extension := equation_complete compiled context.layout context.valid (by
    simp only [Scalar.Circuit.ArithExpr.inBounds, Bool.and_eq_true]
    exact ⟨context.scopeLayout.activation_bound scope, bounded⟩) (by simp [context.inactive])
  exact ⟨extension, context.advance
    ⟨equation_grow compiled, equation_scoped compiled context.scopeLayout context.scopeValid⟩ extension⟩

theorem fresh (context : InactiveContext rom calls scope before initial) {role : Role} {id : Witness}
    (compiled : fresh role before = .ok (id, after)) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      InactiveContext rom calls scope after assignment ∧ id < after.roles.size := by
  obtain ⟨a, extension, bounded, _⟩ := fresh_complete compiled context.layout context.valid (0 : F)
  exact ⟨a, extension, context.advance ⟨fresh_extends compiled, fresh_scoped compiled context.scopeLayout⟩ extension,
    bounded⟩

theorem cell (context : InactiveContext rom calls scope before initial) {address : Polynomial F} {value : Symbolic F}
    (compiled : (modify (fun state => {state with cells := state.cells.push ⟨scope, address, value⟩}) : Build F Unit)
      before = .ok ((), after))
    (addressBound : address.inBounds before.roles.size = true)
    (valueBound : Circuit.Compiler.Bounded before.roles.size value) :
    Extension rom calls before after initial initial ∧ InactiveContext rom calls scope after initial := by
  have extension := cell_complete compiled context.layout context.valid
    (context.scopeLayout.activation_bound scope) addressBound valueBound (by
      intro active
      have impossible : (0 : F) = 1 := context.inactive.symm.trans active
      exact False.elim (zero_ne_one impossible))
  change Except.ok ((), {before with cells := before.cells.push ⟨scope, address, value⟩}) = .ok ((), after) at compiled
  have stateEq := (Prod.mk.inj (Except.ok.inj compiled)).2
  subst after
  exact ⟨extension, context.advance (pushCell_scoped context.scopeLayout ⟨scope, address, value⟩ context.scopeValid) extension⟩

theorem call (context : InactiveContext rom calls scope before initial)
    {name : String} {args : List (Symbolic F)} {result : WireValue Witness}
    (compiled : (modify (fun state => {state with calls := state.calls.push ⟨scope, name, args, result⟩}) : Build F Unit)
      before = .ok ((), after))
    (argsBound : ∀ arg ∈ args, Circuit.Compiler.Bounded before.roles.size arg)
    (resultBound : Circuit.Compiler.Bounded (F := F) before.roles.size (result.map Polynomial.var)) :
    Extension rom calls before after initial initial ∧ InactiveContext rom calls scope after initial := by
  have extension := call_complete compiled context.layout context.valid
    (context.scopeLayout.activation_bound scope) argsBound resultBound (by
      intro active
      have impossible : (0 : F) = 1 := context.inactive.symm.trans active
      exact False.elim (zero_ne_one impossible))
  change Except.ok ((), {before with calls := before.calls.push ⟨scope, name, args, result⟩}) = .ok ((), after) at compiled
  have stateEq := (Prod.mk.inj (Except.ok.inj compiled)).2
  subst after
  exact ⟨extension, context.advance (pushCall_scoped context.scopeLayout ⟨scope, name, args, result⟩ context.scopeValid) extension⟩

theorem validateMany (context : InactiveContext rom calls scope before initial)
    {decls : Declarations} {values : List (Symbolic F)}
    (compiled : (forIn values PUnit.unit (fun value _ => do
      validateValue decls scope value
      pure (ForInStep.yield PUnit.unit)) : Build F PUnit) before = .ok (PUnit.unit, after))
    (bounded : ∀ value ∈ values, Circuit.Compiler.Bounded before.roles.size value) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      InactiveContext rom calls scope after assignment := by
  have wrapped : (do for value in values do validateValue decls scope value : Build F Unit)
      before = .ok ((), after) := bind_ok.mpr ⟨PUnit.unit, after, compiled, rfl⟩
  obtain ⟨a, extension⟩ := validateValues_inactive wrapped context.layout context.scopeLayout context.valid
    context.scopeValid bounded context.inactive
  have structural := forIn_scoped compiled context.scopeLayout context.scopeValid
    (fun _ _ {_ _} run layout bound => validateValue_scoped run layout bound)
  exact ⟨a, extension, context.advance structural extension⟩

theorem failure (context : InactiveContext rom calls scope before initial) {conditions : List (Polynomial F)}
    (compiled : failure scope conditions before = .ok ((), after))
    (bounded : ∀ condition ∈ conditions, condition.inBounds before.roles.size = true) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      InactiveContext rom calls scope after assignment := by
  obtain ⟨a, extension⟩ := failure_complete compiled context.layout context.valid
    (context.scopeLayout.activation_bound scope) bounded (Or.inl context.inactive)
  exact ⟨a, extension, context.advance (failure_scoped compiled context.scopeLayout context.scopeValid) extension⟩

theorem failures (context : InactiveContext rom calls scope before initial) {previous : List (List (Polynomial F))}
    (compiled : (forIn previous PUnit.unit (fun conditions _ => do
      Compiler.failure scope conditions
      pure (ForInStep.yield PUnit.unit)) : Build F PUnit) before = .ok (PUnit.unit, after))
    (bounded : ∀ conditions ∈ previous, ∀ condition ∈ conditions, condition.inBounds before.roles.size = true) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      InactiveContext rom calls scope after assignment := by
  induction previous generalizing before initial with
  | nil =>
      obtain ⟨_, stateEq⟩ := pure_ok.mp (by simpa only [List.forIn_nil] using compiled)
      subst after
      exact ⟨initial, context.refl, context⟩
  | cons conditions rest ih =>
      simp only [List.forIn_cons] at compiled
      obtain ⟨step, middle, stepRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨⟨⟩, last, headRun, headFinish⟩ := bind_ok.mp stepRun
      obtain ⟨rfl, stateEq⟩ := pure_ok.mp headFinish
      subst middle
      obtain ⟨a, headExt, headContext⟩ := context.failure headRun (bounded conditions (by simp))
      obtain ⟨b, tailExt, tailContext⟩ := ih headContext tailRun
        (fun conditions member condition inside => headExt.bound (bounded conditions (by simp [member]) condition inside))
      exact ⟨b, headExt.trans tailExt, tailContext⟩

end InactiveContext
end Aiur.Optimized.Compiler
