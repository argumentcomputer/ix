import Aiur.Scalar.Circuit.Compile
import Aiur.Scalar.Circuit.Selectors

namespace Aiur.Scalar.Circuit

/-- Fresh variables never invalidate the bounds of an earlier expression. -/
theorem ArithExpr.inBounds_mono {expr : ArithExpr F} {before after : Nat}
    (increase : before ≤ after) (bound : expr.inBounds before = true) :
    expr.inBounds after = true := by
  induction expr with
  | const => rfl
  | var id =>
      simp only [ArithExpr.inBounds, decide_eq_true_eq] at bound ⊢
      exact lt_of_lt_of_le bound increase
  | add _ _ leftIH rightIH | sub _ _ leftIH rightIH | mul _ _ leftIH rightIH =>
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at bound ⊢
      exact ⟨leftIH bound.1, rightIH bound.2⟩

theorem Send.inBounds_mono {send : Send F} {before after : Nat}
    (increase : before ≤ after) (bound : send.inBounds before = true) :
    send.inBounds after = true := by
  simp only [Send.inBounds, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at bound ⊢
  exact ⟨⟨lt_of_lt_of_le bound.1.1 increase, ArithExpr.inBounds_mono increase bound.1.2⟩,
    fun expr member => ArithExpr.inBounds_mono increase (bound.2 expr member)⟩

@[simp] theorem Compiler.lift_ok (value : α) (state : Compiler.BuildState F) :
    (liftM (.ok value : Except CompileError α) : Compiler.Build F α) state = .ok (value, state) := rfl

@[simp] theorem Compiler.lift_error (error : CompileError) (state : Compiler.BuildState F) :
    (liftM (.error error : Except CompileError α) : Compiler.Build F α) state = .error error := rfl

/-- Extending a fresh-variable assignment preserves every earlier polynomial. -/
theorem ArithExpr.denote_eq_of_agree [Field F] {left right : Var → F} {bound : Nat}
    (agree : ∀ id < bound, left id = right id) {expr : ArithExpr F}
    (inBounds : expr.inBounds bound = true) : expr.denote left = expr.denote right := by
  induction expr with
  | const => rfl
  | var id => exact agree id (by simpa [ArithExpr.inBounds] using inBounds)
  | add _ _ leftIH rightIH =>
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at inBounds
      simp only [ArithExpr.denote, leftIH inBounds.1, rightIH inBounds.2]
  | sub _ _ leftIH rightIH =>
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at inBounds
      simp only [ArithExpr.denote, leftIH inBounds.1, rightIH inBounds.2]
  | mul _ _ leftIH rightIH =>
      simp only [ArithExpr.inBounds, Bool.and_eq_true] at inBounds
      simp only [ArithExpr.denote, leftIH inBounds.1, rightIH inBounds.2]

theorem Compiler.fresh_run (state : Compiler.BuildState F) :
    Compiler.fresh.run state = .ok (state.nextVar, { state with nextVar := state.nextVar + 1 }) := rfl

@[simp] theorem Compiler.fresh_apply (state : Compiler.BuildState F) :
    Compiler.fresh state = .ok (state.nextVar, { state with nextVar := state.nextVar + 1 }) := rfl

theorem Compiler.constrain_run (state : Compiler.BuildState F) (polynomial : ArithExpr F) :
    (Compiler.constrain polynomial).run state =
      .ok ((), { state with constraints := state.constraints.push polynomial }) := rfl

@[simp] theorem Compiler.constrain_apply (polynomial : ArithExpr F) (state : Compiler.BuildState F) :
    Compiler.constrain polynomial state =
      .ok ((), { state with constraints := state.constraints.push polynomial }) := rfl

@[simp] theorem Compiler.guarded_apply (enable polynomial : ArithExpr F) (state : Compiler.BuildState F) :
    Compiler.guarded enable polynomial state =
      .ok ((), { state with constraints := state.constraints.push (.mul enable polynomial) }) := rfl

theorem satisfies_append [Field F] (left right : List (Constraint F)) (assignment : Var → F) :
    Satisfies (left ++ right) assignment ↔
      Satisfies left assignment ∧ Satisfies right assignment := by
  simp [Satisfies, or_imp, forall_and]

theorem Compiler.exclusionConstraints_satisfies [Field F]
    (selectors : List (ArithExpr F)) (assignment : Var → F) :
    Satisfies (Compiler.exclusionConstraints selectors) assignment ↔
      (selectors.map (ArithExpr.denote assignment)).Pairwise (fun left right => left * right = 0) := by
  induction selectors with
  | nil => simp [Compiler.exclusionConstraints, Satisfies]
  | cons selector rest ih =>
      rw [Compiler.exclusionConstraints, satisfies_append, ih]
      simp [Satisfies, ArithExpr.denote]

theorem ArithExpr.denote_foldl_add [Field F] (selectors : List (ArithExpr F))
    (initial : ArithExpr F) (assignment : Var → F) :
    (selectors.foldl ArithExpr.add initial).denote assignment =
      initial.denote assignment + (selectors.map (ArithExpr.denote assignment)).sum := by
  induction selectors generalizing initial with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons, ArithExpr.denote]
      exact add_assoc _ _ _

/-- The actual emitted equations are exactly the abstract selector conditions. -/
theorem Compiler.selectionConstraints_satisfies [Field F]
    (parent : ArithExpr F) (selectors : List (ArithExpr F)) (assignment : Var → F) :
    Satisfies (Compiler.selectionConstraints parent selectors) assignment ↔
      SelectorsValid (parent.denote assignment) (selectors.map (ArithExpr.denote assignment)) := by
  simp only [Compiler.selectionConstraints, satisfies_append,
    Compiler.exclusionConstraints_satisfies]
  have booleans : Satisfies
      (selectors.map (fun selector => .mul selector (.sub selector (.const 1)))) assignment ↔
      ∀ value ∈ selectors.map (ArithExpr.denote assignment), value * (value - 1) = 0 := by
    simp [Satisfies, ArithExpr.denote]
  rw [booleans]
  have sumEquation : Satisfies
      [.sub (selectors.foldl ArithExpr.add (.const 0)) parent] assignment ↔
      (selectors.map (ArithExpr.denote assignment)).sum = parent.denote assignment := by
    simp [Satisfies, ArithExpr.denote, ArithExpr.denote_foldl_add, sub_eq_zero]
  rw [sumEquation]
  exact ⟨fun ⟨⟨boolean, exclusive⟩, sum⟩ => ⟨boolean, exclusive, sum⟩,
    fun valid => ⟨⟨valid.boolean, valid.exclusive⟩, valid.sum⟩⟩

theorem Compiler.selectOne_run [Field F] (parent : ArithExpr F)
    (selectors : List (ArithExpr F)) (state : Compiler.BuildState F) :
    (Compiler.selectOne parent selectors).run state =
      .ok ((), { state with
        constraints := state.constraints ++ (Compiler.selectionConstraints parent selectors).toArray }) := rfl

@[simp] theorem Compiler.selectOne_apply [Field F] (parent : ArithExpr F)
    (selectors : List (ArithExpr F)) (state : Compiler.BuildState F) :
    Compiler.selectOne parent selectors state =
      .ok ((), { state with
        constraints := state.constraints ++ (Compiler.selectionConstraints parent selectors).toArray }) := rfl

/-- The compiler's input-variable environment agrees with the source parameter bindings. -/
theorem parameter_environment [Zero F] (params : List String) (row : Row F)
    (enough : params.length ≤ row.values.length) :
    (params.zip (List.range params.length)).map (fun binding => (binding.1, row.assignment binding.2)) =
      params.zip (row.values.take params.length) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left enough]
  · intro index leftBound rightBound
    have bound : index < params.length := by simpa using leftBound
    simp [Row.assignment, Nat.lt_of_lt_of_le bound enough]

theorem Row.assignment_of_prefix [Zero F] {before after : Row F}
    (extension : before.values.IsPrefix after.values) {id : Nat} (bound : id < before.values.length) :
    after.assignment id = before.assignment id := by
  have afterBound : id < after.values.length := lt_of_lt_of_le bound extension.length_le
  simp [Row.assignment, bound, afterBound, extension.getElem bound]

/-- Checking patterns gives distinct retained literals and excludes previously seen ones. -/
theorem Compiler.checkPatterns_spec [DecidableEq F] (function : String)
    (arms : List (Pattern F × Expr F)) (seen : List F) :
    Compiler.checkPatterns function arms seen = .ok () ↔
      (Compiler.literalPatterns arms).Nodup ∧
        ∀ value ∈ Compiler.literalPatterns arms, value ∉ seen := by
  induction arms generalizing seen with
  | nil => simp [Compiler.checkPatterns, Compiler.literalPatterns, pure, Except.pure]
  | cons arm rest ih =>
      rcases arm with ⟨pattern, body⟩
      cases pattern with
      | wildcard => simp [Compiler.checkPatterns, Compiler.literalPatterns, pure, Except.pure]
      | literal value =>
          by_cases member : value ∈ seen
          · simp [Compiler.checkPatterns, Compiler.literalPatterns, member, List.nodup_cons,
              bind, Except.bind]
          · have reduction : Compiler.checkPatterns function ((.literal value, body) :: rest) seen =
                Compiler.checkPatterns function rest (value :: seen) := by
              simp [Compiler.checkPatterns, member, bind, pure, Except.bind, Except.pure]
            rw [reduction, ih]
            simp only [Compiler.literalPatterns, List.nodup_cons]
            constructor
            · rintro ⟨distinct, fresh⟩
              refine ⟨⟨?_, distinct⟩, ?_⟩
              · intro repeated
                exact fresh value repeated (by simp)
              · intro next present
                rcases List.mem_cons.mp present with same | present
                · subst next; exact member
                · intro old
                  exact fresh next present (by simp [old])
            · rintro ⟨⟨notRepeated, distinct⟩, fresh⟩
              refine ⟨distinct, ?_⟩
              intro next present old
              rcases List.mem_cons.mp old with same | old
              · subst next; exact notRepeated present
              · exact fresh next (by simp [present]) old

theorem Compiler.lowerFunction_interface [Field F] [DecidableEq F]
    {defn : Function F} {chip : Chip F} (compiled : Compiler.lowerFunction defn = .ok chip) :
    chip.name = defn.name ∧ chip.arity = defn.params.length ∧ chip.output = defn.params.length := by
  unfold Compiler.lowerFunction at compiled
  cases lowered :
      (Compiler.lowerExpr defn.name (defn.params.zip (List.range defn.params.length))
        (.const 1) defn.body).run { nextVar := defn.params.length + 1 } with
  | error error => simp [lowered] at compiled
  | ok result =>
      rcases result with ⟨body, state⟩
      simp [lowered] at compiled
      cases compiled
      exact ⟨rfl, rfl, rfl⟩

private theorem forall₂_of_mapM_ok {f : α → Except ε β} {xs : List α} {ys : List β}
    (mapped : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil] at mapped; cases mapped; exact .nil
  | cons x xs ih =>
      cases hx : f x with
      | error error => simp [hx] at mapped; cases mapped
      | ok y =>
          cases hxs : xs.mapM f with
          | error error => simp [hx, hxs] at mapped; cases mapped
          | ok rest =>
              simp [hx, hxs] at mapped
              cases mapped
              exact .cons hx (ih hxs)

/-- The output list contains precisely the chip compiled from each source function. -/
theorem compile_functions [Field F] [DecidableEq F] {program : Program F} {system : System F}
    (compiled : compile program = .ok system) :
    List.Forall₂ (fun defn chip => Compiler.lowerFunction defn = .ok chip)
      program.functions system.chips := by
  unfold compile at compiled
  cases checked : typecheck program with
  | error error => simp [checked] at compiled; cases compiled
  | ok checkedUnit =>
      cases checkedUnit
      cases mapped : program.functions.mapM Compiler.lowerFunction with
      | error error => simp [checked, mapped] at compiled
      | ok chips =>
          simp [checked, mapped] at compiled
          subst system
          exact forall₂_of_mapM_ok mapped

private theorem lookup_functions [Field F] [DecidableEq F]
    {defns : List (Function F)} {chips : List (Chip F)}
    (compiled : List.Forall₂ (fun defn chip => Compiler.lowerFunction defn = .ok chip) defns chips)
    (name : String) :
    Option.Rel (fun defn chip => Compiler.lowerFunction defn = .ok chip)
      (defns.find? (·.name == name)) (chips.find? (·.name == name)) := by
  induction compiled with
  | nil => exact .none
  | cons head _ ih =>
      have names := (Compiler.lowerFunction_interface head).1
      simp only [List.find?_cons, names]
      split
      · exact .some head
      · exact ih

theorem compile_find_function [Field F] [DecidableEq F]
    {program : Program F} {system : System F} (compiled : compile program = .ok system)
    {name : String} {defn : Function F} (found : program.findFunction? name = some defn) :
    ∃ chip, system.findChip? name = some chip ∧ Compiler.lowerFunction defn = .ok chip := by
  have related := lookup_functions (compile_functions compiled) name
  change Option.Rel _ (program.findFunction? name) (system.findChip? name) at related
  rw [found] at related
  cases target : system.findChip? name with
  | none => rw [target] at related; cases related
  | some chip =>
      rw [target] at related
      cases related with
      | some lowered => exact ⟨chip, rfl, lowered⟩

theorem compile_find_chip [Field F] [DecidableEq F]
    {program : Program F} {system : System F} (compiled : compile program = .ok system)
    {name : String} {chip : Chip F} (found : system.findChip? name = some chip) :
    ∃ defn, program.findFunction? name = some defn ∧ Compiler.lowerFunction defn = .ok chip := by
  have related := lookup_functions (compile_functions compiled) name
  change Option.Rel _ (program.findFunction? name) (system.findChip? name) at related
  rw [found] at related
  cases source : program.findFunction? name with
  | none => rw [source] at related; cases related
  | some defn =>
      rw [source] at related
      cases related with
      | some lowered => exact ⟨defn, rfl, lowered⟩

theorem findFunction_name {program : Program F} {name : String} {defn : Function F}
    (found : program.findFunction? name = some defn) : defn.name = name := by
  have := List.find?_some found
  simpa using this

end Aiur.Scalar.Circuit
