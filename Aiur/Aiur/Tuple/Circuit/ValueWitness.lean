import Aiur.Tuple.Circuit.WitnessBasic

namespace Aiur.Tuple.Circuit.Compiler

set_option maxHeartbeats 1000000

def zeroValue [Zero F] : Ty → Value F
  | .field => .field 0
  | .tuple types => .tuple (types.map zeroValue)
termination_by type => sizeOf type

@[simp] theorem zeroValue_type [Zero F] (type : Ty) : (zeroValue (F := F) type).type = type := by
  cases type with
  | field => simp [zeroValue, Value.type]
  | tuple types =>
      simp only [zeroValue, Value.type, List.map_map, Ty.tuple.injEq]
      conv_rhs => rw [← List.map_id types]
      apply List.map_congr_left
      intro type member
      exact zeroValue_type type
termination_by sizeOf type
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  omega

mutual
  /-- Every value of the declared shape can be assigned to its fresh field leaves. -/
  theorem freshValue_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
      {type : Ty} {vars : Value Var}
      (compiled : freshValue type before = .ok (vars, after)) {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (value : Value F) (shape : value.type = type) :
      ∃ assignment, Extension calls before after initial assignment ∧
        Bounded (F := F) after.nextVar (vars.map ArithExpr.var) ∧ vars.map assignment = value := by
    cases type with
    | field =>
        cases value with
        | tuple => simp [Value.type] at shape
        | field value =>
            simp only [freshValue] at compiled
            obtain ⟨id, middle, allocated, finished⟩ := bind_ok.mp compiled
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨assignment, extension, bound, assigned⟩ := fresh_complete allocated layout valid value
            exact ⟨assignment, extension, by
              simpa [Value.map, ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using bound,
              by simp [Value.map, assigned]⟩
    | tuple types =>
        cases value with
        | field => simp [Value.type] at shape
        | tuple values =>
            simp only [Value.type, Ty.tuple.injEq] at shape
            simp only [freshValue] at compiled
            obtain ⟨vars, middle, allocated, finished⟩ := bind_ok.mp compiled
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨assignment, extension, bound, assigned⟩ :=
              freshValues_complete allocated layout valid values shape
            exact ⟨assignment, extension, by simpa [Value.map] using bound,
              by simp only [Value.map, assigned]⟩
  termination_by sizeOf type
  decreasing_by all_goals simp_all only [Ty.tuple.sizeOf_spec]; all_goals omega

  theorem freshValues_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
      {types : List Ty} {vars : List (Value Var)}
      (compiled : freshValues types before = .ok (vars, after)) {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls initial)
      (values : List (Value F)) (shape : values.map Value.type = types) :
      ∃ assignment, Extension calls before after initial assignment ∧
        (∀ value ∈ vars, Bounded (F := F) after.nextVar (value.map ArithExpr.var)) ∧
        vars.map (Value.map assignment) = values := by
    cases types with
    | nil =>
        cases values with
        | cons => simp at shape
        | nil =>
            simp only [freshValues, pure_ok] at compiled
            obtain ⟨rfl, rfl⟩ := compiled
            exact ⟨initial, .refl layout valid, by simp, rfl⟩
    | cons type types =>
        cases values with
        | nil => simp at shape
        | cons value values =>
            simp only [List.map_cons, List.cons.injEq] at shape
            simp only [freshValues] at compiled
            obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
            obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
            obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
            obtain ⟨a, headExt, headBound, headValue⟩ := freshValue_complete headRun layout valid value shape.1
            obtain ⟨b, tailExt, tailBound, tailValue⟩ :=
              freshValues_complete tailRun headExt.layout headExt.valid values shape.2
            refine ⟨b, headExt.trans tailExt, ?_, ?_⟩
            · intro tree member
              rcases List.mem_cons.mp member with rfl | member
              · exact headBound.mono tailExt.increase
              · exact tailBound tree member
            · simp only [List.map_cons, tailExt.variables headBound, headValue, tailValue]
  termination_by sizeOf types
  decreasing_by all_goals simp_all only [List.cons.sizeOf_spec]; all_goals omega
end

mutual
  theorem constrainValue_complete [Field F] {calls : CallRelation F}
      {enable : ArithExpr F} {left right : Symbolic F} {before after : BuildState F}
      (compiled : constrainValue enable left right before = .ok ((), after)) {assignment : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls assignment)
      (enableBound : enable.inBounds before.nextVar = true)
      (leftBound : Bounded before.nextVar left) (rightBound : Bounded before.nextVar right)
      (equal : enable.denote assignment = 0 ∨
        left.map (ArithExpr.denote assignment) = right.map (ArithExpr.denote assignment)) :
      Extension calls before after assignment assignment := by
    cases left with
    | field left =>
        cases right with
        | tuple => simp [constrainValue] at compiled
        | field right =>
            simp only [constrainValue, guarded] at compiled
            apply constrain_complete compiled layout valid
            · simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using
                And.intro enableBound (And.intro (bounded_field.mp leftBound) (bounded_field.mp rightBound))
            · change enable.denote assignment * (left.denote assignment - right.denote assignment) = 0
              rcases equal with disabled | equal
              · simp [disabled]
              · simp only [Value.map, Value.field.injEq] at equal
                simp [equal]
    | tuple left =>
        cases right with
        | field => simp [constrainValue] at compiled
        | tuple right =>
            simp only [constrainValue] at compiled
            apply constrainValues_complete compiled layout valid enableBound
              (bounded_tuple.mp leftBound) (bounded_tuple.mp rightBound)
            simpa only [Value.map, Value.tuple.injEq] using equal
  termination_by sizeOf left

  theorem constrainValues_complete [Field F] {calls : CallRelation F}
      {enable : ArithExpr F} {left right : List (Symbolic F)} {before after : BuildState F}
      (compiled : constrainValues enable left right before = .ok ((), after)) {assignment : Var → F}
      (layout : before.WellFormed) (valid : before.Valid calls assignment)
      (enableBound : enable.inBounds before.nextVar = true)
      (leftBound : ∀ value ∈ left, Bounded before.nextVar value)
      (rightBound : ∀ value ∈ right, Bounded before.nextVar value)
      (equal : enable.denote assignment = 0 ∨
        left.map (Value.map (ArithExpr.denote assignment)) = right.map (Value.map (ArithExpr.denote assignment))) :
      Extension calls before after assignment assignment := by
    cases left with
    | nil =>
        cases right with
        | nil =>
            simp only [constrainValues, pure_ok, true_and] at compiled
            subst after
            exact .refl layout valid
        | cons => simp [constrainValues] at compiled
    | cons left ls =>
        cases right with
        | nil => simp [constrainValues] at compiled
        | cons right rs =>
            simp only [constrainValues] at compiled
            obtain ⟨finished, middle, headRun, tailRun⟩ := bind_ok.mp compiled
            cases finished
            have headEq : enable.denote assignment = 0 ∨
                left.map (ArithExpr.denote assignment) = right.map (ArithExpr.denote assignment) := by
              rcases equal with disabled | equal
              · exact Or.inl disabled
              · exact Or.inr (List.cons.inj equal).1
            have tailEq : enable.denote assignment = 0 ∨
                ls.map (Value.map (ArithExpr.denote assignment)) = rs.map (Value.map (ArithExpr.denote assignment)) := by
              rcases equal with disabled | equal
              · exact Or.inl disabled
              · exact Or.inr (List.cons.inj equal).2
            have headExt := constrainValue_complete headRun layout valid enableBound
              (leftBound left (by simp)) (rightBound right (by simp)) headEq
            have tailExt := constrainValues_complete tailRun headExt.layout headExt.valid
              (Scalar.Circuit.ArithExpr.inBounds_mono headExt.increase enableBound)
              (fun value member => (leftBound value (by simp [member])).mono headExt.increase)
              (fun value member => (rightBound value (by simp [member])).mono headExt.increase) tailEq
            exact headExt.trans tailExt
  termination_by sizeOf left
end

end Aiur.Tuple.Circuit.Compiler
