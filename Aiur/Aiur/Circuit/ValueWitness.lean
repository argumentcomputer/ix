import Aiur.Circuit.WitnessBasic

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

set_option maxHeartbeats 1000000

def zeroValue [Zero F] (decls : Declarations) (type : Ty) : WireValue F :=
  ⟨type, List.replicate (((decls.layout type).toOption.map Layout.width).getD 0) 0⟩

@[simp] theorem zeroValue_type [Zero F] (decls : Declarations) (type : Ty) :
    (zeroValue (F := F) decls type).type = type := rfl

theorem zeroValue_sized [Zero F] {decls : Declarations} {type : Ty} {layout : Layout}
    (expanded : decls.layout type = .ok layout) :
    (zeroValue (F := F) decls type).Sized decls := by
  exact ⟨layout, expanded, by simp [zeroValue, expanded, Except.toOption]⟩

/-- Bulk allocation permits any field words, including inactive noncanonical values. -/
theorem freshValue_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
    {decls : Declarations} {type : Ty} {vars : WireValue Var}
    (compiled : freshValue decls type before = .ok (vars, after)) {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (value : WireValue F) (shape : value.type = type) (sized : value.Sized decls) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Bounded (F := F) after.nextVar (vars.map ArithExpr.var) ∧ vars.map assignment = value := by
  obtain ⟨expanded, expansion, rfl, rfl⟩ := freshValue_eq compiled
  obtain ⟨other, otherExpansion, width⟩ := sized
  rw [shape, expansion] at otherExpansion
  cases otherExpansion
  let assignment : Var → F := fun id =>
    if id < before.nextVar then initial id else value.words.getD (id - before.nextVar) 0
  have agree : ∀ id < before.nextVar, assignment id = initial id := by
    intro id bound
    simp [assignment, bound]
  have assigned : (List.range' before.nextVar expanded.width).map assignment = value.words := by
    apply List.ext_getElem
    · simp [width]
    · intro i leftBound rightBound
      have bound : i < expanded.width := by simpa using leftBound
      simp [assignment, List.getElem_range', Nat.add_sub_cancel_left, List.getD,
        rightBound, Nat.not_lt.mpr (Nat.le_add_right _ _)]
  have oldValid := valid.of_agree layout agree
  refine ⟨assignment, ⟨by simp, agree, layout.grow (by simp),
    ⟨oldValid.constraints, oldValid.calls, oldValid.memory⟩⟩, ?_, ?_⟩
  · intro p member
    simp only [WireValue.words_map, List.mem_map] at member
    obtain ⟨id, member, rfl⟩ := member
    have bound : id < before.nextVar + expanded.width := by
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp member
      simpa using Nat.add_lt_add_left hi before.nextVar
    simpa [ArithExpr.inBounds, Scalar.Circuit.ArithExpr.inBounds] using bound
  · cases value
    simp_all [WireValue.map]

theorem freshValues_complete [Field F] {calls : CallRelation F} {before after : BuildState F}
    {decls : Declarations} {types : List Ty} {vars : List (WireValue Var)}
    (compiled : freshValues decls types before = .ok (vars, after)) {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (values : List (WireValue F)) (shape : values.map WireValue.type = types)
    (sized : ∀ value ∈ values, value.Sized decls) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      (∀ value ∈ vars, Bounded (F := F) after.nextVar (value.map ArithExpr.var)) ∧
      vars.map (WireValue.map assignment) = values := by
  induction values generalizing vars types before initial with
  | nil =>
      subst types
      simp only [freshValues, List.mapM_nil, pure_ok] at compiled
      obtain ⟨rfl, rfl⟩ := compiled
      exact ⟨initial, .refl layout valid, by simp, rfl⟩
  | cons value values ih =>
      subst types
      simp only [List.map_cons, freshValues, List.mapM_cons] at compiled
      obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨a, headExt, headBound, headValue⟩ :=
        freshValue_complete headRun layout valid value rfl (sized _ (by simp))
      obtain ⟨b, tailExt, tailBound, tailValue⟩ :=
        ih tailRun headExt.layout headExt.valid rfl (fun v h => sized v (by simp [h]))
      refine ⟨b, headExt.trans tailExt, ?_, ?_⟩
      · intro tree member
        rcases List.mem_cons.mp member with rfl | member
        · exact headBound.mono tailExt.increase
        · exact tailBound tree member
      · simp only [List.map_cons, tailExt.variables headBound, headValue, tailValue]

theorem constrainWords_complete [Field F] {calls : CallRelation F}
    {enable : ArithExpr F} {left right : List (ArithExpr F)} {before after : BuildState F}
    (compiled : constrainWords enable left right before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (enableBound : enable.inBounds before.nextVar = true)
    (leftBound : ∀ p ∈ left, p.inBounds before.nextVar = true)
    (rightBound : ∀ p ∈ right, p.inBounds before.nextVar = true)
    (equal : enable.denote assignment = 0 ∨
      left.map (ArithExpr.denote assignment) = right.map (ArithExpr.denote assignment)) :
    Extension rom calls before after assignment assignment := by
  induction left generalizing right before with
  | nil =>
      cases right with
      | nil =>
          obtain ⟨_, rfl⟩ := pure_ok.mp compiled
          exact .refl layout valid
      | cons => simp [constrainWords] at compiled
  | cons x xs ih =>
      cases right with
      | nil => simp [constrainWords] at compiled
      | cons y ys =>
          simp only [constrainWords] at compiled
          obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
          have headEq : enable.denote assignment = 0 ∨ x.denote assignment - y.denote assignment = 0 := by
            rcases equal with h | h
            · exact Or.inl h
            · exact Or.inr (sub_eq_zero.mpr (List.cons.inj h).1)
          have headExt := guarded_complete headRun layout valid enableBound
            (by simpa [Scalar.Circuit.ArithExpr.inBounds] using
              And.intro (leftBound _ (by simp)) (rightBound _ (by simp))) headEq
          have tailEq : enable.denote assignment = 0 ∨
              xs.map (ArithExpr.denote assignment) = ys.map (ArithExpr.denote assignment) := by
            rcases equal with h | h
            · exact Or.inl h
            · exact Or.inr (List.cons.inj h).2
          exact headExt.trans (ih tailRun headExt.layout headExt.valid (headExt.bound enableBound)
            (fun p h => headExt.bound (leftBound p (by simp [h])))
            (fun p h => headExt.bound (rightBound p (by simp [h]))) tailEq)

theorem constrainValue_complete [Field F] {calls : CallRelation F}
    {enable : ArithExpr F} {left right : Symbolic F} {before after : BuildState F}
    (compiled : constrainValue enable left right before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (enableBound : enable.inBounds before.nextVar = true)
    (leftBound : Bounded before.nextVar left) (rightBound : Bounded before.nextVar right)
    (equal : enable.denote assignment = 0 ∨
      left.map (ArithExpr.denote assignment) = right.map (ArithExpr.denote assignment)) :
    Extension rom calls before after assignment assignment := by
  simp only [constrainValue] at compiled
  split at compiled
  · simp [StateT.bind, bind, Except.bind] at compiled
  · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
    obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
    apply constrainWords_complete rest layout valid enableBound leftBound rightBound
    exact equal.imp_right (congrArg WireValue.words)

end Aiur.Circuit.Compiler
