import Aiur.Generic.Lower
import Aiur.Generic.OpenCore

namespace Aiur.Generic

variable {calls : CallRelation F}


@[simp] theorem array_toCore (element : Ty) (length : Nat) :
    (Ty.array element length).toCore = .tuple (List.replicate length element.toCore) := by rw [Ty.toCore]

@[simp] theorem lower_array (env) (items : List (Expr α)) :
    (Expr.array items).lower env = .tuple (items.map (Expr.lower env)) := by rw [Expr.lower]

@[simp] theorem lower_index (env) (value : Expr α) (index : Nat) :
    (Expr.index value index).lower env = .project (value.lower env) index := by rw [Expr.lower]

@[simp] theorem lower_repeat (env) (value : Expr α) (length : Nat) :
    (Expr.repeat value length).lower env = ArrayLowering.repeatValue (value.lower env) length := by rw [Expr.lower]

@[simp] theorem lower_slice (env) (value : Expr α) (start stop : Nat) :
    (Expr.slice value start (some stop)).lower env = ArrayLowering.sliceValue (value.lower env) start stop := by rw [Expr.lower]

namespace ArrayLowering
variable [Field F] [DecidableEq F] {world : Engine.World F}

theorem repeatArgs_iff {locals : Environment F Nat} {name : String} {value : SourceValue F}
    {length : Nat} {before after : Heap F} {values : List (SourceValue F)} :
    OpenCore.EvalArgs world calls ((name, value) :: locals) (List.replicate length (.var name)) before values after ↔
      values = List.replicate length value ∧ after = before := by
  induction length generalizing before values with
  | zero =>
      constructor
      · intro h; cases h; exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩; exact .nil
  | succ length ih =>
      constructor
      · intro h
        cases h with
        | cons head tail =>
            cases head with
            | var lookup =>
                simp only [List.find?_cons, beq_self_eq_true,
                  Option.some.injEq, Prod.mk.injEq, true_and] at lookup
                cases lookup
                obtain ⟨rfl, rfl⟩ := ih.mp tail
                exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, rfl⟩
        exact .cons (.var (by simp)) (ih.mpr ⟨rfl, rfl⟩)

/-- Repetition executes its operand exactly once, sharing any allocated pointers
and nondeterministic result. This includes length zero and preserves the heap. -/
theorem repeatValue_iff {locals : Environment F Nat} {operand : Aiur.Expr F}
    {length : Nat} {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (repeatValue operand length) before result after ↔
      ∃ value, OpenCore.EvalExpr world calls locals operand before value after ∧
        result = .tuple (List.replicate length value) := by
  constructor
  · intro h
    cases h with
    | letValue value matched body =>
        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
        subst_vars
        cases body with
        | tuple items =>
            obtain ⟨rfl, rfl⟩ := repeatArgs_iff.mp items
            exact ⟨_, value, rfl⟩
  · rintro ⟨value, evaluated, rfl⟩
    exact .letValue (bindings := [("$array", value)]) evaluated (by simp [Aiur.Pattern.bindings])
      (.tuple (repeatArgs_iff.mpr ⟨rfl, rfl⟩))

theorem projectArgs_iff {locals : Environment F Nat} {name : String} {value : SourceValue F}
    {indices : List Nat} {before after : Heap F} {values : List (SourceValue F)} :
    OpenCore.EvalArgs world calls ((name, value) :: locals)
        (indices.map (fun i => .project (.var name) i)) before values after ↔
      indices.mapM (projectValue value) = .ok values ∧ after = before := by
  induction indices generalizing before values with
  | nil =>
      constructor
      · intro h; cases h; exact ⟨rfl, rfl⟩
      · rintro ⟨h, rfl⟩
        have : values = [] := by simpa [pure, Except.pure] using h.symm
        subst values
        exact .nil
  | cons index indices ih =>
      constructor
      · intro h
        cases h with
        | cons head tail =>
            cases head with
            | project expr projected =>
                cases expr with
                | var lookup =>
                    simp only [List.find?_cons, beq_self_eq_true,
                      Option.some.injEq, Prod.mk.injEq, true_and] at lookup
                    cases lookup
                    obtain ⟨rest, rfl⟩ := ih.mp tail
                    exact ⟨by simp [List.mapM_cons, projected, rest, bind, Except.bind, pure, Except.pure], rfl⟩
      · rintro ⟨h, rfl⟩
        cases projected : projectValue value index with
        | error e => simp [List.mapM_cons, projected, bind, Except.bind, pure, Except.pure] at h
        | ok head =>
            cases rest : indices.mapM (projectValue value) with
            | error e => simp [List.mapM_cons, projected, rest, bind, Except.bind, pure, Except.pure] at h
            | ok tail =>
                have : values = head :: tail := by simpa [List.mapM_cons, projected, rest, bind, Except.bind, pure, Except.pure] using h.symm
                subst values
                exact .cons (.project (.var (by simp)) projected) (ih.mpr ⟨rest, rfl⟩)

/-- A slice evaluates the array once, then takes only the chosen fixed indices.
The projection sequence itself leaves the heap unchanged, including empty slices. -/
theorem sliceValue_iff {locals : Environment F Nat} {operand : Aiur.Expr F}
    {start stop : Nat} {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (sliceValue operand start stop) before result after ↔
      ∃ value values, OpenCore.EvalExpr world calls locals operand before value after ∧
        ((List.range (stop - start)).map (start + ·)).mapM (projectValue value) = .ok values ∧
        result = .tuple values := by
  have indices : ((List.range (stop - start)).map (start + ·)).map
      (fun i => (Aiur.Expr.project (.var "$array") i : Aiur.Expr F)) =
      (List.range (stop - start)).map (fun i => .project (.var "$array") (start + i)) := by
    simp only [List.map_map, Function.comp_def]
  constructor
  · intro h
    cases h with
    | letValue value matched body =>
        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
        subst_vars
        cases body with
        | tuple items =>
            rw [← indices] at items
            obtain ⟨projected, rfl⟩ := projectArgs_iff.mp items
            exact ⟨_, _, value, projected, rfl⟩
  · rintro ⟨value, values, evaluated, projected, rfl⟩
    apply OpenCore.EvalExpr.letValue (bindings := [("$array", value)]) evaluated (by simp [Aiur.Pattern.bindings])
    apply OpenCore.EvalExpr.tuple
    rw [← indices]
    exact projectArgs_iff.mpr ⟨projected, rfl⟩

end ArrayLowering
end Aiur.Generic
