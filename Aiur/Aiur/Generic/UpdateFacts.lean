import Aiur.Generic.StructFacts
import Aiur.Generic.UpdateSubstitution

namespace Aiur.Generic.UpdateLowering
open SourceSemantics
variable [Field F] [DecidableEq F] {world : Engine.World F} {calls : CallRelation F}

private theorem variable_iff (found : locals.find? (·.1 == name) = some (name, value)) :
    OpenCore.EvalExpr world calls locals (.var name) before result after ↔ result = value ∧ after = before := by
  constructor
  · intro ev; cases ev with
    | var lookup => rw [found] at lookup; cases lookup; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .var found

private theorem let_bind :
    OpenCore.EvalExpr world calls locals (.letValue (.bind name) input body) before result after ↔
      ∃ value middle, OpenCore.EvalExpr world calls locals input before value middle ∧
        OpenCore.EvalExpr world calls ((name, value) :: locals) body middle result after := by
  constructor
  · intro ev; cases ev with
    | letValue operand matched rest =>
        simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
        subst matched
        exact ⟨_, _, operand, rest⟩
  · rintro ⟨value, middle, operand, body⟩
    exact .letValue (bindings := [(name, value)]) operand (by simp [Aiur.Pattern.bindings]) body

private theorem wildcards (n : Nat) (values : List (SourceValue F)) :
    Aiur.Pattern.bindingsList (List.replicate n (.wildcard : Aiur.Pattern F)) values =
      if values.length = n then some [] else none := by
  induction n generalizing values with
  | zero => cases values <;> simp [Aiur.Pattern.bindingsList]
  | succ n ih =>
      cases values with
      | nil => simp [Aiur.Pattern.bindingsList]
      | cons v vs =>
          by_cases h : vs.length = n <;>
            simp [List.replicate_succ, Aiur.Pattern.bindingsList, Aiur.Pattern.bindings, ih, h]

private theorem shape_bindings (types : Types) (step : UpdateStep) (input : SourceValue F) :
    (shape types step).bindings input = (Update.unpack types step input).map (fun _ => []) := by
  cases owner : step.owner <;> cases input <;>
    simp [shape, Update.unpack, owner, Aiur.Pattern.bindings, wildcards,
      Update.nominalName, StructLowering.nominalName]
  all_goals split_ifs <;> simp_all [eq_comm]
  all_goals exact absurd rfl (by assumption)

private theorem unpack_spec (types : Types) (step : UpdateStep) (input : SourceValue F) (values : List (SourceValue F)) :
    Update.unpack types step input = some values ↔
      input = Update.pack types step values ∧ values.length = step.width := by
  cases owner : step.owner <;> cases input <;>
    simp [Update.unpack, Update.pack, owner]
  all_goals aesop

private theorem product_iff :
    OpenCore.EvalExpr world calls locals (product types step es) before result after ↔
      ∃ values, OpenCore.EvalArgs world calls locals es before values after ∧ result = Update.pack types step values := by
  cases owner : step.owner <;> simp only [product, Update.pack, owner]
  all_goals constructor
  all_goals first
    | (intro ev; cases ev; exact ⟨_, by assumption, rfl⟩)
    | (rintro ⟨values, ev, rfl⟩; first | exact .tuple ev | exact .construct ev)

private theorem component_iff
    (found : locals.find? (·.1 == "$withBase") = some ("$withBase", input))
    (unpacked : Update.unpack types step input = some values)
    (bound : index < step.width) :
    OpenCore.EvalExpr world calls locals (component types step index) before result after ↔
      values[index]? = some result ∧ after = before := by
  obtain ⟨rfl, length⟩ := (unpack_spec types step input values).mp unpacked
  cases owner : step.owner with
  | none =>
      simp only [component, owner]
      constructor
      · intro ev; cases ev with
        | project ev op =>
            obtain ⟨rfl, rfl⟩ := (variable_iff found).mp ev
            simpa [Update.pack, owner, projectValue, List.getElem?_eq_getElem (by omega : index < values.length)] using op
      · rintro ⟨h, rfl⟩
        exact .project (.var found) (by simp [Update.pack, owner, projectValue, h])
  | some type =>
      simp only [component, owner]
      rw [StructLowering.member_iff bound]
      simp only [variable_iff found]
      simp [memberValue, Update.pack, owner, constructorName, Update.nominalName, length,
        List.getElem?_eq_getElem (by omega : index < values.length)]
      cases ht : (type.subst types).toCore <;> simp [ht, and_comm]

private theorem args_mapM {es : List (Aiur.Expr F)} {xs : List A} {run : A → Option (SourceValue F)}
    (related : List.Forall₂ (fun e x => ∀ b v a,
      OpenCore.EvalExpr world calls locals e b v a ↔ run x = some v ∧ a = b) es xs) :
    OpenCore.EvalArgs world calls locals es before values after ↔ xs.mapM run = some values ∧ after = before := by
  induction related generalizing before values with
  | nil => constructor
           · intro ev; cases ev; exact ⟨rfl, rfl⟩
           · rintro ⟨h, rfl⟩; cases h; exact .nil
  | cons head _ ih =>
      constructor
      · intro ev; cases ev with
        | cons one rest =>
            obtain ⟨h, rfl⟩ := (head _ _ _).mp one
            obtain ⟨hs, rfl⟩ := ih.mp rest
            exact ⟨by simp [List.mapM_cons, h, hs], rfl⟩
      · rintro ⟨mapped, rfl⟩
        simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at mapped
        obtain ⟨v, hv, vs, hvs, same⟩ := mapped
        cases same
        exact .cons ((head _ _ _).mpr ⟨hv, rfl⟩) (ih.mpr ⟨hvs, rfl⟩)

/-- A path rebuilds precisely the selected component, preserving the operand's
heap and the identity of every untouched pointer. -/
theorem path_iff (target : UpdatePath)
    (newFound : locals.find? (·.1 == "$withNew") = some ("$withNew", replacement)) :
    OpenCore.EvalExpr world calls locals (path types target input) before result after ↔
      ∃ base, OpenCore.EvalExpr world calls locals input before base after ∧
        Update.replace types target base replacement = some result := by
  induction target generalizing locals input before result after with
  | nil =>
      simp only [path, Update.replace, Option.some.injEq]
      constructor
      · intro ev; cases ev with
        | letValue operand matched body =>
            simp only [Aiur.Pattern.bindings, Option.some.injEq] at matched
            subst matched
            obtain ⟨rfl, rfl⟩ := (variable_iff newFound).mp body
            exact ⟨_, operand, rfl⟩
      · rintro ⟨base, operand, rfl⟩
        exact .letValue (bindings := []) operand (by simp [Aiur.Pattern.bindings]) (.var newFound)
  | cons step rest ih =>
      have fields (base : SourceValue F) (parts : List (SourceValue F))
          (unpacked : Update.unpack types step base = some parts) (b w a) :
          OpenCore.EvalArgs world calls (("$withBase", base) :: locals)
            ((List.range step.width).map fun i =>
              if i == step.position then path types rest (component types step i) else component types step i) b w a ↔
            (parts.zipIdx.mapM fun (v, i) =>
              if i == step.position then Update.replace types rest v replacement else some v) = some w ∧ a = b := by
        apply args_mapM
        apply List.forall₂_of_length_eq_of_get
        · simp [(unpack_spec types step base parts).mp unpacked |>.2]
        · intro i hi hv b w a
          have length := ((unpack_spec types step base parts).mp unpacked).2
          have bound : i < step.width := by simpa using hi
          have partBound : i < parts.length := by omega
          simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range, List.getElem_zipIdx, Nat.zero_add]
          by_cases chosen : i == step.position
          · simp only [chosen, ↓reduceIte]
            rw [ih (locals := ("$withBase", base) :: locals) (by simpa using newFound)]
            simp only [component_iff (locals := ("$withBase", base) :: locals) (input := base) (by simp) unpacked bound,
              List.getElem?_eq_getElem partBound, Option.some.injEq]
            constructor
            · rintro ⟨v, ⟨rfl, rfl⟩, h⟩; exact ⟨h, rfl⟩
            · rintro ⟨h, rfl⟩; exact ⟨_, ⟨rfl, rfl⟩, h⟩
          · simpa [chosen, List.getElem?_eq_getElem partBound, eq_comm] using
              (component_iff (world := world) (calls := calls) (before := b) (after := a) (result := w)
                (by simp : (("$withBase", base) :: locals).find? (·.1 == "$withBase") = some ("$withBase", base)) unpacked bound)
      rw [path, let_bind]
      constructor
      · rintro ⟨base, middle, operand, body⟩
        cases body with
        | letValue inspected matched reconstructed =>
            obtain ⟨rfl, rfl⟩ := (variable_iff (value := base) (by simp)).mp inspected
            rw [shape_bindings] at matched
            obtain ⟨parts, unpacked, rfl⟩ := Option.map_eq_some_iff.mp matched
            obtain ⟨values, ev, rfl⟩ := product_iff.mp reconstructed
            obtain ⟨mapped, rfl⟩ := (fields _ parts unpacked _ _ _).mp ev
            exact ⟨_, operand, by simp only [Update.replace, unpacked, bind, Option.bind_some, mapped, Option.pure_def]⟩
      · rintro ⟨base, operand, updated⟩
        simp only [Update.replace, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at updated
        obtain ⟨parts, unpacked, values, mapped, same⟩ := updated
        subst result
        refine ⟨base, after, operand, ?_⟩
        apply OpenCore.EvalExpr.letValue (input := base) (bindings := []) (.var (by simp))
        · rw [shape_bindings, unpacked]; rfl
        · apply product_iff.mpr
          exact ⟨values, (fields base parts unpacked _ _ _).mpr ⟨mapped, rfl⟩, rfl⟩

private theorem project_variable
    (found : locals.find? (·.1 == name) = some (name, .tuple values)) :
    OpenCore.EvalExpr world calls locals (.project (.var name) index) before result after ↔
      values[index]? = some result ∧ after = before := by
  constructor
  · intro ev; cases ev with
    | project operand projected =>
        obtain ⟨rfl, rfl⟩ := (variable_iff found).mp operand
        cases h : values[index]? <;> simp [projectValue, h] at projected
        subst projected
        exact ⟨rfl, rfl⟩
  · rintro ⟨h, rfl⟩
    exact .project (.var found) (by simp [projectValue, h])

private theorem sequence_iff (paths : List UpdatePath)
    (inputFound : locals.find? (·.1 == "$withInputs") = some ("$withInputs", .tuple inputs))
    (currentFound : locals.find? (·.1 == "$withCurrent") = some ("$withCurrent", base))
    (length : (inputs.drop index).length = paths.length) :
    OpenCore.EvalExpr world calls locals (sequence types paths index) before result after ↔
      Update.apply types paths base (inputs.drop index) = some result ∧ after = before := by
  induction paths generalizing locals index base with
  | nil =>
      have empty : inputs.drop index = [] := List.length_eq_zero_iff.mp length
      simp only [sequence, variable_iff currentFound, empty, Update.apply, Option.some.injEq, eq_comm]
  | cons target targets ih =>
      cases dropped : inputs.drop index with
      | nil => simp [dropped] at length
      | cons replacement replacements =>
          have atIndex : inputs[index]? = some replacement := by
            have h := congrArg (fun xs => xs[0]?) dropped
            simpa using h
          have nextDrop : inputs.drop (index + 1) = replacements := by
            rw [← List.drop_drop, dropped]; rfl
          have nextLength : (inputs.drop (index + 1)).length = targets.length := by
            simp [nextDrop, dropped] at length ⊢
            exact length
          rw [sequence, let_bind]
          constructor
          · rintro ⟨newValue, middle, operand, body⟩
            obtain ⟨atNew, rfl⟩ := (project_variable inputFound).mp operand
            have same : newValue = replacement := by rw [atIndex] at atNew; exact (Option.some.inj atNew).symm
            subst newValue
            obtain ⟨nextValue, finalHeap, changed, continued⟩ := let_bind.mp body
            obtain ⟨oldValue, original, updated⟩ := (path_iff target (replacement := replacement) (by simp)).mp changed
            obtain ⟨sameOld, rfl⟩ := (variable_iff (value := base) (by simpa using currentFound)).mp original
            subst oldValue
            have continuation := (ih (base := nextValue) (by simpa using inputFound) (by simp) nextLength).mp continued
            rcases continuation with ⟨tail, rfl⟩
            exact ⟨by simpa [Update.apply, dropped, updated, nextDrop] using tail, rfl⟩
          · rintro ⟨updated, sameHeap⟩
            subst after
            simp only [dropped, Update.apply, bind, Option.bind_eq_some_iff] at updated
            obtain ⟨nextValue, changed, continued⟩ := updated
            refine ⟨replacement, before, (project_variable inputFound).mpr ⟨atIndex, rfl⟩, ?_⟩
            apply let_bind.mpr
            refine ⟨nextValue, before, ?_, ?_⟩
            · apply (path_iff target (replacement := replacement) (by simp)).mpr
              exact ⟨base, .var (by simpa using currentFound), changed⟩
            · apply (ih (base := nextValue) (by simpa using inputFound) (by simp) nextLength).mpr
              exact ⟨by simpa only [nextDrop] using continued, rfl⟩

private theorem apply_length {paths : List UpdatePath} {replacements : List (SourceValue F)}
    (updated : Update.apply types paths base replacements = some result) : replacements.length = paths.length := by
  induction paths generalizing base replacements with
  | nil => cases replacements <;> simp_all [Update.apply]
  | cons path paths ih =>
      cases replacements with
      | nil => simp [Update.apply] at updated
      | cons v vs =>
          simp only [Update.apply, bind, Option.bind_eq_some_iff] at updated
          obtain ⟨value, _, updated⟩ := updated
          simpa using ih updated

/-- Functional updates and their late reconstruction have exactly the same
operand evaluations, results, and heap effects. No typing premise or semantic
assumption about the compiler is needed for this local equivalence. -/
theorem expression_iff :
    OpenCore.EvalExpr world calls locals (expression types paths operands) before result after ↔
      ∃ values, OpenCore.EvalArgs world calls locals operands before values after ∧
        Update.value types paths values = .ok result := by
  rw [expression, let_bind]
  constructor
  · rintro ⟨input, middle, evaluated, body⟩
    cases evaluated with
    | tuple args =>
        rename_i values
        cases body with
        | letValue inspected matched body =>
            have inspectedResult := (variable_iff (value := .tuple values) (by simp)).mp inspected
            obtain ⟨sameValue, sameHeap⟩ := inspectedResult
            subst_vars
            simp only [Aiur.Pattern.bindings, wildcards] at matched
            split at matched
            · rename_i length
              simp only [Option.some.injEq] at matched
              subst matched
              cases values with
              | nil => simp at length
              | cons base replacements =>
                  obtain ⟨current, last, projected, continued⟩ := let_bind.mp body
                  obtain ⟨atCurrent, sameHeap⟩ := (project_variable (by simp :
                    (("$withInputs", .tuple (base :: replacements)) :: locals).find? (·.1 == "$withInputs") =
                      some ("$withInputs", .tuple (base :: replacements)))).mp projected
                  have same : current = base := by simpa using atCurrent.symm
                  subst current
                  subst last
                  have rel := (sequence_iff paths (inputs := base :: replacements) (base := base) (by simp) (by simp)
                    (by simpa using length)).mp continued
                  obtain ⟨updated, sameHeap⟩ := rel
                  subst after
                  exact ⟨_, args, by simp only [Update.value, List.drop_succ_cons, List.drop_zero] at updated ⊢; rw [updated]⟩
            · cases matched
  · rintro ⟨values, args, updated⟩
    cases values with
    | nil => simp [Update.value] at updated
    | cons base replacements =>
        cases applied : Update.apply types paths base replacements with
        | none => simp [Update.value, applied] at updated
        | some output =>
            have same : output = result := by simpa [Update.value, applied] using updated
            subst result
            have length := apply_length applied
            refine ⟨.tuple (base :: replacements), after, .tuple args, ?_⟩
            apply OpenCore.EvalExpr.letValue (input := .tuple (base :: replacements)) (bindings := []) (.var (by simp))
            · simp [Aiur.Pattern.bindings, wildcards, length]
            · apply let_bind.mpr
              refine ⟨base, after, ?_, ?_⟩
              · exact .project (input := .tuple (base :: replacements)) (.var (by simp)) (by simp [projectValue])
              · apply (sequence_iff paths (inputs := base :: replacements) (base := base) (by simp) (by simp) (by simpa using length)).mpr
                exact ⟨by simpa using applied, rfl⟩

end Aiur.Generic.UpdateLowering
