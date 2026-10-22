import Aiur.Generic.PatternLowering
import Aiur.Generic.OpenCore
import Aiur.Generic.BindingOrderFacts
import Mathlib.Data.List.Forall2

namespace Aiur.Generic.PatternLowering

variable {calls : CallRelation F}


def lookupValues (locals : Environment F Nat) : List String → Option (List (SourceValue F))
  | [] => some []
  | name :: names => do
      let (_, value) ← locals.find? (·.1 == name)
      return value :: (← lookupValues locals names)

def resolveBindings (links : List (String × String)) (locals : Environment F Nat) :
    Option (Environment F Nat) :=
  (lookupValues locals (links.map Prod.snd)).map ((links.map Prod.fst).zip ·)

@[simp] theorem resolveBindings_nil : resolveBindings [] locals = some [] := rfl

theorem resolveBindings_cons (user temp : String) (links : List (String × String))
    (locals : Environment F Nat) :
    resolveBindings ((user, temp) :: links) locals = do
      let (_, value) ← locals.find? (·.1 == temp)
      return (user, value) :: (← resolveBindings links locals) := by
  unfold resolveBindings
  simp only [List.map_cons, lookupValues]
  cases locals.find? (·.1 == temp) with
  | none => rfl
  | some pair => cases lookupValues locals (links.map Prod.snd) <;> rfl

theorem resolveBindings_names {links : List (String × String)}
    {locals bindings : Environment F Nat} (found : resolveBindings links locals = some bindings) :
    bindings.map Prod.fst = links.map Prod.fst := by
  induction links generalizing bindings with
  | nil => simp_all
  | cons link links ih =>
      rcases link with ⟨user, temp⟩
      rw [resolveBindings_cons] at found
      cases head : locals.find? (·.1 == temp) with
      | none => simp [head] at found
      | some pair =>
          cases tail : resolveBindings links locals with
          | none => simp [head, tail] at found
          | some rest =>
              simp [head, tail] at found
              subst bindings
              simp only [List.map_cons, ih tail]

theorem resolveBindings_append (left right : List (String × String)) (locals : Environment F Nat) :
    resolveBindings (left ++ right) locals = do
      return (← resolveBindings left locals) ++ (← resolveBindings right locals) := by
  induction left with
  | nil =>
      simp only [List.nil_append, resolveBindings_nil]
      cases resolveBindings right locals <;> rfl
  | cons pair left ih =>
      rcases pair with ⟨user, temp⟩
      rw [List.cons_append, resolveBindings_cons, resolveBindings_cons, ih]
      cases locals.find? (·.1 == temp) <;>
        cases resolveBindings left locals <;> cases resolveBindings right locals <;> rfl

theorem resolveBindings_congr {links : List (String × String)} {left right : Environment F Nat}
    (agree : ∀ name ∈ links.map Prod.snd, left.find? (·.1 == name) = right.find? (·.1 == name)) :
    resolveBindings links left = resolveBindings links right := by
  induction links with
  | nil => rfl
  | cons pair links ih =>
      rcases pair with ⟨user, temp⟩
      rw [resolveBindings_cons, resolveBindings_cons, agree temp (by simp), ih]
      intro n hn; exact agree n (by simp [hn])

theorem lookupValues_length (found : lookupValues locals names = some values) :
    names.length = values.length := by
  induction names generalizing values with
  | nil => simp [lookupValues] at found; subst values; rfl
  | cons n ns ih =>
      cases head : locals.find? (·.1 == n) with
      | none => simp [lookupValues, head] at found
      | some pair =>
          cases tail : lookupValues locals ns with
          | none => simp [lookupValues, List.mapM_cons, head, tail] at found
          | some rest =>
              have same : pair.2 :: rest = values := by
                simpa [lookupValues, List.mapM_cons, head, tail] using found
              subst values
              simp only [List.length_cons, ih tail]

theorem bindingsList_binders [DecidableEq F] (names : List String) (values : List (SourceValue F))
    (lengths : names.length = values.length) :
    Aiur.Pattern.bindingsList (names.map Aiur.Pattern.bind) values = some (names.zip values) := by
  induction names generalizing values with
  | nil => cases values <;> simp_all [Aiur.Pattern.bindingsList]
  | cons name names ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          have len : names.length = values.length := by simpa using lengths
          simp [Aiur.Pattern.bindingsList, Aiur.Pattern.bindings, ih values len]

theorem bindingsList_binders_eq [DecidableEq F] (names : List String) (values : List (SourceValue F)) :
    Aiur.Pattern.bindingsList (names.map Aiur.Pattern.bind) values =
      if names.length = values.length then some (names.zip values) else none := by
  induction names generalizing values with
  | nil => cases values <;> simp [Aiur.Pattern.bindingsList]
  | cons name names ih =>
      cases values with
      | nil => simp [Aiur.Pattern.bindingsList]
      | cons value values =>
          by_cases same : names.length = values.length <;>
            simp [Aiur.Pattern.bindingsList, Aiur.Pattern.bindings, ih values, same]

theorem lookup_zip [DecidableEq F] (names : List String) (values : List (SourceValue F))
    (locals : Environment F Nat) (unique : names.Nodup) (lengths : names.length = values.length) :
    List.Forall₂ (fun name value => ((names.zip values) ++ locals).find? (·.1 == name) = some (name, value)) names values := by
  induction names generalizing values with
  | nil => cases values <;> simp_all
  | cons name names ih =>
      cases values with
      | nil => simp at lengths
      | cons value values =>
          obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
          have lengths : names.length = values.length := by simpa using lengths
          have tail := ih values unique lengths
          apply List.Forall₂.cons (by simp)
          have withMem : List.Forall₂ (fun n v => n ∈ names ∧
              ((names.zip values) ++ locals).find? (·.1 == n) = some (n, v)) names values :=
            (List.forall₂_and_left _ _).mpr ⟨fun _ h => h, tail⟩
          apply withMem.imp
          intro n v h
          have ne : name ≠ n := by intro equal; apply absent; simpa only [equal] using h.1
          simpa [List.find?, ne] using h.2

variable [Field F] [DecidableEq F] {world : Engine.World F}

theorem evalVars_iff {locals : Environment F Nat} {names : List String}
    {values : List (SourceValue F)} {before after : Heap F} :
    OpenCore.EvalArgs world calls locals (names.map Aiur.Expr.var) before values after ↔
      lookupValues locals names = some values ∧ after = before := by
  induction names generalizing before values with
  | nil =>
      constructor
      · intro h; cases h; exact ⟨rfl, rfl⟩
      · rintro ⟨h, rfl⟩
        have same : values = [] := by simpa [lookupValues] using h.symm
        subst values; exact .nil
  | cons name names ih =>
      constructor
      · intro h; cases h with
        | cons head tail =>
            cases head with
            | var found =>
                obtain ⟨rest, rfl⟩ := ih.mp tail
                exact ⟨by simp [lookupValues, List.mapM_cons, found, rest], rfl⟩
      · rintro ⟨h, rfl⟩
        cases head : locals.find? (·.1 == name) with
        | none => simp [lookupValues, List.mapM_cons, head] at h
        | some pair =>
            rcases pair with ⟨n, value⟩
            have same : n = name := by simpa using List.find?_some head
            subst n
            cases rest : lookupValues locals names with
            | none => simp [lookupValues, List.mapM_cons, head, rest] at h
            | some vs =>
                have same : value :: vs = values := by
                  simpa [lookupValues, List.mapM_cons, head, rest] using h
                subst values
                exact .cons (.var head) (ih.mpr ⟨rest, rfl⟩)

/-- User bindings are installed together, after all matching steps finish.
Reading every temporary before installing any user name avoids capture and
preserves the source matcher's left-to-right binding order. -/
theorem bindUsers_iff {bindings : List (String × String)} {locals : Environment F Nat}
    {body : Aiur.Expr F} {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (bindUsers bindings body) before result after ↔
      ∃ values, lookupValues locals (bindings.map Prod.snd) = some values ∧
        OpenCore.EvalExpr world calls (((bindings.map Prod.fst).zip values) ++ locals) body before result after := by
  have sources : bindings.map (fun b => (Aiur.Expr.var b.2 : Aiur.Expr F)) =
      (bindings.map Prod.snd).map Aiur.Expr.var := by simp only [List.map_map, Function.comp_def]
  have names : bindings.map (fun b => (Aiur.Pattern.bind b.1 : Aiur.Pattern F)) =
      (bindings.map Prod.fst).map Aiur.Pattern.bind := by simp only [List.map_map, Function.comp_def]
  constructor
  · intro h; cases h with
    | letValue tuple matched body =>
        cases tuple with
        | tuple items =>
            rename_i values
            rw [sources] at items
            obtain ⟨found, rfl⟩ := evalVars_iff.mp items
            have len : (bindings.map Prod.fst).length = values.length := by
              simpa only [List.length_map] using lookupValues_length found
            have bs := bindingsList_binders (bindings.map Prod.fst) _ len
            simp only [Aiur.Pattern.bindings, names, bs, Option.some.injEq] at matched
            subst_vars
            exact ⟨_, found, body⟩
  · rintro ⟨values, found, body⟩
    have len : (bindings.map Prod.fst).length = values.length := by
      simpa only [List.length_map] using lookupValues_length found
    apply OpenCore.EvalExpr.letValue (bindings := (bindings.map Prod.fst).zip values)
    · apply OpenCore.EvalExpr.tuple
      rw [sources]
      exact evalVars_iff.mpr ⟨found, rfl⟩
    · simp only [Aiur.Pattern.bindings, names, bindingsList_binders _ _ len]
    · exact body

theorem bindUsers_resolved_iff {links : List (String × String)} {locals : Environment F Nat}
    {body : Aiur.Expr F} {before after : Heap F} {result : SourceValue F} :
    OpenCore.EvalExpr world calls locals (bindUsers links body) before result after ↔
      ∃ bindings, resolveBindings links locals = some bindings ∧
        OpenCore.EvalExpr world calls (bindings ++ locals) body before result after := by
  rw [bindUsers_iff]
  constructor
  · rintro ⟨values, found, body⟩
    exact ⟨_, by simp only [resolveBindings, found, Option.map_some], body⟩
  · rintro ⟨bindings, found, body⟩
    cases values : lookupValues locals (links.map Prod.snd) with
    | none => simp [resolveBindings, values] at found
    | some vs =>
        have same : (links.map Prod.fst).zip vs = bindings := by
          simpa only [resolveBindings, values, Option.map_some, Option.some.injEq] using found
        exact ⟨vs, rfl, by simpa only [same] using body⟩

end Aiur.Generic.PatternLowering
