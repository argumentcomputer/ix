import Aiur.Generic.PatternTreeNames

namespace Aiur.Generic.PatternLowering

/-- Resolution relates every link to its value at the same position. -/
theorem resolveBindings_relation {links} {locals bindings : Environment F Nat}
    (resolved : resolveBindings links locals = some bindings) :
    List.Forall₂ (fun link binding => link.1 = binding.1 ∧
      locals.find? (·.1 == link.2) = some (link.2, binding.2)) links bindings := by
  induction links generalizing bindings with
  | nil => simp only [resolveBindings_nil, Option.some.injEq] at resolved; subst bindings; exact .nil
  | cons link links ih =>
      rcases link with ⟨user, temp⟩
      rw [resolveBindings_cons] at resolved
      cases found : locals.find? (·.1 == temp) with
      | none => simp [found] at resolved
      | some pair =>
          have name : pair.1 = temp := by simpa using List.find?_some found
          cases tail : resolveBindings links locals with
          | none => simp [found, tail] at resolved
          | some rest =>
              simp [found, tail] at resolved
              subst bindings
              refine .cons ⟨rfl, ?_⟩ (ih tail)
              simpa only [← name] using found

/-- Gathering positions before or after resolving links has the same result. -/
theorem resolveBindings_reorder {links} {locals bindings : Environment F Nat}
    (resolved : resolveBindings links locals = some bindings) (names positions) :
    (reorderBindings names positions links).bind (resolveBindings · locals) =
      reorderBindings names positions bindings := by
  have rel := resolveBindings_relation resolved
  have atIndex (index : Nat) :
      match links[index]?, bindings[index]? with
      | none, none => True
      | some link, some binding => link.1 = binding.1 ∧
          locals.find? (·.1 == link.2) = some (link.2, binding.2)
      | _, _ => False := by
    clear resolved
    induction rel generalizing index with
    | nil => simp
    | cons head tail ih => cases index <;> simp_all
  induction names generalizing positions with
  | nil => cases positions <;> rfl
  | cons name names ih =>
      cases positions with
      | nil => rfl
      | cons index positions =>
          have cell := atIndex index
          cases left : links[index]? <;> cases right : bindings[index]? <;>
            simp only [left, right] at cell
          · simp [reorderBindings, left, right]
          · rename_i link binding
            cases tail : reorderBindings names positions links with
            | none =>
                have rest := ih positions
                simp only [tail, Option.bind_none] at rest
                simp [reorderBindings, left, right, tail, ← rest]
            | some rest =>
                have tailResolved := ih positions
                simp only [tail, Option.bind_some] at tailResolved
                simp only [reorderBindings, left, right, tail, bind, Option.bind, pure]
                rw [resolveBindings_cons, cell.2, tailResolved]
                rfl

/-- Reading copied temporary bindings recovers the canonical user bindings. -/
theorem resolveBindings_copied (rename : String → String)
    (bindings locals : Environment F Nat)
    (unique : (bindings.map fun binding => rename binding.1).Nodup) :
    resolveBindings (bindings.map fun binding => (binding.1, rename binding.1))
      ((bindings.map fun binding => (rename binding.1, binding.2)) ++ locals) = some bindings := by
  induction bindings with
  | nil => rfl
  | cons binding bindings ih =>
      rcases binding with ⟨name, value⟩
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      simp only [List.map_cons, List.cons_append, resolveBindings_cons, List.find?_cons,
        beq_self_eq_true, ↓reduceIte]
      have unchanged := resolveBindings_congr (links := bindings.map fun b => (b.1, rename b.1))
        (left := (rename name, value) :: ((bindings.map fun b => (rename b.1, b.2)) ++ locals))
        (right := (bindings.map fun b => (rename b.1, b.2)) ++ locals) (by
          intro n member
          have member : n ∈ bindings.map (fun b => rename b.1) := by simpa using member
          have ne : rename name ≠ n := by intro h; apply absent; simpa only [h] using member
          simp [List.find?_cons, ne])
      rw [unchanged, ih unique]
      rfl

/-- Selected alternatives copy only their ordered user bindings into common
slots; all branch-local names remain invisible to the surrounding expression. -/
theorem choice_copied {stem : String} {names positions links}
    {locals bindings : Environment F Nat}
    (resolved : resolveBindings links locals = some bindings)
    (unique : ((choiceBindings stem names).map Prod.snd).Nodup) :
    ∀ aliases installed,
      choiceLinks (choiceBindings stem names) links positions = some aliases →
      resolveBindings aliases locals = some installed →
      ∃ ordered, reorderBindings names positions bindings = some ordered ∧
        resolveBindings (choiceBindings stem names) (installed ++ locals) = some ordered := by
  intro aliases installed aligned copied
  have composed := resolveBindings_reorder resolved
    ((choiceBindings stem names).map Prod.snd) positions
  rw [show reorderBindings ((choiceBindings stem names).map Prod.snd) positions links =
    some aliases from aligned, Option.bind_some, copied] at composed
  have mapped : (choiceBindings stem names).map Prod.snd =
      names.map (fun name => stem ++ ":or:" ++ name) := by simp [choiceBindings]
  rw [mapped, reorderBindings_mapNames] at composed
  cases result : reorderBindings names positions bindings with
  | none => simp [result] at composed
  | some ordered =>
      simp only [result, Option.map_some, Option.some.injEq] at composed
      subst installed
      refine ⟨ordered, rfl, ?_⟩
      have orderedNames := reorderBindings_names result
      have slots : choiceBindings stem names =
          ordered.map (fun binding => (binding.1, stem ++ ":or:" ++ binding.1)) := by
        rw [← orderedNames]
        simp [choiceBindings]
      rw [slots]
      apply resolveBindings_copied
      simpa only [slots, List.map_map, Function.comp_def] using unique

/-- The converse construction supplies exactly the copied bindings requested by
a successful native alternative. -/
theorem choice_copy_exists {stem : String} {names positions links}
    {locals bindings ordered : Environment F Nat}
    (resolved : resolveBindings links locals = some bindings)
    (reordered : reorderBindings names positions bindings = some ordered) :
    ∃ aliases installed,
      choiceLinks (choiceBindings stem names) links positions = some aliases ∧
      resolveBindings aliases locals = some installed := by
  have composed := resolveBindings_reorder resolved
    ((choiceBindings stem names).map Prod.snd) positions
  have mapped : (choiceBindings stem names).map Prod.snd =
      names.map (fun name => stem ++ ":or:" ++ name) := by simp [choiceBindings]
  have result : reorderBindings ((choiceBindings stem names).map Prod.snd) positions bindings =
      some (ordered.map fun pair => (stem ++ ":or:" ++ pair.1, pair.2)) := by
    rw [mapped, reorderBindings_mapNames, reordered, Option.map_some]
  rw [result] at composed
  cases aligned : choiceLinks (choiceBindings stem names) links positions with
  | none => simp only [choiceLinks] at aligned; rw [aligned, Option.bind_none] at composed; contradiction
  | some aliases =>
      rw [show reorderBindings ((choiceBindings stem names).map Prod.snd) positions links =
        some aliases from aligned, Option.bind_some] at composed
      exact ⟨aliases, _, rfl, composed⟩

end Aiur.Generic.PatternLowering
