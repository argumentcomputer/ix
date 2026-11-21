import Aiur.Generic.PatternTreeFacts
import Mathlib.Data.List.Nodup

namespace Aiur.Generic.PatternLowering


theorem writtenNames_append (left right : List (Step F)) :
    writtenNames (left ++ right) = writtenNames left ++ writtenNames right := by
  simp only [writtenNames, stepNames, List.flatMap_append]

theorem writtenNames_flatMap (parts : List A) (steps : A → List (Step F)) :
    writtenNames (parts.flatMap steps) = parts.flatMap (fun part => writtenNames (steps part)) := by
  simp only [writtenNames, stepNames, List.flatMap_assoc]

theorem PlanTree.written (tree : PlanTree F) (input : String) :
    writtenNames (tree.toPlan input).steps = tree.temps := by
  have sub (t : PlanTree F) (smaller : sizeOf t < sizeOf tree) (n : String) :
      writtenNames (t.toPlan n).steps = t.temps := PlanTree.written t n
  cases tree with
  | literal | wildcard | bind => simp only [PlanTree.toPlan, PlanTree.temps, writtenNames, stepNames,
      List.flatMap_cons, List.flatMap_nil, patternNames, List.nil_append]
  | choice stem left right layout =>
      simp only [PlanTree.toPlan, PlanTree.temps, writtenNames, stepNames, List.flatMap_cons, List.flatMap_nil,
        stepNames, List.append_nil]
      rw [← writtenNames, ← writtenNames, sub left (by simp_wf; omega), sub right (by simp_wf; omega)]
  | load name child =>
      simpa only [PlanTree.toPlan, PlanTree.temps, writtenNames, stepNames, List.flatMap_cons,
        List.singleton_append] using congrArg (name :: ·) (sub child (by simp_wf <;> omega) name)
  | tuple parts | construct _ _ parts =>
      have children : parts.flatMap (fun part => writtenNames (part.2.toPlan part.1).steps) =
          parts.flatMap (fun part => part.2.temps) := by
        apply List.flatMap_congr
        intro part hp
        exact sub part.2 (by simp_wf; have := List.sizeOf_lt_of_mem hp; cases part; simp_all only [Prod.mk.sizeOf_spec]; omega) part.1
      simp only [PlanTree.toPlan, PlanTree.temps, writtenNames, stepNames, List.flatMap_cons,
        patternNames, List.map_map, List.flatMap_map, Function.comp_def, List.flatMap_assoc]
      change _ ++ parts.flatMap (fun part => writtenNames (part.2.toPlan part.1).steps) = _
      rw [children]
      congr 1
      change parts.flatMap (fun part => [part.1]) = parts.map Prod.fst
      exact List.map_eq_flatMap.symm
termination_by sizeOf tree
decreasing_by exact smaller

/-- Every temporary used to recover a user binding belongs to this pattern's
input or its generated names. Later sibling patterns cannot change it. -/
theorem PlanTree.binding_sources (tree : PlanTree F) (input : String) :
    ∀ n ∈ (tree.toPlan input).bindings.map Prod.snd, n = input ∨ n ∈ tree.temps := by
  have sub (t : PlanTree F) (smaller : sizeOf t < sizeOf tree) (input n : String)
      (member : n ∈ (t.toPlan input).bindings.map Prod.snd) : n = input ∨ n ∈ t.temps :=
    PlanTree.binding_sources t input n member
  cases tree with
  | literal | wildcard => simp only [PlanTree.toPlan, List.map_nil, List.not_mem_nil, false_implies, implies_true]
  | bind => simp only [PlanTree.toPlan, List.map_cons, List.map_nil, List.mem_singleton]; intros; exact Or.inl ‹_›
  | choice stem left right layout =>
      intro n member
      exact Or.inr (by simpa only [PlanTree.toPlan, PlanTree.temps, List.mem_append] using Or.inr member)
  | load name child =>
      intro n member
      rcases sub child (by simp_wf <;> omega) name n (by simpa only [PlanTree.toPlan] using member) with rfl | h
      · exact Or.inr (by simp [PlanTree.temps])
      · exact Or.inr (by simp [PlanTree.temps, h])
  | tuple parts | construct _ _ parts =>
      intro n member
      simp only [PlanTree.toPlan, List.flatMap_map, List.map_flatMap, List.mem_flatMap] at member
      obtain ⟨part, hp, member⟩ := member
      have h := sub part.2 (by simp_wf; have := List.sizeOf_lt_of_mem hp; cases part; simp_all only [Prod.mk.sizeOf_spec]; omega) part.1 n member
      apply Or.inr
      rcases h with rfl | h
      · simp only [PlanTree.temps, List.mem_append, List.mem_map]
        exact Or.inl ⟨part, hp, rfl⟩
      · simp only [PlanTree.temps, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨part, hp, h⟩
termination_by sizeOf tree
decreasing_by exact smaller

theorem PlanTree.safe_choice {stem : String} {left right : PlanTree F} {layout : OrBindings}
    (safe : (input :: (PlanTree.choice stem left right layout).temps).Nodup) :
    (input :: left.temps).Nodup ∧ (input :: right.temps).Nodup ∧
      ((choiceBindings stem layout.names).map Prod.snd).Nodup := by
  simp only [PlanTree.temps, List.nodup_cons, List.mem_append, not_or, List.nodup_append] at safe ⊢
  tauto

theorem PlanTree.safe_load {name : String} {child : PlanTree F}
    (safe : (input :: (PlanTree.load name child).temps).Nodup) :
    (name :: child.temps).Nodup := by
  simpa only [PlanTree.temps] using List.nodup_cons.mp safe |>.2

theorem PlanTree.safe_children {parts : List (String × PlanTree F)}
    (safe : (parts.map Prod.fst ++ parts.flatMap (fun part => part.2.temps)).Nodup)
    {part : String × PlanTree F} (member : part ∈ parts) :
    (part.1 :: part.2.temps).Nodup := by
  obtain ⟨names, temps, disjoint⟩ := List.nodup_append.mp safe
  rw [List.nodup_cons]
  constructor
  · intro h
    exact disjoint _ (List.mem_map.mpr ⟨part, member, rfl⟩) _
      (List.mem_flatMap.mpr ⟨part, member, h⟩) rfl
  · exact (List.nodup_flatMap.mp temps).1 part member

theorem resolveBindings_unchanged [DecidableEq F]
    {heap : Heap F} {steps : List (Step F)} {locals final : Environment F Nat}
    (attempted : Attempt heap steps locals accepted final)
    (disjoint : ∀ n ∈ links.map Prod.snd, n ∉ writtenNames steps) :
    resolveBindings links final = resolveBindings links locals :=
  resolveBindings_congr (fun n hn => attempted.unchanged (disjoint n hn))

end Aiur.Generic.PatternLowering
