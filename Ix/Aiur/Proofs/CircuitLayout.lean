/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FunctionLayout

/-! Compiled circuit layouts contain every member's input and auxiliary
columns. Selector extents are supplied separately by the checked row counts. -/

namespace Aiur.Bytecode

def MembersColumnBound (functions : Array Function) (members : Array FunIdx) (layout : FunctionLayout) : Prop :=
  7 ≤ layout.auxiliaries ∧ ∀ index ∈ members,
    functions[index]!.layout.inputSize ≤ layout.inputSize ∧
    functions[index]!.layout.auxiliaries ≤ layout.auxiliaries

def CircuitsColumnBound (functions : Array Function) (circuits : Array Circuit) : Prop :=
  ∀ circuit ∈ circuits, MembersColumnBound functions circuit.members circuit.layout

private theorem column_circuits_empty (functions : Array Function) : CircuitsColumnBound functions #[] := by
  simp [CircuitsColumnBound]

private theorem column_circuits_push {functions : Array Function} {circuits : Array Circuit} {circuit : Circuit}
    (before : CircuitsColumnBound functions circuits)
    (member : MembersColumnBound functions circuit.members circuit.layout) :
    CircuitsColumnBound functions (circuits.push circuit) := by
  intro c present
  rcases Array.mem_push.mp present with prior | equal
  · exact before c prior
  · subst c; exact member

private theorem column_bang_of_present {functions : Array Function} {index : Nat} {function : Function}
    (present : functions[index]? = some function) : functions[index]! = function := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, present]
  rfl

private theorem column_member_singleton {functions : Array Function} {index : FunIdx} {function : Function}
    (present : functions[index]? = some function) (valid : function.ComputedLayout) :
    MembersColumnBound functions #[index] function.layout := by
  refine ⟨valid.reserved, ?_⟩
  intro i member
  have equal : i = index := by simpa using member
  subst i
  rw [column_bang_of_present present]
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

private theorem column_array_bang {α : Type} [Inhabited α] (property : α → Prop)
    {array : Array α} (valid : ∀ value ∈ array, property value) (fallback : property default) (index : Nat) :
    property array[index]! := by
  by_cases bound : index < array.size
  · rw [getElem!_pos array index bound]
    exact valid _ (Array.getElem_mem bound)
  · rw [getElem!_neg array index bound]
    exact fallback

private theorem column_first_reserved {functions : Array Function} {members : Array FunIdx}
    (valid : FunctionsComputedLayout functions) (nonempty : 0 < functions.size)
    (constrained : MembersConstrained functions members) :
    7 ≤ functions[members[0]!]!.layout.auxiliaries := by
  refine column_array_bang (fun index : FunIdx => 7 ≤ functions[index]!.layout.auxiliaries)
    (array := members) ?_ ?_ 0
  · intro index member
    obtain ⟨function, present, _⟩ := constrained index member
    rw [column_bang_of_present present]
    exact (valid function (Array.mem_of_getElem? present)).reserved
  · change 7 ≤ functions[0]!.layout.auxiliaries
    rw [getElem!_pos functions 0 nonempty]
    exact (valid _ (Array.getElem_mem nonempty)).reserved

private theorem column_merge_fold (functions : Array Function) (first : FunIdx) (members : List FunIdx)
    (initial : FunctionLayout)
    (firstInput : functions[first]!.layout.inputSize ≤ initial.inputSize)
    (firstAux : functions[first]!.layout.auxiliaries ≤ initial.auxiliaries) :
    let final := members.foldl (fun acc index => if index == first then acc else acc.merge functions[index]!.layout) initial
    initial.inputSize ≤ final.inputSize ∧ initial.auxiliaries ≤ final.auxiliaries ∧
      ∀ index ∈ members, functions[index]!.layout.inputSize ≤ final.inputSize ∧
        functions[index]!.layout.auxiliaries ≤ final.auxiliaries := by
  induction members generalizing initial with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _, by simp⟩
  | cons index members ih =>
    let next := if index == first then initial else initial.merge functions[index]!.layout
    have before : initial.inputSize ≤ next.inputSize ∧ initial.auxiliaries ≤ next.auxiliaries := by
      dsimp only [next]
      split
      · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩
    have here : functions[index]!.layout.inputSize ≤ next.inputSize ∧
        functions[index]!.layout.auxiliaries ≤ next.auxiliaries := by
      dsimp only [next]
      split
      · rename_i equal
        have eq : index = first := beq_iff_eq.mp equal
        subst index
        exact ⟨firstInput, firstAux⟩
      · exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
    have rest := ih next (Nat.le_trans firstInput before.1) (Nat.le_trans firstAux before.2)
    refine ⟨Nat.le_trans before.1 rest.1, Nat.le_trans before.2 rest.2.1, ?_⟩
    intro chosen member
    rcases List.mem_cons.mp member with equal | later
    · subst chosen
      exact ⟨Nat.le_trans here.1 rest.1, Nat.le_trans here.2 rest.2.1⟩
    · exact rest.2.2 chosen later

theorem merged_columnBound (functions : Array Function) (members : Array FunIdx)
    (valid : FunctionsComputedLayout functions) (nonempty : 0 < functions.size)
    (constrained : MembersConstrained functions members) :
    MembersColumnBound functions members
      (members.foldl (init := functions[members[0]!]!.layout)
        fun acc index => if index == members[0]! then acc else acc.merge functions[index]!.layout) := by
  rw [← Array.foldl_toList]
  have folded := column_merge_fold functions members[0]! members.toList functions[members[0]!]!.layout
    (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨Nat.le_trans (column_first_reserved valid nonempty constrained) folded.2.1,
    fun index member => folded.2.2 index (Array.mem_def.mp member)⟩

private theorem list_forIn'_id_invariant {α β : Type} (items : List α)
    (step : (item : α) → item ∈ items → β → Id (ForInStep β)) (property : β → Prop)
    (initial : β) (before : property initial)
    (preserved : ∀ item member acc, property acc → property (step item member acc).run.value) :
    property (forIn' items initial step).run := by
  induction items generalizing initial with
  | nil => exact before
  | cons item items ih =>
    rw [List.forIn'_cons]
    have first := preserved item List.mem_cons_self initial before
    cases computed : step item List.mem_cons_self initial with
    | done next =>
      simp only [computed, Id.run, ForInStep.value] at first
      exact first
    | yield next =>
      simp only [computed, Id.run, ForInStep.value] at first
      exact ih (fun item member => step item (List.mem_cons_of_mem _ member)) next first
        (fun item member acc => preserved item (List.mem_cons_of_mem _ member) acc)

theorem singletonCircuits_columnBound (program : Toplevel) (nameOf : FunIdx → String)
    (valid : FunctionsComputedLayout program.functions) :
    CircuitsColumnBound program.functions (program.singletonCircuits nameOf) := by
  unfold Toplevel.singletonCircuits
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_forIn'_id_invariant _ _ (CircuitsColumnBound program.functions) _ (column_circuits_empty _)
  intro index member circuits before
  split
  · exact column_circuits_push before
      (column_member_singleton (Array.getElem?_eq_getElem _) (valid _ (Array.getElem_mem _)))
  · exact before

end Aiur.Bytecode

namespace Aiur
open Bytecode

private theorem list_forIn_except_invariant {ε α β : Type} (items : List α)
    (step : α → β → Except ε (ForInStep β)) (property : β → Prop) (initial : β)
    (before : property initial)
    (preserved : ∀ item ∈ items, ∀ acc result, property acc → step item acc = .ok result → property result.value)
    {result : β} (computed : forIn items initial step = .ok result) : property result := by
  induction items generalizing initial with
  | nil => cases computed; exact before
  | cons item items ih =>
    simp only [List.forIn_cons, bind, Except.bind] at computed
    split at computed
    · cases computed
    · rename_i next nextComputed
      have first := preserved item List.mem_cons_self initial next before nextComputed
      cases next with
      | done next => cases computed; exact first
      | yield next =>
        exact ih next first (fun item member => preserved item (List.mem_cons_of_mem _ member)) computed

private theorem array_forIn_except_invariant {ε α β : Type} (items : Array α)
    (step : α → β → Except ε (ForInStep β)) (property : β → Prop) (initial : β)
    (before : property initial)
    (preserved : ∀ item ∈ items, ∀ acc result, property acc → step item acc = .ok result → property result.value)
    {result : β} (computed : forIn items initial step = .ok result) : property result := by
  rw [← Array.forIn_toList] at computed
  exact list_forIn_except_invariant items.toList step property initial before
    (fun item member => preserved item (Array.mem_toList_iff.mp member)) computed

private theorem column_members_empty (functions : Array Function) : MembersConstrained functions #[] := by
  simp [MembersConstrained]

private theorem column_members_push {functions : Array Function} {members : Array FunIdx} {index : FunIdx}
    (before : MembersConstrained functions members) (constrained : functions[index]!.constrained = true) :
    MembersConstrained functions (members.push index) := by
  intro i member
  rcases Array.mem_push.mp member with prior | equal
  · exact before i prior
  · subst i
    by_cases bound : index < functions.size
    · exact ⟨functions[index], Array.getElem?_eq_getElem bound,
        by simpa only [getElem!_pos functions index bound] using constrained⟩
    · rw [getElem!_neg functions index bound] at constrained
      contradiction

theorem CompiledToplevel.groupFunctions_columnBound {before after : CompiledToplevel}
    {groups : Array (String × Array String)}
    (functions : FunctionsComputedLayout before.bytecode.functions)
    (nonempty : 0 < before.bytecode.functions.size)
    (valid : CircuitsColumnBound before.bytecode.functions before.bytecode.circuits)
    (accepted : before.groupFunctions groups = .ok after) :
    CircuitsColumnBound after.bytecode.functions after.bytecode.circuits := by
  unfold CompiledToplevel.groupFunctions at accepted
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted
  · cases accepted
  · rename_i resolved resolvedComputed
    have resolvedValid : ∀ pair ∈ resolved.2, MembersConstrained before.bytecode.functions pair.2 := by
      apply array_forIn_except_invariant _ _
        (fun acc => ∀ pair ∈ acc.2, MembersConstrained before.bytecode.functions pair.2) _ ?_ ?_ resolvedComputed
      · simp
      · intro item member acc result accumulated step
        rcases item with ⟨groupName, names⟩
        dsimp only at step
        split at step
        · cases step
        · split at step
          · cases step
          · rename_i named namedComputed
            have namedValid : MembersConstrained before.bytecode.functions named.2 := by
              apply array_forIn_except_invariant _ _
                (fun acc => MembersConstrained before.bytecode.functions acc.2) _ (column_members_empty _) ?_ namedComputed
              intro name nameMember acc result accumulated step
              repeat' first | split at step | (dsimp only at step; split at step)
              all_goals cases step
              all_goals exact column_members_push accumulated (by assumption)
            cases step
            intro pair member
            rcases Array.mem_push.mp member with prior | equal
            · exact accumulated pair prior
            · subst pair; exact namedValid
    split at accepted
    · cases accepted
    · rename_i circuits circuitsComputed
      cases accepted
      apply array_forIn_except_invariant _ _
        (fun acc => CircuitsColumnBound before.bytecode.functions acc.1) _ (column_circuits_empty _) ?_ circuitsComputed
      intro circuit member acc result accumulated step
      split at step
      · split at step
        · cases step
          exact column_circuits_push accumulated (valid circuit member)
        · split at step
          · cases step
            exact accumulated
          · cases step
            apply column_circuits_push accumulated
            apply merged_columnBound _ _ functions nonempty
            exact column_array_bang (fun pair : String × Array FunIdx =>
              MembersConstrained before.bytecode.functions pair.2) resolvedValid (column_members_empty _) _
      · cases step

theorem finishCompilation_columnBound (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) (valid : FunctionsComputedLayout raw.functions) :
    CircuitsColumnBound (finishCompilation source raw names).bytecode.functions
      (finishCompilation source raw names).bytecode.circuits := by
  unfold finishCompilation
  apply singletonCircuits_columnBound
  exact finishCompilation_computedLayout source raw names valid

theorem Source.Toplevel.compile_columnBound {source : Source.Toplevel} {compiled : CompiledToplevel}
    (accepted : source.compile = .ok compiled) :
    CircuitsColumnBound compiled.bytecode.functions compiled.bytecode.circuits := by
  obtain ⟨inlined, typed, concrete, raw, names, _, _, _, lowered, artifact⟩ :=
    source.compile_artifact_of_ok accepted
  rw [artifact]
  exact finishCompilation_columnBound inlined raw names (Concrete.Decls.toBytecode_computedLayout lowered)

theorem BoundVerifier.Backend.circuits_columnBound {selection : BoundVerifier.Selection}
    (backend : BoundVerifier.Backend selection) :
    CircuitsColumnBound backend.compiled.bytecode.functions backend.compiled.bytecode.circuits := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  have valid := Source.Toplevel.compile_columnBound compiled
  split at grouped
  · cases grouped
    exact valid
  · have same := (CompiledToplevel.groupFunctions_preserves_code grouped).2.2.1
    have bound := (Array.getElem?_eq_some_iff.mp backend.present).choose
    rw [same] at bound
    exact CompiledToplevel.groupFunctions_columnBound
      (Source.Toplevel.compile_computedLayout compiled) (by omega) valid grouped

end Aiur
