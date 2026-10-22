import Aiur.Optimized.ScopedWitness
import Aiur.Optimized.ValidationCorrectness
import Aiur.Optimized.ScopedInvariant
import Aiur.LayoutValidation

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

private theorem tagTests_has_tag {count index : Nat} {tag : F}
    (selected : (tagTests count tag index).sum = 1) :
    ∃ i : Fin count, tag = ((index + i.val : Nat) : F) := by
  induction count generalizing index with
  | zero => simp [tagTests] at selected
  | succ count ih =>
      by_cases equal : tag = (index : F)
      · exact ⟨⟨0, by omega⟩, by simpa using equal⟩
      · have tail : (tagTests count tag (index + 1)).sum = 1 := by
          simpa [tagTests, equal] using selected
        obtain ⟨i, tagEq⟩ := ih tail
        exact ⟨⟨i.val + 1, by omega⟩, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tagEq⟩

private def ConstructorInputs (activation : ScopeId → F) (tag : F) (payload : List F) :
    List (String × Layout) → List ScopeId → Nat → Prop
  | [], [], _ => True
  | (_, type) :: constructors, branch :: branches, index =>
      (activation branch = 0 ∨ activation branch = 1 ∧ tag = (index : F) ∧
        type.Admissible (payload.take type.width) ∧ ∀ word ∈ payload.drop type.width, word = 0) ∧
      ConstructorInputs activation tag payload constructors branches (index + 1)
  | _, _, _ => False

private theorem constructorInputs_congr {left right : ScopeId → F} {tag : F} {payload : List F}
    {constructors : List (String × Layout)} {branches : List ScopeId} {index : Nat}
    (same : ∀ branch ∈ branches, left branch = right branch)
    (inputs : ConstructorInputs left tag payload constructors branches index) :
    ConstructorInputs right tag payload constructors branches index := by
  induction constructors generalizing branches index with
  | nil => cases branches <;> simpa [ConstructorInputs] using inputs
  | cons constructor constructors ih =>
      cases branches with
      | nil => exact inputs
      | cons branch branches =>
          obtain ⟨head, tail⟩ := inputs
          exact ⟨by simpa only [same branch (by simp)] using head,
            ih (fun b member => same b (by simp [member])) tail⟩

private theorem constructorInputs_of_admissible
    {activation : ScopeId → F} {tag : F} {payload : List F}
    {constructors : List (String × Layout)} {branches : List ScopeId} {index : Nat}
    (sizeEq : branches.length = constructors.length)
    (choices : ∀ (j : Nat) (bound : j < branches.length),
      activation branches[j] = 0 ∨ activation branches[j] = 1 ∧ tag = ((index + j : Nat) : F))
    (admissible : Layout.AdmissibleConstructors constructors tag payload index) :
    ConstructorInputs activation tag payload constructors branches index := by
  induction constructors generalizing branches index with
  | nil =>
      cases branches with
      | nil => trivial
      | cons => simp at sizeEq
  | cons constructor constructors ih =>
      rcases constructor with ⟨name, type⟩
      cases branches with
      | nil => simp at sizeEq
      | cons branch branches =>
          simp only [Layout.AdmissibleConstructors] at admissible
          refine ⟨?_, ih (by simpa using sizeEq) ?_ admissible.2⟩
          · rcases choices 0 (by simp) with inactive | ⟨active, tagEq⟩
            · exact Or.inl inactive
            · have tagEq : tag = (index : F) := by simpa using tagEq
              exact Or.inr ⟨active, tagEq, admissible.1 tagEq⟩
          · intro j bound
            convert choices (j + 1) (by simp; omega) using 1 <;>
              simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> rfl

private theorem constructorInputs_inactive
    {activation : ScopeId → F} {tag : F} {payload : List F}
    {constructors : List (String × Layout)} {branches : List ScopeId} {index : Nat}
    (sizeEq : branches.length = constructors.length)
    (inactive : ∀ branch ∈ branches, activation branch = 0) :
    ConstructorInputs activation tag payload constructors branches index := by
  induction constructors generalizing branches index with
  | nil =>
      cases branches with
      | nil => trivial
      | cons => simp at sizeEq
  | cons constructor constructors ih =>
      cases branches with
      | nil => simp at sizeEq
      | cons branch branches =>
          exact ⟨Or.inl (inactive branch (by simp)),
            ih (by simpa using sizeEq) (fun b member => inactive b (by simp [member]))⟩

private theorem validation_choice_complete
    {scope : ScopeId} {constructors : List (String × Layout)} {branches : List ScopeId}
    {tag : Polynomial F} {payload : List (Polynomial F)} {before after : State F}
    (compiled : choice scope constructors.length before = .ok (branches, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial)
    (tagBound : tag.inBounds before.roles.size = true)
    (payloadBound : ∀ word ∈ payload, word.inBounds before.roles.size = true)
    (acceptable : (before.activation scope).denote initial = 0 ∨
      (before.activation scope).denote initial = 1 ∧
        (tagTests constructors.length (tag.denote initial) 0).sum = 1 ∧
        Layout.AdmissibleConstructors constructors (tag.denote initial)
          (payload.map (Circuit.ArithExpr.denote initial)) 0) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      ConstructorInputs (fun branch => (after.activation branch).denote assignment)
        (tag.denote assignment) (payload.map (Circuit.ArithExpr.denote assignment)) constructors branches 0 := by
  have length := choice_length compiled
  rcases acceptable with inactive | ⟨active, tagSum, admissible⟩
  · obtain ⟨a, ext, childValues⟩ := choice_complete compiled layout scopeLayout valid none
      (by simpa using inactive)
    refine ⟨a, ext, constructorInputs_inactive length ?_⟩
    intro branch member
    obtain ⟨i, bound, rfl⟩ := List.mem_iff_getElem.mp member
    simpa [choiceSelected] using childValues ⟨i, bound⟩
  · obtain ⟨selected, tagEq⟩ := tagTests_has_tag tagSum
    obtain ⟨a, ext, childValues⟩ := choice_complete compiled layout scopeLayout valid (some selected)
      (by simpa using active)
    refine ⟨a, ext, ?_⟩
    rw [ext.polynomial tagBound, ext.words payloadBound]
    apply constructorInputs_of_admissible length _ admissible
    intro j bound
    have child := childValues ⟨j, bound⟩
    by_cases selectedHere : selected.val = j
    · right
      refine ⟨?_, ?_⟩
      · simpa [choiceSelected, selectedHere] using child
      · simpa [selectedHere] using tagEq
    · left
      simpa [choiceSelected, selectedHere] using child

mutual
  /-- Canonical words admit validation witnesses. Disabled values need no
  canonical shape beyond the shape already accepted by compilation. -/
  theorem validate_complete {type : Layout} {scope : ScopeId}
      {words : List (Polynomial F)} {before after : State F}
      (compiled : validate scope type words before = .ok ((), after))
      {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
      (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
      (bounded : ∀ word ∈ words, word.inBounds before.roles.size = true)
      (admissible : (before.activation scope).denote initial = 0 ∨
        (before.activation scope).denote initial = 1 ∧
          type.Admissible (words.map (Circuit.ArithExpr.denote initial))) :
      ∃ assignment, Extension rom calls before after initial assignment := by
    cases type with
    | field =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest => cases rest with
          | cons => simp [validate] at compiled
          | nil =>
              obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
              exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
    | ptr target =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest => cases rest with
          | cons => simp [validate] at compiled
          | nil =>
              obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
              exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
    | tuple layouts =>
        exact validateList_complete (by simpa only [validate] using compiled) layout scopeLayout valid
          scopeValid bounded (by simpa only [Layout.Admissible] using admissible)
    | enum name constructors =>
        simp only [validate] at compiled
        cases parts : Layout.enumParts constructors.length (.const 0) words with
        | none => simp [parts] at compiled
        | some pair =>
            rcases pair with ⟨tag, payload⟩
            simp only [parts] at compiled
            split at compiled
            · simp [StateT.bind, bind, Except.bind] at compiled
            · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
              obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
              obtain ⟨branches, middle, choiceRun, constructorsRun⟩ := bind_ok.mp rest
              obtain ⟨tagBound, payloadBound⟩ := Layout.enumParts_all parts (by rfl) bounded
              have acceptable : (before.activation scope).denote initial = 0 ∨
                  (before.activation scope).denote initial = 1 ∧
                    (tagTests constructors.length (tag.denote initial) 0).sum = 1 ∧
                    Layout.AdmissibleConstructors constructors (tag.denote initial)
                      (payload.map (Circuit.ArithExpr.denote initial)) 0 := by
                rcases admissible with inactive | ⟨active, good⟩
                · exact Or.inl inactive
                · simp only [Layout.Admissible, Nat.cast_zero, Circuit.Compiler.enumParts_denote parts initial] at good
                  exact Or.inr ⟨active, good.2⟩
              obtain ⟨a, choiceExt, selected⟩ := validation_choice_complete choiceRun layout scopeLayout valid
                tagBound payloadBound acceptable
              obtain ⟨b, constructorsExt⟩ := validateConstructors_complete constructorsRun choiceExt.layout
                (choice_scoped choiceRun scopeLayout) choiceExt.validAssignment
                (choice_child_bound choiceRun) (choiceExt.bound tagBound)
                (fun p member => choiceExt.bound (payloadBound p member)) selected
              exact ⟨b, choiceExt.trans constructorsExt⟩
  termination_by sizeOf type

  theorem validateList_complete {types : List Layout} {scope : ScopeId}
      {words : List (Polynomial F)} {before after : State F}
      (compiled : validateList scope types words before = .ok ((), after))
      {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
      (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
      (bounded : ∀ word ∈ words, word.inBounds before.roles.size = true)
      (admissible : (before.activation scope).denote initial = 0 ∨
        (before.activation scope).denote initial = 1 ∧
          Layout.AdmissibleList types (words.map (Circuit.ArithExpr.denote initial))) :
      ∃ assignment, Extension rom calls before after initial assignment := by
    cases types with
    | nil => cases words with
      | nil =>
          obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validateList] using compiled)
          exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
      | cons => simp [validateList] at compiled
    | cons type types =>
        simp only [validateList] at compiled
        split at compiled
        · simp [StateT.bind, bind, Except.bind] at compiled
        · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
          obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
          obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp rest
          have headBound : ∀ p ∈ words.take type.width, p.inBounds before.roles.size = true :=
            fun p member => bounded p (List.mem_of_mem_take member)
          have tailBound : ∀ p ∈ words.drop type.width, p.inBounds before.roles.size = true :=
            fun p member => bounded p (List.mem_of_mem_drop member)
          have headAdmissible : (before.activation scope).denote initial = 0 ∨
              (before.activation scope).denote initial = 1 ∧
                type.Admissible ((words.take type.width).map (Circuit.ArithExpr.denote initial)) := by
            rcases admissible with inactive | ⟨active, good⟩
            · exact Or.inl inactive
            · simp only [Layout.AdmissibleList] at good
              exact Or.inr ⟨active, by simpa only [List.map_take] using good.1⟩
          obtain ⟨a, headExt⟩ := validate_complete headRun layout scopeLayout valid scopeValid headBound headAdmissible
          obtain ⟨headStructure, headScoped⟩ := validate_scoped headRun scopeLayout scopeValid
          have tailAdmissible : (middle.activation scope).denote a = 0 ∨
              (middle.activation scope).denote a = 1 ∧
                Layout.AdmissibleList types ((words.drop type.width).map (Circuit.ArithExpr.denote a)) := by
            rw [headExt.activation headStructure scopeLayout scopeValid, headExt.words tailBound]
            rcases admissible with inactive | ⟨active, good⟩
            · exact Or.inl inactive
            · simp only [Layout.AdmissibleList] at good
              exact Or.inr ⟨active, by simpa only [List.map_drop] using good.2⟩
          obtain ⟨b, tailExt⟩ := validateList_complete tailRun headExt.layout headScoped headExt.validAssignment
            (headStructure.scopeValid scopeValid) (fun p member => headExt.bound (tailBound p member)) tailAdmissible
          exact ⟨b, headExt.trans tailExt⟩
  termination_by sizeOf types

  private theorem validateConstructors_complete
      {constructors : List (String × Layout)} {branches : List ScopeId} {tag : Polynomial F}
      {payload : List (Polynomial F)} {index : Nat} {before after : State F}
      (compiled : validateConstructors constructors branches tag payload index before = .ok ((), after))
      {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
      (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
      (valid : before.Valid rom calls initial)
      (branchesValid : ∀ branch ∈ branches, branch < before.scopes.size)
      (tagBound : tag.inBounds before.roles.size = true)
      (bounded : ∀ word ∈ payload, word.inBounds before.roles.size = true)
      (inputs : ConstructorInputs (fun branch => (before.activation branch).denote initial)
        (tag.denote initial) (payload.map (Circuit.ArithExpr.denote initial)) constructors branches index) :
      ∃ assignment, Extension rom calls before after initial assignment := by
    cases constructors with
    | nil => cases branches with
      | nil =>
          obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validateConstructors] using compiled)
          exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
      | cons => simp [validateConstructors] at compiled
    | cons pair constructors =>
        rcases hpair : pair with ⟨name, type⟩
        rw [hpair] at compiled inputs
        cases branches with
        | nil => simp [validateConstructors] at compiled
        | cons branch branches =>
            simp only [validateConstructors] at compiled
            obtain ⟨⟨⟩, afterTag, tagRun, afterTagBind⟩ := bind_ok.mp compiled
            obtain ⟨⟨⟩, afterValue, valueRun, afterValueBind⟩ := bind_ok.mp afterTagBind
            obtain ⟨⟨⟩, afterPadding, paddingRun, tailRun⟩ := bind_ok.mp afterValueBind
            obtain ⟨head, tail⟩ := inputs
            have branchValid := branchesValid branch (by simp)
            have tagExt := equation_complete tagRun layout valid (by
              simp [Scalar.Circuit.ArithExpr.inBounds, scopeLayout.activation_bound branch, tagBound]) (by
                rcases head with inactive | ⟨active, tagEq, _⟩
                · simp [inactive]
                · simp [Scalar.Circuit.ArithExpr.denote, tagEq])
            have tagState := equation_eq tagRun
            subst afterTag
            have tagScoped := scopeLayout.equation branchValid (.sub tag (.const (index : F)))
            have valueBound : ∀ p ∈ payload.take type.width, p.inBounds before.roles.size = true :=
              fun p member => bounded p (List.mem_of_mem_take member)
            have paddingBound : ∀ p ∈ payload.drop type.width, p.inBounds before.roles.size = true :=
              fun p member => bounded p (List.mem_of_mem_drop member)
            have valueAdmissible : (before.activation branch).denote initial = 0 ∨
                (before.activation branch).denote initial = 1 ∧
                  type.Admissible ((payload.take type.width).map (Circuit.ArithExpr.denote initial)) := by
              rcases head with inactive | ⟨active, _, good, _⟩
              · exact Or.inl inactive
              · exact Or.inr ⟨active, by simpa only [List.map_take] using good⟩
            obtain ⟨a, valueExt⟩ := validate_complete valueRun tagExt.layout tagScoped tagExt.validAssignment
              branchValid valueBound valueAdmissible
            obtain ⟨valueStructure, valueScoped⟩ := validate_scoped valueRun tagScoped branchValid
            have untilValue := tagExt.trans valueExt
            have activation := valueExt.activation valueStructure tagScoped branchValid
            have paddingZero : (afterValue.activation branch).denote a = 0 ∨
                ∀ p ∈ payload.drop type.width, p.denote a = 0 := by
              rw [activation]
              rcases head with inactive | ⟨_, _, _, zeros⟩
              · exact Or.inl inactive
              · right
                intro p member
                rw [untilValue.polynomial (paddingBound p member)]
                apply zeros
                rw [← List.map_drop]
                exact List.mem_map.mpr ⟨p, member, rfl⟩
            have paddingRun' : (do for p in payload.drop type.width do equation branch p : Build F Unit)
                afterValue = .ok ((), afterPadding) := bind_ok.mpr ⟨PUnit.unit, afterPadding, paddingRun, rfl⟩
            have paddingExt := equations_complete paddingRun' valueExt.layout valueExt.validAssignment
              (valueScoped.activation_bound branch) (fun p member => untilValue.bound (paddingBound p member)) paddingZero
            have paddingScoped := equations_scoped paddingRun' valueScoped (valueStructure.scopeValid branchValid)
            have paddingScopes := equations_scopes paddingRun'
            have throughPadding := untilValue.trans paddingExt
            have tailValid : ∀ b ∈ branches, b < afterPadding.scopes.size := by
              intro b member
              rw [paddingScopes]
              exact valueStructure.scopeValid (branchesValid b (by simp [member]))
            have tailInputs : ConstructorInputs (fun b => (afterPadding.activation b).denote a)
                (tag.denote a) (payload.map (Circuit.ArithExpr.denote a)) constructors branches (index + 1) := by
              rw [throughPadding.polynomial tagBound, throughPadding.words bounded]
              apply constructorInputs_congr _ tail
              intro b member
              have bValid := branchesValid b (by simp [member])
              have same := valueExt.activation valueStructure tagScoped bValid
              simpa only [State.activation, paddingScopes] using same.symm
            obtain ⟨b, tailExt⟩ := validateConstructors_complete tailRun throughPadding.layout paddingScoped
              (Extension.validAssignment throughPadding) tailValid (throughPadding.bound tagBound)
              (fun p member => throughPadding.bound (bounded p member)) tailInputs
            exact ⟨b, throughPadding.trans tailExt⟩
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

theorem validateValue_complete {decls : Declarations} (tags : decls.tagsValid F = true)
    {scope : ScopeId} {wire : Symbolic F} {before after : State F}
    (compiled : validateValue decls scope wire before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
    (bounded : Circuit.Compiler.Bounded before.roles.size wire)
    (decodable : (before.activation scope).denote initial = 0 ∨
      (before.activation scope).denote initial = 1 ∧
        ∃ value, (wire.map (Circuit.ArithExpr.denote initial)).decode decls = some value) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  simp only [validateValue] at compiled
  obtain ⟨type, middle, expanded, run⟩ := bind_ok.mp compiled
  obtain ⟨expansion, stateEq⟩ := getLayout_eq expanded
  subst middle
  apply validate_complete run layout scopeLayout valid scopeValid bounded
  rcases decodable with inactive | ⟨active, value, decoded⟩
  · exact Or.inl inactive
  · obtain ⟨_, _, other, found, decoded⟩ := WireValue.decode_spec decoded
    simp only [WireValue.type_map, expansion, Except.ok.injEq] at found
    subst other
    exact Or.inr ⟨active, Layout.decode_admissible (Declarations.layout_tagSafe tags expansion) decoded⟩

theorem validateValue_inactive {decls : Declarations}
    {scope : ScopeId} {wire : Symbolic F} {before after : State F}
    (compiled : validateValue decls scope wire before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
    (bounded : Circuit.Compiler.Bounded before.roles.size wire)
    (inactive : (before.activation scope).denote initial = 0) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  simp only [validateValue] at compiled
  obtain ⟨type, middle, expanded, run⟩ := bind_ok.mp compiled
  obtain ⟨_, stateEq⟩ := getLayout_eq expanded
  subst middle
  exact validate_complete run layout scopeLayout valid scopeValid bounded (Or.inl inactive)

theorem validateValues_complete {decls : Declarations} (tags : decls.tagsValid F = true)
    {scope : ScopeId} {wires : List (Symbolic F)} {before after : State F}
    (compiled : (do for wire in wires do validateValue decls scope wire : Build F Unit)
      before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
    (bounded : ∀ wire ∈ wires, Circuit.Compiler.Bounded before.roles.size wire)
    (decodable : (before.activation scope).denote initial = 0 ∨
      (before.activation scope).denote initial = 1 ∧
        ∀ wire ∈ wires, ∃ value, (wire.map (Circuit.ArithExpr.denote initial)).decode decls = some value) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  induction wires generalizing before initial with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
  | cons wire wires ih =>
      simp only [List.forIn_cons, bind_assoc, pure_bind] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨a, headExt⟩ := validateValue_complete tags headRun layout scopeLayout valid scopeValid
        (bounded wire (by simp)) (decodable.imp_right (fun h => ⟨h.1, h.2 wire (by simp)⟩))
      obtain ⟨headStructure, headScoped⟩ := validateValue_scoped headRun scopeLayout scopeValid
      obtain ⟨b, tailExt⟩ := ih tailRun headExt.layout headScoped headExt.validAssignment
        (headStructure.scopeValid scopeValid) (fun w member => (bounded w (by simp [member])).mono headExt.increase) (by
          rw [headExt.activation headStructure scopeLayout scopeValid]
          rcases decodable with inactive | ⟨active, good⟩
          · exact Or.inl inactive
          · right
            refine ⟨active, ?_⟩
            intro w member
            rw [headExt.value (bounded w (by simp [member]))]
            exact good w (by simp [member]))
      exact ⟨b, headExt.trans tailExt⟩

theorem validateValues_inactive {decls : Declarations}
    {scope : ScopeId} {wires : List (Symbolic F)} {before after : State F}
    (compiled : (do for wire in wires do validateValue decls scope wire : Build F Unit)
      before = .ok ((), after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (scopeLayout : before.Scoped)
    (valid : before.Valid rom calls initial) (scopeValid : scope < before.scopes.size)
    (bounded : ∀ wire ∈ wires, Circuit.Compiler.Bounded before.roles.size wire)
    (inactive : (before.activation scope).denote initial = 0) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  induction wires generalizing before initial with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid)⟩
  | cons wire wires ih =>
      simp only [List.forIn_cons, bind_assoc, pure_bind] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨a, headExt⟩ := validateValue_inactive headRun layout scopeLayout valid scopeValid
        (bounded wire (by simp)) inactive
      obtain ⟨headStructure, headScoped⟩ := validateValue_scoped headRun scopeLayout scopeValid
      obtain ⟨b, tailExt⟩ := ih tailRun headExt.layout headScoped headExt.validAssignment
        (headStructure.scopeValid scopeValid) (fun w member => (bounded w (by simp [member])).mono headExt.increase)
        ((headExt.activation headStructure scopeLayout scopeValid).trans inactive)
      exact ⟨b, headExt.trans tailExt⟩

end Aiur.Optimized.Compiler
