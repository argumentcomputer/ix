import Aiur.Optimized.PrimitiveCorrectness
import Aiur.Optimized.ChoiceFacts
import Aiur.LayoutShape
import Aiur.EncodingTypes

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem State.Extends.active {before after : State F} (extension : before.Extends after)
    {scope : ScopeId} {assignment : Witness → F}
    (active : (before.activation scope).denote assignment = 1) :
    (after.activation scope).denote assignment = 1 := by
  rw [extension.activation (by rw [active]; exact one_ne_zero)]
  exact active

theorem equation_extends {scope : ScopeId} {polynomial : Polynomial F} {before after : State F}
    (compiled : equation scope polynomial before = .ok ((), after)) : before.Extends after := by
  obtain rfl := equation_eq compiled
  exact ⟨fun _ _ => id, by simp, fun _ => id, fun _ => id⟩

theorem equations_extends {scope : ScopeId} {conditions : List (Polynomial F)} {before after : State F}
    (compiled : (do for condition in conditions do equation scope condition : Build F Unit)
      before = .ok ((), after)) : before.Extends after := by
  induction conditions generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact .refl before
  | cons condition conditions ih =>
      simp [List.forIn_cons, equation, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        StateT.bind, bind, Except.bind, StateT.pure, pure, Except.pure] at compiled
      exact (equation_extends (scope := scope) (polynomial := condition) rfl).trans (ih compiled)

mutual
  theorem validate_sound {layout : Layout} (proper : layout.TuplePayloads)
      (safe : layout.TagSafe F) {scope : ScopeId} {words : List (Polynomial F)}
      {before after : State F} (compiled : validate scope layout words before = .ok ((), after)) :
      before.Extends after ∧ ∀ (rom : WireROM F) (calls : Circuit.CallRelation F) (assignment : Witness → F),
        (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
        before.Valid rom calls assignment ∧ ((before.activation scope).denote assignment = 1 →
          ∃ value, layout.decode (words.map (Circuit.ArithExpr.denote assignment)) = some value) := by
    cases layout with
    | field =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest =>
            cases rest with
            | cons => simp [validate] at compiled
            | nil =>
                obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
                exact ⟨.refl _, fun _ _ assignment _ valid => ⟨valid, fun _ =>
                  ⟨.field (word.denote assignment), by simp [Layout.decode]⟩⟩⟩
    | ptr target =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest =>
            cases rest with
            | cons => simp [validate] at compiled
            | nil =>
                obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
                exact ⟨.refl _, fun _ _ assignment _ valid => ⟨valid, fun _ =>
                  ⟨.ptr target (word.denote assignment), by simp [Layout.decode]⟩⟩⟩
    | tuple layouts =>
        simp only [validate] at compiled
        obtain ⟨extension, meaning⟩ := validateList_sound
          (by simpa only [Layout.TuplePayloads] using proper)
          (by simpa only [Layout.TagSafe] using safe) compiled
        exact ⟨extension, fun rom calls assignment root valid => by
          obtain ⟨previous, decoded⟩ := meaning rom calls assignment root valid
          exact ⟨previous, fun active => by
            obtain ⟨values, decoded⟩ := decoded active
            exact ⟨.tuple values, by simp [Layout.decode, decoded]⟩⟩⟩
    | enum name constructors =>
        simp only [validate] at compiled
        cases parts : Layout.enumParts constructors.length (.const 0) words with
        | none => simp [parts] at compiled
        | some pair =>
            rcases pair with ⟨tag, payload⟩
            simp only [parts] at compiled
            split at compiled
            · simp [StateT.bind, bind, Except.bind] at compiled
            · rename_i width
              have width : payload.length = Layout.payloadWidth constructors := by simpa using width
              obtain ⟨⟨⟩, unchangedState, unchanged, choiceBind⟩ := bind_ok.mp compiled
              obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
              subst unchangedState
              obtain ⟨branches, middle, choiceRun, ctorRun⟩ := bind_ok.mp choiceBind
              have choiceExtension := choice_extends choiceRun
              simp only [Layout.TagSafe] at safe
              obtain ⟨ctorExtension, meaning⟩ := validateConstructors_sound
                (by simpa only [Layout.TuplePayloads] using proper) safe.1 safe.2 ctorRun
              refine ⟨choiceExtension.trans ctorExtension, fun rom calls assignment root valid => ?_⟩
              obtain ⟨middleValid, decoded⟩ := meaning rom calls assignment (choiceExtension.active root) valid
              refine ⟨middleValid.of_extends choiceExtension, fun active => ?_⟩
              obtain ⟨branch, member, enabled⟩ := choice_active choiceRun middleValid root active
              obtain ⟨_, _, _, _, ⟨ctor, args⟩, decoded⟩ := decoded branch member enabled
              exact ⟨.construct name ctor args, by simp [Layout.decode, Circuit.Compiler.enumParts_denote parts assignment, width, decoded]⟩
  termination_by sizeOf layout

  theorem validateList_sound {layouts : List Layout}
      (proper : ∀ layout ∈ layouts, layout.TuplePayloads)
      (safe : ∀ layout ∈ layouts, layout.TagSafe F)
      {scope : ScopeId} {words : List (Polynomial F)} {before after : State F}
      (compiled : validateList scope layouts words before = .ok ((), after)) :
      before.Extends after ∧ ∀ (rom : WireROM F) (calls : Circuit.CallRelation F) (assignment : Witness → F),
        (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
        before.Valid rom calls assignment ∧ ((before.activation scope).denote assignment = 1 →
          ∃ values, Layout.decodeList layouts (words.map (Circuit.ArithExpr.denote assignment)) = some values) := by
    cases layouts with
    | nil =>
        cases words with
        | nil =>
            obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validateList] using compiled)
            exact ⟨.refl _, fun _ _ _ _ valid => ⟨valid, fun _ => ⟨[], by simp [Layout.decodeList]⟩⟩⟩
        | cons => simp [validateList] at compiled
    | cons layout layouts =>
        simp only [validateList] at compiled
        split at compiled
        · simp [StateT.bind, bind, Except.bind] at compiled
        · obtain ⟨⟨⟩, unchangedState, unchanged, validationBind⟩ := bind_ok.mp compiled
          obtain ⟨_, stateEq⟩ := pure_ok.mp unchanged
          subst unchangedState
          obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp validationBind
          obtain ⟨headExtension, headMeaning⟩ := validate_sound
            (proper _ (by simp)) (safe _ (by simp)) headRun
          obtain ⟨tailExtension, tailMeaning⟩ := validateList_sound
            (fun l h => proper l (by simp [h])) (fun l h => safe l (by simp [h])) tailRun
          refine ⟨headExtension.trans tailExtension, fun rom calls assignment root valid => ?_⟩
          obtain ⟨middleValid, tails⟩ := tailMeaning rom calls assignment (headExtension.active root) valid
          obtain ⟨previous, heads⟩ := headMeaning rom calls assignment root middleValid
          refine ⟨previous, fun active => ?_⟩
          obtain ⟨head, headDecode⟩ := heads active
          obtain ⟨tail, tailDecode⟩ := tails (headExtension.active active)
          exact ⟨head :: tail, by simp [Layout.decodeList, ← List.map_take, ← List.map_drop, headDecode, tailDecode]⟩
  termination_by sizeOf layouts

  theorem validateConstructors_sound {constructors : List (String × Layout)}
      (proper : ∀ pair ∈ constructors, (∃ layouts, pair.2 = .tuple layouts) ∧ pair.2.TuplePayloads)
      {index : Nat} (tags : TagsDistinct F index constructors.length)
      (safe : ∀ pair ∈ constructors, pair.2.TagSafe F)
      {branches : List ScopeId} {tag : Polynomial F} {payload : List (Polynomial F)}
      {before after : State F}
      (compiled : validateConstructors constructors branches tag payload index before = .ok ((), after)) :
      before.Extends after ∧ ∀ (rom : WireROM F) (calls : Circuit.CallRelation F) (assignment : Witness → F),
        (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
        before.Valid rom calls assignment ∧ (∀ branch ∈ branches,
          (before.activation branch).denote assignment = 1 →
          ∃ actual, index ≤ actual ∧ actual < index + constructors.length ∧
            tag.denote assignment = (actual : F) ∧
            ∃ value, Layout.decodeConstructor constructors (tag.denote assignment)
              (payload.map (Circuit.ArithExpr.denote assignment)) index = some value) := by
    cases constructors with
    | nil =>
        cases branches with
        | nil =>
            obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validateConstructors] using compiled)
            exact ⟨.refl _, fun _ _ _ _ valid => ⟨valid, by simp⟩⟩
        | cons => simp [validateConstructors] at compiled
    | cons pair constructors =>
        rcases hpair : pair with ⟨name, layout⟩
        rw [hpair] at compiled tags proper safe
        cases branches with
        | nil => simp [validateConstructors] at compiled
        | cons branch branches =>
            simp only [validateConstructors] at compiled
            obtain ⟨⟨⟩, s₁, tagRun, validationBind⟩ := bind_ok.mp compiled
            obtain ⟨⟨⟩, s₂, payloadRun, paddingBind⟩ := bind_ok.mp validationBind
            obtain ⟨⟨⟩, s₃, paddingRun, tailRun⟩ := bind_ok.mp paddingBind
            have tagExtension := equation_extends tagRun
            obtain ⟨⟨layouts, tupleEq⟩, layoutProper⟩ := proper (name, layout) (by simp)
            obtain ⟨payloadExtension, payloadMeaning⟩ := validate_sound
              layoutProper (safe _ (by simp)) payloadRun
            have paddingRun' : (do for word in payload.drop layout.width do equation branch word : Build F Unit)
                s₂ = .ok ((), s₃) := bind_ok.mpr ⟨(), s₃, paddingRun, rfl⟩
            have paddingExtension := equations_extends paddingRun'
            obtain ⟨tailExtension, tailMeaning⟩ := validateConstructors_sound
              (fun p h => proper p (by simp [h])) tags.tail (fun p h => safe p (by simp [h])) tailRun
            have beforePadding := tagExtension.trans payloadExtension
            have beforeTail := beforePadding.trans paddingExtension
            refine ⟨beforeTail.trans tailExtension, fun rom calls assignment root valid => ?_⟩
            obtain ⟨s₃valid, tails⟩ := tailMeaning rom calls assignment (beforeTail.active root) valid
            obtain ⟨s₂valid, padding⟩ := equations_sound paddingRun' s₃valid
            obtain ⟨s₁valid, payloads⟩ := payloadMeaning rom calls assignment (tagExtension.active root) s₂valid
            obtain ⟨previous, tagEquation⟩ := equation_valid tagRun s₁valid
            refine ⟨previous, fun selected member active => ?_⟩
            rcases List.mem_cons.mp member with rfl | member
            · have tagEqual : tag.denote assignment = (index : F) := by
                simpa only [active, Scalar.Circuit.ArithExpr.denote, one_mul, sub_eq_zero] using tagEquation
              obtain ⟨value, decoded⟩ := payloads (tagExtension.active active)
              have type := Layout.decode_type decoded
              rw [tupleEq, Layout.type] at type
              cases value with
              | field | ptr | construct => simp [Value.type] at type
              | tuple values =>
                  have zeros : ((payload.map (Circuit.ArithExpr.denote assignment)).drop layout.width).all
                      (fun x => decide (x = 0)) = true := by
                    have zero : ∀ word ∈ payload.drop layout.width, word.denote assignment = 0 := by
                      intro word member
                      simpa only [beforePadding.active active, one_mul] using padding word member
                    simpa [← List.map_drop] using zero
                  exact ⟨index, le_rfl, by simp, tagEqual, (name, values), by
                    simp [Layout.decodeConstructor, tagEqual, ← List.map_take, decoded, zeros]⟩
            · obtain ⟨actual, lo, hi, tagEqual, value, decoded⟩ := tails selected member (beforeTail.active active)
              have different : tag.denote assignment ≠ (index : F) := by
                intro same
                have equal := tags actual index (by omega) (by simp only [List.length_cons]; omega)
                  le_rfl (by simp) (tagEqual.symm.trans same)
                omega
              exact ⟨actual, by omega, by simp only [List.length_cons]; omega, tagEqual,
                value, by simp [Layout.decodeConstructor, different, decoded]⟩
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

/-- An active validated interface decodes to a canonical typed source value. -/
theorem validateValue_sound {decls : Declarations} (checked : checkDeclarations decls = .ok ())
    (tags : decls.tagsValid F = true) {scope : ScopeId} {wire : Symbolic F} {before after : State F}
    (compiled : validateValue decls scope wire before = .ok ((), after)) :
    before.Extends after ∧ ∀ (rom : WireROM F) (calls : Circuit.CallRelation F) (assignment : Witness → F),
      (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
      before.Valid rom calls assignment ∧ ((before.activation scope).denote assignment = 1 →
        ∃ value, (wire.map (Circuit.ArithExpr.denote assignment)).decode decls = some value) := by
  simp only [validateValue] at compiled
  obtain ⟨layout, middle, expanded, run⟩ := bind_ok.mp compiled
  obtain ⟨expansion, stateEq⟩ := getLayout_eq expanded
  subst middle
  obtain ⟨extension, meaning⟩ := validate_sound (Declarations.layout_describes expansion).tuplePayloads
    (Declarations.layout_tagSafe tags expansion) run
  refine ⟨extension, fun rom calls assignment root valid => ?_⟩
  obtain ⟨previous, decoded⟩ := meaning rom calls assignment root valid
  refine ⟨previous, fun active => ?_⟩
  obtain ⟨value, decoded⟩ := decoded active
  exact ⟨value, WireValue.decode_of_layout (wire := wire.map (Circuit.ArithExpr.denote assignment))
    checked expansion decoded⟩

theorem validateValues_sound {decls : Declarations} (checked : checkDeclarations decls = .ok ())
    (tags : decls.tagsValid F = true) {scope : ScopeId} {wires : List (Symbolic F)} {before after : State F}
    (compiled : (do for wire in wires do validateValue decls scope wire : Build F Unit)
      before = .ok ((), after)) :
    before.Extends after ∧ ∀ (rom : WireROM F) (calls : Circuit.CallRelation F) (assignment : Witness → F),
      (before.activation 0).denote assignment = 1 → after.Valid rom calls assignment →
      before.Valid rom calls assignment ∧ ((before.activation scope).denote assignment = 1 →
        ∀ wire ∈ wires, ∃ value, (wire.map (Circuit.ArithExpr.denote assignment)).decode decls = some value) := by
  induction wires generalizing before with
  | nil =>
      have same : before = after := by
        simpa [List.forIn_nil, pure, StateT.pure, StateT.bind, bind, Except.bind, Except.pure] using compiled
      subst after
      exact ⟨.refl _, fun _ _ _ _ valid => ⟨valid, by simp⟩⟩
  | cons wire wires ih =>
      simp only [List.forIn_cons, bind_assoc, pure_bind] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨headExtension, headMeaning⟩ := validateValue_sound checked tags headRun
      obtain ⟨tailExtension, tailMeaning⟩ := ih tailRun
      refine ⟨headExtension.trans tailExtension, fun rom calls assignment root valid => ?_⟩
      obtain ⟨middleValid, tail⟩ := tailMeaning rom calls assignment (headExtension.active root) valid
      obtain ⟨previous, head⟩ := headMeaning rom calls assignment root middleValid
      exact ⟨previous, fun active => by
        simpa using And.intro (head active) (tail (headExtension.active active))⟩

end Aiur.Optimized.Compiler
