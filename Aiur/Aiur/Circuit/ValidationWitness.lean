import Aiur.Circuit.IndicatorWitness
import Aiur.Circuit.ValidationCorrectness
import Aiur.LayoutValidation
import Aiur.Scalar.Circuit.WitnessBasic

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

set_option maxHeartbeats 1600000

theorem Extension.words [Field F] {calls : CallRelation F} {before after : BuildState F}
    {a b : Var → F} (extension : Extension rom calls before after a b) {words : List (ArithExpr F)}
    (bounded : ∀ word ∈ words, word.inBounds before.nextVar = true) :
    words.map (ArithExpr.denote b) = words.map (ArithExpr.denote a) :=
  List.map_congr_left (fun word member => extension.polynomial (bounded word member))

theorem zeroWords_complete [Field F] {enable : ArithExpr F} {words : List (ArithExpr F)}
    {before after : BuildState F} (compiled : zeroWords enable words before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (enableBound : enable.inBounds before.nextVar = true)
    (bounded : ∀ word ∈ words, word.inBounds before.nextVar = true)
    (zero : enable.denote assignment = 0 ∨ ∀ word ∈ words, word.denote assignment = 0) :
    Extension rom calls before after assignment assignment := by
  induction words generalizing before with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_ok.mp compiled
      exact .refl layout valid
  | cons word words ih =>
      simp only [zeroWords] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      have ext := guarded_complete headRun layout valid enableBound (bounded _ (by simp))
        (zero.imp_right (fun zeros => zeros _ (by simp)))
      exact ext.trans (ih tailRun ext.layout ext.valid (ext.bound enableBound)
        (fun p h => ext.bound (bounded p (by simp [h])))
        (zero.imp_right (fun zeros p h => zeros p (by simp [h]))))

mutual
  /-- Validation adds witnesses for any canonical value, or for arbitrary inactive words. -/
  theorem validate_complete [Field F] [DecidableEq F] {type : Layout}
      {enable : ArithExpr F} {words : List (ArithExpr F)} {before after : BuildState F}
      (compiled : validate type enable words before = .ok ((), after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid rom calls initial)
      (enableBound : enable.inBounds before.nextVar = true)
      (bounded : ∀ word ∈ words, word.inBounds before.nextVar = true)
      (admissible : enable.denote initial = 0 ∨ type.Admissible (words.map (ArithExpr.denote initial))) :
      ∃ assignment, Extension rom calls before after initial assignment := by
    cases type with
    | field =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest => cases rest with
          | cons => simp [validate] at compiled
          | nil =>
              obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
              exact ⟨initial, .refl layout valid⟩
    | ptr target =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest => cases rest with
          | cons => simp [validate] at compiled
          | nil =>
              obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validate] using compiled)
              exact ⟨initial, .refl layout valid⟩
    | tuple layouts =>
        exact validateList_complete (by simpa only [validate] using compiled) layout valid enableBound bounded
          (by simpa only [Layout.Admissible] using admissible)
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
              obtain ⟨tests, middle, ctorRun, sumRun⟩ := bind_ok.mp rest
              obtain ⟨tagBound, payloadBound⟩ := Layout.enumParts_all parts (by rfl) bounded
              have choices : enable.denote initial = 0 ∨ Layout.AdmissibleConstructors constructors
                  (tag.denote initial) (payload.map (ArithExpr.denote initial)) 0 := by
                rcases admissible with zero | formed
                · exact Or.inl zero
                · simp only [Layout.Admissible, Nat.cast_zero, Circuit.Compiler.enumParts_denote parts initial] at formed
                  exact Or.inr formed.2.2
              obtain ⟨a, ext, testsBound, testsEq⟩ := validateConstructors_complete ctorRun layout valid
                enableBound tagBound payloadBound choices
              have sumBound : (tests.foldl ArithExpr.add (.const (0 : F))).inBounds middle.nextVar = true := by
                exact Scalar.Circuit.Compiler.foldl_add_inBounds (by rfl) testsBound
              have zero : enable.denote a = 0 ∨
                  (ArithExpr.sub (tests.foldl ArithExpr.add (.const (0 : F))) (.const 1)).denote a = 0 := by
                rcases admissible with h | h
                · exact Or.inl ((ext.polynomial enableBound).trans h)
                · right
                  simp only [Layout.Admissible, Nat.cast_zero, Circuit.Compiler.enumParts_denote parts initial] at h
                  simpa [Scalar.Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote_foldl_add,
                    testsEq, h.2.1]
              have last := guarded_complete sumRun ext.layout ext.valid (ext.bound enableBound)
                (by simpa [Scalar.Circuit.ArithExpr.inBounds] using sumBound) zero
              exact ⟨a, ext.trans last⟩
  termination_by sizeOf type

  theorem validateList_complete [Field F] [DecidableEq F] {types : List Layout}
      {enable : ArithExpr F} {words : List (ArithExpr F)} {before after : BuildState F}
      (compiled : validateList types enable words before = .ok ((), after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid rom calls initial)
      (enableBound : enable.inBounds before.nextVar = true)
      (bounded : ∀ word ∈ words, word.inBounds before.nextVar = true)
      (admissible : enable.denote initial = 0 ∨ Layout.AdmissibleList types (words.map (ArithExpr.denote initial))) :
      ∃ assignment, Extension rom calls before after initial assignment := by
    cases types with
    | nil => cases words with
      | nil =>
          obtain ⟨_, rfl⟩ := pure_ok.mp (by simpa only [validateList] using compiled)
          exact ⟨initial, .refl layout valid⟩
      | cons => simp [validateList] at compiled
    | cons type types =>
        simp only [validateList] at compiled
        split at compiled
        · simp [StateT.bind, bind, Except.bind] at compiled
        · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
          obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
          obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp rest
          have headBound : ∀ p ∈ words.take type.width, p.inBounds before.nextVar = true :=
            fun p h => bounded p (List.mem_of_mem_take h)
          have tailBound : ∀ p ∈ words.drop type.width, p.inBounds before.nextVar = true :=
            fun p h => bounded p (List.mem_of_mem_drop h)
          have headAdmissible : enable.denote initial = 0 ∨
              type.Admissible ((words.take type.width).map (ArithExpr.denote initial)) := by
            rcases admissible with zero | good
            · exact Or.inl zero
            · simp only [Layout.AdmissibleList] at good
              exact Or.inr (by simpa only [List.map_take] using good.1)
          obtain ⟨a, headExt⟩ := validate_complete headRun layout valid enableBound headBound headAdmissible
          have tailAdmissible : enable.denote a = 0 ∨
              Layout.AdmissibleList types ((words.drop type.width).map (ArithExpr.denote a)) := by
            rw [headExt.polynomial enableBound, headExt.words tailBound]
            rcases admissible with zero | good
            · exact Or.inl zero
            · simp only [Layout.AdmissibleList] at good
              exact Or.inr (by simpa only [List.map_drop] using good.2)
          obtain ⟨b, tailExt⟩ := validateList_complete tailRun headExt.layout headExt.valid
            (headExt.bound enableBound) (fun p h => headExt.bound (tailBound p h)) tailAdmissible
          exact ⟨b, headExt.trans tailExt⟩
  termination_by sizeOf types

  theorem validateConstructors_complete [Field F] [DecidableEq F]
      {constructors : List (String × Layout)} {enable tag : ArithExpr F}
      {payload tests : List (ArithExpr F)} {index : Nat} {before after : BuildState F}
      (compiled : validateConstructors constructors enable tag payload index before = .ok (tests, after))
      {calls : CallRelation F} {initial : Var → F}
      (layout : before.WellFormed) (valid : before.Valid rom calls initial)
      (enableBound : enable.inBounds before.nextVar = true)
      (tagBound : tag.inBounds before.nextVar = true)
      (bounded : ∀ word ∈ payload, word.inBounds before.nextVar = true)
      (admissible : enable.denote initial = 0 ∨ Layout.AdmissibleConstructors constructors
        (tag.denote initial) (payload.map (ArithExpr.denote initial)) index) :
      ∃ assignment, Extension rom calls before after initial assignment ∧
        (∀ test ∈ tests, test.inBounds after.nextVar = true) ∧
        tests.map (ArithExpr.denote assignment) = tagTests constructors.length (tag.denote initial) index := by
    cases constructors with
    | nil =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [validateConstructors] using compiled)
        exact ⟨initial, .refl layout valid, by simp, rfl⟩
    | cons pair rest =>
        rcases hpair : pair with ⟨name, type⟩
        rw [hpair] at compiled admissible
        simp only [validateConstructors] at compiled
        obtain ⟨test, s₁, indicatorRun, run⟩ := bind_ok.mp compiled
        obtain ⟨⟨⟩, s₂, payloadRun, run⟩ := bind_ok.mp run
        obtain ⟨⟨⟩, s₃, paddingRun, run⟩ := bind_ok.mp run
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp run
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨a, testExt, testBound⟩ := equalIndicator_complete indicatorRun layout valid
          (by simpa [Scalar.Circuit.ArithExpr.inBounds] using tagBound)
        have testEq : test.denote a = if tag.denote initial = (index : F) then 1 else 0 := by
          have matched := (equalIndicator_sound indicatorRun testExt.valid).2
          simpa [Scalar.Circuit.ArithExpr.denote, testExt.polynomial tagBound, sub_eq_zero] using matched
        have selectedBound : (ArithExpr.mul enable test).inBounds s₁.nextVar = true := by
          simp [Scalar.Circuit.ArithExpr.inBounds, testExt.bound enableBound, testBound]
        have headBound : ∀ p ∈ payload.take type.width, p.inBounds before.nextVar = true :=
          fun p h => bounded p (List.mem_of_mem_take h)
        have padBound : ∀ p ∈ payload.drop type.width, p.inBounds before.nextVar = true :=
          fun p h => bounded p (List.mem_of_mem_drop h)
        have headAdmissible : (ArithExpr.mul enable test).denote a = 0 ∨
            type.Admissible ((payload.take type.width).map (ArithExpr.denote a)) := by
          rw [testExt.words headBound]
          rcases admissible with zero | good
          · left; simp [Scalar.Circuit.ArithExpr.denote, testExt.polynomial enableBound, zero]
          · simp only [Layout.AdmissibleConstructors] at good
            by_cases selected : tag.denote initial = (index : F)
            · exact Or.inr (by simpa only [List.map_take] using (good.1 selected).1)
            · left; simp [Scalar.Circuit.ArithExpr.denote, testEq, selected]
        obtain ⟨b, payloadExt⟩ := validate_complete payloadRun testExt.layout testExt.valid selectedBound
          (fun p h => testExt.bound (headBound p h)) headAdmissible
        have untilPayload := testExt.trans payloadExt
        have paddingZero : (ArithExpr.mul enable test).denote b = 0 ∨
            ∀ p ∈ payload.drop type.width, p.denote b = 0 := by
          change ArithExpr.denote b (.mul enable test) = 0 ∨ _
          rw [payloadExt.polynomial selectedBound]
          rcases admissible with zero | good
          · left; simp [Scalar.Circuit.ArithExpr.denote, testExt.polynomial enableBound, zero]
          · simp only [Layout.AdmissibleConstructors] at good
            by_cases selected : tag.denote initial = (index : F)
            · right
              intro p member
              rw [untilPayload.polynomial (padBound p member)]
              exact (good.1 selected).2 _ (by rw [← List.map_drop]; exact List.mem_map.mpr ⟨p, member, rfl⟩)
            · left; simp [Scalar.Circuit.ArithExpr.denote, testEq, selected]
        have paddingExt := zeroWords_complete paddingRun payloadExt.layout payloadExt.valid
          (payloadExt.bound selectedBound) (fun p h => untilPayload.bound (padBound p h)) paddingZero
        have throughPadding := untilPayload.trans paddingExt
        have tailAdmissible : enable.denote b = 0 ∨ Layout.AdmissibleConstructors rest
            (tag.denote b) (payload.map (ArithExpr.denote b)) (index + 1) := by
          rw [throughPadding.polynomial enableBound, throughPadding.polynomial tagBound, throughPadding.words bounded]
          exact admissible.imp_right (fun good => by
            simp only [Layout.AdmissibleConstructors] at good
            exact good.2)
        obtain ⟨c, tailExt, tailBound, tailEq⟩ := validateConstructors_complete tailRun throughPadding.layout throughPadding.valid
          (throughPadding.bound enableBound) (throughPadding.bound tagBound) (fun p h => throughPadding.bound (bounded p h)) tailAdmissible
        have suffix := (payloadExt.trans paddingExt).trans tailExt
        refine ⟨c, throughPadding.trans tailExt, ?_, ?_⟩
        · simpa using And.intro (suffix.bound testBound) tailBound
        · simp only [List.map_cons, suffix.polynomial testBound, testEq, tailEq,
            throughPadding.polynomial tagBound, List.length_cons, tagTests]
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

theorem validateValue_complete [Field F] [DecidableEq F] {decls : Declarations}
    (tags : decls.tagsValid F = true) {enable : ArithExpr F} {wire : Symbolic F}
    {before after : BuildState F}
    (compiled : validateValue decls enable wire before = .ok ((), after))
    {calls : CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (enableBound : enable.inBounds before.nextVar = true) (bounded : Bounded before.nextVar wire)
    (decodable : enable.denote initial = 0 ∨
      ∃ value, (wire.map (ArithExpr.denote initial)).decode decls = some value) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  simp only [validateValue] at compiled
  obtain ⟨type, middle, expanded, run⟩ := bind_ok.mp compiled
  obtain ⟨expansion, rfl⟩ := getLayout_eq expanded
  apply validate_complete run layout valid enableBound bounded
  rcases decodable with zero | ⟨value, decoded⟩
  · exact Or.inl zero
  · obtain ⟨_, _, other, found, decoded⟩ := WireValue.decode_spec decoded
    simp only [WireValue.type_map, expansion, Except.ok.injEq] at found
    subst other
    exact Or.inr (Layout.decode_admissible (Declarations.layout_tagSafe tags expansion) decoded)

theorem validateValues_complete [Field F] [DecidableEq F] {decls : Declarations}
    (tags : decls.tagsValid F = true) {enable : ArithExpr F} {wires : List (Symbolic F)}
    {before after : BuildState F}
    (compiled : validateValues decls enable wires before = .ok ((), after))
    {calls : CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (enableBound : enable.inBounds before.nextVar = true)
    (bounded : ∀ wire ∈ wires, Bounded before.nextVar wire)
    (decodable : enable.denote initial = 0 ∨
      ∀ wire ∈ wires, ∃ value, (wire.map (ArithExpr.denote initial)).decode decls = some value) :
    ∃ assignment, Extension rom calls before after initial assignment := by
  induction wires generalizing before initial with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_ok.mp compiled
      exact ⟨initial, .refl layout valid⟩
  | cons wire wires ih =>
      simp only [validateValues] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨a, headExt⟩ := validateValue_complete tags headRun layout valid enableBound
        (bounded _ (by simp)) (decodable.imp_right (fun h => h _ (by simp)))
      obtain ⟨b, tailExt⟩ := ih tailRun headExt.layout headExt.valid (headExt.bound enableBound)
        (fun w h => (bounded w (by simp [h])).mono headExt.increase) (by
          rw [headExt.polynomial enableBound]
          rcases decodable with zero | good
          · exact Or.inl zero
          · right
            intro w member
            rw [headExt.value (bounded w (by simp [member]))]
            exact good w (by simp [member]))
      exact ⟨b, headExt.trans tailExt⟩

end Aiur.Circuit.Compiler
