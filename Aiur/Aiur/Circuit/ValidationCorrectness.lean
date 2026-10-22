import Aiur.Circuit.Indicator
import Aiur.WireCodec
import Aiur.LayoutShape
import Aiur.EncodingTypes

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

set_option maxHeartbeats 1000000

theorem zeroWords_sound [Field F] {enable : ArithExpr F} {words : List (ArithExpr F)}
    {before after : BuildState F} (compiled : zeroWords enable words before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧
      (enable.denote assignment = 1 → ∀ word ∈ words, word.denote assignment = 0) := by
  induction words generalizing before with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_ok.mp compiled
      exact ⟨valid, by simp⟩
  | cons word words ih =>
      simp only [zeroWords] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨middleValid, zeros⟩ := ih tailRun
      obtain ⟨previous, equation⟩ := constrain_valid headRun middleValid
      refine ⟨previous, fun active => ?_⟩
      change enable.denote assignment * word.denote assignment = 0 at equation
      simp only [active, one_mul] at equation
      simpa [equation] using zeros active

mutual
  /-- Satisfying the active validation equations guarantees a canonical decoded value. -/
  theorem validate_sound [Field F] [DecidableEq F] {layout : Layout}
      (proper : layout.TuplePayloads) {enable : ArithExpr F} {words : List (ArithExpr F)}
      {before after : BuildState F} (compiled : validate layout enable words before = .ok ((), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ (enable.denote assignment = 1 →
        ∃ value, layout.decode (words.map (ArithExpr.denote assignment)) = some value) := by
    cases layout with
    | field =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest =>
            cases rest with
            | cons => simp [validate] at compiled
            | nil =>
                simp only [validate] at compiled
                obtain ⟨_, rfl⟩ := pure_ok.mp compiled
                exact ⟨valid, fun _ => ⟨.field (word.denote assignment), by simp [Layout.decode]⟩⟩
    | ptr target =>
        cases words with
        | nil => simp [validate] at compiled
        | cons word rest =>
            cases rest with
            | cons => simp [validate] at compiled
            | nil =>
                simp only [validate] at compiled
                obtain ⟨_, rfl⟩ := pure_ok.mp compiled
                exact ⟨valid, fun _ => ⟨.ptr target (word.denote assignment), by simp [Layout.decode]⟩⟩
    | tuple layouts =>
        simp only [validate] at compiled
        obtain ⟨previous, decoded⟩ := validateList_sound
          (by simpa only [Layout.TuplePayloads] using proper) compiled valid
        exact ⟨previous, fun active => by
          obtain ⟨values, decoded⟩ := decoded active
          exact ⟨.tuple values, by simp [Layout.decode, decoded]⟩⟩
    | enum name constructors =>
        simp only [validate] at compiled
        cases parts : Layout.enumParts constructors.length (.const 0) words with
        | none => simp [parts] at compiled
        | some pair =>
            rcases pair with ⟨tag, payload⟩
            simp only [parts] at compiled
            split at compiled
            · simp [StateT.bind, bind, Except.bind] at compiled
            · rename_i length
              have length : payload.length = Layout.payloadWidth constructors := by simpa using length
              obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
              obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
              obtain ⟨tests, middle, ctorRun, sumRun⟩ := bind_ok.mp rest
              obtain ⟨middleValid, sumEquation⟩ := constrain_valid sumRun valid
              obtain ⟨previous, choices⟩ := validateConstructors_sound
                (by simpa only [Layout.TuplePayloads] using proper) ctorRun middleValid
              refine ⟨previous, fun active => ?_⟩
              rcases choices active with ⟨⟨ctor, args⟩, decoded⟩ | absent
              · exact ⟨.construct name ctor args, by simp [Layout.decode, Circuit.Compiler.enumParts_denote parts assignment, length, decoded]⟩
              · have zero : (tests.map (ArithExpr.denote assignment)).sum = 0 :=
                  List.sum_eq_zero (by simpa using absent)
                have sum : (tests.map (ArithExpr.denote assignment)).sum = 1 := by
                  simpa [Scalar.Circuit.ArithExpr.denote, Scalar.Circuit.ArithExpr.denote_foldl_add,
                    active, sub_eq_zero] using sumEquation
                exact (zero_ne_one (zero.symm.trans sum)).elim
  termination_by sizeOf layout

  theorem validateList_sound [Field F] [DecidableEq F] {layouts : List Layout}
      (proper : ∀ layout ∈ layouts, layout.TuplePayloads) {enable : ArithExpr F} {words : List (ArithExpr F)}
      {before after : BuildState F} (compiled : validateList layouts enable words before = .ok ((), after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ (enable.denote assignment = 1 →
        ∃ values, Layout.decodeList layouts (words.map (ArithExpr.denote assignment)) = some values) := by
    cases layouts with
    | nil =>
        cases words with
        | nil =>
            simp only [validateList] at compiled
            obtain ⟨_, rfl⟩ := pure_ok.mp compiled
            exact ⟨valid, fun _ => ⟨[], by simp [Layout.decodeList]⟩⟩
        | cons => simp [validateList] at compiled
    | cons layout layouts =>
        simp only [validateList] at compiled
        split at compiled
        · simp [StateT.bind, bind, Except.bind] at compiled
        · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp compiled
          obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
          obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp rest
          obtain ⟨middleValid, tails⟩ := validateList_sound (fun l h => proper l (by simp [h])) tailRun valid
          obtain ⟨previous, heads⟩ := validate_sound (proper _ (by simp)) headRun middleValid
          refine ⟨previous, fun active => ?_⟩
          obtain ⟨head, headDecode⟩ := heads active
          obtain ⟨tail, tailDecode⟩ := tails active
          exact ⟨head :: tail, by simp [Layout.decodeList, ← List.map_take, ← List.map_drop, headDecode, tailDecode]⟩
  termination_by sizeOf layouts

  theorem validateConstructors_sound [Field F] [DecidableEq F]
      {constructors : List (String × Layout)}
      (proper : ∀ pair ∈ constructors,
        (∃ layouts, pair.2 = .tuple layouts) ∧ pair.2.TuplePayloads)
      {enable tag : ArithExpr F} {payload tests : List (ArithExpr F)} {index : Nat}
      {before after : BuildState F}
      (compiled : validateConstructors constructors enable tag payload index before = .ok (tests, after))
      {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
      before.Valid rom calls assignment ∧ (enable.denote assignment = 1 →
        (∃ value, Layout.decodeConstructor constructors (tag.denote assignment)
          (payload.map (ArithExpr.denote assignment)) index = some value) ∨
          (∀ test ∈ tests, test.denote assignment = 0)) := by
    cases constructors with
    | nil =>
        simp only [validateConstructors] at compiled
        obtain ⟨rfl, rfl⟩ := pure_ok.mp compiled
        exact ⟨valid, fun _ => Or.inr (by simp)⟩
    | cons pair constructors =>
        rcases hpair : pair with ⟨name, layout⟩
        rw [hpair] at compiled proper
        simp only [validateConstructors] at compiled
        obtain ⟨test, s₁, indicatorRun, rest⟩ := bind_ok.mp compiled
        obtain ⟨⟨⟩, s₂, payloadRun, rest⟩ := bind_ok.mp rest
        obtain ⟨⟨⟩, s₃, paddingRun, rest⟩ := bind_ok.mp rest
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨s₃valid, tails⟩ := validateConstructors_sound (fun p h => proper p (by simp [h])) tailRun valid
        obtain ⟨s₂valid, padding⟩ := zeroWords_sound paddingRun s₃valid
        obtain ⟨⟨layouts, tupleEq⟩, layoutProper⟩ := proper (name, layout) (by simp)
        obtain ⟨s₁valid, payloads⟩ := validate_sound layoutProper payloadRun s₂valid
        obtain ⟨previous, indicator⟩ := equalIndicator_sound indicatorRun s₁valid
        refine ⟨previous, fun active => ?_⟩
        change test.denote assignment = if tag.denote assignment - (index : F) = 0 then 1 else 0 at indicator
        by_cases matchedTag : tag.denote assignment = (index : F)
        · have selected : (ArithExpr.mul enable test).denote assignment = 1 := by
            simp [Scalar.Circuit.ArithExpr.denote, active, indicator, matchedTag]
          obtain ⟨value, decoded⟩ := payloads selected
          have type := Layout.decode_type decoded
          rw [tupleEq, Layout.type] at type
          cases value with
          | field | ptr | construct => simp [Value.type] at type
          | tuple values =>
              have zeros : ((payload.map (ArithExpr.denote assignment)).drop layout.width).all
                  (fun x => decide (x = 0)) = true := by
                simpa [← List.map_drop] using padding selected
              exact Or.inl ⟨(name, values), by
                simp [Layout.decodeConstructor, matchedTag, ← List.map_take, decoded, zeros]⟩
        · simp only [sub_eq_zero, matchedTag, ↓reduceIte] at indicator
          rcases tails active with ⟨value, decoded⟩ | absent
          · exact Or.inl ⟨value, by simp [Layout.decodeConstructor, matchedTag, decoded]⟩
          · exact Or.inr (by simpa [indicator] using absent)
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

/-- Active interface and ROM encodings have a well-formed nominal source value. -/
theorem validateValue_sound [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {enable : ArithExpr F} {wire : Symbolic F}
    {before after : BuildState F}
    (compiled : validateValue decls enable wire before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧ (enable.denote assignment = 1 →
      ∃ value, (wire.map (ArithExpr.denote assignment)).decode decls = some value) := by
  simp only [validateValue] at compiled
  obtain ⟨layout, middle, expanded, run⟩ := bind_ok.mp compiled
  obtain ⟨expansion, rfl⟩ := getLayout_eq expanded
  obtain ⟨previous, decoded⟩ := validate_sound (Declarations.layout_describes expansion).tuplePayloads run valid
  refine ⟨previous, fun active => ?_⟩
  obtain ⟨value, decoded⟩ := decoded active
  exact ⟨value, WireValue.decode_of_layout (wire := wire.map (ArithExpr.denote assignment)) checked expansion decoded⟩

theorem validateValues_sound [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {enable : ArithExpr F} {wires : List (Symbolic F)}
    {before after : BuildState F}
    (compiled : validateValues decls enable wires before = .ok ((), after))
    {calls : CallRelation F} {assignment : Var → F} (valid : after.Valid rom calls assignment) :
    before.Valid rom calls assignment ∧ (enable.denote assignment = 1 →
      ∀ wire ∈ wires, ∃ value, (wire.map (ArithExpr.denote assignment)).decode decls = some value) := by
  induction wires generalizing before with
  | nil =>
      obtain ⟨_, rfl⟩ := pure_ok.mp compiled
      exact ⟨valid, by simp⟩
  | cons wire wires ih =>
      simp only [validateValues] at compiled
      obtain ⟨⟨⟩, middle, headRun, tailRun⟩ := bind_ok.mp compiled
      obtain ⟨middleValid, tails⟩ := ih tailRun
      obtain ⟨beforeValid, head⟩ := validateValue_sound checked headRun middleValid
      exact ⟨beforeValid, fun active => by simpa using And.intro (head active) (tails active)⟩

end Aiur.Circuit.Compiler
