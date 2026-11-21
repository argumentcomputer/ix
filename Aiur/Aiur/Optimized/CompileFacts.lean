import Aiur.Optimized.ReferenceState

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

theorem fresh_extends {role : Role} {id : Witness} {before after : State F}
    (compiled : fresh role before = .ok (id, after)) : before.Extends after := by
  obtain ⟨_, rfl⟩ := fresh_eq compiled
  exact ⟨fun _ _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩

theorem freshList_preserves {α : Type} {items : List α} {role : Role}
    {ids : List Witness} {before after : State F}
    (compiled : (items.mapM (fun _ => fresh role)) before = .ok (ids, after)) :
    after.scopes = before.scopes ∧ after.equations = before.equations ∧
      after.calls = before.calls ∧ after.cells = before.cells := by
  induction items generalizing before ids with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons item items ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨id, middle, headRun, tailBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp tailBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨_, stateEq⟩ := fresh_eq headRun
      subst middle
      simpa only using ih tailRun

theorem freshValue_preserves {decls : Declarations} {role : Role} {type : Ty}
    {value : WireValue Witness} {before after : State F}
    (compiled : freshValue decls role type before = .ok (value, after)) :
    after.scopes = before.scopes ∧ after.equations = before.equations ∧
      after.calls = before.calls ∧ after.cells = before.cells := by
  simp only [freshValue] at compiled
  obtain ⟨layout, middle, expanded, tailBind⟩ := bind_ok.mp compiled
  obtain ⟨_, stateEq⟩ := getLayout_eq expanded
  subst middle
  obtain ⟨words, last, wordsRun, finished⟩ := bind_ok.mp tailBind
  obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
  exact freshList_preserves wordsRun

theorem freshValue_extends {decls : Declarations} {role : Role} {type : Ty}
    {value : WireValue Witness} {before after : State F}
    (compiled : freshValue decls role type before = .ok (value, after)) :
    before.Extends after := by
  obtain ⟨scopes, equations, calls, cells⟩ := freshValue_preserves compiled
  exact ⟨by simpa only [scopes] using (State.Extends.refl before).scopes,
    by simp [equations], by simp [calls], by simp [cells]⟩

theorem freshValue_type {decls : Declarations} {role : Role} {type : Ty}
    {value : WireValue Witness} {before after : State F}
    (compiled : freshValue decls role type before = .ok (value, after)) : value.type = type :=
  (Circuit.Compiler.freshValue_spec (freshValue_reference compiled)).2.2.1

theorem freshValues_preserves {decls : Declarations} {role : Role} {types : List Ty}
    {values : List (WireValue Witness)} {before after : State F}
    (compiled : (types.mapM (freshValue decls role)) before = .ok (values, after)) :
    after.scopes = before.scopes ∧ after.equations = before.equations ∧
      after.calls = before.calls ∧ after.cells = before.cells := by
  induction types generalizing before values with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
      exact ⟨rfl, rfl, rfl, rfl⟩
  | cons type types ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨value, middle, headRun, restBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp restBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨hs, he, hc, hm⟩ := freshValue_preserves headRun
      obtain ⟨ts, te, tc, tm⟩ := ih tailRun
      exact ⟨ts.trans hs, te.trans he, tc.trans hc, tm.trans hm⟩

theorem destination_spec {decls : Declarations} {scope : ScopeId} {type : Ty}
    {target : Option (WireValue Witness)} {value : WireValue Witness} {before after : State F}
    (compiled : destination decls scope type target before = .ok (value, after)) :
    before.Extends after ∧ after.scopes = before.scopes ∧ value.type = type := by
  cases target with
  | none =>
      exact ⟨freshValue_extends compiled, (freshValue_preserves compiled).1, freshValue_type compiled⟩
  | some target =>
      simp only [destination] at compiled
      split at compiled
      · simp [StateT.bind, bind, Except.bind] at compiled
      · rename_i same
        obtain ⟨⟨⟩, middle, emptyRun, finished⟩ := bind_ok.mp compiled
        obtain ⟨_, stateEq⟩ := pure_ok.mp emptyRun
        subst middle
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        exact ⟨.refl _, rfl, Classical.not_not.mp same⟩

theorem lower_target {program : Program F} {function : String} {locals : Locals F}
    {scope : ScopeId} {expr : Expr F} {target : WireValue Witness} {output : Symbolic F}
    {before after : State F}
    (compiled : lower program function locals scope expr (some target) before = .ok (output, after)) :
    output = target.map Polynomial.var := by
  unfold lower at compiled
  obtain ⟨value, middle, _, restBind⟩ := bind_ok.mp compiled
  obtain ⟨_, last, _, finished⟩ := bind_ok.mp restBind
  exact (pure_ok.mp finished).1.symm

theorem destination_extends {decls : Declarations} {scope : ScopeId} {type : Ty}
    {target : Option (WireValue Witness)} {value : WireValue Witness} {before after : State F}
    (compiled : destination decls scope type target before = .ok (value, after)) :
    before.Extends after := (destination_spec compiled).1

theorem destination_valid {decls : Declarations} {scope : ScopeId} {type : Ty}
    {target : Option (WireValue Witness)} {value : WireValue Witness} {before after : State F}
    (compiled : destination decls scope type target before = .ok (value, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {assignment : Witness → F}
    (valid : after.Valid rom calls assignment) : before.Valid rom calls assignment :=
  valid.of_extends (destination_extends compiled)

theorem asField_eq {value : Symbolic F} {polynomial : Polynomial F} {before after : State F}
    (compiled : asField value before = .ok (polynomial, after)) :
    value = .field polynomial ∧ before = after := by
  cases value with
  | mk type words =>
      cases type <;> cases words <;> simp [asField] at compiled
      rename_i word rest
      cases rest <;> simp [asField] at compiled
      obtain ⟨rfl, rfl⟩ := compiled
      exact ⟨rfl, rfl⟩

private theorem except_bind_ok {first : Except ε α} {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [bind, Except.bind]

theorem function_stages {program : Program F} {config : Config} {fn : Function F} {chip : ScopedChip F}
    {validateInputs : Bool} (compiled : function program config fn validateInputs = .ok chip) :
    ∃ (inputs : List (WireValue Witness)) (output : WireValue Witness)
      (s₁ s₂ s₃ : State F) (body : Symbolic F) (s₄ : State F),
      ((fn.params.map Prod.snd).mapM (freshValue program.enums .input))
        ({config, scopes := #[⟨.const 1, []⟩]} : State F) = .ok (inputs, s₁) ∧
      freshValue program.enums .output fn.result s₁ = .ok (output, s₂) ∧
      validateParameters program.enums validateInputs inputs s₂ = .ok ((), s₃) ∧
      lower program fn.name ((fn.params.map Prod.fst).zip (inputs.map (WireValue.map Polynomial.var)))
        0 fn.body (some output) s₃ = .ok (body, s₄) ∧
      chip = ⟨fn.name, inputs, output, s₄.roles, s₄.aliases, s₄.scopes,
        s₄.equations, s₄.calls, s₄.cells, s₄.choices⟩ := by
  unfold function at compiled
  obtain ⟨⟨⟨inputs, output⟩, state⟩, run, finished⟩ := except_bind_ok.mp compiled
  simp only [pure, Except.pure, Except.ok.injEq] at finished
  subst chip
  obtain ⟨inputs, s₁, inputsRun, rest₁⟩ := bind_ok.mp run
  obtain ⟨output, s₂, outputRun, rest₂⟩ := bind_ok.mp rest₁
  obtain ⟨⟨⟩, s₃, inputsValid, rest₃⟩ := bind_ok.mp rest₂
  obtain ⟨body, s₄, bodyRun, rest₄⟩ := bind_ok.mp rest₃
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pure_ok.mp rest₄
  exact ⟨inputs, output, s₁, s₂, s₃, body, s₄,
    inputsRun, outputRun, inputsValid, bodyRun, rfl⟩

theorem freshValues_types {decls : Declarations} {role : Role} {types : List Ty}
    {values : List (WireValue Witness)} {before after : State F}
    (compiled : (types.mapM (freshValue decls role)) before = .ok (values, after)) :
    values.map WireValue.type = types := by
  induction types generalizing before values with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.mapM_nil] using compiled)
      rfl
  | cons type types ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨value, middle, headRun, restBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp restBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      simp only [List.map_cons, freshValue_type headRun, ih tailRun]

theorem function_interface {program : Program F} {config : Config} {fn : Function F} {chip : ScopedChip F}
    {validateInputs : Bool} (compiled : function program config fn validateInputs = .ok chip) :
    chip.name = fn.name ∧ chip.inputs.map WireValue.type = fn.params.map Prod.snd ∧ chip.output.type = fn.result := by
  obtain ⟨_, _, _, _, _, _, _, inputsRun, outputRun, _, _, rfl⟩ := function_stages compiled
  exact ⟨rfl, freshValues_types inputsRun, freshValue_type outputRun⟩

end Aiur.Optimized.Compiler
