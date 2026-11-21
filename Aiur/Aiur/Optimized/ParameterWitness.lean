import Aiur.Optimized.PrimitiveWitness
import Aiur.Optimized.ScopedInvariant
import Aiur.Circuit.ParameterWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]

theorem freshValues_decoded_complete {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {role : Role} {types : List Ty} {vars : List (WireValue Witness)} {before after : State F}
    (compiled : (types.mapM (freshValue decls role)) before = .ok (vars, after))
    {rom : WireROM F} {calls : Circuit.CallRelation F} {initial : Witness → F}
    (layout : before.toReference.WellFormed) (valid : before.Valid rom calls initial)
    (values : List (Value F)) (shape : values.map Value.type = types)
    (formed : ∀ value ∈ values, value.wellFormed decls = true) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      (∀ wire ∈ vars, Circuit.Compiler.Bounded (F := F) after.roles.size (wire.map Polynomial.var)) ∧
      DecodesValues decls (vars.map (WireValue.map assignment)) values := by
  induction values generalizing vars types before initial with
  | nil =>
      subst types
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.map_nil, List.mapM_nil, List.reverse_nil] using compiled)
      exact ⟨initial, .refl layout ((before.valid_iff_reference rom calls initial).mp valid), by simp, .nil⟩
  | cons value values ih =>
      subst types
      simp only [List.map_cons, List.mapM_cons] at compiled
      obtain ⟨head, middle, headRun, tailBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp tailBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨a, headExt, headBound, headDecode⟩ := freshValue_decoded_complete checked tags headRun
        layout valid value rfl (formed _ (by simp))
      obtain ⟨b, tailExt, tailBound, tailDecode⟩ := ih tailRun headExt.layout headExt.validAssignment rfl
        (fun v h => formed v (by simp [h]))
      refine ⟨b, headExt.trans tailExt, ?_, .cons ?_ tailDecode⟩
      · simpa [State.toReference] using And.intro (headBound.mono tailExt.increase) tailBound
      · rw [tailExt.variables headBound]
        exact headDecode

theorem freshValues_scoped {decls : Declarations} {role : Role} {types : List Ty}
    {vars : List (WireValue Witness)} {before after : State F}
    (compiled : (types.mapM (freshValue decls role)) before = .ok (vars, after))
    (scopeLayout : before.Scoped) : after.Scoped := by
  induction types generalizing vars before with
  | nil =>
      obtain ⟨rfl, rfl⟩ := pure_ok.mp (by simpa only [List.map_nil, List.mapM_nil, List.reverse_nil] using compiled)
      exact scopeLayout
  | cons type types ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨head, middle, headRun, tailBind⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp tailBind
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      exact ih tailRun (freshValue_scoped headRun scopeLayout)

theorem validateValues_scoped {decls : Declarations} {scope : ScopeId} {wires : List (Symbolic F)}
    {before after : State F}
    (compiled : (do for wire in wires do validateValue decls scope wire : Build F Unit)
      before = .ok ((), after))
    (scopeLayout : before.Scoped) (scopeValid : scope < before.scopes.size) :
    before.Extends after ∧ after.Scoped := by
  obtain ⟨⟨⟩, middle, loopRun, finished⟩ := bind_ok.mp compiled
  obtain ⟨_, rfl⟩ := pure_ok.mp finished
  exact forIn_scoped loopRun scopeLayout scopeValid
    (fun _ _ {_ _} run layout bound => validateValue_scoped run layout bound)

end Aiur.Optimized.Compiler
