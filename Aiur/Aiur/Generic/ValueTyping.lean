import Aiur.Generic.Runtime
import Aiur.ValueFormed

namespace Aiur.Generic

/-- The declarations needed to validate an actual value. Pointer targets are
opaque here; the typechecker separately validates their names and layouts. -/
def knownType (decls : Declarations) : Aiur.Ty → Bool
  | .field | .ptr _ => true
  | .tuple ts => (ts.map (knownType decls)).all id
  | .enum n => (decls.findEnum? n).isSome
termination_by t => sizeOf t

def closedEnums (decls : Declarations) : Prop :=
  ∀ d ∈ decls, ∀ c ∈ d.constructors, ∀ t ∈ c.fields, knownType decls t = true

instance (decls : Declarations) : Decidable (closedEnums decls) :=
  inferInstanceAs (Decidable (∀ d ∈ decls, ∀ c ∈ d.constructors, ∀ t ∈ c.fields, knownType decls t = true))

theorem formed_agrees {enums : String → Option Aiur.EnumDecl} {decls : Declarations}
    (agree : ∀ n d, decls.findEnum? n = some d → enums n = some d)
    (closed : closedEnums decls) (v : Value F A) (known : knownType decls v.type = true) :
    wellFormed enums v = v.wellFormed decls := by
  cases v with
  | field | ptr => simp [wellFormed, Value.wellFormed]
  | tuple xs =>
      simp only [Value.type, knownType, List.all_map, List.all_eq_true, Function.comp_def, id_eq] at known
      simp only [wellFormed, Value.wellFormed]
      congr 1
      apply List.map_congr_left
      intro v hv
      exact formed_agrees agree closed v (known v hv)
  | construct n c xs =>
      cases found : decls.findEnum? n with
      | none => simp [Value.type, knownType, found] at known
      | some d =>
          have resolved := agree n d found
          simp only [wellFormed, Value.wellFormed, Declarations.findConstructor?, found,
            resolved, bind, Option.bind]
          cases ctor : d.constructors.find? (·.name == c) with
          | none => rfl
          | some definition =>
              by_cases types : xs.map Value.type = definition.fields
              · simp only [types, decide_true, Bool.true_and]
                congr 1
                apply List.map_congr_left
                intro v hv
                apply formed_agrees agree closed v
                apply closed d (List.mem_of_find?_eq_some found) definition (List.mem_of_find?_eq_some ctor)
                rw [← types]
                exact List.mem_map.mpr ⟨v, hv, rfl⟩
              · simp [types]
termination_by sizeOf v

theorem hasType_agrees {enums : String → Option Aiur.EnumDecl} {decls : Declarations}
    (agree : ∀ n d, decls.findEnum? n = some d → enums n = some d)
    (closed : closedEnums decls) (t : Aiur.Ty) (known : knownType decls t = true) (v : Value F A) :
    hasType enums t v = v.hasType decls t := by
  by_cases same : v.type = t
  · simp [hasType, Value.hasType, same, formed_agrees agree closed v (by simpa [same] using known)]
  · simp [hasType, Value.hasType, same]

end Aiur.Generic
