import Aiur.LayoutComposition
import Aiur.Memory.Encoding

namespace Aiur

/-- Every pointer annotation in a value names declared types, including nested payloads. -/
def Value.PointerNames (decls : Declarations) : Value F A → Prop
  | .field _ => True
  | .ptr target _ => target.checkNames decls = .ok ()
  | .tuple values | .construct _ _ values => ∀ value ∈ values, value.PointerNames decls
termination_by value => sizeOf value

@[simp] theorem Value.pointerNames_field (decls : Declarations) (x : F) :
    (@Value.field F A x).PointerNames decls := by simp [PointerNames]

@[simp] theorem Value.pointerNames_tuple (decls : Declarations) (values : List (Value F A)) :
    (.tuple values : Value F A).PointerNames decls ↔ ∀ value ∈ values, value.PointerNames decls := by
  rw [PointerNames]

@[simp] theorem Value.pointerNames_construct (decls : Declarations) (name ctor : String) (values : List (Value F A)) :
    (.construct name ctor values : Value F A).PointerNames decls ↔ ∀ value ∈ values, value.PointerNames decls := by
  rw [PointerNames]

theorem Value.pointerNames_of_free {decls : Declarations} {value : Value F A}
    (free : value.pointerFree = true) : value.PointerNames decls := by
  cases value with
  | field => simp [PointerNames]
  | ptr => simp [pointerFree] at free
  | tuple values | construct name ctor values =>
      simp only [PointerNames]
      simp only [pointerFree, List.all_map, List.all_eq_true] at free
      intro value member
      exact value.pointerNames_of_free (free value member)
termination_by sizeOf value

theorem Value.type_names {decls : Declarations} {value : Value F A}
    (formed : value.wellFormed decls = true) (names : value.PointerNames decls) :
    value.type.checkNames decls = .ok () := by
  cases value with
  | field => simp [Value.type, Ty.checkNames]
  | ptr => simpa only [PointerNames, Value.type, Ty.checkNames] using names
  | tuple values =>
      simp only [Value.type, Ty.checkNames]
      apply forIn_success
      intro type member
      obtain ⟨value, valueMember, rfl⟩ := List.mem_map.mp member
      exact Value.type_names ((Value.wellFormed_tuple _ _).mp formed value valueMember)
        ((Value.pointerNames_tuple _ _).mp names value valueMember)
  | construct name ctor values =>
      obtain ⟨definition, found, _, _⟩ := (Value.wellFormed_construct _ _ _ _).mp formed
      cases enumFound : decls.findEnum? name with
      | none => simp [Declarations.findConstructor?, enumFound] at found
      | some declaration => simp [Value.type, Ty.checkNames, enumFound]
termination_by sizeOf value

def Value.Good (decls : Declarations) (value : Value F A) : Prop :=
  value.wellFormed decls = true ∧ value.PointerNames decls

def Environment.Good (decls : Declarations) (locals : Environment F A) : Prop :=
  ∀ binding ∈ locals, binding.2.Good decls

def Heap.Good (decls : Declarations) (heap : Heap F) : Prop :=
  ∀ value ∈ heap, value.Good decls

theorem Environment.Good.formed {decls : Declarations} {locals : Environment F A}
    (good : locals.Good decls) : locals.WellFormed decls := fun binding member => (good binding member).1

@[simp] theorem Environment.good_append {decls : Declarations} {left right : Environment F A} :
    (left ++ right).Good decls ↔ left.Good decls ∧ right.Good decls := by
  simp [Good, or_imp, forall_and]

@[simp] theorem Value.good_field (decls : Declarations) (x : F) : (@Value.field F A x).Good decls := ⟨by simp, by simp⟩

@[simp] theorem Value.good_tuple (decls : Declarations) (values : List (Value F A)) :
    (.tuple values : Value F A).Good decls ↔ ∀ value ∈ values, value.Good decls := by
  simp [Good, forall_and]

mutual
  theorem Pattern.bindings_pointerNames [DecidableEq F] {decls : Declarations}
      {pattern : Pattern F} {value : Value F A} {locals : Environment F A}
      (names : value.PointerNames decls) (matched : pattern.bindings value = some locals) :
      ∀ binding ∈ locals, binding.2.PointerNames decls := by
    cases pattern with
    | wildcard => simp only [Pattern.bindings, Option.some.injEq] at matched; subst locals; simp
    | bind name => simp only [Pattern.bindings, Option.some.injEq] at matched; subst locals; simpa using names
    | literal literal =>
        cases value with
        | tuple | ptr | construct => simp [Pattern.bindings] at matched
        | field x =>
            simp only [Pattern.bindings] at matched
            split at matched
            · cases matched; simp
            · cases matched
    | tuple patterns =>
        cases value with
        | field | ptr | construct => simp [Pattern.bindings] at matched
        | tuple values =>
            simp only [Pattern.bindings] at matched
            exact Pattern.bindingsList_pointerNames (by simpa only [Value.PointerNames] using names) matched
    | construct name ctor patterns =>
        cases value with
        | field | tuple | ptr => simp [Pattern.bindings] at matched
        | construct actual constructor values =>
            simp only [Pattern.bindings] at matched
            split at matched
            · exact Pattern.bindingsList_pointerNames (by simpa only [Value.PointerNames] using names) matched
            · cases matched
  termination_by sizeOf pattern

  theorem Pattern.bindingsList_pointerNames [DecidableEq F] {decls : Declarations}
      {patterns : List (Pattern F)} {values : List (Value F A)} {locals : Environment F A}
      (names : ∀ value ∈ values, value.PointerNames decls)
      (matched : Pattern.bindingsList patterns values = some locals) :
      ∀ binding ∈ locals, binding.2.PointerNames decls := by
    cases patterns with
    | nil => cases values <;> simp_all [Pattern.bindingsList]
    | cons pattern patterns =>
        cases values with
        | nil => simp [Pattern.bindingsList] at matched
        | cons value values =>
            simp only [Pattern.bindingsList] at matched
            obtain ⟨head, headRun, rest⟩ := Option.bind_eq_some_iff.mp matched
            obtain ⟨tail, tailRun, finished⟩ := Option.bind_eq_some_iff.mp rest
            simp only [Option.pure_def, Option.some.injEq] at finished
            subst locals
            have h := Pattern.bindings_pointerNames (names _ (by simp)) headRun
            have t := Pattern.bindingsList_pointerNames (fun v hv => names v (by simp [hv])) tailRun
            simpa only [List.mem_append, or_imp, forall_and] using And.intro h t
  termination_by sizeOf patterns
end

theorem Pattern.bindings_good [DecidableEq F] {decls : Declarations}
    {pattern : Pattern F} {value : Value F A} {locals : Environment F A}
    (good : value.Good decls) (matched : pattern.bindings value = some locals) : locals.Good decls :=
  fun binding member => ⟨Pattern.bindings_wellFormed good.1 matched binding member,
    Pattern.bindings_pointerNames good.2 matched binding member⟩

theorem selectArm_good [DecidableEq F] {decls : Declarations}
    {value : Value F A} {arms : List (Pattern F × Expr F)} {locals : Environment F A} {body : Expr F}
    (good : value.Good decls) (selected : selectArm value arms = some (locals, body)) : locals.Good decls := by
  induction arms with
  | nil => simp [selectArm] at selected
  | cons arm arms ih =>
      rcases arm with ⟨pattern, branch⟩
      cases matched : pattern.bindings value with
      | none => exact ih (by simpa [selectArm, matched] using selected)
      | some bindings =>
          simp [selectArm, matched] at selected
          rcases selected with ⟨rfl, rfl⟩
          exact Pattern.bindings_good good matched

end Aiur
