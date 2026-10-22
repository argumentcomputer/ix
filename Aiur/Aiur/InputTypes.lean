import Aiur.Tables
import Aiur.DeclarationFacts

namespace Aiur

/-- Type-wide pointer freedom implies value-level pointer freedom for every well-typed value. -/
theorem Layout.Describes.pointerFree {decls : Declarations} {layout : Layout} {type : Ty}
    (described : layout.Describes decls type) {value : Value F A}
    (free : layout.pointerFree = true) (typed : value.hasType decls type = true) :
    value.pointerFree = true := by
  refine Layout.Describes.rec
    (motive_1 := fun layout type _ => ∀ value : Value F A,
      layout.pointerFree = true → value.hasType decls type = true → value.pointerFree = true)
    (motive_2 := fun layouts types _ => ∀ values : List (Value F A),
      (∀ layout ∈ layouts, layout.pointerFree = true) →
      values.map Value.type = types → (∀ value ∈ values, value.wellFormed decls = true) →
      ∀ value ∈ values, value.pointerFree = true)
    (motive_3 := fun layouts ctors _ => ∀ name (values : List (Value F A)) ctor,
      ctors.find? (·.name == name) = some ctor →
      (∀ pair ∈ layouts, pair.2.pointerFree = true) →
      values.map Value.type = ctor.fields → (∀ value ∈ values, value.wellFormed decls = true) →
      ∀ value ∈ values, value.pointerFree = true)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ described value free typed
  · intro value _ typed
    cases value <;> simp_all [Value.hasType, Value.type, Value.pointerFree]
  · intro target value free _; simp [Layout.pointerFree] at free
  · intro layouts types related ih value free typed
    cases value with
    | field | ptr | construct => simp [Value.hasType, Value.type] at typed
    | tuple values =>
        simp only [Value.hasType, Value.type, Ty.tuple.injEq, Bool.and_eq_true,
          decide_eq_true_eq, Value.wellFormed, List.all_map, List.all_eq_true] at typed
        simpa [Value.pointerFree] using ih values
          (by simpa [Layout.pointerFree] using free) typed.1 typed.2
  · intro name definition constructors found related ih value free typed
    cases value with
    | field | ptr | tuple => simp [Value.hasType, Value.type] at typed
    | construct name ctor values =>
        simp only [Value.hasType, Value.type, Ty.enum.injEq, Bool.and_eq_true,
          decide_eq_true_eq] at typed
        obtain ⟨rfl, formed⟩ := typed
        simp only [Value.wellFormed, Declarations.findConstructor?, found] at formed
        split at formed
        · cases formed
        · rename_i definition selected
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_map,
            List.all_eq_true] at formed
          simpa [Value.pointerFree] using ih ctor values definition selected
            (by simpa [Layout.pointerFree] using free) formed.1 formed.2
  · intro values _ typed _
    have empty : values = [] := List.map_eq_nil_iff.mp typed
    simp [empty]
  · intro layout type layouts types head tail headIH tailIH values free typed formed
    cases values with
    | nil => simp at typed
    | cons value values =>
        simp only [List.map_cons, List.cons.injEq] at typed
        have h := headIH value (free layout (by simp))
          (by simp [Value.hasType, typed.1, formed value (by simp)])
        have t := tailIH values (fun l hl => free l (by simp [hl])) typed.2
          (fun v hv => formed v (by simp [hv]))
        simpa using And.intro h t
  · simp
  · intro ctorName layout layouts ctors definition same head tail headIH tailIH name values ctor selected free
      typed formed
    subst ctorName
    simp only [List.find?_cons] at selected
    split at selected
    · cases selected
      have h := headIH (.tuple values) (free (definition.name, layout) (by simp))
        (by simpa [Value.hasType, Value.type, Value.wellFormed, typed] using formed)
      simpa [Value.pointerFree] using h
    · exact tailIH name values ctor selected (fun p hp => free p (by simp [hp])) typed formed

theorem Value.pointerFree_of_type {decls : Declarations} {value : Value F A}
    (free : value.type.pointerFree decls = true) (formed : value.wellFormed decls = true) :
    value.pointerFree = true := by
  unfold Ty.pointerFree at free
  cases expanded : decls.layout value.type with
  | error error => simp [expanded] at free
  | ok layout =>
      exact (Declarations.layout_describes expanded).pointerFree
        (by simpa [expanded] using free) (by simp [Value.hasType, formed])

theorem prepareCall_signature [DecidableEq F] {program : Program F} {name : String}
    {args : List (Value F A)} {locals : Environment F A} {expr : Expr F}
    (prepared : prepareCall program name args = .ok (locals, expr)) :
    ∃ signature, program.findSignature? name = some signature ∧
      signature.params.map Prod.snd = args.map Value.type ∧
      ∀ value ∈ args, value.wellFormed program.enums = true := by
  rcases prepareCall_spec prepared with function | table
  · obtain ⟨fn, found, types, formed, _, _⟩ := function
    exact ⟨_, Program.signature_of_function found, types, formed⟩
  · obtain ⟨_, absent, looked, _, _⟩ := table
    obtain ⟨map, _, found, types, formed, _⟩ := lookupMap_spec looked
    exact ⟨_, Program.signature_of_map absent found, types, formed⟩

theorem prepareCall_publicArguments [DecidableEq F] {program : Program F} {name : String}
    {args : List (Value F A)} {locals : Environment F A} {expr : Expr F}
    (entry : checkEntry program name = .ok ())
    (prepared : prepareCall program name args = .ok (locals, expr)) :
    ∀ value ∈ args, value.type.pointerFree program.enums = true ∧ value.wellFormed program.enums = true := by
  obtain ⟨signature, found, types, formed⟩ := prepareCall_signature prepared
  obtain ⟨other, checked, free⟩ := (checkEntry_ok program name).mp entry
  have same := Option.some.inj (found.symm.trans checked)
  subst other
  rw [types] at free
  exact fun value member => ⟨free _ (List.mem_map.mpr ⟨value, member, rfl⟩), formed value member⟩

theorem prepareCall_entry [DecidableEq F] {program : Program F} {name : String}
    {args : List (Value F A)} {locals : Environment F A} {expr : Expr F}
    (prepared : prepareCall program name args = .ok (locals, expr))
    (free : ∀ value ∈ args, value.type.pointerFree program.enums = true) :
    checkEntry program name = .ok () := by
  obtain ⟨signature, found, types, _⟩ := prepareCall_signature prepared
  apply (checkEntry_ok program name).mpr
  refine ⟨signature, found, ?_⟩
  simpa [types] using free

theorem EvalFn.publicArguments [Field F] [DecidableEq F] {program : Program F} {name : String}
    {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalFn program name args before value after) (entry : checkEntry program name = .ok ()) :
    ∀ value ∈ args, value.type.pointerFree program.enums = true ∧ value.wellFormed program.enums = true := by
  cases evaluated with
  | intro prepared _ => exact prepareCall_publicArguments entry prepared

theorem EvalFn.public_pointerFree [Field F] [DecidableEq F] {program : Program F} {name : String}
    {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F}
    (evaluated : EvalFn program name args before value after) (entry : checkEntry program name = .ok ()) :
    ∀ value ∈ args, value.pointerFree = true := by
  intro value member
  have valid := evaluated.publicArguments entry value member
  exact Value.pointerFree_of_type valid.1 valid.2

theorem ROMEvalCall.publicArguments [Field F] [DecidableEq F] {program : Program F} {name : String}
    {args : List (Value F)} {value : Value F} {rom : ROM F}
    (evaluated : ROMEvalCall rom program name args value) (entry : checkEntry program name = .ok ()) :
    ∀ value ∈ args, value.type.pointerFree program.enums = true ∧ value.wellFormed program.enums = true := by
  cases evaluated with
  | intro prepared _ => exact prepareCall_publicArguments entry prepared

theorem ROMEvalCall.entry_of_publicArguments [Field F] [DecidableEq F]
    {program : Program F} {name : String} {args : List (Value F)} {value : Value F} {rom : ROM F}
    (evaluated : ROMEvalCall rom program name args value)
    (free : ∀ value ∈ args, value.type.pointerFree program.enums = true) :
    checkEntry program name = .ok () := by
  cases evaluated with
  | intro prepared _ => exact prepareCall_entry prepared free

end Aiur
