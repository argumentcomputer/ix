import Aiur.WireBoundary
import Aiur.DeclarationChecks

namespace Aiur

set_option maxHeartbeats 1000000

private def payloadFormed (decls : Declarations) (fields : List Ty) (args : List (Value F)) : Bool :=
  decide (args.map Value.type = fields) && (args.map (Value.wellFormed decls)).all id

/-- Encoding is defined exactly for well-typed constructor data. -/
theorem Layout.Describes.encode_isSome [NatCast F] [Zero F] {decls : Declarations}
    {layout : Layout} {ty : Ty} (described : layout.Describes decls ty) :
    ∀ value : Value F, (layout.encode value).isSome = value.hasType decls ty := by
  refine Layout.Describes.rec
    (motive_1 := fun layout ty _ => ∀ value : Value F,
      (layout.encode value).isSome = value.hasType decls ty)
    (motive_2 := fun layouts types _ => ∀ values : List (Value F),
      (Layout.encodeList layouts values).isSome = payloadFormed decls types values)
    (motive_3 := fun layouts ctors _ => ∀ name (args : List (Value F)) start,
      (Layout.encodeConstructor layouts name args start).isSome =
        match ctors.find? (·.name == name) with
        | none => false
        | some ctor => payloadFormed decls ctor.fields args)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ described
  ·
    intro value
    cases value <;> simp [Layout.encode, Value.hasType, Value.type]
  · intro target value
    cases value <;> simp [Layout.encode, Value.hasType, Value.type]
    split <;> simp_all [eq_comm]
  · intro layouts types typed ih value
    cases value <;> simp [Layout.encode, Value.hasType, Value.type]
    rename_i values
    simpa [Value.wellFormed, payloadFormed] using ih values
  · intro name definition constructors found typed ih value
    cases value with
    | field | ptr | tuple => simp [Layout.encode, Value.hasType, Value.type]
    | construct actual ctor args =>
        by_cases same : name = actual
        · subst actual
          have inner := ih ctor args 0
          cases result : Layout.encodeConstructor constructors ctor args 0 with
          | none =>
              cases lookup : definition.constructors.find? (·.name == ctor) <;>
              simpa [Layout.encode, result, Value.hasType, Value.type, Value.wellFormed,
                Declarations.findConstructor?, found, payloadFormed, lookup] using inner
          | some pair =>
              cases lookup : definition.constructors.find? (·.name == ctor) <;>
              simpa [Layout.encode, result, Value.hasType, Value.type, Value.wellFormed,
                Declarations.findConstructor?, found, payloadFormed, lookup] using inner
        · simp [Layout.encode, same, Value.hasType, Value.type, Ne.symm same]
  · intro values
    cases values <;> simp [Layout.encodeList, payloadFormed]
  · intro layout type layouts types head tail headIH tailIH values
    cases values with
    | nil => simp [Layout.encodeList, payloadFormed]
    | cons value values =>
        have h := headIH value
        have t := tailIH values
        cases headRun : layout.encode value <;> cases tailRun : Layout.encodeList layouts values <;>
          simp_all [Layout.encodeList, payloadFormed, Value.hasType, Bool.and_assoc]
  · intro name args start; simp [Layout.encodeConstructor]
  · intro name layout layouts ctors ctor same head tail headIH tailIH requested args start
    subst name
    by_cases selected : ctor.name = requested
    · have inner := headIH (.tuple args)
      cases run : layout.encode (.tuple args) <;>
        simp_all [Layout.encodeConstructor, List.find?_cons, selected, Value.hasType,
          Value.type, Value.wellFormed, payloadFormed]
    · simpa [Layout.encodeConstructor, List.find?_cons, selected] using tailIH requested args (start + 1)

theorem Layout.Describes.encode_wellTyped [NatCast F] [Zero F] {decls : Declarations}
    {layout : Layout} {ty : Ty} (described : layout.Describes decls ty)
    {value : Value F} {words : List F} (encoded : layout.encode value = some words) :
    value.type = ty ∧ value.wellFormed decls = true := by
  have formed := described.encode_isSome value
  simpa [encoded, Value.hasType] using formed.symm

theorem Layout.Describes.encode_total [NatCast F] [Zero F] {decls : Declarations}
    {layout : Layout} {ty : Ty} (described : layout.Describes decls ty)
    {value : Value F} (type : value.type = ty) (formed : value.wellFormed decls = true) :
    ∃ words, layout.encode value = some words := by
  have some := described.encode_isSome (F := F) value
  rw [Value.hasType, type] at some
  simp only [decide_true, formed, Bool.and_self] at some
  exact Option.isSome_iff_exists.mp some

/-- Canonical decoding produces declared constructor payload types. -/
theorem Layout.Describes.decode_wellTyped [NatCast F] [Zero F] [DecidableEq F]
    {decls : Declarations} {layout : Layout} {ty : Ty}
    (described : layout.Describes decls ty) (unique : layout.NamesUnique)
    {words : List F} {value : Value F} (decoded : layout.decode words = some value) :
    value.type = ty ∧ value.wellFormed decls = true :=
  described.encode_wellTyped (Layout.encode_decode unique decoded)

theorem Declarations.layout_namesUnique {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {ty : Ty} {layout : Layout}
    (expanded : decls.layout ty = .ok layout) : layout.NamesUnique :=
  (Declarations.layout_describes expanded).namesUnique (checkDeclarations_names checked).2

theorem Declarations.layout_tagSafe [NatCast F] [DecidableEq F] {decls : Declarations}
    (tags : decls.tagsValid F = true) {ty : Ty} {layout : Layout}
    (expanded : decls.layout ty = .ok layout) : layout.TagSafe F := by
  apply (Declarations.layout_describes expanded).tagSafe
  intro decl member
  exact tagsDistinct_zero (((Declarations.tagsValid_spec decls).mp tags) decl member)

theorem WireValue.decode_of_layout [NatCast F] [Zero F] [DecidableEq F]
    {decls : Declarations} (checked : checkDeclarations decls = .ok ())
    {wire : WireValue F} {layout : Layout} (expanded : decls.layout wire.type = .ok layout)
    {value : Value F} (decoded : layout.decode wire.words = some value) :
    wire.decode decls = some value := by
  obtain ⟨typed, formed⟩ := (Declarations.layout_describes expanded).decode_wellTyped
    (Declarations.layout_namesUnique checked expanded) decoded
  simp [WireValue.decode, expanded, Except.toOption, decoded, Value.hasType, typed, formed]

end Aiur
