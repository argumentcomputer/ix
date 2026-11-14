import Aiur.Wire
import Aiur.DeclarationFacts

namespace Aiur.Layout

@[simp] theorem payloadWidth_nil : payloadWidth [] = 0 := rfl
@[simp] theorem payloadWidth_cons (name : String) (layout : Layout) (rest : List (String × Layout)) :
    payloadWidth ((name, layout) :: rest) = max layout.width (payloadWidth rest) := rfl

mutual
  theorem encode_length [NatCast F] [Zero F] {layout : Layout} {value : Value F} {words : List F}
      (encoded : layout.encode value = some words) : words.length = layout.width := by
    cases layout with
    | field =>
        cases value <;> simp [encode] at encoded
        case field value => subst words; simp [Layout.width]
    | ptr target =>
        cases value <;> simp [encode] at encoded
        case ptr actual address =>
          obtain ⟨rfl, rfl⟩ := encoded
          simp [Layout.width]
    | tuple layouts =>
        cases value <;> simp [encode] at encoded
        case tuple values => simpa only [Layout.width] using encodeList_length encoded
    | enum name constructors =>
        cases value <;> simp only [encode] at encoded
        case field => cases encoded
        case tuple => cases encoded
        case ptr => cases encoded
        case construct actual ctor args =>
          split at encoded
          · cases encoded
          · obtain ⟨⟨index, payload⟩, chosen, finished⟩ := Option.bind_eq_some_iff.mp encoded
            have bound := encodeConstructor_length chosen
            simp only [Option.pure_def, Option.some.injEq] at finished
            subst words
            simp only [enumWords_length, List.length_append, List.length_replicate, Layout.width]
            change tagWidth constructors.length +
              (payload.length + (payloadWidth constructors - payload.length)) =
              tagWidth constructors.length + payloadWidth constructors
            omega
  termination_by sizeOf layout

  theorem encodeList_length [NatCast F] [Zero F] {layouts : List Layout}
      {values : List (Value F)} {words : List F}
      (encoded : encodeList layouts values = some words) :
      words.length = (layouts.map Layout.width).sum := by
    cases layouts with
    | nil => cases values <;> simp_all [encodeList]
    | cons layout layouts =>
        cases values with
        | nil => simp [encodeList, encodeConstructor] at encoded
        | cons value values =>
            simp only [encodeList] at encoded
            obtain ⟨head, headRun, rest⟩ := Option.bind_eq_some_iff.mp encoded
            obtain ⟨tail, tailRun, finished⟩ := Option.bind_eq_some_iff.mp rest
            simp only [Option.pure_def, Option.some.injEq] at finished
            subst words
            simp [encode_length headRun, encodeList_length tailRun]
  termination_by sizeOf layouts

  theorem encodeConstructor_length [NatCast F] [Zero F] {constructors : List (String × Layout)}
      {ctor : String} {args : List (Value F)} {start index : Nat} {words : List F}
      (encoded : encodeConstructor constructors ctor args start = some (index, words)) :
      words.length ≤ payloadWidth constructors := by
    cases constructors with
    | nil => simp [encodeList, encodeConstructor] at encoded
    | cons entry constructors =>
        rcases hentry : entry with ⟨name, layout⟩
        rw [hentry] at encoded
        simp only [encodeConstructor] at encoded
        split at encoded
        · obtain ⟨payload, run, finished⟩ := Option.bind_eq_some_iff.mp encoded
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at finished
          rcases finished with ⟨rfl, rfl⟩
          rw [encode_length run, payloadWidth_cons]
          exact Nat.le_max_left _ _
        · exact (encodeConstructor_length encoded).trans (Nat.le_max_right _ _)
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [Layout.enum.sizeOf_spec, Layout.tuple.sizeOf_spec,
      List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

mutual
  theorem decode_type [NatCast F] [Zero F] [DecidableEq F] {layout : Layout}
      {words : List F} {value : Value F} (decoded : layout.decode words = some value) :
      value.type = layout.type := by
    cases layout with
    | field =>
        cases words with
        | nil => simp [decode] at decoded
        | cons x xs =>
            cases xs with
            | cons => simp [decode] at decoded
            | nil => simp only [decode, Option.some.injEq] at decoded; subst value; simp [Value.type, Layout.type]
    | ptr target =>
        cases words with
        | nil => simp [decode] at decoded
        | cons x xs =>
            cases xs with
            | cons => simp [decode] at decoded
            | nil => simp only [decode, Option.some.injEq] at decoded; subst value; simp [Value.type, Layout.type]
    | tuple layouts =>
        simp only [decode] at decoded
        obtain ⟨values, run, finished⟩ := Option.bind_eq_some_iff.mp decoded
        simp only [Option.pure_def, Option.some.injEq] at finished
        subst value
        simp only [Value.type, Layout.type, Ty.tuple.injEq]
        exact decodeList_types run
    | enum name constructors =>
        simp only [decode] at decoded
        obtain ⟨⟨tag, payload⟩, _, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        split at decoded
        · obtain ⟨⟨ctor, args⟩, _, finished⟩ := Option.bind_eq_some_iff.mp decoded
          cases finished
          simp [Value.type, Layout.type]
        · cases decoded
  termination_by sizeOf layout

  theorem decodeList_types [NatCast F] [Zero F] [DecidableEq F] {layouts : List Layout}
      {words : List F} {values : List (Value F)}
      (decoded : decodeList layouts words = some values) :
      values.map Value.type = layouts.map Layout.type := by
    cases layouts with
    | nil => cases words <;> simp_all [decodeList]
    | cons layout layouts =>
        simp only [decodeList] at decoded
        obtain ⟨head, headRun, rest⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨tail, tailRun, finished⟩ := Option.bind_eq_some_iff.mp rest
        simp only [Option.pure_def, Option.some.injEq] at finished
        subst values
        simp [decode_type headRun, decodeList_types tailRun]
  termination_by sizeOf layouts
end

end Aiur.Layout
