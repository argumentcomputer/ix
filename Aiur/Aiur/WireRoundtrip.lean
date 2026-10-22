import Aiur.WireCodec

namespace Aiur

set_option maxHeartbeats 1000000

/-- Distinct tags in a segment of the constructor numbering. -/
def TagsDistinct (F : Type) [NatCast F] (start count : Nat) : Prop :=
  ∀ i j, start ≤ i → i < start + count → start ≤ j → j < start + count →
    (i : F) = (j : F) → i = j

theorem TagsDistinct.tail [NatCast F] {start count : Nat}
    (safe : TagsDistinct F start (count + 1)) : TagsDistinct F (start + 1) count := by
  intro i j il ih jl jh same
  exact safe i j (by omega) (by omega) (by omega) (by omega) same

/-- Every nested enum's tags remain distinct in the selected field. -/
def Layout.TagSafe (F : Type) [NatCast F] : Layout → Prop
  | .field | .ptr _ => True
  | .tuple layouts => ∀ layout ∈ layouts, layout.TagSafe F
  | .enum _ constructors => TagsDistinct F 0 constructors.length ∧
      ∀ pair ∈ constructors, pair.2.TagSafe F
termination_by layout => sizeOf layout
decreasing_by
  all_goals simp_wf
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first | omega | cases ‹String × Layout›; simp_all only [Prod.mk.sizeOf_spec]; omega

namespace Layout

theorem encodeConstructor_index [NatCast F] [Zero F] {constructors : List (String × Layout)}
    {ctor : String} {args : List (Value F)} {start index : Nat} {words : List F}
    (encoded : encodeConstructor constructors ctor args start = some (index, words)) :
    start ≤ index ∧ index < start + constructors.length := by
  induction constructors generalizing start with
  | nil => simp [encodeConstructor] at encoded
  | cons pair rest ih =>
      rcases pair with ⟨name, layout⟩
      simp only [encodeConstructor] at encoded
      split at encoded
      · obtain ⟨payload, _, finished⟩ := Option.bind_eq_some_iff.mp encoded
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at finished
        rcases finished with ⟨rfl, rfl⟩
        simp
      · have bounds := ih encoded
        simp only [List.length_cons]
        omega

mutual
  /-- Encoding followed by decoding recovers exactly the original nominal value. -/
  theorem decode_encode [NatCast F] [Zero F] [DecidableEq F] {layout : Layout}
      (safe : layout.TagSafe F) {value : Value F} {words : List F}
      (encoded : layout.encode value = some words) : layout.decode words = some value := by
    cases layout with
    | field =>
        cases value <;> simp [encode] at encoded
        case field value => subst words; simp [decode]
    | ptr target =>
        cases value <;> simp [encode] at encoded
        case ptr actual address =>
          obtain ⟨rfl, rfl⟩ := encoded
          simp [decode]
    | tuple layouts =>
        cases value <;> simp [encode] at encoded
        case tuple values =>
          simp [decode, decodeList_encode (by simpa only [TagSafe] using safe) encoded]
    | enum name constructors =>
        cases value <;> simp only [encode] at encoded
        case field => cases encoded
        case ptr => cases encoded
        case tuple => cases encoded
        case construct actual ctor args =>
          split at encoded
          · cases encoded
          · rename_i same
            have same : name = actual := by simpa using same
            subst actual
            obtain ⟨⟨index, payload⟩, chosen, finished⟩ := Option.bind_eq_some_iff.mp encoded
            simp only [Option.pure_def, Option.some.injEq] at finished
            subst words
            have width := encodeConstructor_length chosen
            have length : (payload ++ List.replicate (payloadWidth constructors - payload.length) (0 : F)).length =
                payloadWidth constructors := by simp only [List.length_append, List.length_replicate]; omega
            have implicit : constructors.length = 1 → (index : F) = ((0 : Nat) : F) := by
              intro singleton
              have bound := encodeConstructor_index chosen
              have same : index = 0 := by omega
              rw [same]
            simp only [TagSafe] at safe
            simp only [decode, enumParts_enumWords _ implicit, bind, Option.bind, length, ↓reduceIte]
            rw [decodeConstructor_encode safe.1 safe.2 chosen]
            rfl
  termination_by sizeOf layout

  theorem decodeList_encode [NatCast F] [Zero F] [DecidableEq F] {layouts : List Layout}
      (safe : ∀ layout ∈ layouts, layout.TagSafe F) {values : List (Value F)} {words : List F}
      (encoded : encodeList layouts values = some words) : decodeList layouts words = some values := by
    cases layouts with
    | nil => cases values <;> simp_all [encodeList, decodeList]
    | cons layout layouts =>
        cases values with
        | nil => simp [encodeList] at encoded
        | cons value values =>
            simp only [encodeList] at encoded
            obtain ⟨head, headRun, rest⟩ := Option.bind_eq_some_iff.mp encoded
            obtain ⟨tail, tailRun, finished⟩ := Option.bind_eq_some_iff.mp rest
            simp only [Option.pure_def, Option.some.injEq] at finished
            subst words
            have width := encode_length headRun
            simp only [decodeList, ← width, List.take_left, List.drop_left]
            rw [decode_encode (safe _ (by simp)) headRun,
              decodeList_encode (fun l h => safe l (by simp [h])) tailRun]
            rfl
  termination_by sizeOf layouts

  theorem decodeConstructor_encode [NatCast F] [Zero F] [DecidableEq F]
      {constructors : List (String × Layout)} {ctor : String} {args : List (Value F)}
      {start index : Nat} {payload : List F}
      (tags : TagsDistinct F start constructors.length)
      (safe : ∀ pair ∈ constructors, pair.2.TagSafe F)
      (encoded : encodeConstructor constructors ctor args start = some (index, payload))
      (padding : Nat) :
      decodeConstructor constructors (index : F) (payload ++ List.replicate padding 0) start = some (ctor, args) := by
    cases constructors with
    | nil => simp [encodeConstructor] at encoded
    | cons pair rest =>
        rcases hpair : pair with ⟨name, layout⟩
        rw [hpair] at encoded safe tags
        simp only [encodeConstructor] at encoded
        split at encoded
        · rename_i same
          subst name
          obtain ⟨words, headRun, finished⟩ := Option.bind_eq_some_iff.mp encoded
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at finished
          rcases finished with ⟨rfl, rfl⟩
          have width := encode_length headRun
          simp only [decodeConstructor, ↓reduceIte, ← width, List.take_left, List.drop_left]
          rw [decode_encode (safe (ctor, layout) (by simp)) headRun]
          simp
        · have bounds := encodeConstructor_index encoded
          have different : (index : F) ≠ (start : F) := by
            intro same
            have equal := tags index start (by omega) (by simp only [List.length_cons]; omega) (by omega)
              (by simp) same
            omega
          simp only [decodeConstructor, different, ↓reduceIte]
          exact decodeConstructor_encode tags.tail (fun p h => safe p (by simp [h])) encoded padding
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

end Layout
end Aiur
