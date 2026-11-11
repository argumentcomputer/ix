import Aiur.WireRoundtrip

namespace Aiur

set_option maxHeartbeats 1000000

def Layout.NamesUnique : Layout → Prop
  | .field | .ptr _ => True
  | .tuple layouts => ∀ layout ∈ layouts, layout.NamesUnique
  | .enum _ constructors => (constructors.map Prod.fst).Nodup ∧
      ∀ pair ∈ constructors, pair.2.NamesUnique
termination_by layout => sizeOf layout
decreasing_by
  all_goals simp_wf
  all_goals
    have h := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first | omega | cases ‹String × Layout›; simp_all only [Prod.mk.sizeOf_spec]; omega

namespace Layout

private theorem all_zero [Zero F] [DecidableEq F] {words : List F}
    (zero : words.all (fun x => decide (x = 0)) = true) : words = List.replicate words.length 0 := by
  induction words with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at zero
      rw [zero.1, List.length_cons, List.replicate_succ]
      exact congrArg (fun xs => 0 :: xs) (ih zero.2)

mutual
  /-- Decoding accepts precisely canonical encodings, with no nonzero unused columns. -/
  theorem encode_decode [NatCast F] [Zero F] [DecidableEq F] {layout : Layout}
      (unique : layout.NamesUnique) {value : Value F} {words : List F}
      (decoded : layout.decode words = some value) : layout.encode value = some words := by
    cases layout with
    | field =>
        cases words with
        | nil => simp [decode] at decoded
        | cons x xs =>
            cases xs with
            | cons => simp [decode] at decoded
            | nil => simp only [decode, Option.some.injEq] at decoded; subst value; simp [encode]
    | ptr target =>
        cases words with
        | nil => simp [decode] at decoded
        | cons x xs =>
            cases xs with
            | cons => simp [decode] at decoded
            | nil => simp only [decode, Option.some.injEq] at decoded; subst value; simp [encode]
    | tuple layouts =>
        simp only [decode] at decoded
        obtain ⟨values, run, finished⟩ := Option.bind_eq_some_iff.mp decoded
        simp only [Option.pure_def, Option.some.injEq] at finished
        subst value
        simpa only [encode] using encodeList_decode (by simpa only [NamesUnique] using unique) run
    | enum name constructors =>
        simp only [decode] at decoded
        obtain ⟨⟨tag, payload⟩, parts, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        split at decoded
        · rename_i length
          obtain ⟨⟨ctor, args⟩, run, finished⟩ := Option.bind_eq_some_iff.mp decoded
          simp only [Option.pure_def, Option.some.injEq] at finished
          subst value
          simp only [NamesUnique] at unique
          obtain ⟨_, index, encodedWords, encoded, tagEq, paddingEq⟩ :=
            encodeConstructor_decode unique.1 unique.2 run
          simp only [encode, ne_eq, not_true_eq_false, ↓reduceIte, encoded, Option.bind_some]
          dsimp only [bind, Option.bind]
          rw [← length, ← paddingEq, ← tagEq, enumParts_words parts]
          rfl
        · cases decoded
  termination_by sizeOf layout

  theorem encodeList_decode [NatCast F] [Zero F] [DecidableEq F] {layouts : List Layout}
      (unique : ∀ layout ∈ layouts, layout.NamesUnique)
      {values : List (Value F)} {words : List F}
      (decoded : decodeList layouts words = some values) : encodeList layouts values = some words := by
    cases layouts with
    | nil => cases words <;> simp_all [decodeList, encodeList]
    | cons layout layouts =>
        simp only [decodeList] at decoded
        obtain ⟨value, headRun, rest⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨values, tailRun, finished⟩ := Option.bind_eq_some_iff.mp rest
        simp only [Option.pure_def, Option.some.injEq] at finished
        subst_vars
        simp only [encodeList, encode_decode (unique _ (by simp)) headRun, Option.bind_some,
          encodeList_decode (fun l h => unique l (by simp [h])) tailRun]
        simp
  termination_by sizeOf layouts

  theorem encodeConstructor_decode [NatCast F] [Zero F] [DecidableEq F]
      {constructors : List (String × Layout)} {ctor : String} {args : List (Value F)}
      {start : Nat} {tag : F} {payload : List F}
      (names : (constructors.map Prod.fst).Nodup)
      (unique : ∀ pair ∈ constructors, pair.2.NamesUnique)
      (decoded : decodeConstructor constructors tag payload start = some (ctor, args)) :
      ctor ∈ constructors.map Prod.fst ∧ ∃ index words,
        encodeConstructor constructors ctor args start = some (index, words) ∧
        tag = (index : F) ∧
        payload = words ++ List.replicate (payload.length - words.length) 0 := by
    cases constructors with
    | nil => simp [decodeConstructor] at decoded
    | cons pair rest =>
        rcases hpair : pair with ⟨name, layout⟩
        rw [hpair] at decoded names unique
        simp only [List.map_cons, List.nodup_cons] at names
        simp only [decodeConstructor] at decoded
        split at decoded
        · rename_i selected
          obtain ⟨value, run, finished⟩ := Option.bind_eq_some_iff.mp decoded
          cases value with
          | field | ptr | construct => simp only [] at finished; cases finished
          | tuple values =>
              dsimp only at finished
              split at finished
              · rename_i zero
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at finished
                rcases finished with ⟨rfl, rfl⟩
                have encoded := encode_decode (unique (name, layout) (by simp)) run
                have width := encode_length encoded
                refine ⟨by simp, start, payload.take layout.width, ?_, selected, ?_⟩
                · simp [encodeConstructor, encoded]
                · have padding := all_zero zero
                  rw [List.length_drop] at padding
                  rw [width, ← padding]
                  exact (List.take_append_drop _ _).symm
              · cases finished
        · obtain ⟨member, index, words, encoded, tagEq, paddingEq⟩ :=
            encodeConstructor_decode names.2 (fun p h => unique p (by simp [h])) decoded
          have different : name ≠ ctor := by intro same; subst name; exact names.1 member
          refine ⟨by simp [member], index, words, ?_, tagEq, paddingEq⟩
          simpa only [encodeConstructor, different, ↓reduceIte] using encoded
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

theorem decode_length [NatCast F] [Zero F] [DecidableEq F] {layout : Layout}
    (unique : layout.NamesUnique) {words : List F} {value : Value F}
    (decoded : layout.decode words = some value) : words.length = layout.width :=
  encode_length (encode_decode unique decoded)

end Layout
end Aiur
