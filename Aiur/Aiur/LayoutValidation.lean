import Aiur.WireCanonical
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Aiur

/-- The field values of the exact tag tests, in declaration order. -/
def tagTests [Zero F] [One F] [NatCast F] [DecidableEq F] : Nat → F → Nat → List F
  | 0, _, _ => []
  | count + 1, tag, start => (if tag = (start : F) then 1 else 0) :: tagTests count tag (start + 1)

mutual
  /-- Semantic conditions enforced by the enum validation gadget. -/
  def Layout.Admissible [Field F] [DecidableEq F] : Layout → List F → Prop
    | .field, [_] | .ptr _, [_] => True
    | .tuple layouts, words => Layout.AdmissibleList layouts words
    | .enum _ constructors, words =>
      match Layout.enumParts constructors.length ((0 : Nat) : F) words with
      | none => False
      | some (tag, payload) =>
        payload.length = Layout.payloadWidth constructors ∧
        (tagTests constructors.length tag 0).sum = 1 ∧
        Layout.AdmissibleConstructors constructors tag payload 0
    | _, _ => False
  termination_by layout _ => sizeOf layout

  def Layout.AdmissibleList [Field F] [DecidableEq F] : List Layout → List F → Prop
    | [], [] => True
    | layout :: layouts, words =>
        layout.Admissible (words.take layout.width) ∧
        Layout.AdmissibleList layouts (words.drop layout.width)
    | [], _ :: _ => False
  termination_by layouts _ => sizeOf layouts

  def Layout.AdmissibleConstructors [Field F] [DecidableEq F] :
      List (String × Layout) → F → List F → Nat → Prop
    | [], _, _, _ => True
    | (_, layout) :: constructors, tag, payload, start =>
        (tag = (start : F) → layout.Admissible (payload.take layout.width) ∧
          ∀ word ∈ payload.drop layout.width, word = 0) ∧
        Layout.AdmissibleConstructors constructors tag payload (start + 1)
  termination_by constructors _ _ _ => sizeOf constructors
end

private theorem absent_tests [Field F] [DecidableEq F] {tag : F} {count start : Nat}
    (absent : ∀ i, start ≤ i → i < start + count → tag ≠ (i : F)) :
    tagTests count tag start = List.replicate count 0 := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      have different := absent start le_rfl (by omega)
      simp only [tagTests, different, ↓reduceIte, List.replicate_succ]
      rw [ih (fun i lo hi => absent i (by omega) (by omega))]

private theorem absent_constructors [Field F] [DecidableEq F]
    {constructors : List (String × Layout)} {tag : F} {payload : List F} {start : Nat}
    (absent : ∀ i, start ≤ i → i < start + constructors.length → tag ≠ (i : F)) :
    Layout.AdmissibleConstructors constructors tag payload start := by
  induction constructors generalizing start with
  | nil => simp [Layout.AdmissibleConstructors]
  | cons pair rest ih =>
      rcases pair with ⟨name, layout⟩
      simp only [Layout.AdmissibleConstructors]
      exact ⟨fun same => (absent start le_rfl (by simp) same).elim,
        ih (fun i lo hi => absent i (by omega) (by simp only [List.length_cons]; omega))⟩

mutual
  theorem Layout.decode_admissible [Field F] [DecidableEq F] {layout : Layout}
      (safe : layout.TagSafe F) {words : List F} {value : Value F}
      (decoded : layout.decode words = some value) : layout.Admissible words := by
    cases layout with
    | field => cases words with
      | nil => simp [Layout.decode] at decoded
      | cons word rest => cases rest with
        | nil => simp [Layout.Admissible]
        | cons => simp [Layout.decode] at decoded
    | ptr target => cases words with
      | nil => simp [Layout.decode] at decoded
      | cons word rest => cases rest with
        | nil => simp [Layout.Admissible]
        | cons => simp [Layout.decode] at decoded
    | tuple layouts =>
        simp only [Layout.decode] at decoded
        obtain ⟨values, inner, _⟩ := Option.bind_eq_some_iff.mp decoded
        simp only [Layout.Admissible]
        exact Layout.decodeList_admissible (by simpa only [Layout.TagSafe] using safe) inner
    | enum name constructors =>
        simp only [Layout.decode] at decoded
        obtain ⟨⟨tag, payload⟩, parts, decoded⟩ := Option.bind_eq_some_iff.mp decoded
        split at decoded
        · rename_i width
          obtain ⟨pair, inner, _⟩ := Option.bind_eq_some_iff.mp decoded
          simp only [Layout.TagSafe] at safe
          simp only [Layout.Admissible, parts]
          exact ⟨width, Layout.decodeConstructor_admissible safe.1 safe.2 inner⟩
        · cases decoded
  termination_by sizeOf layout

  theorem Layout.decodeList_admissible [Field F] [DecidableEq F] {layouts : List Layout}
      (safe : ∀ layout ∈ layouts, layout.TagSafe F) {words : List F} {values : List (Value F)}
      (decoded : Layout.decodeList layouts words = some values) : Layout.AdmissibleList layouts words := by
    cases layouts with
    | nil => cases words <;> simp_all [Layout.decodeList, Layout.AdmissibleList]
    | cons layout layouts =>
        simp only [Layout.decodeList] at decoded
        obtain ⟨value, headRun, rest⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨values, tailRun, _⟩ := Option.bind_eq_some_iff.mp rest
        simp only [Layout.AdmissibleList]
        exact ⟨Layout.decode_admissible (safe _ (by simp)) headRun,
          Layout.decodeList_admissible (fun l h => safe l (by simp [h])) tailRun⟩
  termination_by sizeOf layouts

  theorem Layout.decodeConstructor_admissible [Field F] [DecidableEq F]
      {constructors : List (String × Layout)} {tag : F} {payload : List F} {start : Nat}
      (tags : TagsDistinct F start constructors.length)
      (safe : ∀ pair ∈ constructors, pair.2.TagSafe F) {value : String × List (Value F)}
      (decoded : Layout.decodeConstructor constructors tag payload start = some value) :
      (tagTests constructors.length tag start).sum = 1 ∧
        Layout.AdmissibleConstructors constructors tag payload start := by
    cases constructors with
    | nil => simp [Layout.decodeConstructor] at decoded
    | cons pair rest =>
        rcases hpair : pair with ⟨name, layout⟩
        rw [hpair] at decoded tags safe
        simp only [Layout.decodeConstructor] at decoded
        split at decoded
        · rename_i selected
          obtain ⟨result, payloadRun, finished⟩ := Option.bind_eq_some_iff.mp decoded
          cases result with
          | field | ptr | construct => cases finished
          | tuple args =>
              dsimp only at finished
              split at finished
              · rename_i zeroPadding
                have absent : ∀ i, start + 1 ≤ i → i < start + 1 + rest.length → tag ≠ (i : F) := by
                  intro i lo hi same
                  have equal := tags start i (by omega) (by simp) (by omega)
                    (by simp only [List.length_cons]; omega) (selected.symm.trans same)
                  omega
                simp only [Layout.AdmissibleConstructors]
                refine ⟨?_, ?_⟩
                · simp only [List.length_cons, tagTests, selected, ↓reduceIte]
                  have tailZero := absent_tests absent
                  rw [selected] at tailZero
                  simp [tailZero]
                · exact ⟨fun _ => ⟨Layout.decode_admissible (safe (name, layout) (by simp)) payloadRun,
                    by simpa using zeroPadding⟩, absent_constructors absent⟩
              · cases finished
        · rename_i notSelected
          obtain ⟨sum, acceptable⟩ := Layout.decodeConstructor_admissible tags.tail
            (fun p h => safe p (by simp [h])) decoded
          simp only [Layout.AdmissibleConstructors]
          exact ⟨by simpa [tagTests, notSelected] using sum,
            ⟨fun h => (notSelected h).elim, acceptable⟩⟩
  termination_by sizeOf constructors
  decreasing_by
    all_goals simp_all only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    all_goals omega
end

end Aiur
