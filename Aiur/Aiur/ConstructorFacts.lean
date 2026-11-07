import Aiur.LayoutUnique
import Aiur.EncodingTypes

namespace Aiur

theorem ConstructorsDescribe.at {decls : Declarations} {layouts : List (String × Layout)}
    {constructors : List ConstructorDecl} (related : ConstructorsDescribe decls layouts constructors)
    {index : Nat} {ctor : ConstructorDecl} (found : constructors[index]? = some ctor) :
    ∃ layout, layouts[index]? = some (ctor.name, layout) ∧ layout.Describes decls (.tuple ctor.fields) := by
  cases related with
  | nil => simp at found
  | @cons name layout layouts ctors head same described tail =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst ctor
          exact ⟨layout, by simp [same], described⟩
      | succ index =>
          exact tail.at (by simpa using found)
termination_by sizeOf constructors

theorem ConstructorsDescribe.length {decls : Declarations} {layouts : List (String × Layout)}
    {constructors : List ConstructorDecl} (related : ConstructorsDescribe decls layouts constructors) :
    layouts.length = constructors.length := by
  cases related with
  | nil => rfl
  | cons _ _ tail => simp [tail.length]
termination_by sizeOf constructors

/-- Decoding identifies an actual declaration position and its selected payload. -/
theorem Layout.decodeConstructor_spec [NatCast F] [Zero F] [DecidableEq F]
    {constructors : List (String × Layout)} {tag : F} {payload : List F} {start : Nat}
    {ctor : String} {args : List (Value F)}
    (decoded : Layout.decodeConstructor constructors tag payload start = some (ctor, args)) :
    ∃ index layout, constructors[index]? = some (ctor, layout) ∧
      tag = ((start + index : Nat) : F) ∧
      layout.decode (payload.take layout.width) = some (.tuple args) := by
  induction constructors generalizing start with
  | nil => simp [Layout.decodeConstructor] at decoded
  | cons pair rest ih =>
      rcases pair with ⟨name, layout⟩
      simp only [Layout.decodeConstructor] at decoded
      split at decoded
      · rename_i selected
        obtain ⟨value, payloadRun, finished⟩ := Option.bind_eq_some_iff.mp decoded
        cases value with
        | field | ptr | construct => cases finished
        | tuple values =>
            dsimp only at finished
            split at finished
            · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at finished
              rcases finished with ⟨rfl, rfl⟩
              exact ⟨0, layout, by simp, by simpa using selected, payloadRun⟩
            · cases finished
      · obtain ⟨index, chosen, atIndex, tagEq, inner⟩ := ih decoded
        exact ⟨index + 1, chosen, by simpa using atIndex,
          by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tagEq, inner⟩

private theorem nodup_index {items : List α} (unique : items.Nodup) {i j : Nat} {value : α}
    (left : items[i]? = some value) (right : items[j]? = some value) : i = j := by
  obtain ⟨hi, left⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨hj, right⟩ := List.getElem?_eq_some_iff.mp right
  exact unique.getElem_inj_iff.mp (left.trans right.symm)

/-- Distinct representable tags are equivalent to the nominal constructor identity. -/
theorem Layout.decodeConstructor_match [NatCast F] [Zero F] [DecidableEq F]
    {constructors : List (String × Layout)} (names : (constructors.map Prod.fst).Nodup)
    {start : Nat} (tags : TagsDistinct F start constructors.length)
    {index : Nat} {ctor : String} {layout : Layout}
    (found : constructors[index]? = some (ctor, layout))
    {tag : F} {payload : List F} {actual : String} {args : List (Value F)}
    (decoded : Layout.decodeConstructor constructors tag payload start = some (actual, args)) :
    (tag = ((start + index : Nat) : F) ↔ actual = ctor) ∧
      (actual = ctor → layout.decode (payload.take layout.width) = some (.tuple args)) := by
  obtain ⟨selected, chosen, atSelected, tagEq, payloadRun⟩ := Layout.decodeConstructor_spec decoded
  have hi := (List.getElem?_eq_some_iff.mp found).1
  have hs := (List.getElem?_eq_some_iff.mp atSelected).1
  have sameIndex : actual = ctor → selected = index := by
    intro same
    apply nodup_index names (value := ctor)
    · simpa [List.getElem?_map, atSelected, same]
    · simp [List.getElem?_map, found]
  have samePair : selected = index → (actual, chosen) = (ctor, layout) := by
    intro same
    rw [same, found] at atSelected
    exact Option.some.inj atSelected.symm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro matchTag
    have sumEq := tags (start + selected) (start + index) (by omega) (by omega)
      (by omega) (by omega) (tagEq.symm.trans matchTag)
    exact (Prod.mk.inj (samePair (by omega))).1
  · intro same
    simpa [sameIndex same] using tagEq
  · intro same
    have pairEq := samePair (sameIndex same)
    have layoutEq := (Prod.mk.inj pairEq).2
    simpa [layoutEq] using payloadRun

end Aiur
