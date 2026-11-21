import Aiur.Circuit.WitnessBasic
import Aiur.WireRelation
import Aiur.LayoutUnique

namespace Aiur.Circuit.Compiler

/-- Slicing is static and neither allocates variables nor adds constraints. -/
theorem splitValues_spec {decls : Declarations} {types : List Ty} {words : List α}
    {values : List (WireValue α)} {before after : BuildState F}
    (compiled : splitValues decls types words before = .ok (values, after)) :
    after = before ∧ values.map WireValue.type = types ∧ values.flatMap WireValue.words = words ∧
      ∀ value ∈ values, value.Sized decls := by
  induction types generalizing words values before with
  | nil => cases words with
    | nil =>
        obtain ⟨rfl, rfl⟩ := pure_ok.mp compiled
        exact ⟨rfl, rfl, rfl, by simp⟩
    | cons => simp [splitValues] at compiled
  | cons type types ih =>
      simp only [splitValues] at compiled
      obtain ⟨layout, middle, expanded, rest⟩ := bind_ok.mp compiled
      obtain ⟨expansion, rfl⟩ := getLayout_eq expanded
      split at rest
      · simp [StateT.bind, bind, Except.bind] at rest
      · rename_i width
        obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
        obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
        obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        obtain ⟨rfl, typesEq, wordsEq, shaped⟩ := ih tailRun
        refine ⟨rfl, by simp [typesEq], ?_, ?_⟩
        · simp [wordsEq]
        · intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact ⟨layout, expansion, by
              change (words.take layout.width).length = layout.width
              rw [List.length_take, Nat.min_eq_left (by omega)]⟩
          · exact shaped value member

theorem splitValues_bounded {decls : Declarations} {types : List Ty} {words : List (ArithExpr F)}
    {values : List (Symbolic F)} {before after : BuildState F}
    (compiled : splitValues decls types words before = .ok (values, after)) {bound : Nat}
    (bounded : ∀ word ∈ words, word.inBounds bound = true) :
    ∀ value ∈ values, Bounded bound value := by
  have flat := (splitValues_spec compiled).2.2.1
  intro value member p leaf
  apply bounded
  rw [← flat]
  exact List.mem_flatMap.mpr ⟨value, member, leaf⟩

/-- Static slicing commutes with the canonical tuple decoder. -/
theorem splitValues_decodeList [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {types : List Ty} {layouts : List Layout}
    (described : LayoutsDescribe decls layouts types)
    {words : List (ArithExpr F)} {wires : List (Symbolic F)} {before after : BuildState F}
    (compiled : splitValues decls types words before = .ok (wires, after))
    {assignment : Var → F} {values : List (Value F)}
    (decoded : Layout.decodeList layouts (words.map (ArithExpr.denote assignment)) = some values) :
    DecodesValues decls (wires.map (WireValue.map (ArithExpr.denote assignment))) values := by
  cases described with
  | nil =>
      cases words with
      | cons => simp [splitValues] at compiled
      | nil =>
          obtain ⟨rfl, rfl⟩ := pure_ok.mp compiled
          simp only [List.map_nil, Layout.decodeList, Option.some.injEq] at decoded
          subst values
          exact .nil
  | @cons layout type layouts types head tail =>
      simp only [splitValues] at compiled
      obtain ⟨expanded, middle, expansionRun, rest⟩ := bind_ok.mp compiled
      obtain ⟨expansion, rfl⟩ := getLayout_eq expansionRun
      have same := head.unique (Declarations.layout_describes expansion)
      subst expanded
      split at rest
      · simp [StateT.bind, bind, Except.bind] at rest
      · obtain ⟨⟨⟩, middle, unchanged, rest⟩ := bind_ok.mp rest
        obtain ⟨_, rfl⟩ := pure_ok.mp unchanged
        obtain ⟨other, last, tailRun, finished⟩ := bind_ok.mp rest
        obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
        simp only [Layout.decodeList] at decoded
        obtain ⟨value, headDecode, restDecode⟩ := Option.bind_eq_some_iff.mp decoded
        obtain ⟨values, tailDecode, finished⟩ := Option.bind_eq_some_iff.mp restDecode
        simp only [Option.pure_def, Option.some.injEq] at finished
        subst finished
        exact .cons (WireValue.decode_of_layout checked expansion (by
          simpa only [WireValue.map, List.map_take] using headDecode))
          (splitValues_decodeList checked tail tailRun (by simpa only [List.map_drop] using tailDecode))
termination_by sizeOf types

/-- A decoded tuple splits into the encodings of exactly its components. -/
theorem splitValues_decode [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {types : List Ty} {words : List (ArithExpr F)}
    {wires : List (Symbolic F)} {before after : BuildState F}
    (compiled : splitValues decls types words before = .ok (wires, after))
    {assignment : Var → F} {value : Value F}
    (decoded : (WireValue.mk (.tuple types) (words.map (ArithExpr.denote assignment))).decode decls = some value) :
    ∃ values, value = .tuple values ∧
      DecodesValues decls (wires.map (WireValue.map (ArithExpr.denote assignment))) values := by
  obtain ⟨_, _, layout, expanded, decoded⟩ := WireValue.decode_spec decoded
  have described := Declarations.layout_describes expanded
  cases described with
  | tuple relation =>
      simp only [Layout.decode] at decoded
      obtain ⟨values, inner, finished⟩ := Option.bind_eq_some_iff.mp decoded
      simp only [Option.pure_def, Option.some.injEq] at finished
      exact ⟨values, finished.symm, splitValues_decodeList checked relation compiled inner⟩

end Aiur.Circuit.Compiler
