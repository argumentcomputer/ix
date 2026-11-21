import Aiur.Circuit.SplitFacts
import Aiur.ConstructorFacts

namespace Aiur.Circuit.Compiler

/-- A matching enum tag exposes exactly the declared payload tuple. -/
theorem enum_payload_decoded [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {name : String} {definition : EnumDecl} (found : decls.findEnum? name = some definition)
    {index : Nat} {ctor : ConstructorDecl} (atIndex : definition.constructors[index]? = some ctor)
    {layout : Layout} (expanded : decls.layout (.tuple ctor.fields) = .ok layout)
    {tag : ArithExpr F} {payload : List (ArithExpr F)} {wires : List (Symbolic F)}
    {words : List (ArithExpr F)}
    (parts : Layout.enumParts definition.constructors.length (.const 0) words = some (tag, payload))
    {before after : BuildState F}
    (splitRun : splitValues decls ctor.fields (payload.take layout.width) before = .ok (wires, after))
    {assignment : Var → F} {value : Value F}
    (decoded : (WireValue.mk (.enum name)
      (words.map (ArithExpr.denote assignment))).decode decls = some value) :
    ∃ actual args, value = .construct name actual args ∧
      (tag.denote assignment = (index : F) ↔ actual = ctor.name) ∧
      (actual = ctor.name → DecodesValues decls
        (wires.map (WireValue.map (ArithExpr.denote assignment))) args) := by
  obtain ⟨_, _, overall, overallRun, rawDecode⟩ := WireValue.decode_spec decoded
  have description := Declarations.layout_describes overallRun
  cases description with
  | @enum _ other constructors enumFound related =>
      have same := Option.some.inj (found.symm.trans enumFound)
      subst other
      obtain ⟨chosen, chosenAt, chosenDescription⟩ := related.at atIndex
      have sameLayout := chosenDescription.unique (Declarations.layout_describes expanded)
      subst chosen
      have parts := enumParts_denote parts assignment
      rw [← related.length] at parts
      simp only [Layout.decode, Nat.cast_zero, parts, bind, Option.bind] at rawDecode
      split at rawDecode
      · obtain ⟨⟨actual, args⟩, ctorDecode, finished⟩ := Option.bind_eq_some_iff.mp rawDecode
        simp only [Option.pure_def, Option.some.injEq] at finished
        subst value
        have unique := Declarations.layout_namesUnique checked overallRun
        have safe := Declarations.layout_tagSafe tags overallRun
        simp only [Layout.NamesUnique] at unique
        simp only [Layout.TagSafe] at safe
        obtain ⟨tagMatch, payloadDecode⟩ := Layout.decodeConstructor_match unique.1 safe.1 chosenAt ctorDecode
        refine ⟨actual, args, rfl, by simpa using tagMatch, ?_⟩
        intro matched
        have payloadDecoded := payloadDecode matched
        cases chosenDescription with
        | tuple components =>
            simp only [Layout.decode] at payloadDecoded
            obtain ⟨values, valuesDecode, finished⟩ := Option.bind_eq_some_iff.mp payloadDecoded
            simp only [Option.pure_def, Option.some.injEq, Value.tuple.injEq] at finished
            subst values
            exact splitValues_decodeList checked components splitRun
              (by simpa only [List.map_take] using valuesDecode)
      · cases rawDecode

end Aiur.Circuit.Compiler
