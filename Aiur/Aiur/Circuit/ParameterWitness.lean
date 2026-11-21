import Aiur.Circuit.EncodingWitness

namespace Aiur.Circuit.Compiler

variable {F : Type} {rom : WireROM F}

theorem freshValues_decoded_complete [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {types : List Ty} {vars : List (WireValue Var)} {before after : BuildState F}
    (compiled : freshValues decls types before = .ok (vars, after))
    {calls : Circuit.CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (values : List (Value F)) (shape : values.map Value.type = types)
    (formed : ∀ value ∈ values, value.wellFormed decls = true) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      (∀ wire ∈ vars, Bounded (F := F) after.nextVar (wire.map ArithExpr.var)) ∧
      DecodesValues decls (vars.map (WireValue.map assignment)) values := by
  induction values generalizing vars types before initial with
  | nil =>
      subst types
      obtain ⟨rfl, rfl⟩ := pure_ok.mp compiled
      exact ⟨initial, .refl layout valid, by simp, .nil⟩
  | cons value values ih =>
      subst types
      simp only [List.map_cons, freshValues, List.mapM_cons] at compiled
      obtain ⟨head, middle, headRun, rest⟩ := bind_ok.mp compiled
      obtain ⟨tail, last, tailRun, finished⟩ := bind_ok.mp rest
      obtain ⟨rfl, rfl⟩ := pure_ok.mp finished
      obtain ⟨a, headExt, headBound, headDecode⟩ := freshValue_decoded_complete checked tags headRun
        layout valid value rfl (formed _ (by simp))
      obtain ⟨b, tailExt, tailBound, tailDecode⟩ := ih tailRun headExt.layout headExt.valid rfl
        (fun v h => formed v (by simp [h]))
      refine ⟨b, headExt.trans tailExt, ?_, .cons ?_ tailDecode⟩
      · simpa using And.intro (headBound.mono tailExt.increase) tailBound
      · rw [tailExt.variables headBound]
        exact headDecode

theorem parameter_types (params : List (String × Ty)) (args : List (Value F))
    (types : params.map Prod.snd = args.map Value.type) :
    environmentTypes ((params.map Prod.fst).zip args) = params := by
  induction params generalizing args with
  | nil => cases args <;> simp_all [environmentTypes]
  | cons param params ih =>
      cases args with
      | nil => simp at types
      | cons arg args =>
          simp only [List.map_cons, List.cons.injEq] at types
          simp only [List.map_cons, List.zip_cons_cons, environmentTypes, List.map_cons]
          rw [← types.1]
          exact congrArg (param :: ·) (ih args types.2)

theorem parameter_bounded {names : List String} {inputs : List (WireValue Var)} {bound : Nat}
    (bounded : ∀ input ∈ inputs, Bounded (F := F) bound (input.map ArithExpr.var)) :
    LocalsBounded (F := F) bound (names.zip (inputs.map (WireValue.map ArithExpr.var))) := by
  intro binding member
  obtain ⟨_, inside⟩ := List.of_mem_zip member
  obtain ⟨input, inputMember, same⟩ := List.mem_map.mp inside
  rw [← same]
  exact bounded input inputMember

theorem parameter_wellFormed {decls : Declarations} {names : List String} {values : List (Value F)}
    (formed : ∀ value ∈ values, value.wellFormed decls = true) :
    Environment.WellFormed decls (names.zip values) := by
  intro binding member
  exact formed binding.2 (List.of_mem_zip member).2

end Aiur.Circuit.Compiler
