import Aiur.Generic.PreparationExpressionFacts
import Aiur.Generic.CoreRuntime
import Aiur.Generic.ControlLoweringFacts

namespace Aiur.Generic

theorem Preparation.function_ok {program : Program F} {key : Instance} {core : Aiur.Function F}
    (compiled : Preparation.function program key = .ok core) :
    ∃ fn types prepared body, program.findFunction? key.name = some fn ∧
      arguments fn.typeParams key.types = .ok types ∧
      Preparation.expression program (program.consts.length + 1) types fn.body = .ok prepared ∧
      ControlLower.function prepared (fn.params.map Prod.fst) = .ok body ∧
      body.lowerSafe [] ∧
      core = {
        name := key.symbol
        params := fn.params.map fun (name, type) => (name, (type.subst types).toCore)
        result := (fn.result.subst types).toCore
        body := body.lower [] } := by
  cases found : program.findFunction? key.name with
  | none => simp [Preparation.function, found] at compiled
  | some fn =>
      simp only [Preparation.function, found, except_bind_ok] at compiled
      obtain ⟨types, args, prepared, expanded, body, control, rest⟩ := compiled
      split at rest
      · simp at rest
      · rename_i safe
        obtain rfl := except_pure_ok.mp rest
        exact ⟨fn, types, prepared, body, rfl, args, expanded, control, by simpa using safe, rfl⟩

/-- Successful compiler lookup identifies the original closure, its prepared
body, and the decidable lowering certificate. It cannot substitute a different
function or reinterpret a failed function lookup as a map. -/
theorem Source.compilerFunction_spec [DecidableEq F] {s : Source F}
    (compiled : s.compilerFunction? name = some core) :
    ∃ source prepared body, s.program.sourceFunction? name = some source ∧
      Preparation.expression s.program (s.program.consts.length + 1) source.types source.body = .ok prepared ∧
      ControlLower.function prepared (source.params.map Prod.fst) = .ok body ∧
      body.lowerSafe [] ∧ core.params = source.params ∧ core.body = body.lower [] := by
  cases decoded : Instance.ofSymbol name with
  | error e => simp [Source.compilerFunction?, decoded, Except.toOption, bind, Except.bind] at compiled
  | ok key =>
      have checked : Preparation.function s.program key = .ok core := by
        cases run : Preparation.function s.program key <;>
          simpa [Source.compilerFunction?, decoded, run, Except.toOption, bind, Except.bind] using compiled
      obtain ⟨fn, types, prepared, body, found, args, expanded, control, safe, rfl⟩ := Preparation.function_ok checked
      refine ⟨⟨types, fn.params.map (fun (n, t) => (n, (t.subst types).toCore)), fn.body⟩,
        prepared, body, ?_, expanded, ?_, safe, rfl, rfl⟩
      · simp [Program.sourceFunction?, decoded, found, args, Except.toOption]
      · simpa only [List.map_map, Function.comp_def] using control

theorem SourceFunction.prepare_iff {fn : SourceFunction F}
    {types : SourceSemantics.Types} {locals : Environment F Nat} {body : Expr F}
    {args : List (SourceValue F)} {enums : String → Option Aiur.EnumDecl} :
    fn.prepare enums args = .ok (types, locals, body) ↔
      fn.params.map Prod.snd = args.map Value.type ∧ (args.map (wellFormed enums)).all id = true ∧
      types = fn.types ∧ locals = (fn.params.map Prod.fst).zip args ∧ body = fn.body := by
  unfold SourceFunction.prepare
  split
  · rename_i valid
    simp only [Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩; exact ⟨valid.1, valid.2, rfl, rfl, rfl⟩
    · rintro ⟨_, _, rfl, rfl, rfl⟩; exact ⟨rfl, rfl, rfl⟩
  · rename_i invalid
    constructor
    · intro h; cases h
    · rintro ⟨typed, formed, _, _, _⟩; exact (invalid ⟨typed, formed⟩).elim

end Aiur.Generic
