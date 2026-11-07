import Aiur.Optimized.Program
import Aiur.Optimized.CompileFacts

namespace Aiur.Optimized

variable {F : Type} [Field F] [DecidableEq F]

theorem compile_stages {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact) :
    typecheck program = .ok () ∧ program.enums.tagsValid F = true ∧
      artifact.entries = entries ∧ artifact.config = config ∧
      program.functions.mapM (fun function => do layOut config (← Compiler.function program config function (entries.contains function.name))) =
        .ok artifact.layouts ∧
      artifact.unmerged = ⟨artifact.layouts.map (·.chip), program.enums, program.tables, program.maps⟩ := by
  unfold compile at compiled
  dsimp only at compiled
  split at compiled
  · simp [bind, Except.bind] at compiled
  · simp only [pure_bind] at compiled
    obtain ⟨⟨⟩, checked, rest₁⟩ := except_bind_ok.mp compiled
    have checked : typecheck program = .ok () := by
      cases found : typecheck program with
      | error error => simp [found, Except.mapError] at checked
      | ok unit => cases unit; rfl
    obtain ⟨⟨⟩, _, rest₂⟩ := except_bind_ok.mp rest₁
    obtain ⟨⟨⟩, tags, rest₃⟩ := except_bind_ok.mp rest₂
    obtain ⟨layouts, mapped, rest₄⟩ := except_bind_ok.mp rest₃
    obtain ⟨result, deduplicated, rest₅⟩ := except_bind_ok.mp rest₄
    obtain ⟨⟨⟩, formed, finished⟩ := except_bind_ok.mp rest₅
    split at finished
    · obtain rfl := except_pure_ok.mp finished
      refine ⟨checked, ?_, rfl, rfl, mapped, rfl⟩
      apply (Declarations.tagsValid_spec program.enums).mpr
      have each := forIn_ok (items := program.enums)
        (action := fun declaration => (Circuit.checkEnumTags F declaration).mapError reprStr) (by
          have combined := congrArg (fun result : Except String PUnit => result >>= fun _ =>
            (pure () : Except String Unit)) tags
          simpa only [bind, Except.bind, pure, Except.pure] using combined)
      intro declaration member
      have accepted := each declaration member
      cases found : Circuit.checkEnumTags F declaration with
      | error error => simp [found, Except.mapError] at accepted
      | ok unit =>
          unfold Circuit.checkEnumTags at found
          split at found
          · assumption
          · cases found
    · cases finished

theorem Artifact.unmerged_wellFormed (artifact : Artifact F) : artifact.unmerged.WellFormed := by
  have accepted := artifact.deduplication.2.2.2.2.2.2.1
  have checked := Circuit.checkChips_iff.mp accepted
  exact ⟨checked.1, checked.2.1⟩

theorem Artifact.wellFormed (artifact : Artifact F) : artifact.system.WellFormed := by
  have accepted := artifact.deduplication.2.2.2.2.2.2.2.1
  have checked := Circuit.checkChips_iff.mp accepted
  exact ⟨checked.1, checked.2.1⟩

theorem compile_enums {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact) : artifact.system.enums = program.enums := by
  have unmerged := (compile_stages compiled).2.2.2.2.2
  exact artifact.deduplication.2.2.2.2.2.1.trans (by rw [unmerged])

private theorem forall₂_of_mapM_ok {f : α → Except ε β} {xs : List α} {ys : List β}
    (mapped : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil] at mapped; cases mapped; exact .nil
  | cons x xs ih =>
      cases hx : f x with
      | error error => simp [hx] at mapped; cases mapped
      | ok y =>
          cases hxs : xs.mapM f with
          | error error => simp [hx, hxs] at mapped; cases mapped
          | ok rest =>
              simp [hx, hxs] at mapped
              cases mapped
              exact .cons hx (ih hxs)

def FunctionLowered (program : Program F) (config : Config) (entries : List String) (function : Function F) (chip : Circuit.Chip F) : Prop :=
  ∃ logical layout, Compiler.function program config function (entries.contains function.name) = .ok logical ∧
    layOut config logical = .ok layout ∧ layout.chip = chip

theorem FunctionLowered.interface {program : Program F} {config : Config} {entries : List String} {function : Function F}
    {chip : Circuit.Chip F} (compiled : FunctionLowered program config entries function chip) :
    chip.name = function.name ∧ chip.inputs.map WireValue.type = function.params.map Prod.snd ∧
      chip.output.type = function.result := by
  obtain ⟨logical, layout, lowered, laidOut, rfl⟩ := compiled
  have source := Compiler.function_interface lowered
  have physical := layOut_interface laidOut
  exact ⟨physical.1.trans source.1, physical.2.1.trans source.2.1, physical.2.2.trans source.2.2⟩

theorem compile_functions {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact) :
    List.Forall₂ (FunctionLowered program config entries) program.functions artifact.unmerged.chips := by
  have stages := compile_stages compiled
  have mapped := forall₂_of_mapM_ok stages.2.2.2.2.1
  rw [stages.2.2.2.2.2]
  apply List.forall₂_map_right_iff.mpr
  apply mapped.imp
  intro function layout run
  obtain ⟨logical, lowered, laidOut⟩ := except_bind_ok.mp run
  exact ⟨logical, layout, lowered, laidOut, rfl⟩

private theorem lookup_functions {program : Program F} {config : Config} {entries : List String}
    {functions : List (Function F)} {chips : List (Circuit.Chip F)}
    (compiled : List.Forall₂ (FunctionLowered program config entries) functions chips) (name : String) :
    Option.Rel (FunctionLowered program config entries)
      (functions.find? (·.name == name)) (chips.find? (·.name == name)) := by
  induction compiled with
  | nil => exact .none
  | cons head _ ih =>
      have names := head.interface.1
      simp only [List.find?_cons, names]
      split
      · exact .some head
      · exact ih

theorem compile_find_function {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact)
    {name : String} {function : Function F} (found : program.findFunction? name = some function) :
    ∃ chip, artifact.unmerged.findChip? name = some chip ∧ FunctionLowered program config entries function chip := by
  have related := lookup_functions (compile_functions compiled) name
  change Option.Rel _ (program.findFunction? name) (artifact.unmerged.findChip? name) at related
  rw [found] at related
  cases target : artifact.unmerged.findChip? name with
  | none => rw [target] at related; cases related
  | some chip =>
      rw [target] at related
      cases related with
      | some lowered => exact ⟨chip, rfl, lowered⟩

theorem compile_find_chip {program : Program F} {entries : List String} {config : Config} {artifact : Artifact F}
    (compiled : compile program entries config = .ok artifact)
    {name : String} {chip : Circuit.Chip F} (found : artifact.unmerged.findChip? name = some chip) :
    ∃ function, program.findFunction? name = some function ∧ FunctionLowered program config entries function chip := by
  have related := lookup_functions (compile_functions compiled) name
  change Option.Rel _ (program.findFunction? name) (artifact.unmerged.findChip? name) at related
  rw [found] at related
  cases source : program.findFunction? name with
  | none => rw [source] at related; cases related
  | some function =>
      rw [source] at related
      cases related with
      | some lowered => exact ⟨function, rfl, lowered⟩

theorem Artifact.check_iff {artifact : Artifact F} {rom : WireROM F} {root : Circuit.Message F}
    {rows : List (Circuit.Row F)} :
    artifact.check rom root rows = .ok () ↔ root.channel ∈ artifact.entries ∧
      artifact.system.check rom root rows = .ok () := by
  unfold Artifact.check
  by_cases selected : root.channel ∈ artifact.entries
  · simp only [List.contains_iff_mem, selected, ↓reduceIte, pure_bind, true_and]
    cases checked : artifact.system.check rom root rows <;> simp [Except.mapError, checked]
  · simp [List.contains_iff_mem, selected, bind, Except.bind]

theorem Artifact.checkMemo_iff {artifact : Artifact F} {rom : WireROM F} {root : Circuit.Message F}
    {rows : List (Circuit.WeightedRow F)} :
    artifact.checkMemo rom root rows = .ok () ↔ root.channel ∈ artifact.entries ∧
      artifact.system.checkMemo rom root rows = .ok () := by
  unfold Artifact.checkMemo
  by_cases selected : root.channel ∈ artifact.entries
  · simp only [List.contains_iff_mem, selected, ↓reduceIte, pure_bind, true_and]
    cases checked : artifact.system.checkMemo rom root rows <;> simp [Except.mapError, checked]
  · simp [List.contains_iff_mem, selected, bind, Except.bind]

end Aiur.Optimized
