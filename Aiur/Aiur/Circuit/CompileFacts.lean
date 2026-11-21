import Aiur.Circuit.BuildFacts
import Aiur.TypecheckFacts
import Aiur.EncodingTypes

namespace Aiur.Circuit

variable {F : Type} {rom : WireROM F}

private theorem except_bind_ok {first : Except ε α} {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [bind, Except.bind]

/-- Expose interface validation separately from the function body. -/
theorem Compiler.lowerFunction_stages [Field F] [DecidableEq F]
    {program : Program F} {fn : Function F} {chip : Chip F}
    (compiled : Compiler.lowerFunction program fn = .ok chip) :
    ∃ inputs output s₁ s₂ s₃ s₄ body s₅ s₆,
      Compiler.freshValues program.enums (fn.params.map Prod.snd) {} = .ok (inputs, s₁) ∧
      Compiler.freshValue program.enums fn.result s₁ = .ok (output, s₂) ∧
      Compiler.validateValues program.enums (.const 1)
        (inputs.map (WireValue.map ArithExpr.var)) s₂ = .ok ((), s₃) ∧
      Compiler.validateValue program.enums (.const 1) (output.map ArithExpr.var) s₃ = .ok ((), s₄) ∧
      Compiler.lowerExpr program fn.name
        ((fn.params.map Prod.fst).zip (inputs.map (WireValue.map ArithExpr.var)))
        (.const 1) fn.body s₄ = .ok (body, s₅) ∧
      Compiler.constrainValue (.const 1) (output.map ArithExpr.var) body s₅ = .ok ((), s₆) ∧
      chip = ⟨fn.name, inputs, output.map ArithExpr.var, s₆.nextVar, s₆.constraints.toList, s₆.sends.toList, s₆.memory.toList⟩ := by
  unfold Compiler.lowerFunction at compiled
  obtain ⟨⟨⟨inputs, output⟩, state⟩, run, finished⟩ := except_bind_ok.mp compiled
  simp only [pure, Except.pure, Except.ok.injEq] at finished
  subst chip
  obtain ⟨inputs, s₁, inputsRun, rest⟩ := Compiler.bind_ok.mp run
  obtain ⟨output, s₂, outputRun, rest⟩ := Compiler.bind_ok.mp rest
  obtain ⟨⟨⟩, s₃, inputsValid, rest⟩ := Compiler.bind_ok.mp rest
  obtain ⟨⟨⟩, s₄, outputValid, rest⟩ := Compiler.bind_ok.mp rest
  obtain ⟨body, s₅, bodyRun, rest⟩ := Compiler.bind_ok.mp rest
  obtain ⟨⟨⟩, s₆, constraintRun, rest⟩ := Compiler.bind_ok.mp rest
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Compiler.pure_ok.mp rest
  exact ⟨inputs, output, s₁, s₂, s₃, s₄, body, s₅, s₆,
    inputsRun, outputRun, inputsValid, outputValid, bodyRun, constraintRun, rfl⟩

theorem Compiler.lowerFunction_interface [Field F] [DecidableEq F]
    {program : Program F} {fn : Function F} {chip : Chip F}
    (compiled : Compiler.lowerFunction program fn = .ok chip) :
    chip.name = fn.name ∧ chip.inputs.map WireValue.type = fn.params.map Prod.snd ∧
      chip.output.type = fn.result := by
  obtain ⟨_, _, _, _, _, _, _, _, _, inputsRun, outputRun, _, _, _, _, rfl⟩ := lowerFunction_stages compiled
  exact ⟨rfl, (freshValues_spec inputsRun).2.2.1, (freshValue_spec outputRun).2.2.1⟩

/-- Compilation checks field tag injectivity independently of allocation capacity. -/
theorem compile_stages [Field F] [DecidableEq F] {program : Program F} {system : System F}
    (compiled : compile program = .ok system) :
    typecheck program = .ok () ∧ program.enums.tagsValid F = true ∧
      program.functions.mapM (Compiler.lowerFunction program) = .ok system.chips ∧
      system.enums = program.enums ∧ system.tables = program.tables ∧ system.maps = program.maps := by
  unfold compile at compiled
  obtain ⟨⟨⟩, checked, rest⟩ := except_bind_ok.mp compiled
  have checked : typecheck program = .ok () := by
    cases h : typecheck program with
    | error error => simp [h, Except.mapError] at checked
    | ok unit => cases unit; rfl
  obtain ⟨⟨⟩, tags, rest⟩ := except_bind_ok.mp rest
  obtain ⟨chips, mapped, last⟩ := except_bind_ok.mp rest
  obtain ⟨⟨⟩, _, finished⟩ := except_bind_ok.mp last
  have same := except_pure_ok.mp finished
  subst system
  refine ⟨checked, ?_, mapped, rfl, rfl, rfl⟩
  apply (Declarations.tagsValid_spec program.enums).mpr
  have each := forIn_ok (items := program.enums) (action := checkEnumTags F) (by
    have combined := congrArg (fun r : Except CompileError PUnit => r >>= fun _ =>
      (pure () : Except CompileError Unit)) tags
    simpa only [bind, Except.bind, pure, Except.pure] using combined)
  intro decl member
  have accepted := each decl member
  unfold checkEnumTags at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Successful compilation certifies the complete output namespace and
layouts, including functions unused by a particular execution. -/
theorem compile_checkChips [Field F] [DecidableEq F] {program : Program F} {system : System F}
    (compiled : compile program = .ok system) : checkChips [] system.chips = .ok () := by
  unfold compile at compiled
  obtain ⟨_, _, rest₁⟩ := except_bind_ok.mp compiled
  obtain ⟨_, _, rest₂⟩ := except_bind_ok.mp rest₁
  obtain ⟨chips, _, rest₃⟩ := except_bind_ok.mp rest₂
  obtain ⟨_, formed, finished⟩ := except_bind_ok.mp rest₃
  obtain rfl := except_pure_ok.mp finished
  cases checked : checkChips [] chips with
  | error error => simp [checked, Except.mapError] at formed
  | ok value => cases value; rfl


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

theorem compile_functions [Field F] [DecidableEq F] {program : Program F} {system : System F}
    (compiled : compile program = .ok system) :
    List.Forall₂ (fun fn chip => Compiler.lowerFunction program fn = .ok chip)
      program.functions system.chips := by
  exact forall₂_of_mapM_ok (compile_stages compiled).2.2.1

private theorem lookup_functions [Field F] [DecidableEq F] {program : Program F}
    {fns : List (Function F)} {chips : List (Chip F)}
    (compiled : List.Forall₂ (fun fn chip => Compiler.lowerFunction program fn = .ok chip) fns chips)
    (name : String) :
    Option.Rel (fun fn chip => Compiler.lowerFunction program fn = .ok chip)
      (fns.find? (·.name == name)) (chips.find? (·.name == name)) := by
  induction compiled with
  | nil => exact .none
  | cons head _ ih =>
      have names := (Compiler.lowerFunction_interface head).1
      simp only [List.find?_cons, names]
      split
      · exact .some head
      · exact ih

theorem compile_find_function [Field F] [DecidableEq F]
    {program : Program F} {system : System F} (compiled : compile program = .ok system)
    {name : String} {fn : Function F} (found : program.findFunction? name = some fn) :
    ∃ chip, system.findChip? name = some chip ∧ Compiler.lowerFunction program fn = .ok chip := by
  have related := lookup_functions (compile_functions compiled) name
  change Option.Rel _ (program.findFunction? name) (system.findChip? name) at related
  rw [found] at related
  cases target : system.findChip? name with
  | none => rw [target] at related; cases related
  | some chip =>
      rw [target] at related
      cases related with
      | some lowered => exact ⟨chip, rfl, lowered⟩

theorem compile_find_chip [Field F] [DecidableEq F]
    {program : Program F} {system : System F} (compiled : compile program = .ok system)
    {name : String} {chip : Chip F} (found : system.findChip? name = some chip) :
    ∃ fn, program.findFunction? name = some fn ∧ Compiler.lowerFunction program fn = .ok chip := by
  have related := lookup_functions (compile_functions compiled) name
  change Option.Rel _ (program.findFunction? name) (system.findChip? name) at related
  rw [found] at related
  cases source : program.findFunction? name with
  | none => rw [source] at related; cases related
  | some fn =>
      rw [source] at related
      cases related with
      | some lowered => exact ⟨fn, rfl, lowered⟩

theorem findFunction_name {program : Program F} {name : String} {fn : Function F}
    (found : program.findFunction? name = some fn) : fn.name = name := by
  have := List.find?_some found
  simpa using this

end Aiur.Circuit
