import Aiur.Tuple.Circuit.BuildFacts

namespace Aiur.Tuple.Circuit

private theorem except_bind_ok {first : Except ε α} {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔ ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [bind, Except.bind]

/-- Expose the actual stages of compiling a function, without changing the compiler. -/
theorem Compiler.lowerFunction_stages [Field F] [DecidableEq F]
    {program : Program F} {fn : Function F} {chip : Chip F}
    (compiled : Compiler.lowerFunction program fn = .ok chip) :
    ∃ inputs output s₁ s₂ body s₃ s₄,
      Compiler.freshValues (fn.params.map Prod.snd) {} = .ok (inputs, s₁) ∧
      Compiler.freshValue fn.result s₁ = .ok (output, s₂) ∧
      Compiler.lowerExpr program fn.name
        ((fn.params.map Prod.fst).zip (inputs.map (Value.map ArithExpr.var)))
        (.const 1) fn.body s₂ = .ok (body, s₃) ∧
      Compiler.constrainValue (.const 1) (output.map ArithExpr.var) body s₃ = .ok ((), s₄) ∧
      chip = ⟨fn.name, inputs, output, s₄.nextVar, s₄.constraints.toList, s₄.sends.toList⟩ := by
  unfold Compiler.lowerFunction at compiled
  obtain ⟨⟨⟨inputs, output⟩, state⟩, run, finished⟩ := except_bind_ok.mp compiled
  simp only [pure, Except.pure, Except.ok.injEq] at finished
  subst chip
  obtain ⟨inputs, s₁, inputsRun, rest⟩ := Compiler.bind_ok.mp run
  obtain ⟨output, s₂, outputRun, rest⟩ := Compiler.bind_ok.mp rest
  obtain ⟨body, s₃, bodyRun, rest⟩ := Compiler.bind_ok.mp rest
  obtain ⟨finished, s₄, constraintRun, rest⟩ := Compiler.bind_ok.mp rest
  cases finished
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := Compiler.pure_ok.mp rest
  exact ⟨inputs, output, s₁, s₂, body, s₃, s₄, inputsRun, outputRun, bodyRun, constraintRun, rfl⟩

theorem Compiler.lowerFunction_interface [Field F] [DecidableEq F]
    {program : Program F} {fn : Function F} {chip : Chip F}
    (compiled : Compiler.lowerFunction program fn = .ok chip) :
    chip.name = fn.name ∧ chip.inputs.map Value.type = fn.params.map Prod.snd ∧
      chip.output.type = fn.result := by
  obtain ⟨_, _, _, _, _, _, _, inputsRun, outputRun, _, _, rfl⟩ := lowerFunction_stages compiled
  exact ⟨rfl, (freshValues_spec inputsRun).2.2, (freshValue_spec outputRun).2.2⟩

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
  unfold compile at compiled
  cases checked : typecheck program with
  | error error => simp [checked] at compiled; cases compiled
  | ok checkedUnit =>
      cases checkedUnit
      cases mapped : program.functions.mapM (Compiler.lowerFunction program) with
      | error error => simp [checked, mapped] at compiled
      | ok chips =>
          simp [checked, mapped] at compiled
          subst system
          exact forall₂_of_mapM_ok mapped

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

end Aiur.Tuple.Circuit
