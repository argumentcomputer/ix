/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.BoundVerifier

/-!
# Reference execution through the selected circuit grouping

Successful grouping preserves the source, function map, complete function
array and memory widths. Its partition change therefore preserves reference
execution, including errors and final I/O state. The selected backend can
reflect that execution back through final compilation metadata and checked
deduplication to the same named function in the actual lowering output. This
does not yet extract execution from AIR witnesses or reflect earlier passes.
-/

namespace Aiur

theorem CompiledToplevel.groupFunctions_preserves_code
    {before after : CompiledToplevel} {groups : Array (String × Array String)}
    (accepted : before.groupFunctions groups = .ok after) :
    after.source = before.source ∧ after.nameMap = before.nameMap ∧
    after.bytecode.functions = before.bytecode.functions ∧
    after.bytecode.memorySizes = before.bytecode.memorySizes := by
  unfold CompiledToplevel.groupFunctions at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · cases accepted
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem CompiledToplevel.groupFunctions_sameCode
    {before after : CompiledToplevel} {groups : Array (String × Array String)}
    (accepted : before.groupFunctions groups = .ok after) :
    Bytecode.Eval.SameCode after.bytecode before.bytecode := by
  have same := (groupFunctions_preserves_code accepted).2.2.1
  exact Bytecode.Eval.SameCode.ofFunctionsEq same

/-- Equality includes error results and final I/O state at every fuel value. -/
theorem CompiledToplevel.groupFunctions_preserves_execution
    {before after : CompiledToplevel} {groups : Array (String × Array String)}
    (accepted : before.groupFunctions groups = .ok after)
    (function : Bytecode.FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat) :
    Bytecode.Eval.runFunction after.bytecode function args io fuel =
      Bytecode.Eval.runFunction before.bytecode function args io fuel :=
  Bytecode.Eval.runFunction_sameCode (groupFunctions_sameCode accepted)
    function args io fuel

/-- The actual selected compilation preserves the ungrouped reference run. -/
theorem BoundVerifier.Backend.reference_execution
    {selection : BoundVerifier.Selection} (backend : BoundVerifier.Backend selection)
    (function : Bytecode.FunIdx) (args : Array G) (io : IOBuffer) (fuel : Nat) :
    ∃ initial, selection.source.compile = .ok initial ∧
      Bytecode.Eval.runFunction backend.compiled.bytecode function args io fuel =
        Bytecode.Eval.runFunction initial.bytecode function args io fuel := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  refine ⟨initial, compiled, ?_⟩
  split at grouped
  · cases grouped
    rfl
  · exact CompiledToplevel.groupFunctions_preserves_execution grouped function args io fuel

/-- Reference success at the selected entrypoint reflects to the exact
deduplicated output of the successful source compiler stages. No AIR or
cryptographic acceptance premise is substituted for reference execution. -/
theorem BoundVerifier.Backend.execution_reflects
    {selection : BoundVerifier.Selection} (backend : BoundVerifier.Backend selection)
    {args : Array G} {io : IOBuffer} {fuel : Nat} {result : Array G × IOBuffer}
    (accepted : Bytecode.Eval.runFunction backend.compiled.bytecode
      selection.function args io fuel = .ok result) :
    ∃ inlined typed concrete raw names,
      selection.source.inlineCalls = .ok inlined ∧
      inlined.checkAndSimplify = .ok typed ∧
      typed.concretize = .ok concrete ∧
      concrete.toBytecode = .ok (raw, names) ∧
      Bytecode.Eval.runFunction raw.deduplicate.1
        selection.function args io fuel = .ok result := by
  obtain ⟨initial, compiled, execution⟩ :=
    backend.reference_execution selection.function args io fuel
  obtain ⟨inlined, typed, concrete, raw, names, hi, ht, hc, hb, artifact⟩ :=
    Source.Toplevel.compile_artifact_of_ok compiled
  refine ⟨inlined, typed, concrete, raw, names, hi, ht, hc, hb, ?_⟩
  apply finishCompilation_reflects (source := inlined) (names := names)
  rw [← artifact]
  exact execution.symm.trans accepted

/-- Grouping retains the selected entrypoint as well as its reference run. -/
theorem BoundVerifier.Backend.reference_entrypoint
    {selection : BoundVerifier.Selection} (backend : BoundVerifier.Backend selection)
    (args : Array G) (io : IOBuffer) (fuel : Nat) :
    ∃ initial, selection.source.compile = .ok initial ∧
      initial.getFuncIdx selection.entrypoint = some selection.function ∧
      Bytecode.Eval.runFunction backend.compiled.bytecode selection.function args io fuel =
        Bytecode.Eval.runFunction initial.bytecode selection.function args io fuel := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  refine ⟨initial, compiled, ?_⟩
  split at grouped
  · cases grouped
    exact ⟨backend.selected, rfl⟩
  · have sameNames := (CompiledToplevel.groupFunctions_preserves_code grouped).2.1
    exact ⟨by simpa only [CompiledToplevel.getFuncIdx, sameNames] using backend.selected,
      CompiledToplevel.groupFunctions_preserves_execution grouped selection.function args io fuel⟩

/-- Successful execution of the selected backend reflects through grouping,
metadata and checked deduplication to the same named function in the actual
lowering output. The earlier source passes and AIR extraction are separate. -/
theorem BoundVerifier.Backend.execution_reflects_raw
    {selection : BoundVerifier.Selection} (backend : BoundVerifier.Backend selection)
    {args : Array G} {io : IOBuffer} {fuel : Nat} {result : Array G × IOBuffer}
    (accepted : Bytecode.Eval.runFunction backend.compiled.bytecode
      selection.function args io fuel = .ok result) :
    ∃ inlined typed concrete raw names original,
      selection.source.inlineCalls = .ok inlined ∧
      inlined.checkAndSimplify = .ok typed ∧
      typed.concretize = .ok concrete ∧
      concrete.toBytecode = .ok (raw, names) ∧
      names[Global.mk selection.entrypoint]? = some original ∧
      raw.deduplicate.2 original = selection.function ∧
      Bytecode.Eval.runFunction raw original args io fuel = .ok result := by
  obtain ⟨initial, compiled, selected, execution⟩ := backend.reference_entrypoint args io fuel
  obtain ⟨inlined, typed, concrete, raw, names, hi, ht, hc, hb, artifact⟩ :=
    Source.Toplevel.compile_artifact_of_ok compiled
  rw [artifact] at selected
  obtain ⟨original, named, remapped⟩ := finishCompilation_nameMap_image selected
  refine ⟨inlined, typed, concrete, raw, names, original, hi, ht, hc, hb, named, remapped, ?_⟩
  apply (finishCompilation_preserves_execution inlined raw names original args io fuel result).mpr
  rw [remapped, ← artifact]
  exact execution.symm.trans accepted

end Aiur
