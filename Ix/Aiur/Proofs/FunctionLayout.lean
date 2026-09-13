/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CompilerLayout

/-! Successful compilation supplies the exact computed layout for every
function. The property survives deduplication and circuit grouping. -/

namespace Aiur.Bytecode

def Function.ComputedLayout (function : Function) : Prop :=
  let computed := ((Concrete.Bytecode.blockLayout function.body).run
    (.new function.layout.inputSize)).2.functionLayout
  function.layout = { computed with lookups := computed.lookups + 1 }

def FunctionsComputedLayout (functions : Array Function) : Prop :=
  ∀ function ∈ functions, function.ComputedLayout

theorem functionsComputedLayout_empty : FunctionsComputedLayout #[] := by
  simp [FunctionsComputedLayout]

theorem functionsComputedLayout_push {functions : Array Function} {function : Function}
    (before : FunctionsComputedLayout functions) (valid : function.ComputedLayout) :
    FunctionsComputedLayout (functions.push function) := by
  intro chosen member
  rcases Array.mem_push.mp member with prior | equal
  · exact before chosen prior
  · subst chosen; exact valid

theorem Function.ComputedLayout.auxiliaries {function : Function} (valid : function.ComputedLayout) :
    function.layout.auxiliaries = ((Concrete.Bytecode.blockLayout function.body).run
      (.new function.layout.inputSize)).2.functionLayout.auxiliaries := by
  have field := congrArg FunctionLayout.auxiliaries valid
  exact field

theorem Function.ComputedLayout.reserved {function : Function} (valid : function.ComputedLayout) :
    7 ≤ function.layout.auxiliaries := by
  rw [valid.auxiliaries]
  exact (Concrete.Bytecode.blockLayout_fields function.body (.new function.layout.inputSize)).2.2

theorem Function.ComputedLayout.selectors {function : Function} (valid : function.ComputedLayout) :
    function.layout.selectors = function.body.controlCounts.leaves := by
  have field := congrArg FunctionLayout.selectors valid
  have count := (Concrete.Bytecode.blockLayout_fields function.body (.new function.layout.inputSize)).2.1
  exact field.trans (by simpa only [Concrete.Bytecode.LayoutMState.new, Nat.zero_add] using count)

end Aiur.Bytecode

namespace Aiur.Concrete
open Aiur.Bytecode

private theorem layout_result_computed {body : Block} {size : Nat} {state : Bytecode.LayoutMState}
    {resultUnit : Unit} (computed : (Bytecode.blockLayout body).run (.new size) = (resultUnit, state)) :
    let final := { state.functionLayout with lookups := state.functionLayout.lookups + 1 }
    let calculated := ((Bytecode.blockLayout body).run (.new final.inputSize)).2.functionLayout
    final = { calculated with lookups := calculated.lookups + 1 } := by
  have input := (Bytecode.blockLayout_fields body (.new size)).1
  rw [computed] at input
  change state.functionLayout.inputSize = size at input
  dsimp only
  rw [input, computed]
  simp only [input]

theorem Function.compile_computedLayout {layoutMap : LayoutMap} {function : Function}
    {body : Block} {state : Bytecode.LayoutMState}
    (compiled : function.compile layoutMap = .ok (body, state)) (entry constrained : Bool) :
    (Aiur.Bytecode.Function.mk body state.functionLayout entry constrained).ComputedLayout := by
  unfold Function.compile at compiled
  simp only [bind, Except.bind, pure, Except.pure] at compiled
  repeat' first
    | split at compiled
    | (dsimp only at compiled; split at compiled)
  all_goals cases compiled
  all_goals exact layout_result_computed (by assumption)

private theorem except_foldlM_invariant {ε α β : Type} (items : List α) (step : β → α → Except ε β)
    (property : β → Prop) (initial : β) (before : property initial)
    (preserved : ∀ acc item result, property acc → step acc item = .ok result → property result)
    {result : β} (computed : items.foldlM step initial = .ok result) : property result := by
  induction items generalizing initial with
  | nil => cases computed; exact before
  | cons item items ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at computed
    split at computed
    · cases computed
    · rename_i next nextComputed
      exact ih next (preserved initial item next before nextComputed) computed

theorem Decls.toBytecode_computedLayout {decls : Decls} {program : Toplevel}
    {names : Std.HashMap Global FunIdx} (compiled : decls.toBytecode = .ok (program, names)) :
    FunctionsComputedLayout program.functions := by
  unfold Decls.toBytecode at compiled
  simp only [bind, Except.bind, pure, Except.pure] at compiled
  split at compiled
  · cases compiled
  · split at compiled
    · cases compiled
    · rename_i result folded
      cases compiled
      unfold IndexMap.foldlM at folded
      rw [← Array.foldlM_toList] at folded
      apply except_foldlM_invariant _ _ (fun result => FunctionsComputedLayout result.1) _
        functionsComputedLayout_empty ?_ folded
      intro acc item result before step
      rcases item with ⟨name, declaration⟩
      cases declaration <;> dsimp only at step
      all_goals first
        | (cases step; exact before)
        | (split at step
           · cases step
           · rename_i result compiled
             cases step
             exact functionsComputedLayout_push before (Function.compile_computedLayout compiled _ _))

end Aiur.Concrete

namespace Aiur.Bytecode

theorem Function.ComputedLayout.rewrite {function : Function} (valid : function.ComputedLayout)
    (rename : FunIdx → FunIdx) : { function with body := rewriteBlock rename function.body }.ComputedLayout := by
  unfold Function.ComputedLayout at *
  rw [Concrete.Bytecode.rewriteBlock_layout]
  exact valid

theorem deduplicate_newFunctions_computedLayout (functions : Array Function)
    (classes : Array Nat) (canonical : Array Bool) (rename : FunIdx → FunIdx)
    (valid : FunctionsComputedLayout functions) :
    FunctionsComputedLayout (deduplicate_newFunctions functions classes canonical rename) := by
  unfold deduplicate_newFunctions
  apply Array.foldl_induction (fun _ result => FunctionsComputedLayout result) functionsComputedLayout_empty
  intro index accumulated before
  dsimp only
  split
  · apply functionsComputedLayout_push before
    apply Function.ComputedLayout.rewrite
    apply valid
    exact (Array.of_mem_zip (Array.getElem_mem index.isLt)).2
  · exact before

theorem Toplevel.deduplicateCandidate_computedLayout (program : Toplevel)
    (valid : FunctionsComputedLayout program.functions) :
    FunctionsComputedLayout program.deduplicateCandidate.1.functions := by
  unfold Toplevel.deduplicateCandidate
  dsimp only
  split
  · exact valid
  · exact deduplicate_newFunctions_computedLayout _ _ _ _ valid

theorem Toplevel.deduplicate_computedLayout (program : Toplevel)
    (valid : FunctionsComputedLayout program.functions) :
    FunctionsComputedLayout program.deduplicate.1.functions := by
  unfold Toplevel.deduplicate checkedRenaming
  dsimp only
  split
  · exact program.deduplicateCandidate_computedLayout valid
  · exact valid

end Aiur.Bytecode

namespace Aiur
open Bytecode

theorem finishCompilation_computedLayout (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) (valid : FunctionsComputedLayout raw.functions) :
    FunctionsComputedLayout (finishCompilation source raw names).bytecode.functions := by
  unfold finishCompilation
  intro function member
  obtain ⟨index, bound, equal⟩ := Array.exists_of_mem_mapIdx member
  subst function
  change raw.deduplicate.1.functions[index].ComputedLayout
  exact raw.deduplicate_computedLayout valid _ (Array.getElem_mem bound)

theorem Source.Toplevel.compile_computedLayout {source : Source.Toplevel} {compiled : CompiledToplevel}
    (accepted : source.compile = .ok compiled) : FunctionsComputedLayout compiled.bytecode.functions := by
  obtain ⟨inlined, typed, concrete, raw, names, _, _, _, lowered, artifact⟩ :=
    source.compile_artifact_of_ok accepted
  rw [artifact]
  exact finishCompilation_computedLayout inlined raw names (Concrete.Decls.toBytecode_computedLayout lowered)

theorem BoundVerifier.Backend.functions_computedLayout {selection : BoundVerifier.Selection}
    (backend : BoundVerifier.Backend selection) : FunctionsComputedLayout backend.compiled.bytecode.functions := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  have valid := Source.Toplevel.compile_computedLayout compiled
  split at grouped
  · cases grouped
    exact valid
  · rw [(CompiledToplevel.groupFunctions_preserves_code grouped).2.2.1]
    exact valid

end Aiur
