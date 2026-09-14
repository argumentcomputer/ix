/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitReflection

/-!
Compose native-style circuit emission and base-graph compilation. Swept graph
constraints and every physical lookup slot have the valued circuit meaning,
including constant-zero elimination, root deduplication, and shared providers.
-/

namespace Aiur.NativeAIR.CircuitEmitter
open OpEmitter Compiler

theorem equations_vanish {values : Values G} {expressions : List Expr} {results : List G}
    (evaluated : expressions.mapM (evalExpr values) = some results) :
    ExprsVanish goldilocksOps values expressions ↔ ∀ result ∈ results, result = 0 := by
  have related := AIR.mapM_forall₂ evaluated (fun _ _ _ reflected => reflected)
  clear evaluated
  induction related with
  | nil => constructor <;> intro _ _ member <;> cases member
  | cons reflected _ ih =>
    rw [ExprsVanish.cons, List.forall_mem_cons]
    constructor
    · intro ⟨zero, zeros⟩
      exact ⟨Option.some.inj (reflected.symm.trans zero), ih.mp zeros⟩
    · intro ⟨zero, zeros⟩
      exact ⟨zero ▸ reflected, ih.mpr zeros⟩

structure Compiled where
  emission : Emission
  base : BaseCompilation

def compileCircuit (widths : GraphWidths) (program : Bytecode.Toplevel) (circuit : Bytecode.Circuit) : Option Compiled := do
  let emission ← emitCircuit program circuit
  let base ← compileBase widths emission.lookups emission.equations
  return ⟨emission, base⟩

theorem compileCircuit_reflects {values : Values G} (row : Nat → G) {widths : GraphWidths}
    (fits : values.Fits widths) (program : Bytecode.Toplevel) (circuit : Bytecode.Circuit) {compiled : Compiled}
    (built : compileCircuit widths program circuit = some compiled)
    (reads : ∀ index < compiled.emission.readBound,
      (values.columns .main .current)[index]? = some (row index)) :
    ∃ result buffer, circuit.emitRow row program = some result ∧
      compiled.base.graph.sweep goldilocksOps values = some buffer ∧
      (Vanishes goldilocksOps buffer compiled.base.graph.zeros ↔ ∀ equation ∈ result.equations, equation = 0) ∧
      compiled.base.graph.lookups.mapM (readLookup buffer) =
        some (List.ofFn fun slot : Fin result.lookupCount => result.lookup slot.val) := by
  simp only [compileCircuit, bind, Option.bind] at built
  split at built
  · cases built
  rename_i emission emitted
  dsimp only at built
  split at built
  · cases built
  rename_i base baseCompiled
  cases built
  obtain ⟨result, resultEmitted, evaluated⟩ := emitCircuit_reflects row program circuit emitted reads
  obtain ⟨buffer, swept, lookups, zeros⟩ := compileBase_reflects goldilocksGraphLaws fits
    emission.lookups emission.equations baseCompiled
  have equations := (Emission.eval_components evaluated).2.2.2.2.2.2.2.2.2.1
  obtain ⟨messages, exprReads, graphReads⟩ := lookups.read
  exact ⟨result, buffer, resultEmitted, swept, zeros.trans (equations_vanish equations),
    graphReads.trans (exprReads.symm.trans (Emission.lookups_eval evaluated))⟩

end Aiur.NativeAIR.CircuitEmitter
