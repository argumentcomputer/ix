import Compilatrix.IxIR1.Eval
import Compilatrix.IxIR2.Eval
import Compilatrix.IxIR2.Lower

/-!
# Compositional simulation interface for structured lowering

This file fixes the theorem shape before the proof is scaled over every
instruction. The first local lemma discharges the operand boundary shared by
all instruction cases: an IxIR₁ atom and its generated IxIR₂ atom resolve to
the same runtime value under an explicit environment relation.
-/

namespace Compilatrix.IxIR2.Lower.Sim

open Compilatrix.IxIR2

abbrev RVal := IxIR1.RVal

/-- Translate one source atom through an explicit source-slot-to-target-atom
map. This is the runtime view of the environment mapping recorded on CFG
edges by `Lower.EdgeTrace`. -/
def translateAtom (mapping : Array Atom) : IxIR1.Atom → Option Atom
  | .var index => mapping[index]?
  | .lit literal => some (.lit literal)
  | .erased => some .erased

/-- Every live source environment slot resolves through its generated target
atom to the same runtime value. Dead ownership slots are deliberately absent
from this semantic premise. -/
def EnvRel (source : List RVal) (target : Array RVal)
    (mapping : Array Atom) : Prop :=
  ∀ (index : Nat) (value : RVal), source[index]? = some value →
    ∃ atom, mapping[index]? = some atom ∧
      Eval.resolveAtom target atom = .ok value

/-- Operand resolution is representation-independent once the generated
environment map is related. This is the common first step of the `move`,
memory-operation, call, return, and switch simulation cases. -/
theorem resolveAtom_of_envRel {source : List RVal} {target : Array RVal}
    {mapping : Array Atom} (relation : EnvRel source target mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok value) :
    Eval.resolveAtom target targetAtom = .ok value := by
  cases sourceAtom with
  | var index =>
      have sourceGet : source[index]? = some value := by
        cases found : source[index]? with
        | none => simp [IxIR1.resolveAtom, found] at resolved
        | some candidate =>
            have equal : candidate = value := by
              simpa [IxIR1.resolveAtom, found] using resolved
            exact congrArg some equal
      obtain ⟨mapped, mappedGet, mappedValue⟩ := relation index value sourceGet
      simp only [translateAtom] at translated
      rw [mappedGet] at translated
      cases translated
      exact mappedValue
  | lit literal =>
      simp only [translateAtom, Option.some.injEq] at translated
      subst targetAtom
      simp only [IxIR1.resolveAtom, Except.ok.injEq] at resolved
      subst value
      rfl
  | erased =>
      simp only [translateAtom, Option.some.injEq] at translated
      subst targetAtom
      simp only [IxIR1.resolveAtom, Except.ok.injEq] at resolved
      subst value
      rfl

/-- Baseline logical execution preserves the exact IxIR₁ heap and value.
Later credit insertion weakens this to heap isomorphism; keeping the stronger
baseline relation makes that proof boundary explicit. -/
structure OutcomeRel (source : IxIR1.Store × RVal)
    (target : Eval.Result) : Prop where
  heap : target.store.heap = source.1
  value : target.value = source.2
  resetAttempts : target.store.resetAttempts = 0
  hotResets : target.store.hotResets = 0
  coldResets : target.store.coldResets = 0
  reusedPayloadUnits : target.store.reusedPayloadUnits = 0

/-- The block-compositional proof's public whole-main endpoint. Fuel is not
equated: source success existentially obtains independent target control and
heap-traversal budgets. -/
def SuccessfulMainSimulation (sourceContext : IxIR1.Ctx)
    (targetContext : Eval.Context) (sourceMain : IxIR1.Code)
    (targetProgram : Program) : Prop :=
  ∀ {sourceFuel sourceOut},
    IxIR1.runMain sourceContext sourceMain sourceFuel = .ok sourceOut →
    ∃ controlFuel heapFuel targetOut,
      Eval.runMain targetContext .logical targetProgram controlFuel heapFuel =
          .ok targetOut ∧
        OutcomeRel sourceOut targetOut

end Compilatrix.IxIR2.Lower.Sim
