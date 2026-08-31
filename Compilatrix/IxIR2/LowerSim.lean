import Compilatrix.IxIR1.Eval
import Compilatrix.IxIR2.Eval
import Compilatrix.IxIR2.Lower

/-!
# Compositional simulation interface for structured lowering

This file fixes the theorem shape before the proof is scaled over every
instruction. Its foundation discharges scalar and vector operand resolution,
extends related environments across value and erased bindings, and closes the
first public small-step case for an IxIR₁ `pure` lowered to IxIR₂ `move`.
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

/-- Appending a new SSA value does not change resolution of any atom that was
already valid in the frame. -/
theorem resolveAtom_push_old {target : Array RVal} {atom : Atom}
    {value extra : RVal}
    (resolved : Eval.resolveAtom target atom = .ok value) :
    Eval.resolveAtom (target.push extra) atom = .ok value := by
  cases atom with
  | lit literal => exact resolved
  | erased => exact resolved
  | reg index =>
      have notEnd : index ≠ target.size := by
        intro equal
        subst index
        simp [Eval.resolveAtom] at resolved
      simpa [Eval.resolveAtom, Array.getElem?_push, notEnd] using resolved

/-- Result-producing instructions prepend one source de Bruijn binding while
appending one target SSA register. -/
theorem EnvRel.bindValue {source : List RVal} {target : Array RVal}
    {mapping : Array Atom} (relation : EnvRel source target mapping)
    (value : RVal) :
    EnvRel (value :: source) (target.push value)
      (#[.reg target.size] ++ mapping) := by
  intro index candidate sourceGet
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceGet
      subst candidate
      refine ⟨.reg target.size, ?_, ?_⟩
      · simp [Array.getElem?_append]
      · simp [Eval.resolveAtom]
  | succ index =>
      have oldGet : source[index]? = some candidate := by
        simpa using sourceGet
      obtain ⟨atom, mapped, resolved⟩ := relation index candidate oldGet
      refine ⟨atom, ?_, resolveAtom_push_old resolved⟩
      simpa [Array.getElem?_append] using mapped

/-- Effect-only IxIR₂ instructions append no SSA value; their IxIR₁ result
binder is represented directly by the erased atom. -/
theorem EnvRel.bindErased {source : List RVal} {target : Array RVal}
    {mapping : Array Atom} (relation : EnvRel source target mapping) :
    EnvRel (.erased :: source) target (#[.erased] ++ mapping) := by
  intro index candidate sourceGet
  cases index with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at sourceGet
      subst candidate
      refine ⟨.erased, ?_, rfl⟩
      simp [Array.getElem?_append]
  | succ index =>
      have oldGet : source[index]? = some candidate := by
        simpa using sourceGet
      obtain ⟨atom, mapped, resolved⟩ := relation index candidate oldGet
      refine ⟨atom, ?_, resolved⟩
      simpa [Array.getElem?_append] using mapped

/-- A target `move` takes exactly one public small step, preserving the store,
stack, and credits while advancing the program counter and appending its
resolved value.  This packages the evaluator reduction needed by the source
`pure` instruction case. -/
theorem step_move {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {atom : Atom} {value : RVal}
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .move atom)
    (resolved : Eval.resolveAtom frame.values atom = .ok value) :
    Eval.Step context interpretation machine
      { machine with
        control := .running
          { frame with
            pc := frame.pc + 1
            values := frame.values.push value }
          stack } := by
  exact Eval.Step.move control blockAt pc instruction resolved

/-- The source `pure`/target `move` boundary preserves operand meaning and the
environment relation needed by the continuation. -/
theorem pure_move_preserves {source : List RVal} {target : Array RVal}
    {mapping : Array Atom} (relation : EnvRel source target mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (resolved : IxIR1.resolveAtom source sourceAtom = .ok value) :
    Eval.resolveAtom target targetAtom = .ok value ∧
      EnvRel (value :: source) (target.push value)
        (#[.reg target.size] ++ mapping) := by
  exact ⟨resolveAtom_of_envRel relation translated resolved,
    relation.bindValue value⟩

/-- First instruction-level simulation case: a related IxIR₁ `pure` operand
drives the generated IxIR₂ `move` step, and the successor environments are
again related. -/
theorem simulate_pure_move {context : Eval.Context}
    {interpretation : Eval.Interpretation} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {source : List RVal} {mapping : Array Atom}
    (relation : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .move targetAtom) :
    Eval.Step context interpretation machine
        { machine with
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack } ∧
      EnvRel (value :: source) (frame.values.push value)
        (#[.reg frame.values.size] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel relation translated sourceResolved
  exact ⟨step_move control blockAt pc instruction targetResolved,
    relation.bindValue value⟩

/-- Pointwise translation of an operand vector. Keeping this relation
separate from the executable translators makes it compose directly with
generated instruction equations. -/
inductive AtomsListRel (mapping : Array Atom) :
    List IxIR1.Atom → List Atom → Prop where
  | nil : AtomsListRel mapping [] []
  | cons : translateAtom mapping sourceAtom = some targetAtom →
      AtomsListRel mapping sourceAtoms targetAtoms →
      AtomsListRel mapping (sourceAtom :: sourceAtoms)
        (targetAtom :: targetAtoms)

def AtomsRel (mapping : Array Atom) (source : Array IxIR1.Atom)
    (target : Array Atom) : Prop :=
  AtomsListRel mapping source.toList target.toList

private theorem except_bind_eq_ok {ε α β : Type} {input : Except ε α}
    {next : α → Except ε β} {output : β}
    (bound : input.bind next = .ok output) :
    ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input with
  | error error => cases bound
  | ok value => exact ⟨value, rfl, bound⟩

private theorem resolveFold_of_envRel {source : List RVal}
    {target : Array RVal} {mapping : Array Atom}
    (relation : EnvRel source target mapping)
    {sourceAtoms : List IxIR1.Atom} {targetAtoms : List Atom}
    (atoms : AtomsListRel mapping sourceAtoms targetAtoms) :
    ∀ (accumulator output : List RVal),
      List.foldlM
          (fun values atom => do
            return values ++ [← IxIR1.resolveAtom source atom])
          accumulator sourceAtoms = .ok output →
      List.foldlM
          (fun values atom => do
            return values.push (← Eval.resolveAtom target atom))
          accumulator.toArray targetAtoms = .ok output.toArray := by
  induction atoms with
  | nil =>
      intro accumulator output resolved
      simp only [List.foldlM_nil] at resolved ⊢
      cases resolved
      rfl
  | @cons sourceAtom targetAtom sourceAtoms targetAtoms translated _ ih =>
      intro accumulator output resolved
      simp only [List.foldlM_cons] at resolved ⊢
      obtain ⟨nextAccumulator, headResolved, tailResolved⟩ :=
        except_bind_eq_ok resolved
      obtain ⟨value, sourceResolved, nextResolved⟩ :=
        except_bind_eq_ok headResolved
      have nextEqual : nextAccumulator = accumulator ++ [value] := by
        simpa using Except.ok.inj nextResolved.symm
      subst nextAccumulator
      have targetResolved :
          Eval.resolveAtom target targetAtom = .ok value :=
        resolveAtom_of_envRel relation translated sourceResolved
      rw [targetResolved]
      have appendArray :
          (accumulator ++ [value]).toArray = accumulator.toArray.push value := by
        apply Array.ext'
        simp
      change List.foldlM
          (fun values atom => do
            return values.push (← Eval.resolveAtom target atom))
          (accumulator.toArray.push value) targetAtoms = .ok output.toArray
      rw [← appendArray]
      exact ih (accumulator ++ [value]) output tailResolved

/-- Operand-vector resolution agrees pointwise, including result order. -/
theorem resolveAtoms_of_envRel {source : List RVal} {target : Array RVal}
    {mapping : Array Atom} (relation : EnvRel source target mapping)
    {sourceAtoms : Array IxIR1.Atom} {targetAtoms : Array Atom}
    (atoms : AtomsRel mapping sourceAtoms targetAtoms)
    {values : List RVal}
    (resolved : IxIR1.resolveAtoms source sourceAtoms = .ok values) :
    Eval.resolveAtoms target targetAtoms = .ok values.toArray := by
  unfold Eval.resolveAtoms
  rw [← Array.foldlM_toList]
  apply resolveFold_of_envRel relation atoms [] values
  simpa only [IxIR1.resolveAtoms, Array.foldlM_toList] using resolved

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
