import Compilatrix.IxIR1.Eval
import Compilatrix.IxIR2.Eval
import Compilatrix.IxIR2.Lower

/-!
# Compositional simulation interface for structured lowering

This file fixes the theorem shape before the proof is scaled over every
instruction. Its foundation discharges scalar and vector operand resolution,
extends related environments across value and erased bindings, and closes the
public small-step cases for IxIR₁ `pure`/IxIR₂ `move` and exact ordinary
constructor allocation, scalar and heap-bearing shared-retain paths, scalar
and nonunit shared-release paths, scalar unique drop, checked scalar-leaf
unique free, and checked non-consuming projection.
-/

namespace Compilatrix.IxIR2.Lower.Sim

open Compilatrix.IxIR2

abbrev RVal := IxIR1.RVal

/-- The structured baseline executes against exactly the IxIR₁ heap and
does not exercise any reset/reuse-credit counters.  Peak-live accounting is a
target-only observation and is intentionally omitted. -/
structure StoreRel (source : IxIR1.Store) (target : Eval.Store) : Prop where
  heap : target.heap = source
  resetAttempts : target.resetAttempts = 0
  hotResets : target.hotResets = 0
  coldResets : target.coldResets = 0
  reusedPayloadUnits : target.reusedPayloadUnits = 0

/-- Ordinary allocation preserves the exact baseline store relation. -/
theorem StoreRel.alloc {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) (world : Compilatrix.Ixon.Owned)
    (node : IxIR1.Node) :
    StoreRel (source.allocNode world node).1
      (target.allocNode world node).1 := by
  constructor
  · rw [Eval.Store.allocNode_heap, relation.heap]
  · change target.resetAttempts = 0
    exact relation.resetAttempts
  · change target.hotResets = 0
    exact relation.hotResets
  · change target.coldResets = 0
    exact relation.coldResets
  · change target.reusedPayloadUnits = 0
    exact relation.reusedPayloadUnits

/-- Related stores choose the same fresh location. -/
theorem StoreRel.alloc_location {source : IxIR1.Store}
    {target : Eval.Store} (relation : StoreRel source target)
    (world : Compilatrix.Ixon.Owned) (node : IxIR1.Node) :
    (target.allocNode world node).2 =
      (source.allocNode world node).2 := by
  rw [Eval.Store.allocNode_location, relation.heap]

/-- Updating the same node preserves exact heap correspondence. -/
theorem StoreRel.setBox {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) (location : Nat)
    (box : IxIR1.NodeBox) :
    StoreRel (source.setBox location box) (target.setBox location box) := by
  constructor
  · rw [Eval.Store.setBox_heap, relation.heap]
  · exact relation.resetAttempts
  · exact relation.hotResets
  · exact relation.coldResets
  · exact relation.reusedPayloadUnits

/-- Killing the same location preserves exact heap correspondence. -/
theorem StoreRel.kill {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) (location : Nat) :
    StoreRel (source.kill location) (target.kill location) := by
  constructor
  · rw [Eval.Store.kill_heap, relation.heap]
  · exact relation.resetAttempts
  · exact relation.hotResets
  · exact relation.coldResets
  · exact relation.reusedPayloadUnits

/-- Charging the same RC operation preserves exact store correspondence. -/
theorem StoreRel.rcTick {source : IxIR1.Store} {target : Eval.Store}
    (relation : StoreRel source target) :
    StoreRel source.rcTick target.rcTick := by
  constructor
  · rw [Eval.Store.rcTick_heap, relation.heap]
  · exact relation.resetAttempts
  · exact relation.hotResets
  · exact relation.coldResets
  · exact relation.reusedPayloadUnits

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

/-- Retaining a scalar is operationally inert. -/
theorem retainShared_of_scalar {store : Eval.Store} {value : RVal}
    (scalar : Eval.RVal.isScalar value = true) :
    Eval.retainShared store value = .ok store := by
  cases value <;> simp [Eval.RVal.isScalar, Eval.retainShared] at scalar ⊢

/-- Releasing a scalar leaves the store unchanged and spends exactly the one
heap-traversal unit used to inspect the work-list item. -/
theorem releaseShared_of_scalar {store : Eval.Store} {value : RVal}
    (heapFuel : Nat) (scalar : Eval.RVal.isScalar value = true) :
    Eval.releaseShared (heapFuel + 1) store value = .ok (store, heapFuel) := by
  cases value <;>
    simp [Eval.RVal.isScalar, Eval.releaseShared,
      Eval.releaseSharedWork] at scalar ⊢

/-- Dropping a unique scalar has the same one-item heap-budget behavior as a
shared scalar release. -/
theorem dropUnique_of_scalar {store : Eval.Store} {value : RVal}
    (heapFuel : Nat) (scalar : Eval.RVal.isScalar value = true) :
    Eval.dropUnique (heapFuel + 1) store value = .ok (store, heapFuel) := by
  cases value <;>
    simp [Eval.RVal.isScalar, Eval.dropUnique,
      Eval.dropUniqueWork] at scalar ⊢

/-- The scalar branch of IxIR₁ `dup` and IxIR₂ `retainShared` is an
identical store-preserving step. -/
theorem simulate_dup_retain_scalar {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .retainShared targetAtom) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dup sourceAtom) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (value :: source) (frame.values.push value)
        (#[.reg frame.values.size] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetStep := Eval.Step.retainShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved (retainShared_of_scalar scalar)
  refine ⟨?_, targetStep, stores, environments.bindValue value⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  cases value with
  | loc location => simp [Eval.RVal.isScalar] at scalar
  | lit literal => rfl
  | erased => rfl

/-- The heap-bearing branch increments the same shared node and RC counter in
both exact stores before binding the retained location. -/
theorem simulate_dup_retain_shared {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {location : Nat} {box : IxIR1.NodeBox}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .retainShared targetAtom) :
    let nextBox := { box with rc := box.rc + 1 }
    let sourceStore' := (sourceStore.setBox location nextBox).rcTick
    let targetStore' := (machine.store.setBox location nextBox).rcTick
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dup sourceAtom) = .ok (sourceStore', .loc location) ∧
      Eval.Step context interpretation machine
        { machine with
          store := targetStore'
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc location) }
            stack } ∧
      StoreRel sourceStore' targetStore' ∧
      EnvRel (.loc location :: source)
        (frame.values.push (.loc location))
        (#[.reg frame.values.size] ++ mapping) := by
  dsimp only
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have retained :
      Eval.retainShared machine.store (.loc location) =
        .ok ((machine.store.setBox location
          { box with rc := box.rc + 1 }).rcTick) := by
    unfold Eval.retainShared
    simp only
    rw [targetGet]
    simp only
    rw [shared]
    rfl
  have targetStep := Eval.Step.retainShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved retained
  refine ⟨?_, targetStep,
    (stores.setBox location { box with rc := box.rc + 1 }).rcTick,
    environments.bindValue (.loc location)⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceGet]
  simp only
  rw [shared]

/-- A scalar IxIR₁ shared drop and its effect-only IxIR₂ release leave the
exact store and runtime environments unchanged.  The target accounts for the
single scalar work-list visit in its independent heap budget. -/
theorem simulate_drop_release_scalar {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .releaseShared targetAtom) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.drop sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (.erased :: source) frame.values
        (#[.erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have released :
      Eval.releaseShared machine.heapFuel machine.store value =
        .ok (machine.store, targetHeapFuel) := by
    rw [heapFuel]
    exact releaseShared_of_scalar targetHeapFuel scalar
  have targetStep := Eval.Step.releaseShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved released
  refine ⟨?_, targetStep, stores, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  cases value with
  | loc location => simp [Eval.RVal.isScalar] at scalar
  | lit literal => rfl
  | erased => rfl

/-- A scalar IxIR₁ unique drop and its effect-only IxIR₂ counterpart preserve
the exact store while spending one target heap-traversal unit. -/
theorem simulate_dropU_dropUnique_scalar {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved : IxIR1.resolveAtom source sourceAtom = .ok value)
    (scalar : Eval.RVal.isScalar value = true)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] = .dropUnique targetAtom) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.dropU sourceAtom) = .ok (sourceStore, .erased) ∧
      Eval.Step context interpretation machine
        { store := machine.store
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (.erased :: source) frame.values
        (#[.erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok value :=
    resolveAtom_of_envRel environments translated sourceResolved
  have dropped :
      Eval.dropUnique machine.heapFuel machine.store value =
        .ok (machine.store, targetHeapFuel) := by
    rw [heapFuel]
    exact dropUnique_of_scalar targetHeapFuel scalar
  have targetStep := Eval.Step.dropUnique (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved dropped
  refine ⟨?_, targetStep, stores, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  cases value with
  | loc location => simp [Eval.RVal.isScalar] at scalar
  | lit literal => rfl
  | erased => rfl

/-- Releasing a shared node with more than one owner decrements the same
refcount and charges the same RC operation in both exact stores.  This is the
non-recursive heap-bearing branch of deep shared release. -/
theorem simulate_drop_release_shared_nonunit {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef}
    {sourceDropFuel targetHeapFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {location : Nat} {box : IxIR1.NodeBox}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (shared : box.world = .shared)
    (nonzero : box.rc ≠ 0)
    (nonunit : box.rc ≠ 1)
    (heapFuel : machine.heapFuel = targetHeapFuel + 1)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .releaseShared targetAtom) :
    let nextBox := { box with rc := box.rc - 1 }
    let sourceStore' := sourceStore.rcTick.setBox location nextBox
    let targetStore' := machine.store.rcTick.setBox location nextBox
    IxIR1.runOp sourceContext ((sourceDropFuel + 1) + 1) sourceCurrent
          sourceStore source (.drop sourceAtom) =
        .ok (sourceStore', .erased) ∧
      Eval.Step context interpretation machine
        { store := targetStore'
          heapFuel := targetHeapFuel
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel sourceStore' targetStore' ∧
      EnvRel (.erased :: source) frame.values
        (#[.erased] ++ mapping) := by
  dsimp only
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have released :
      Eval.releaseShared machine.heapFuel machine.store (.loc location) =
        .ok (machine.store.rcTick.setBox location
          { box with rc := box.rc - 1 }, targetHeapFuel) := by
    rw [heapFuel]
    simp [Eval.releaseShared, Eval.releaseSharedWork, targetGet, shared,
      nonzero, nonunit]
  have targetStep := Eval.Step.releaseShared (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved released
  refine ⟨?_, targetStep, (stores.rcTick).setBox location
    { box with rc := box.rc - 1 }, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [IxIR1.dropVal.eq_def]
  simp only
  rw [sourceGet]
  simp [shared, nonunit]

/-- A checked scalar-leaf IxIR₁ free and IxIR₂ `freeUnique` kill the same
unique constructor location and bind the source's erased effect result. -/
theorem simulate_free_freeUnique {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {cid : IxIR1.CtorId} {location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (unique : box.world = .unique)
    (node : box.node = .ctorN cid fields)
    (scalarFields : fields.all Eval.RVal.isScalar = true)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .freeUnique targetAtom cid) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.free sourceAtom) =
        .ok (sourceStore.kill location, .erased) ∧
      Eval.Step context interpretation machine
        { machine with
          store := machine.store.kill location
          control := .running { frame with pc := frame.pc + 1 } stack } ∧
      StoreRel (sourceStore.kill location)
        (machine.store.kill location) ∧
      EnvRel (.erased :: source) frame.values
        (#[.erased] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetStep := Eval.Step.freeUnique (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved targetGet unique node scalarFields
  refine ⟨?_, targetStep, stores.kill location, environments.bindErased⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceGet]
  simp only
  rw [unique]

/-- A checked IxIR₂ fetch refines the corresponding non-consuming IxIR₁
projection when the owner's exact constructor sidecar identifies the runtime
node.  Both machines keep the store unchanged and bind the same field value. -/
theorem simulate_fetch {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {interpretation : Eval.Interpretation}
    {machine : Eval.Machine} {frame : Eval.Frame}
    {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {sourceAtom : IxIR1.Atom} {targetAtom : Atom}
    {cid : IxIR1.CtorId} {field location : Nat}
    {box : IxIR1.NodeBox} {fields : Array RVal} {value : RVal}
    (translated : translateAtom mapping sourceAtom = some targetAtom)
    (sourceResolved :
      IxIR1.resolveAtom source sourceAtom = .ok (.loc location))
    (sourceGet : sourceStore.get? location = some box)
    (node : box.node = .ctorN cid fields)
    (fieldAt : fields[field]? = some value)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .fetch targetAtom cid field) :
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.fetch sourceAtom field) = .ok (sourceStore, value) ∧
      Eval.Step context interpretation machine
        { machine with
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push value }
            stack } ∧
      StoreRel sourceStore machine.store ∧
      EnvRel (value :: source) (frame.values.push value)
        (#[.reg frame.values.size] ++ mapping) := by
  have targetResolved :
      Eval.resolveAtom frame.values targetAtom = .ok (.loc location) :=
    resolveAtom_of_envRel environments translated sourceResolved
  have targetGet : machine.store.get? location = some box := by
    unfold Eval.Store.get?
    rw [stores.heap]
    exact sourceGet
  have targetStep := Eval.Step.fetch (context := context)
    (interpretation := interpretation) control blockAt pc instruction
    targetResolved targetGet node fieldAt
  refine ⟨?_, targetStep, stores, environments.bindValue value⟩
  unfold IxIR1.runOp
  simp only
  rw [sourceResolved]
  simp only [bind, Except.bind]
  rw [sourceGet]
  simp only
  rw [node]
  simp only
  rw [fieldAt]

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

/-- Ordinary allocation is the first heap-changing instruction case.  The
source and logical target allocate the same constructor at the same fresh
location, preserve the exact baseline store relation, and bind related result
slots. -/
theorem simulate_alloc {sourceContext : IxIR1.Ctx}
    {sourceCurrent : IxIR1.FnDef} {sourceFuel : Nat}
    {context : Eval.Context} {machine : Eval.Machine}
    {frame : Eval.Frame} {stack : List Eval.Continuation} {block : Block}
    {sourceStore : IxIR1.Store} {source : List RVal}
    {mapping : Array Atom}
    (stores : StoreRel sourceStore machine.store)
    (environments : EnvRel source frame.values mapping)
    {world : Compilatrix.Ixon.Owned} {cid : IxIR1.CtorId}
    {sourceArguments : Array IxIR1.Atom}
    {targetArguments : Array Atom} {schema : CtorSchema}
    {values : List RVal}
    (arguments : AtomsRel mapping sourceArguments targetArguments)
    (sourceResolved :
      IxIR1.resolveAtoms source sourceArguments = .ok values)
    (fields : Eval.FieldWorlds machine.store schema values.toArray)
    (control : machine.control = .running frame stack)
    (blockAt : frame.definition.blocks[frame.block]? = some block)
    (pc : frame.pc < block.instructions.size)
    (instruction : block.instructions[frame.pc] =
      .alloc world cid targetArguments)
    (schemaAt : context.schemas world cid = some schema) :
    let node := IxIR1.Node.ctorN cid values.toArray
    let sourceAllocation := sourceStore.allocNode world node
    let targetAllocation := machine.store.allocNode world node
    IxIR1.runOp sourceContext (sourceFuel + 1) sourceCurrent sourceStore
          source (.alloc world cid sourceArguments) =
        .ok (sourceAllocation.1, .loc sourceAllocation.2) ∧
      Eval.Step context .logical machine
        { machine with
          store := targetAllocation.1
          control := .running
            { frame with
              pc := frame.pc + 1
              values := frame.values.push (.loc sourceAllocation.2) }
            stack } ∧
      StoreRel sourceAllocation.1 targetAllocation.1 ∧
      EnvRel (.loc sourceAllocation.2 :: source)
        (frame.values.push (.loc sourceAllocation.2))
        (#[.reg frame.values.size] ++ mapping) := by
  dsimp only
  have targetResolved :
      Eval.resolveAtoms frame.values targetArguments = .ok values.toArray :=
    resolveAtoms_of_envRel environments arguments sourceResolved
  have locationEq :
      (machine.store.allocNode world (.ctorN cid values.toArray)).2 =
        (sourceStore.allocNode world (.ctorN cid values.toArray)).2 :=
    stores.alloc_location world (.ctorN cid values.toArray)
  have targetStep := Eval.Step.alloc (interpretation := .logical)
    control blockAt pc instruction schemaAt targetResolved fields
  dsimp only at targetStep
  rw [locationEq] at targetStep
  refine ⟨?_, targetStep,
    stores.alloc world (.ctorN cid values.toArray), ?_⟩
  · unfold IxIR1.runOp
    simp only
    rw [sourceResolved]
    rfl
  · exact environments.bindValue
      (.loc (sourceStore.allocNode world (.ctorN cid values.toArray)).2)

/-- Baseline logical execution preserves the exact IxIR₁ heap and value.
Later credit insertion weakens this to heap isomorphism; keeping the stronger
baseline relation makes that proof boundary explicit. -/
structure OutcomeRel (source : IxIR1.Store × RVal)
    (target : Eval.Result) extends StoreRel source.1 target.store where
  value : target.value = source.2

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
