/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LookupLayout

/-!
Decode the native memory column layout and its four valued equations.
Satisfied canonical traces supply valid memory rows and the same weighted
lookup providers; the checked global trace budget gives functional memory.
Compilation supplies distinct canonical memory widths. This removes separate
memory-validity and width hypotheses from backend trace execution. Extraction
from the native verifier, compiler refinement and certified semantic and
cryptographic soundness remain separate obligations.
-/

namespace Aiur.AIR

abbrev MemoryColumns (width : Nat) := Fin (3 + width) → G

def decodeMemoryRow (width : Nat) (columns : MemoryColumns width) : MemoryRow :=
  ⟨columns ⟨1, by omega⟩, columns ⟨0, by omega⟩, columns ⟨2, by omega⟩,
    Array.ofFn fun i : Fin width => columns ⟨3 + i.val, by omega⟩⟩

def memoryColumnEquations (width : Nat) (current next : MemoryColumns width) (transition : G) : List G :=
  let selector := current ⟨1, by omega⟩
  let nextSelector := next ⟨1, by omega⟩
  [selector * (selector - 1),
    current ⟨0, by omega⟩ * (1 - selector),
    (nextSelector * transition) * (selector - 1),
    (nextSelector * transition) * (current ⟨2, by omega⟩ + 1 - next ⟨2, by omega⟩)]

def memoryColumnLookup (width : Nat) (columns : MemoryColumns width) : G × List G :=
  (0 - columns ⟨0, by omega⟩,
    (memoryMessage width (columns ⟨2, by omega⟩) (decodeMemoryRow width columns).contents).map
      fun value => columns ⟨1, by omega⟩ * value)

def memoryColumnProvider (width : Nat) (columns : MemoryColumns width) : Provider (List G) :=
  ((memoryColumnLookup width columns).2, columns ⟨0, by omega⟩)

def memoryNextIndex {height : Nat} (index : Fin height) : Fin height :=
  if next : index.val + 1 < height then ⟨index.val + 1, next⟩ else ⟨0, by omega⟩

def memoryMatrixEquations (width height : Nat) (matrix : Fin height → MemoryColumns width)
    (index : Fin height) : List G :=
  memoryColumnEquations width (matrix index) (matrix (memoryNextIndex index))
    (if index.val + 1 < height then 1 else 0)

def MemoryMatrixSatisfied (width height : Nat) (matrix : Fin height → MemoryColumns width) : Prop :=
  ∀ index, ∀ equation ∈ memoryMatrixEquations width height matrix index, equation = 0

def decodeMemoryRows (width height : Nat) (matrix : Fin height → MemoryColumns width) : Array MemoryRow :=
  Array.ofFn fun index => decodeMemoryRow width (matrix index)

def memoryMatrixProviders (width height : Nat) (matrix : Fin height → MemoryColumns width) :
    List (Provider (List G)) :=
  List.ofFn fun index => memoryColumnProvider width (matrix index)

theorem decodeMemoryRow_width (width : Nat) (columns : MemoryColumns width) :
    (decodeMemoryRow width columns).contents.size = width := by
  simp only [decodeMemoryRow, Array.size_ofFn]

theorem decodeMemoryRows_size (width height : Nat) (matrix : Fin height → MemoryColumns width) :
    (decodeMemoryRows width height matrix).size = height := by
  simp only [decodeMemoryRows, Array.size_ofFn]

theorem memoryColumnProvider_reflect (width : Nat) (current next : MemoryColumns width) (transition : G)
    (satisfied : ∀ equation ∈ memoryColumnEquations width current next transition, equation = 0)
    (messageWidth : Nat) :
    Provider.PaddedEq messageWidth (memoryColumnProvider width current)
      (memoryMessage width (decodeMemoryRow width current).pointer
        (decodeMemoryRow width current).contents, (decodeMemoryRow width current).multiplicity) := by
  refine ⟨rfl, ?_⟩
  intro nonzero
  have activity : activityConstraint (current ⟨0, by omega⟩) (current ⟨1, by omega⟩) = 0 :=
    satisfied _ (by simp only [memoryColumnEquations, List.mem_cons]; exact Or.inr (Or.inl rfl))
  have active := nonzero_multiplicity_selector_one activity nonzero
  change padMessage messageWidth
    ((memoryMessage width (current ⟨2, by omega⟩) (decodeMemoryRow width current).contents).map
      fun value => current ⟨1, by omega⟩ * value) = _
  rw [active]
  simp only [G.mul_comm (1 : G), G.mul_one]
  rw [List.map_id']
  rfl

theorem decodeMemoryRows_polynomials (width height : Nat) (matrix : Fin height → MemoryColumns width)
    (satisfied : MemoryMatrixSatisfied width height matrix) :
    MemoryRowsPolynomials width (decodeMemoryRows width height matrix) := by
  constructor
  · intro i bound
    have rowBound : i < height := by simpa only [decodeMemoryRows_size] using bound
    have checked := satisfied ⟨i, rowBound⟩
    simp only [decodeMemoryRows, Array.getElem_ofFn, decodeMemoryRow, booleanConstraint]
    exact checked _ (by simp [memoryMatrixEquations, memoryColumnEquations])
  · intro i bound
    have rowBound : i < height := by simpa only [decodeMemoryRows_size] using bound
    have checked := satisfied ⟨i, rowBound⟩
    simp only [decodeMemoryRows, Array.getElem_ofFn, decodeMemoryRow, activityConstraint]
    exact checked _ (by simp [memoryMatrixEquations, memoryColumnEquations])
  · intro i bound
    simp only [decodeMemoryRows, Array.getElem_ofFn, decodeMemoryRow_width]
  · intro i bound
    have rowBound : i + 1 < height := by simpa only [decodeMemoryRows_size] using bound
    have checked := satisfied ⟨i, by omega⟩
    have equation := checked _ (show ((matrix (memoryNextIndex ⟨i, by omega⟩)) ⟨1, by omega⟩ *
      (if i + 1 < height then (1 : G) else 0)) * (matrix ⟨i, by omega⟩ ⟨1, by omega⟩ - 1) ∈
      memoryMatrixEquations width height matrix ⟨i, by omega⟩ from by
        simp [memoryMatrixEquations, memoryColumnEquations])
    simpa only [memoryNextIndex, rowBound, if_pos, dif_pos, G.mul_one,
      memoryActivityTransition, decodeMemoryRows, Array.getElem_ofFn, decodeMemoryRow] using equation
  · intro i bound
    have rowBound : i + 1 < height := by simpa only [decodeMemoryRows_size] using bound
    have checked := satisfied ⟨i, by omega⟩
    have equation := checked _ (show ((matrix (memoryNextIndex ⟨i, by omega⟩)) ⟨1, by omega⟩ *
      (if i + 1 < height then (1 : G) else 0)) *
        (matrix ⟨i, by omega⟩ ⟨2, by omega⟩ + 1 - matrix (memoryNextIndex ⟨i, by omega⟩) ⟨2, by omega⟩) ∈
      memoryMatrixEquations width height matrix ⟨i, by omega⟩ from by
        simp [memoryMatrixEquations, memoryColumnEquations])
    simpa only [memoryNextIndex, rowBound, if_pos, dif_pos, G.mul_one,
      memoryPointerTransition, decodeMemoryRows, Array.getElem_ofFn, decodeMemoryRow] using equation

theorem decodeMemoryRows_valid (width height : Nat) (matrix : Fin height → MemoryColumns width)
    (satisfied : MemoryMatrixSatisfied width height matrix) :
    MemoryRowsValid width (decodeMemoryRows width height matrix) :=
  (decodeMemoryRows_polynomials width height matrix satisfied).valid

private theorem memory_forall₂_ofFn {α β : Type} {relation : α → β → Prop}
    {height : Nat} (left : Fin height → α) (right : Fin height → β)
    (related : ∀ index, relation (left index) (right index)) :
    List.Forall₂ relation (List.ofFn left) (List.ofFn right) := by
  induction height with
  | zero => simp only [List.ofFn_zero]; exact .nil
  | succ height ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (related 0) (ih (fun i => left i.succ) (fun i => right i.succ) (fun i => related i.succ))

private theorem memoryProviders_toList (rows : Array MemoryRow) :
    memoryProviders rows = rows.toList.map (fun row => ((row.pointer, row.contents), row.multiplicity)) := by
  have list := congrArg (List.map fun row : MemoryRow => ((row.pointer, row.contents), row.multiplicity))
    (List.ofFn_getElem (xs := rows.toList))
  simpa only [memoryProviders, List.map_ofFn, Function.comp_def, Array.length_toList,
    Fin.getElem_fin, Array.getElem_toList] using list

theorem decodeMemoryRows_providers (width height : Nat) (matrix : Fin height → MemoryColumns width) :
    mapProviders (fun request => memoryMessage width request.1 request.2)
      (memoryProviders (decodeMemoryRows width height matrix)) =
      List.ofFn (fun index =>
        (memoryMessage width (decodeMemoryRow width (matrix index)).pointer
          (decodeMemoryRow width (matrix index)).contents, (decodeMemoryRow width (matrix index)).multiplicity)) := by
  rw [memoryProviders_toList]
  simp only [mapProviders, decodeMemoryRows, Array.toList_ofFn,
    List.map_ofFn, Function.comp_def]

theorem memoryMatrixProviders_reflect (width height : Nat) (matrix : Fin height → MemoryColumns width)
    (satisfied : MemoryMatrixSatisfied width height matrix) (messageWidth : Nat) :
    List.Forall₂ (Provider.PaddedEq messageWidth) (memoryMatrixProviders width height matrix)
      (mapProviders (fun request => memoryMessage width request.1 request.2)
        (memoryProviders (decodeMemoryRows width height matrix))) := by
  rw [decodeMemoryRows_providers]
  apply memory_forall₂_ofFn
  intro index
  exact memoryColumnProvider_reflect width (matrix index) (matrix (memoryNextIndex index))
    (if index.val + 1 < height then 1 else 0) (satisfied index) messageWidth

end Aiur.AIR

namespace Aiur

private theorem memorySizes_distinct (sizes : Concrete.Bytecode.MemSizes) : sizes.toArray.toList.Nodup := by
  change sizes.toArray.toList.Pairwise (fun a b => a ≠ b)
  simpa only [Std.TreeSet.toList_toArray, Std.compare_eq_iff_eq] using sizes.distinct_toList

theorem Concrete.Decls.toBytecode_memorySizes_distinct {decls : Concrete.Decls}
    {program : Bytecode.Toplevel} {names : Std.HashMap Global Bytecode.FunIdx}
    (compiled : decls.toBytecode = .ok (program, names)) : program.memorySizes.toList.Nodup := by
  unfold Concrete.Decls.toBytecode at compiled
  simp only [bind, Except.bind, pure, Except.pure] at compiled
  split at compiled
  · cases compiled
  · split at compiled
    · cases compiled
    · cases compiled
      exact memorySizes_distinct _

theorem Bytecode.Toplevel.deduplicate_memorySizes (program : Bytecode.Toplevel) :
    program.deduplicate.1.memorySizes = program.memorySizes := by
  unfold Bytecode.Toplevel.deduplicate Bytecode.checkedRenaming
  dsimp only
  split
  · unfold Bytecode.Toplevel.deduplicateCandidate
    dsimp only
    split <;> rfl
  · rfl

theorem finishCompilation_memorySizes (source : Source.Toplevel) (raw : Bytecode.Toplevel)
    (names : Std.HashMap Global Bytecode.FunIdx) :
    (finishCompilation source raw names).bytecode.memorySizes = raw.memorySizes := by
  have preserved (program : Bytecode.Toplevel) :
      program.withCallComponents.memorySizes = program.memorySizes := by
    unfold Bytecode.Toplevel.withCallComponents
    dsimp only
    split <;> rfl
  cases flag : source.componentRanks <;>
    simp [finishCompilation, flag, preserved, raw.deduplicate_memorySizes]

theorem Source.Toplevel.compile_memorySizes_distinct {source : Source.Toplevel} {compiled : CompiledToplevel}
    (accepted : source.compile = .ok compiled) : compiled.bytecode.memorySizes.toList.Nodup := by
  obtain ⟨inlined, typed, concrete, raw, names, _, _, _, lowered, artifact⟩ :=
    source.compile_artifact_of_ok accepted
  rw [artifact, finishCompilation_memorySizes]
  exact Concrete.Decls.toBytecode_memorySizes_distinct lowered

theorem BoundVerifier.Backend.memorySizes_distinct {selection : BoundVerifier.Selection}
    (backend : BoundVerifier.Backend selection) : backend.compiled.bytecode.memorySizes.toList.Nodup := by
  obtain ⟨initial, compiled, grouped⟩ := backend.compilation_stages
  have distinct := Source.Toplevel.compile_memorySizes_distinct compiled
  split at grouped
  · cases grouped; exact distinct
  · rw [(CompiledToplevel.groupFunctions_preserves_code grouped).2.2.2]
    exact distinct

theorem BoundVerifier.Backend.memorySizes_canonical {selection : BoundVerifier.Selection}
    (backend : BoundVerifier.Backend selection) :
    ∀ width ∈ backend.compiled.bytecode.memorySizes.toList, width < gSize.toNat := by
  have checked := backend.lookupShapes
  simp only [Bytecode.Toplevel.validateLookupShapes, Bool.and_eq_true] at checked
  intro width member
  have valid := Array.all_eq_true'.mp checked.2.1 width (Array.mem_toList_iff.mp member)
  exact of_decide_eq_true valid

end Aiur

namespace Aiur.AIR

inductive MemoryTraces : List Nat → Type where
  | nil : MemoryTraces []
  | inactive (width : Nat) {widths : List Nat} (rest : MemoryTraces widths) : MemoryTraces (width :: widths)
  | active (width degree : Nat) (matrix : Fin (2^degree) → MemoryColumns width)
      {widths : List Nat} (rest : MemoryTraces widths) : MemoryTraces (width :: widths)

def MemoryTraces.bitmap {widths : List Nat} : MemoryTraces widths → List Bool
  | .nil => []
  | .inactive _ rest => false :: rest.bitmap
  | .active _ _ _ rest => true :: rest.bitmap

def MemoryTraces.degrees {widths : List Nat} : MemoryTraces widths → List Nat
  | .nil => []
  | .inactive _ rest => rest.degrees
  | .active _ degree _ rest => degree :: rest.degrees

def MemoryTraces.capacity {widths : List Nat} : MemoryTraces widths → Nat
  | .nil => 0
  | .inactive _ rest => rest.capacity
  | .active _ degree _ rest => 2^degree + rest.capacity

def MemoryTraces.rows {widths : List Nat} : MemoryTraces widths → Nat → Array MemoryRow
  | .nil, _ => #[]
  | .inactive width rest, size => if size = width then #[] else rest.rows size
  | .active width degree matrix rest, size =>
    if size = width then decodeMemoryRows width (2^degree) matrix else rest.rows size

def MemoryTraces.providers {widths : List Nat} : MemoryTraces widths → List (Provider (List G))
  | .nil => []
  | .inactive _ rest => rest.providers
  | .active width degree matrix rest => memoryMatrixProviders width (2^degree) matrix ++ rest.providers

def MemoryTraces.Satisfied {widths : List Nat} : MemoryTraces widths → Prop
  | .nil => True
  | .inactive _ rest => rest.Satisfied
  | .active width degree matrix rest => MemoryMatrixSatisfied width (2^degree) matrix ∧ rest.Satisfied

theorem MemoryTraces.slot_sum_append {widths : List Nat} (traces : MemoryTraces widths)
    (otherSlots : List Nat) (otherActive : List Bool) (otherDegrees : List Nat) :
    lookupSlotSum (List.replicate widths.length 1 ++ otherSlots)
      (traces.bitmap ++ otherActive) (traces.degrees ++ otherDegrees) =
      (lookupSlotSum otherSlots otherActive otherDegrees).map (traces.capacity + ·) := by
  induction traces with
  | nil =>
    simp only [List.length_nil, List.replicate_zero, List.nil_append, bitmap, degrees, capacity, Nat.zero_add]
    cases lookupSlotSum otherSlots otherActive otherDegrees <;> rfl
  | inactive width rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.cons_append, bitmap, degrees, capacity, lookupSlotSum]
    exact ih
  | active width degree matrix rest ih =>
    simp only [List.length_cons, List.replicate_succ, List.cons_append, bitmap, degrees, capacity,
      lookupSlotSum, ih, bind, Option.bind, Nat.mul_one]
    cases lookupSlotSum otherSlots otherActive otherDegrees <;>
      simp only [Option.map_none, Option.map_some, pure, Nat.add_assoc]

private theorem memoryRows_empty_valid (width : Nat) : MemoryRowsValid width #[] := by
  constructor <;> intro i bound <;> simp at bound

theorem MemoryTraces.rows_valid {widths : List Nat} (traces : MemoryTraces widths)
    (satisfied : traces.Satisfied) (width : Nat) : MemoryRowsValid width (traces.rows width) := by
  induction traces with
  | nil => exact memoryRows_empty_valid _
  | inactive size rest ih =>
    simp only [MemoryTraces.rows]
    split
    · exact memoryRows_empty_valid _
    · exact ih satisfied
  | active size degree matrix rest ih =>
    simp only [MemoryTraces.rows]
    split
    · rename_i equal
      subst width
      exact decodeMemoryRows_valid _ _ _ satisfied.1
    · exact ih satisfied.2

theorem MemoryTraces.rows_size_le {widths : List Nat} (traces : MemoryTraces widths) (width : Nat) :
    (traces.rows width).size ≤ traces.capacity := by
  induction traces with
  | nil => exact Nat.le_refl _
  | inactive size rest ih =>
    simp only [MemoryTraces.rows, MemoryTraces.capacity]
    split
    · exact Nat.zero_le _
    · exact ih
  | active size degree matrix rest ih =>
    simp only [MemoryTraces.rows, MemoryTraces.capacity]
    split
    · rw [decodeMemoryRows_size]; omega
    · exact Nat.le_trans ih (Nat.le_add_left _ _)

def memoryTableProviders (widths : List Nat) (rows : Nat → Array MemoryRow) : List (Provider (List G)) :=
  widths.flatMap fun width => mapProviders (fun request => memoryMessage width request.1 request.2)
    (memoryProviders (rows width))

private theorem memoryTableProviders_cons (width : Nat) (widths : List Nat) (rows : Nat → Array MemoryRow) :
    memoryTableProviders (width :: widths) rows =
      mapProviders (fun request => memoryMessage width request.1 request.2) (memoryProviders (rows width)) ++
        memoryTableProviders widths rows := rfl

private theorem memoryTableProviders_congr (widths : List Nat) (left right : Nat → Array MemoryRow)
    (equal : ∀ width ∈ widths, left width = right width) :
    memoryTableProviders widths left = memoryTableProviders widths right := by
  induction widths with
  | nil => rfl
  | cons width widths ih =>
    rw [memoryTableProviders_cons, memoryTableProviders_cons, equal width List.mem_cons_self]
    rw [ih (fun size member => equal size (List.mem_cons_of_mem _ member))]

theorem MemoryTraces.providers_reflect {widths : List Nat} (traces : MemoryTraces widths)
    (distinct : widths.Nodup) (satisfied : traces.Satisfied) (messageWidth : Nat) :
    List.Forall₂ (Provider.PaddedEq messageWidth) traces.providers (memoryTableProviders widths traces.rows) := by
  induction traces with
  | nil => exact .nil
  | @inactive width widths rest ih =>
    have unique := List.nodup_cons.mp distinct
    have tail : memoryTableProviders widths (MemoryTraces.rows (.inactive width rest)) =
        memoryTableProviders widths rest.rows := by
      apply memoryTableProviders_congr
      intro size member
      have different : size ≠ width := fun equal => unique.1 (equal ▸ member)
      simp only [MemoryTraces.rows, if_neg different]
    rw [memoryTableProviders_cons, tail]
    have empty : MemoryTraces.rows (.inactive width rest) width = #[] := by simp [MemoryTraces.rows]
    rw [empty]
    simpa only [memoryProviders, Array.size_empty, List.ofFn_zero, mapProviders, List.map_nil,
      List.nil_append, MemoryTraces.providers] using ih unique.2 satisfied
  | @active width degree matrix widths rest ih =>
    have unique := List.nodup_cons.mp distinct
    have tail : memoryTableProviders widths (MemoryTraces.rows (.active width degree matrix rest)) =
        memoryTableProviders widths rest.rows := by
      apply memoryTableProviders_congr
      intro size member
      have different : size ≠ width := fun equal => unique.1 (equal ▸ member)
      simp only [MemoryTraces.rows, if_neg different]
    rw [memoryTableProviders_cons, tail]
    have first : MemoryTraces.rows (.active width degree matrix rest) width =
        decodeMemoryRows width (2^degree) matrix := by simp [MemoryTraces.rows]
    rw [first]
    exact forall₂_append (memoryMatrixProviders_reflect _ _ _ satisfied.1 messageWidth)
      (ih unique.2 satisfied.2)

theorem MemoryTraces.capacity_bounded {widths : List Nat} (traces : MemoryTraces widths)
    {circuits : List Bytecode.Circuit} (functions : CircuitTraces circuits)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (accepted : lookupQueryBound
      (circuits.map (·.layout.lookups) ++ (List.replicate widths.length 1 ++ otherSlots))
      (functions.bitmap ++ (traces.bitmap ++ otherActive))
      (functions.degrees ++ (traces.degrees ++ otherDegrees)) = some result) :
    traces.capacity + 1 < gSize.toNat := by
  obtain ⟨_, total, shape, count, bounded⟩ := lookupQueryBound_sound accepted
  rw [functions.slot_sum_append, traces.slot_sum_append] at shape
  cases other : lookupSlotSum otherSlots otherActive otherDegrees with
  | none => simp only [other, Option.map_none, reduceCtorEq] at shape
  | some extra =>
    simp only [other, Option.map_some, Option.some.injEq] at shape
    omega

theorem MemoryTraces.functional {widths : List Nat} (traces : MemoryTraces widths)
    (satisfied : traces.Satisfied) (bounded : traces.capacity < gSize.toNat)
    {width : Nat} {pointer : G} {left right : Array G}
    (loadedLeft : memoryFacts traces.rows width pointer left)
    (loadedRight : memoryFacts traces.rows width pointer right) : left = right :=
  memoryFacts_functional traces.rows (traces.rows_valid satisfied)
    (fun size => Nat.lt_of_le_of_lt (traces.rows_size_le size) bounded) loadedLeft loadedRight

theorem MemoryTraces.functional_of_budget {widths : List Nat} (traces : MemoryTraces widths)
    {circuits : List Bytecode.Circuit} (functions : CircuitTraces circuits)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (accepted : lookupQueryBound
      (circuits.map (·.layout.lookups) ++ (List.replicate widths.length 1 ++ otherSlots))
      (functions.bitmap ++ (traces.bitmap ++ otherActive))
      (functions.degrees ++ (traces.degrees ++ otherDegrees)) = some result)
    (satisfied : traces.Satisfied) {width : Nat} {pointer : G} {left right : Array G}
    (loadedLeft : memoryFacts traces.rows width pointer left)
    (loadedRight : memoryFacts traces.rows width pointer right) : left = right := by
  have bounded := traces.capacity_bounded functions accepted
  exact traces.functional satisfied (by omega) loadedLeft loadedRight

def MemoryTraces.auxiliary {widths : List Nat} (traces : MemoryTraces widths)
    (byte1 : Byte1Kind → Fin 256 → G) (byte2 : Byte2Kind → Fin 65536 → G) : AuxiliaryTables :=
  ⟨widths, traces.rows, byte1, byte2⟩

theorem MemoryTraces.circuitProviders_reflect {widths : List Nat} (traces : MemoryTraces widths)
    (distinct : widths.Nodup) (satisfied : traces.Satisfied) (messageWidth : Nat)
    (byte1 : Byte1Kind → Fin 256 → G) (byte2 : Byte2Kind → Fin 65536 → G)
    (circuits : List CircuitEmission) :
    List.Forall₂ (Provider.PaddedEq messageWidth)
      (circuitProviders circuits ++ (traces.providers ++ byte1Providers byte1 ++ byte2Providers byte2))
      ((traces.auxiliary byte1 byte2).circuitProviders circuits) :=
  forall₂_append (paddedProviders_refl _ _) (forall₂_append
    (forall₂_append (traces.providers_reflect distinct satisfied messageWidth) (paddedProviders_refl _ _))
    (paddedProviders_refl _ _))

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem Backend.memory_trace_execution {selection : Selection} (backend : Backend selection)
    (generic : selection.source.componentRanks = false)
    (functions : CircuitTraces backend.compiled.bytecode.circuits.toList)
    (memories : MemoryTraces backend.compiled.bytecode.memorySizes.toList)
    (byte1 : Byte1Kind → Fin 256 → G) (byte2 : Byte2Kind → Fin 65536 → G)
    {witnesses : List CircuitWitness}
    (emitted : functions.emitWitnesses backend.compiled.bytecode = some witnesses)
    {otherSlots : List Nat} {otherActive : List Bool} {otherDegrees : List Nat} {result : Nat}
    (budget : lookupQueryBound
      (backend.compiled.bytecode.circuits.toList.map (·.layout.lookups) ++
        (List.replicate backend.compiled.bytecode.memorySizes.size 1 ++ otherSlots))
      (functions.bitmap ++ (memories.bitmap ++ otherActive))
      (functions.degrees ++ (memories.degrees ++ otherDegrees)) = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList ::
        encodedCircuitQueryPool (witnesses.map (·.emission)))
      (circuitProviders (witnesses.map (·.emission)) ++
        (memories.providers ++ byte1Providers byte1 ++ byte2Providers byte2)))
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied) (memorySatisfied : memories.Satisfied) :
    Execution backend.compiled.bytecode (memoryFacts memories.rows)
      ⟨selection.function, input, selection.success, 0⟩ := by
  have decoded := balanced.congr_providers
    (memories.circuitProviders_reflect backend.memorySizes_distinct memorySatisfied width byte1 byte2 _)
  exact backend.bounded_trace_execution generic (memories.auxiliary byte1 byte2) functions emitted budget width input arity
    decoded publicWidth queryWidths (memories.rows_valid memorySatisfied) backend.memorySizes_canonical satisfied

end Aiur.BoundVerifier
