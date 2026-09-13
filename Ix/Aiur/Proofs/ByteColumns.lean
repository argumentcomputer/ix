/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.MemoryColumns

/-!
The native fixed-height guard requires active byte tables at degrees 8 and 16.
Physical byte columns and fixed preprocessed columns supply exactly the
logical byte providers, up to enumeration order. A system trace combines
canonical function, memory and byte assignments and their lookup budget.
Its balanced, satisfying columns imply execution of the selected success
call and functional memory. Native expression/codec/verifier refinement,
compiler refinement and the certified semantic/cryptographic endpoint remain
separate obligations.
-/

namespace Aiur

def fixedTraceHeights : List Nat → List Bool → List Nat → Bool
  | [], [], [] => true
  | height :: heights, false :: active, degrees => height == 0 && fixedTraceHeights heights active degrees
  | height :: heights, true :: active, degree :: degrees =>
    (height == 0 || (degree < 64 && height == 2^degree)) && fixedTraceHeights heights active degrees
  | _, _, _ => false

inductive FixedTraceHeights : List Nat → List Bool → List Nat → Prop where
  | nil : FixedTraceHeights [] [] []
  | inactive {heights : List Nat} {active : List Bool} {degrees : List Nat}
      (rest : FixedTraceHeights heights active degrees) :
      FixedTraceHeights (0 :: heights) (false :: active) degrees
  | active (height degree : Nat) {heights : List Nat} {active : List Bool} {degrees : List Nat}
      (matched : height = 0 ∨ degree < 64 ∧ height = 2^degree)
      (rest : FixedTraceHeights heights active degrees) :
      FixedTraceHeights (height :: heights) (true :: active) (degree :: degrees)

theorem fixedTraceHeights_sound {heights : List Nat} {active : List Bool} {degrees : List Nat}
    (accepted : fixedTraceHeights heights active degrees = true) : FixedTraceHeights heights active degrees := by
  induction heights generalizing active degrees with
  | nil =>
    cases active <;> cases degrees <;> simp only [fixedTraceHeights, Bool.false_eq_true] at accepted
    exact .nil
  | cons height heights ih =>
    cases active with
    | nil => simp only [fixedTraceHeights, Bool.false_eq_true] at accepted
    | cons enabled active =>
      cases enabled with
      | false =>
        simp only [fixedTraceHeights, Bool.and_eq_true, beq_iff_eq] at accepted
        obtain ⟨rfl, accepted⟩ := accepted
        exact .inactive (ih accepted)
      | true =>
        cases degrees with
        | nil => simp only [fixedTraceHeights, Bool.false_eq_true] at accepted
        | cons degree degrees =>
          simp only [fixedTraceHeights, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
            decide_eq_true_eq] at accepted
          exact .active height degree accepted.1 (ih accepted.2)

theorem fixedTraceHeights_complete {heights : List Nat} {active : List Bool} {degrees : List Nat}
    (valid : FixedTraceHeights heights active degrees) : fixedTraceHeights heights active degrees = true := by
  induction valid with
  | nil => rfl
  | inactive rest ih => exact ih
  | active height degree matched rest ih =>
    simp only [fixedTraceHeights, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq]
    exact ⟨matched, ih⟩

theorem FixedTraceHeights.alignment {heights : List Nat} {active : List Bool} {degrees : List Nat}
    (valid : FixedTraceHeights heights active degrees) :
    heights.length = active.length ∧ degrees.length = (active.filter id).length := by
  induction valid with
  | nil => exact ⟨rfl, rfl⟩
  | inactive rest ih => simpa only [List.length_cons, List.filter_cons, id_eq,
      Bool.false_eq_true, ↓reduceIte, Nat.add_right_cancel_iff] using ih
  | active height degree matched rest ih => simpa only [List.length_cons, List.filter_cons, id_eq,
      ↓reduceIte, Nat.add_right_cancel_iff] using ih

end Aiur

namespace Aiur.AIR

abbrev Byte1Columns := Fin 3 → G
abbrev Byte2Columns := Fin 10 → G

def Byte1Kind.column : Byte1Kind → Fin 3
  | .bits => 0
  | .shiftLeft => 1
  | .shiftRight => 2

def Byte2Kind.column : Byte2Kind → Fin 10
  | .xor => 0
  | .add => 1
  | .sub => 2
  | .and => 3
  | .or => 4
  | .lessThan => 5
  | .range => 6
  | .mul => 7
  | .split7 => 8
  | .split4 => 9

def byte1PreprocessedColumns (row : Fin 256) : Fin 11 → G :=
  fun column => (byte1Preprocessed row)[column.val]?.getD 0

def byte2PreprocessedColumns (row : Fin 65536) : Fin 14 → G :=
  fun column => (byte2Preprocessed row)[column.val]?.getD 0

def byte1ColumnLookup (kind : Byte1Kind) (preprocessed : Fin 11 → G) (columns : Byte1Columns) :
    G × List G :=
  (0 - columns kind.column, match kind with
    | .bits => [2, preprocessed 0] ++ List.ofFn (fun bit : Fin 8 => preprocessed ⟨1 + bit.val, by omega⟩)
    | .shiftLeft => [3, preprocessed 0, preprocessed 9]
    | .shiftRight => [4, preprocessed 0, preprocessed 10])

def byte2ColumnLookup (kind : Byte2Kind) (preprocessed : Fin 14 → G) (columns : Byte2Columns) :
    G × List G :=
  (0 - columns kind.column, [kind.channel, preprocessed 0, preprocessed 1] ++ match kind with
    | .xor => [preprocessed 2]
    | .add => [preprocessed 3]
    | .sub => [preprocessed 4]
    | .and => [preprocessed 5]
    | .or => [preprocessed 6]
    | .lessThan => [preprocessed 7]
    | .range => []
    | .mul => [preprocessed 8, preprocessed 9]
    | .split7 => [preprocessed 10, preprocessed 11]
    | .split4 => [preprocessed 12, preprocessed 13])

def byte1ColumnProvider (kind : Byte1Kind) (row : Fin 256) (columns : Byte1Columns) :
    Provider (List G) := ((byte1ColumnLookup kind (byte1PreprocessedColumns row) columns).2, columns kind.column)

def byte2ColumnProvider (kind : Byte2Kind) (row : Fin 65536) (columns : Byte2Columns) :
    Provider (List G) := ((byte2ColumnLookup kind (byte2PreprocessedColumns row) columns).2, columns kind.column)

theorem byte1ColumnProvider_reflect (kind : Byte1Kind) (row : Fin 256) (columns : Byte1Columns) :
    byte1ColumnProvider kind row columns =
      (byte1Request kind (G.ofNat row.val) (byte1Outputs kind row), columns kind.column) := by
  cases kind <;>
    simp [byte1ColumnProvider, byte1ColumnLookup, byte1PreprocessedColumns, byte1Preprocessed,
      byte1Request, byte1Outputs, Byte1Kind.channel, Byte1Kind.column, List.ofFn_succ]
  all_goals simp [Array.getElem_push,
    show (9 : Fin 11).val = 9 from rfl, show (10 : Fin 11).val = 10 from rfl]

theorem byte2ColumnProvider_reflect (kind : Byte2Kind) (row : Fin 65536) (columns : Byte2Columns) :
    byte2ColumnProvider kind row columns =
      (byte2Request kind (byteRangeMessage row).1 (byteRangeMessage row).2 (byte2Outputs kind row),
        columns kind.column) := by
  cases kind <;>
    simp [byte2ColumnProvider, byte2ColumnLookup, byte2PreprocessedColumns, byte2Preprocessed,
      byte2Request, byte2Outputs, Byte2Kind.channel, Byte2Kind.column]
  all_goals repeat constructor
  all_goals rfl

end Aiur.AIR

namespace Aiur

theorem fixedTraceHeights_bytes {active : List Bool} {degrees : List Nat}
    (accepted : fixedTraceHeights [256, 65536] active degrees = true) :
    active = [true, true] ∧ degrees = [8, 16] := by
  have valid := fixedTraceHeights_sound accepted
  cases valid with
  | active _ degree first rest =>
    have firstPower : 2^degree = 2^8 := by
      rcases first with impossible | ⟨_, power⟩
      · contradiction
      · exact power.symm
    have firstDegree := (Nat.pow_right_inj (by decide : 1 < 2)).mp firstPower
    cases rest with
    | active _ next second rest =>
      have secondPower : 2^next = 2^16 := by
        rcases second with impossible | ⟨_, power⟩
        · contradiction
        · exact power.symm
      have secondDegree := (Nat.pow_right_inj (by decide : 1 < 2)).mp secondPower
      cases rest
      exact ⟨rfl, by rw [firstDegree, secondDegree]⟩

end Aiur

namespace Aiur.AIR

theorem CircuitTraces.fixed_heights_append {circuits : List Bytecode.Circuit} (traces : CircuitTraces circuits)
    (heights : List Nat) (active : List Bool) (degrees : List Nat) :
    fixedTraceHeights (List.replicate circuits.length 0 ++ heights)
      (traces.bitmap ++ active) (traces.degrees ++ degrees) = fixedTraceHeights heights active degrees := by
  induction traces with
  | nil => rfl
  | inactive circuit rest ih =>
    simpa only [List.length_cons, List.replicate_succ, List.cons_append, bitmap, CircuitTraces.degrees,
      fixedTraceHeights, beq_self_eq_true, Bool.true_and] using ih
  | active circuit degree values rest ih =>
    simpa only [List.length_cons, List.replicate_succ, List.cons_append, bitmap, CircuitTraces.degrees,
      fixedTraceHeights, beq_self_eq_true, Bool.true_or, Bool.true_and] using ih

theorem MemoryTraces.fixed_heights_append {widths : List Nat} (traces : MemoryTraces widths)
    (heights : List Nat) (active : List Bool) (degrees : List Nat) :
    fixedTraceHeights (List.replicate widths.length 0 ++ heights)
      (traces.bitmap ++ active) (traces.degrees ++ degrees) = fixedTraceHeights heights active degrees := by
  induction traces with
  | nil => rfl
  | inactive width rest ih =>
    simpa only [List.length_cons, List.replicate_succ, List.cons_append, bitmap, MemoryTraces.degrees,
      fixedTraceHeights, beq_self_eq_true, Bool.true_and] using ih
  | active width degree matrix rest ih =>
    simpa only [List.length_cons, List.replicate_succ, List.cons_append, bitmap, MemoryTraces.degrees,
      fixedTraceHeights, beq_self_eq_true, Bool.true_or, Bool.true_and] using ih

theorem canonical_byte_metadata {circuits : List Bytecode.Circuit} (functions : CircuitTraces circuits)
    {widths : List Nat} (memories : MemoryTraces widths)
    {active : List Bool} {degrees : List Nat}
    (accepted : fixedTraceHeights
      (List.replicate circuits.length 0 ++ (List.replicate widths.length 0 ++ [256, 65536]))
      (functions.bitmap ++ (memories.bitmap ++ active))
      (functions.degrees ++ (memories.degrees ++ degrees)) = true) :
    active = [true, true] ∧ degrees = [8, 16] := by
  rw [functions.fixed_heights_append, memories.fixed_heights_append] at accepted
  exact fixedTraceHeights_bytes accepted

end Aiur.AIR

namespace Aiur.AIR

theorem suppliedWeight_perm {α : Type} [DecidableEq α] {left right : List (Provider α)}
    (permutation : left.Perm right) (message : α) : suppliedWeight message left = suppliedWeight message right := by
  induction permutation with
  | nil => rfl
  | cons provider permutation ih =>
    change (if provider.1 = message then provider.2 + suppliedWeight message _ else suppliedWeight message _) =
      (if provider.1 = message then provider.2 + suppliedWeight message _ else suppliedWeight message _)
    rw [ih]
  | swap a b rest =>
    by_cases left : a.1 = message <;> by_cases right : b.1 = message <;>
      simp only [suppliedWeight, List.foldr_cons, left, right, ↓reduceIte]
    rw [← G.add_assoc, G.add_comm b.2 a.2, G.add_assoc]
  | trans first last ih ih' => exact ih.trans ih'

theorem PaddedLookupBalance.perm_providers {width : Nat} {queries : List (List G)}
    {left right : List (Provider (List G))} (balanced : PaddedLookupBalance width queries left)
    (permutation : left.Perm right) : PaddedLookupBalance width queries right := by
  intro message
  exact (balanced message).trans (suppliedWeight_perm (permutation.map _) message)

private theorem flatMap_append_perm {α β : Type} (items : List α) (left right : α → List β) :
    (items.flatMap fun item => left item ++ right item).Perm (items.flatMap left ++ items.flatMap right) := by
  induction items with
  | nil => exact .nil
  | cons item items ih =>
    simp only [List.flatMap_cons]
    have first := (List.Perm.refl (left item ++ right item)).append ih
    apply first.trans
    simpa only [List.append_assoc] using
      ((show (right item ++ items.flatMap left).Perm (items.flatMap left ++ right item) from
        List.perm_append_comm).append_right
        (items.flatMap right)).append_left (left item)

theorem flatMap_map_swap {α β γ : Type} (left : List α) (right : List β) (value : α → β → γ) :
    (left.flatMap fun a => right.map (value a)).Perm (right.flatMap fun b => left.map (fun a => value a b)) := by
  induction right with
  | nil => simp
  | cons b right ih =>
    simp only [List.map_cons, List.flatMap_cons]
    have split := flatMap_append_perm left (fun a => [value a b]) (fun a => right.map (value a))
    simp only [← List.map_eq_flatMap] at split
    exact split.trans ((List.Perm.refl _).append ih)

def byte1MatrixProviders (matrix : Fin 256 → Byte1Columns) : List (Provider (List G)) :=
  (List.finRange 256).flatMap fun row => Byte1Kind.all.map fun kind => byte1ColumnProvider kind row (matrix row)

def byte2MatrixProviders (matrix : Fin 65536 → Byte2Columns) : List (Provider (List G)) :=
  (List.finRange 65536).flatMap fun row => Byte2Kind.all.map fun kind => byte2ColumnProvider kind row (matrix row)

theorem byte1MatrixProviders_reflect (matrix : Fin 256 → Byte1Columns) :
    (byte1MatrixProviders matrix).Perm (byte1Providers fun kind row => matrix row kind.column) := by
  have swapped := flatMap_map_swap (List.finRange 256) Byte1Kind.all
    (fun row kind => byte1ColumnProvider kind row (matrix row))
  simpa only [byte1MatrixProviders, byte1ColumnProvider_reflect, byte1Providers,
    List.finRange, List.map_ofFn, Function.comp_def] using swapped

theorem byte2MatrixProviders_reflect (matrix : Fin 65536 → Byte2Columns) :
    (byte2MatrixProviders matrix).Perm (byte2Providers fun kind row => matrix row kind.column) := by
  have swapped := flatMap_map_swap (List.finRange 65536) Byte2Kind.all
    (fun row kind => byte2ColumnProvider kind row (matrix row))
  simpa only [byte2MatrixProviders, byte2ColumnProvider_reflect, byte2Providers,
    List.finRange, List.map_ofFn, Function.comp_def] using swapped

structure ByteTraces where
  unary : Fin 256 → Byte1Columns
  binary : Fin 65536 → Byte2Columns

def ByteTraces.providers (traces : ByteTraces) : List (Provider (List G)) :=
  byte1MatrixProviders traces.unary ++ byte2MatrixProviders traces.binary

def ByteTraces.byte1Weights (traces : ByteTraces) : Byte1Kind → Fin 256 → G :=
  fun kind row => traces.unary row kind.column

def ByteTraces.byte2Weights (traces : ByteTraces) : Byte2Kind → Fin 65536 → G :=
  fun kind row => traces.binary row kind.column

theorem ByteTraces.providers_reflect (traces : ByteTraces) :
    traces.providers.Perm (byte1Providers traces.byte1Weights ++ byte2Providers traces.byte2Weights) :=
  (byte1MatrixProviders_reflect traces.unary).append (byte2MatrixProviders_reflect traces.binary)

structure SystemTraces (program : Bytecode.Toplevel) where
  functions : CircuitTraces program.circuits.toList
  memories : MemoryTraces program.memorySizes.toList
  bytes : ByteTraces

def SystemTraces.bitmap {program : Bytecode.Toplevel} (traces : SystemTraces program) : List Bool :=
  traces.functions.bitmap ++ (traces.memories.bitmap ++ [true, true])

def SystemTraces.degrees {program : Bytecode.Toplevel} (traces : SystemTraces program) : List Nat :=
  traces.functions.degrees ++ (traces.memories.degrees ++ [8, 16])

def systemFixedHeights (program : Bytecode.Toplevel) : List Nat :=
  List.replicate program.circuits.size 0 ++ (List.replicate program.memorySizes.size 0 ++ [256, 65536])

def systemLookupSlots (program : Bytecode.Toplevel) : List Nat :=
  program.circuits.toList.map (·.layout.lookups) ++ (List.replicate program.memorySizes.size 1 ++ [3, 10])

def SystemTraces.queryBound {program : Bytecode.Toplevel} (traces : SystemTraces program) : Option Nat :=
  lookupQueryBound (systemLookupSlots program) traces.bitmap traces.degrees

def SystemTraces.providers {program : Bytecode.Toplevel} (traces : SystemTraces program)
    (circuits : List CircuitEmission) : List (Provider (List G)) :=
  circuitProviders circuits ++ (traces.memories.providers ++ traces.bytes.providers)

theorem SystemTraces.fixed_heights {program : Bytecode.Toplevel} (traces : SystemTraces program) :
    fixedTraceHeights (systemFixedHeights program) traces.bitmap traces.degrees = true := by
  unfold systemFixedHeights bitmap degrees
  rw [← Array.length_toList, traces.functions.fixed_heights_append]
  rw [← Array.length_toList, traces.memories.fixed_heights_append]
  rfl

theorem SystemTraces.memory_functional {program : Bytecode.Toplevel} (traces : SystemTraces program)
    {result : Nat} (budget : traces.queryBound = some result) (satisfied : traces.memories.Satisfied)
    {width : Nat} {pointer : G} {left right : Array G}
    (loadedLeft : memoryFacts traces.memories.rows width pointer left)
    (loadedRight : memoryFacts traces.memories.rows width pointer right) : left = right :=
  traces.memories.functional_of_budget traces.functions budget satisfied loadedLeft loadedRight

end Aiur.AIR

namespace Aiur.BoundVerifier
open AIR Bytecode.AIR

theorem Backend.column_trace_execution {selection : Selection} (backend : Backend selection)
    (traces : SystemTraces backend.compiled.bytecode) {witnesses : List CircuitWitness}
    (emitted : traces.functions.emitWitnesses backend.compiled.bytecode = some witnesses)
    {result : Nat} (budget : traces.queryBound = some result)
    (width : Nat) (input : Array G) (arity : input.size = selection.inputSize)
    (balanced : PaddedLookupBalance width
      ((buildClaim selection.function input selection.success).toList ::
        encodedCircuitQueryPool (witnesses.map (·.emission)))
      (traces.providers (witnesses.map (·.emission))))
    (publicWidth : (buildClaim selection.function input selection.success).size + 1 ≤ width)
    (queryWidths : ∀ query ∈ encodedCircuitQueryPool (witnesses.map (·.emission)), query.length ≤ width)
    (satisfied : ∀ witness ∈ witnesses, witness.Satisfied) (memorySatisfied : traces.memories.Satisfied) :
    Execution backend.compiled.bytecode (memoryFacts traces.memories.rows)
      ⟨selection.function, input, selection.success, 0⟩ := by
  unfold SystemTraces.providers at balanced
  have replaced := balanced.perm_providers
    ((traces.bytes.providers_reflect.append_left traces.memories.providers).append_left
      (circuitProviders (witnesses.map CircuitWitness.emission)))
  rw [← List.append_assoc traces.memories.providers] at replaced
  exact backend.memory_trace_execution traces.functions traces.memories
    traces.bytes.byte1Weights traces.bytes.byte2Weights emitted budget width input arity
    replaced publicWidth queryWidths satisfied memorySatisfied

end Aiur.BoundVerifier
