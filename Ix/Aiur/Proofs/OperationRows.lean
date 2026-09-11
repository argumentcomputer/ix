/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.GlobalLookups

/-!
Valued emission and local execution for every native bytecode operation.
The model retains expression degree, constant folding, fresh auxiliary-column
allocation, logical map extension, polynomial values and raw query parts.
Active satisfying emissions derive relational steps and operation sequences
using byte and memory facts from the global lookup pool.

This is a total Lean model. Identifying its reads and metadata with the Rust
expression emitter, proving index and layout validity, and extracting its
active query parts from shared slots remain explicit obligations.
-/

namespace Aiur.AIR
open Bytecode

/-- One evaluated logical value, retaining the native emitter's expression
degree and whether its frontend expression is syntactically constant. -/
structure RowValue where
  value : G
  degree : Nat
  constant : Bool
  deriving Repr, DecidableEq

def RowValue.variable (value : G) : RowValue := ⟨value, 1, false⟩
def RowValue.konst (value : G) : RowValue := ⟨value, 0, true⟩
def rowValues (values : Array RowValue) : Array G := values.map RowValue.value

def RowValue.add (left right : RowValue) : RowValue :=
  ⟨left.value + right.value, max left.degree right.degree, left.constant && right.constant⟩

def RowValue.sub (left right : RowValue) : RowValue :=
  ⟨left.value - right.value, max left.degree right.degree, left.constant && right.constant⟩

/-- Multiplication by a known zero also folds a nonconstant expression to
a constant; the native operation's degree bookkeeping remains independent. -/
def RowValue.mul (left right : RowValue) : RowValue :=
  ⟨left.value * right.value, left.degree + right.degree,
    (left.constant && right.constant) || (left.constant && left.value == 0) ||
      (right.constant && right.value == 0)⟩

def rowAdvice (row : Nat → G) (start count : Nat) : Array RowValue :=
  Array.ofFn fun index : Fin count => RowValue.variable (row (start + index.val))

def RowValue.pack (values : Array RowValue) : RowValue :=
  ⟨Bytecode.AIR.packWord (rowValues values),
    values.toList.foldl (fun degree value => max degree value.degree) 0,
    values.all (·.constant)⟩

def readRowWord (values : Array RowValue) (indices : Array ValIdx) : Option RowValue := do
  let word ← Bytecode.AIR.readWord (rowValues values) indices
  let bytes := indices.map fun index => values[index]?.getD (RowValue.konst 0)
  return { RowValue.pack bytes with value := word }

/-- One operation's evaluated outputs and newly emitted constraints. Lookup
messages are ungated contributions; slot assembly supplies their selector.
`used` is the exact number of fresh auxiliary columns consumed. -/
structure OpEmission where
  outputs : Array RowValue := #[]
  used : Nat := 0
  equations : List G := []
  queries : List (List G) := []
  calls : List (Bytecode.AIR.Call × (Fin 6 → G)) := []

def emitAdvice (row : Nat → G) (count : Nat) : OpEmission :=
  { outputs := rowAdvice row 0 count, used := count }

def emitByte1 (row : Nat → G) (kind : Byte1Kind) (index : ValIdx)
    (values : Array RowValue) : Option OpEmission := do
  let input ← values[index]?
  let outputs := rowAdvice row 0 kind.outputSize
  return {
    outputs, used := kind.outputSize
    queries := [byte1Request kind input.value (rowValues outputs)] }

def Byte2Kind.extendRowOutputs (kind : Byte2Kind) (left right : RowValue)
    (outputs : Array RowValue) : Array RowValue :=
  let low := ((rowValues outputs)[0]?).getD 0
  let degree := max (max left.degree right.degree) 1
  match kind with
  | .add => outputs.push ⟨(left.value + right.value - low) * inverse256, degree, false⟩
  | .sub => outputs.push ⟨(low + right.value - left.value) * inverse256, degree, false⟩
  | _ => outputs

def emitByte2 (row : Nat → G) (kind : Byte2Kind) (left right : ValIdx)
    (values : Array RowValue) : Option OpEmission := do
  let x ← values[left]?
  let y ← values[right]?
  let outputs := rowAdvice row 0 kind.outputSize
  return {
    outputs := kind.extendRowOutputs x y outputs, used := kind.outputSize
    queries := [byte2Request kind x.value y.value (rowValues outputs)] }

def range4Queries (bytes : Fin 4 → G) : List (List G) :=
  [rangeMessage (bytes 0, bytes 1), rangeMessage (bytes 2, bytes 3)]

def emitU32LessThan (row : Nat → G) (selector : G) (left right : ValIdx)
    (values : Array RowValue) : Option OpEmission := do
  let a ← values[left]?
  let b ← values[right]?
  let x : Fin 4 → G := fun index => row index.val
  let y : Fin 4 → G := fun index => row (4 + index.val)
  let z : Fin 4 → G := fun index => row (8 + index.val)
  return {
    outputs := #[⟨1 - u32Carries x y z 4, 1, false⟩], used := 12
    equations := selector * (a.value - pack4 x) :: selector * (b.value - pack4 z) ::
      List.ofFn (fun index : Fin 4 => selector * booleanConstraint (u32Carries x y z index.succ)),
    queries := range4Queries x ++ range4Queries y ++ range4Queries z }

def emitU32Add (row : Nat → G) (left right : Array ValIdx)
    (third : Option (Array ValIdx)) (values : Array RowValue) : Option OpEmission := do
  let x ← readRowWord values left
  let y ← readRowWord values right
  let sum ← match third with
    | none => some (x.add y)
    | some indices => (readRowWord values indices).map fun z => (x.add y).add z
  let bytes := rowAdvice row 0 4
  let packed := RowValue.pack bytes
  return { outputs := bytes.push ⟨(sum.value - packed.value) * 0xfffffffe00000002,
      max sum.degree packed.degree, false⟩, used := 4 }

/-- Valued model of one native operation. Invalid reads, malformed word
widths and the native constant-`eq_zero` degree assertion return `none`.
Store operands are checked in the incoming logical scope; identifying that
scope with the Rust emitter's post-pointer reads requires index validity. -/
def emitOp (row : Nat → G) (selector rank : G) (op : Op)
    (values : Array RowValue) : Option OpEmission :=
  match op with
  | .const value => some { outputs := #[RowValue.konst value] }
  | .add a b => do return { outputs := #[(← values[a]?).add (← values[b]?)] }
  | .sub a b => do return { outputs := #[(← values[a]?).sub (← values[b]?)] }
  | .mul a b => do
    let x ← values[a]?
    let y ← values[b]?
    let product := x.mul y
    if product.degree < 2 then return { outputs := #[product] }
    else return {
      outputs := #[RowValue.variable (row 0)], used := 1
      equations := [selector * (row 0 - product.value)] }
  | .eqZero a => do
    let input ← values[a]?
    if input.constant then
      if input.degree = 0 then return { outputs := #[RowValue.konst (G.eqZero input.value)] }
      else none
    else return {
      outputs := #[RowValue.variable (row 1)], used := 2
      equations := [selector * input.value * row 1,
        selector * (input.value * row 0 + row 1 - 1)] }
  | .call function indices size unconstrained =>
    if unconstrained then some (emitAdvice row size)
    else do
      let inputs ← Bytecode.AIR.readValues (rowValues values) indices
      let outputs := rowAdvice row 0 size
      let request : Bytecode.AIR.Call := ⟨function, inputs, rowValues outputs, row size⟩
      let gap : Fin 6 → G := fun index => row (size + 1 + index.val)
      return {
        outputs, used := size + 7
        equations := [selector * callOrderConstraint rank request.rank (packRank gap)],
        queries := functionMessage request :: (rankByteQueries gap).map rangeMessage,
        calls := [(request, gap)] }
  | .store indices => do
    let contents ← Bytecode.AIR.readValues (rowValues values) indices
    return {
      outputs := #[RowValue.variable (row 0)], used := 1
      queries := [memoryMessage indices.size (row 0) contents] }
  | .load size index => do
    let pointer ← values[index]?
    let outputs := rowAdvice row 0 size
    return {
      outputs, used := size
      queries := [memoryMessage size pointer.value (rowValues outputs)] }
  | .assertEq xs ys _ => do
    if xs.size ≠ ys.size then none else do
      let left ← Bytecode.AIR.readValues (rowValues values) xs
      let right ← Bytecode.AIR.readValues (rowValues values) ys
      return { equations := List.ofFn fun i : Fin left.size =>
        selector * (left[i] - right[i.val]?.getD 0) }
  | .ioGetInfo .. => some (emitAdvice row 2)
  | .ioRead _ _ size => some (emitAdvice row size)
  | .ioSetInfo .. | .ioWrite .. | .debug .. => some {}
  | .u8BitDecomposition index => emitByte1 row .bits index values
  | .u8ShiftLeft index => emitByte1 row .shiftLeft index values
  | .u8ShiftRight index => emitByte1 row .shiftRight index values
  | .u8Xor a b => emitByte2 row .xor a b values
  | .u8Add a b => emitByte2 row .add a b values
  | .u8Sub a b => emitByte2 row .sub a b values
  | .u8And a b => emitByte2 row .and a b values
  | .u8Or a b => emitByte2 row .or a b values
  | .u8LessThan a b => emitByte2 row .lessThan a b values
  | .u8RangeCheck a b => emitByte2 row .range a b values
  | .u8Mul a b => emitByte2 row .mul a b values
  | .u8XorSplit7 a b => emitByte2 row .split7 a b values
  | .u8XorSplit4 a b => emitByte2 row .split4 a b values
  | .u32LessThan a b => emitU32LessThan row selector a b values
  | .unconstrainedBigUintDivMod .. => some (emitAdvice row 2)
  | .unconstrainedGToBytes .. => some (emitAdvice row 8)
  | .unconstrainedGInverse .. => some (emitAdvice row 1)
  | .unconstrainedU32Add a b => emitU32Add row a b none values
  | .unconstrainedU32Add3 a b c => emitU32Add row a b (some c) values
  | .u32ToField indices => do return { outputs := #[← readRowWord values indices] }

theorem rowValues_read {values : Array RowValue} {index : ValIdx} {value : RowValue}
    (read : values[index]? = some value) : (rowValues values)[index]? = some value.value := by
  simp only [rowValues, Array.getElem?_map, read, Option.map_some]

theorem rowValues_advice_size (row : Nat → G) (start count : Nat) :
    (rowValues (rowAdvice row start count)).size = count := by
  simp only [rowValues, rowAdvice, Array.size_map, Array.size_ofFn]

theorem rowValues_singleton (value : RowValue) : rowValues #[value] = #[value.value] := by
  simp only [rowValues, Array.map_singleton]

theorem rowValues_empty : rowValues #[] = #[] := by
  simp only [rowValues, Array.map_empty]

theorem rowValues_extendOutputs (kind : Byte2Kind) (left right : RowValue)
    (outputs : Array RowValue) :
    rowValues (kind.extendRowOutputs left right outputs) =
      kind.extendOutputs left.value right.value (rowValues outputs) := by
  cases kind <;> simp only [Byte2Kind.extendRowOutputs, Byte2Kind.extendOutputs,
    rowValues, Array.map_push]

theorem readRowWord_value {values : Array RowValue} {indices : Array ValIdx} {word : RowValue}
    (read : readRowWord values indices = some word) :
    Bytecode.AIR.readWord (rowValues values) indices = some word.value := by
  simp only [readRowWord, bind, Option.bind] at read
  split at read
  · cases read
  · have equal := Option.some.inj read
    rw [← equal]
    assumption

theorem emitByte1_step {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries) (memory : Bytecode.AIR.Memory)
    {row : Nat → G} {kind : Byte1Kind} {index : ValIdx} {values : Array RowValue}
    {emission : OpEmission} (emitted : emitByte1 row kind index values = some emission)
    (queried : emission.queries ⊆ queries) :
    Bytecode.AIR.Step memory (kind.op index) (rowValues values)
      (rowValues values ++ rowValues emission.outputs) (emission.calls.map Prod.fst) := by
  simp only [emitByte1, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i input read
    have equal := Option.some.inj emitted
    subst emission
    exact global.byte1_step memory (rowValues_read read) (rowValues_advice_size _ _ _)
      (queried List.mem_cons_self)

theorem emitByte2_step {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries) (memory : Bytecode.AIR.Memory)
    {row : Nat → G} {kind : Byte2Kind} {left right : ValIdx} {values : Array RowValue}
    {emission : OpEmission} (emitted : emitByte2 row kind left right values = some emission)
    (queried : emission.queries ⊆ queries) :
    Bytecode.AIR.Step memory (kind.op left right) (rowValues values)
      (rowValues values ++ rowValues emission.outputs) (emission.calls.map Prod.fst) := by
  simp only [emitByte2, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i x readX
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i y readY
      have equal := Option.some.inj emitted
      subst emission
      simp only [rowValues_extendOutputs]
      exact global.byte2_step memory (rowValues_read readX) (rowValues_read readY)
        (rowValues_advice_size _ _ _) (queried List.mem_cons_self)

theorem GlobalLookups.range4 {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries) (bytes : Fin 4 → G)
    (queried : range4Queries bytes ⊆ queries) : ∀ i, (bytes i).n < 256 := by
  have first := global.byte2 (kind := .range) (x := bytes 0) (y := bytes 1) (outputs := #[]) rfl
    (queried (by simp [range4Queries, rangeMessage]))
  have last := global.byte2 (kind := .range) (outputs := #[]) rfl
    (queried (by simp [range4Queries, rangeMessage] : rangeMessage (bytes 2, bytes 3) ∈ range4Queries bytes))
  intro i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact first.1
  · exact first.2.1
  · exact last.1
  · exact last.2.1

theorem emitU32LessThan_step {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries) (memory : Bytecode.AIR.Memory)
    {row : Nat → G} {selector : G} {left right : ValIdx} {values : Array RowValue}
    {emission : OpEmission} (emitted : emitU32LessThan row selector left right values = some emission)
    (active : selector = 1) (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (queried : emission.queries ⊆ queries) :
    Bytecode.AIR.Step memory (.u32LessThan left right) (rowValues values)
      (rowValues values ++ rowValues emission.outputs) (emission.calls.map Prod.fst) := by
  simp only [emitU32LessThan, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i a readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i b readB
      have equal := Option.some.inj emitted
      subst emission
      simp only [rowValues_singleton]
      apply active_u32_less_than_step memory active (rowValues_read readA) (rowValues_read readB)
        (fun index => row index.val) (fun index => row (4 + index.val)) (fun index => row (8 + index.val))
      · exact global.range4 _ (fun message member => queried
          (List.mem_append_left _ (List.mem_append_left _ member)))
      · exact global.range4 _ (fun message member => queried
          (List.mem_append_left _ (List.mem_append_right _ member)))
      · exact global.range4 _ (fun message member => queried (List.mem_append_right _ member))
      · exact satisfied _ List.mem_cons_self
      · exact satisfied _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · intro index
        apply satisfied
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨index, rfl⟩))

theorem emitU32Add_step (memory : Bytecode.AIR.Memory)
    {row : Nat → G} {left right : Array ValIdx} {values : Array RowValue} {emission : OpEmission}
    (emitted : emitU32Add row left right none values = some emission) :
    Bytecode.AIR.Step memory (.unconstrainedU32Add left right) (rowValues values)
      (rowValues values ++ rowValues emission.outputs) (emission.calls.map Prod.fst) := by
  simp only [emitU32Add, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i x readX
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i y readY
      have equal := Option.some.inj emitted
      subst emission
      apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 4))
      simp only [Bytecode.AIR.primitive, readRowWord_value readX, readRowWord_value readY,
        Bytecode.AIR.adviceOfSize, rowValues_advice_size, ite_true, bind, Option.bind]
      simp only [RowValue.add, RowValue.pack, rowValues, Array.map_push, pure]

theorem emitU32Add3_step (memory : Bytecode.AIR.Memory)
    {row : Nat → G} {left right third : Array ValIdx} {values : Array RowValue} {emission : OpEmission}
    (emitted : emitU32Add row left right (some third) values = some emission) :
    Bytecode.AIR.Step memory (.unconstrainedU32Add3 left right third) (rowValues values)
      (rowValues values ++ rowValues emission.outputs) (emission.calls.map Prod.fst) := by
  simp only [emitU32Add, bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  · rename_i x readX
    dsimp only at emitted
    split at emitted
    · cases emitted
    · rename_i y readY
      dsimp only at emitted
      cases readZ : readRowWord values third with
      | none => simp only [readZ, Option.map_none] at emitted; cases emitted
      | some z =>
        simp only [readZ, Option.map_some] at emitted
        have equal := Option.some.inj emitted
        subst emission
        apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 4))
        simp only [Bytecode.AIR.primitive, readRowWord_value readX, readRowWord_value readY,
          readRowWord_value readZ, Bytecode.AIR.adviceOfSize, rowValues_advice_size,
          ite_true, bind, Option.bind]
        simp only [RowValue.add, RowValue.pack, rowValues, Array.map_push, pure]

theorem active_array_equality {selector : G} {left right : Array G}
    (active : selector = 1) (sizes : left.size = right.size)
    (equations : ∀ equation ∈ (List.ofFn fun i : Fin left.size =>
      selector * (left[i] - right[i.val]?.getD 0)), equation = 0) : left = right := by
  apply Array.ext sizes
  intro index leftBound rightBound
  have equal := active_case active (equations _ (List.mem_ofFn.mpr ⟨⟨index, leftBound⟩, rfl⟩))
  simpa only [Fin.getElem_fin, Array.getElem?_eq_getElem rightBound, Option.getD_some] using equal

/-- A successful valued emission on an active row has the full relational
meaning of its bytecode operation. Byte and memory facts come from the one
global pool; constrained calls remain requests for the later rank induction. -/
theorem emitOp_step {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    {program : Toplevel} {op : Op} (shape : op.lookupShape program = true)
    {row : Nat → G} {selector rank : G} {values : Array RowValue} {emission : OpEmission}
    (emitted : emitOp row selector rank op values = some emission)
    (active : selector = 1) (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (queried : emission.queries ⊆ queries) :
    Bytecode.AIR.Step (memoryFacts tables.memory) op (rowValues values)
      (rowValues values ++ rowValues emission.outputs) (emission.calls.map Prod.fst) := by
  cases op with
  | const value =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := #[])
    simp only [Bytecode.AIR.primitive, rowValues_singleton, RowValue.konst]
  | add a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i x readX
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i y readY
        have equal := Option.some.inj emitted
        subst emission
        apply Bytecode.AIR.Step.primitive (advice := #[])
        simp only [Bytecode.AIR.primitive, rowValues_read readX, rowValues_read readY,
          bind, Option.bind, pure, rowValues_singleton, RowValue.add]
  | sub a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i x readX
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i y readY
        have equal := Option.some.inj emitted
        subst emission
        apply Bytecode.AIR.Step.primitive (advice := #[])
        simp only [Bytecode.AIR.primitive, rowValues_read readX, rowValues_read readY,
          bind, Option.bind, pure, rowValues_singleton, RowValue.sub]
  | mul a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i x readX
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i y readY
        dsimp only at emitted
        split at emitted
        · have equal := Option.some.inj emitted
          subst emission
          apply Bytecode.AIR.Step.primitive (advice := #[])
          simp only [Bytecode.AIR.primitive, rowValues_read readX, rowValues_read readY,
            bind, Option.bind, pure, rowValues_singleton, RowValue.mul]
        · have equal := Option.some.inj emitted
          subst emission
          have product := active_case active (satisfied _ List.mem_cons_self)
          apply Bytecode.AIR.Step.primitive (advice := #[])
          simp only [Bytecode.AIR.primitive, rowValues_read readX, rowValues_read readY,
            bind, Option.bind, pure, rowValues_singleton, RowValue.variable, product, RowValue.mul]
  | eqZero a =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i input read
      dsimp only at emitted
      split at emitted
      · split at emitted
        · have equal := Option.some.inj emitted
          subst emission
          apply Bytecode.AIR.Step.primitive (advice := #[])
          simp only [Bytecode.AIR.primitive, rowValues_read read, bind, Option.bind,
            pure, rowValues_singleton, RowValue.konst]
        · cases emitted
      · have equal := Option.some.inj emitted
        subst emission
        have result := active_eqZero active (satisfied _ List.mem_cons_self)
          (satisfied _ (List.mem_cons_of_mem _ List.mem_cons_self))
        apply Bytecode.AIR.Step.primitive (advice := #[])
        simp only [Bytecode.AIR.primitive, rowValues_read read, bind, Option.bind,
          pure, rowValues_singleton, RowValue.variable, result]
  | call function indices size unconstrained =>
    cases unconstrained with
    | true =>
      simp only [emitOp, ite_true, Option.some.injEq] at emitted
      subst emission
      apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 size))
      simp only [Bytecode.AIR.primitive, Bytecode.AIR.adviceOfSize, rowValues_advice_size, ite_true, emitAdvice]
    | false =>
      simp only [emitOp, Bool.false_eq_true, ite_false, bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      · rename_i inputs read
        have equal := Option.some.inj emitted
        subst emission
        exact Bytecode.AIR.Step.call
          (request := ⟨function, inputs, rowValues (rowAdvice row 0 size), row size⟩)
          read (rowValues_advice_size row 0 size)
  | store indices =>
    have widthBound : indices.size < gSize.toNat := by
      simpa only [Op.lookupShape, decide_eq_true_eq] using shape
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i contents read
      have equal := Option.some.inj emitted
      subst emission
      have size := Bytecode.AIR.readValues_size read
      have fact := global.memory_fact memoryValid canonical widthBound size (queried List.mem_cons_self)
      rw [← size] at fact
      simpa only [rowValues_singleton, RowValue.variable, Array.push_eq_append, List.map_nil] using
        Bytecode.AIR.Step.store read fact
  | load size index =>
    have widthBound : size < gSize.toNat := by
      simpa only [Op.lookupShape, decide_eq_true_eq] using shape
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i pointer read
      have equal := Option.some.inj emitted
      subst emission
      exact Bytecode.AIR.Step.load (rowValues_read read) (rowValues_advice_size _ _ _)
        (global.memory_fact memoryValid canonical widthBound (rowValues_advice_size _ _ _)
          (queried List.mem_cons_self))
  | assertEq xs ys message =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i sameSize
      split at emitted
      · cases emitted
      · rename_i left readLeft
        dsimp only at emitted
        split at emitted
        · cases emitted
        · rename_i right readRight
          have equal := Option.some.inj emitted
          subst emission
          have sizes : left.size = right.size := by
            have := Bytecode.AIR.readValues_size readLeft
            have := Bytecode.AIR.readValues_size readRight
            omega
          have contents := active_array_equality active sizes satisfied
          apply Bytecode.AIR.Step.primitive (advice := #[])
          simp only [rowValues_empty]
          simp only [Bytecode.AIR.primitive, readLeft, readRight, bind, Option.bind,
            if_pos contents]
  | ioGetInfo key data =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 2))
    simp only [Bytecode.AIR.primitive, Bytecode.AIR.adviceOfSize, rowValues_advice_size, ite_true, emitAdvice]
  | ioRead key offset size =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 size))
    simp only [Bytecode.AIR.primitive, Bytecode.AIR.adviceOfSize, rowValues_advice_size, ite_true, emitAdvice]
  | ioSetInfo key data flag length =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := #[])
    simp only [Bytecode.AIR.primitive, rowValues, Array.map_empty]
  | ioWrite key data =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := #[])
    simp only [Bytecode.AIR.primitive, rowValues, Array.map_empty]
  | debug message data =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := #[])
    simp only [Bytecode.AIR.primitive, rowValues, Array.map_empty]
  | u8BitDecomposition index => exact emitByte1_step global _ emitted queried
  | u8ShiftLeft index => exact emitByte1_step global _ emitted queried
  | u8ShiftRight index => exact emitByte1_step global _ emitted queried
  | u8Xor a b => exact emitByte2_step global _ emitted queried
  | u8Add a b => exact emitByte2_step global _ emitted queried
  | u8Sub a b => exact emitByte2_step global _ emitted queried
  | u8And a b => exact emitByte2_step global _ emitted queried
  | u8Or a b => exact emitByte2_step global _ emitted queried
  | u8LessThan a b => exact emitByte2_step global _ emitted queried
  | u8RangeCheck a b => exact emitByte2_step global _ emitted queried
  | u8Mul a b => exact emitByte2_step global _ emitted queried
  | u8XorSplit7 a b => exact emitByte2_step global _ emitted queried
  | u8XorSplit4 a b => exact emitByte2_step global _ emitted queried
  | u32LessThan a b => exact emitU32LessThan_step global _ emitted active satisfied queried
  | unconstrainedBigUintDivMod a b =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 2))
    simp only [Bytecode.AIR.primitive, Bytecode.AIR.adviceOfSize, rowValues_advice_size, ite_true, emitAdvice]
  | unconstrainedGToBytes index =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 8))
    simp only [Bytecode.AIR.primitive, Bytecode.AIR.adviceOfSize, rowValues_advice_size, ite_true, emitAdvice]
  | unconstrainedGInverse index =>
    simp only [emitOp, Option.some.injEq] at emitted
    subst emission
    apply Bytecode.AIR.Step.primitive (advice := rowValues (rowAdvice row 0 1))
    simp only [Bytecode.AIR.primitive, Bytecode.AIR.adviceOfSize, rowValues_advice_size, ite_true, emitAdvice]
  | unconstrainedU32Add a b => exact emitU32Add_step _ emitted
  | unconstrainedU32Add3 a b c => exact emitU32Add3_step _ emitted
  | u32ToField indices =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i word read
      have equal := Option.some.inj emitted
      subst emission
      apply Bytecode.AIR.Step.primitive (advice := #[])
      simp only [Bytecode.AIR.primitive, readRowWord_value read, bind, Option.bind,
        pure, rowValues_singleton]

structure OpsEmission where
  values : Array RowValue
  column : Nat
  equations : List G := []
  queries : List (List G) := []
  calls : List (Bytecode.AIR.Call × (Fin 6 → G)) := []

/-- Native operation order, including the logical map extension and exact
advance of the auxiliary-column cursor after each operation. -/
def emitOps (row : Nat → G) (selector rank : G) :
    List Op → Array RowValue → Nat → Option OpsEmission
  | [], values, column => some { values, column }
  | op :: ops, values, column => do
    let first ← emitOp (fun i => row (column + i)) selector rank op values
    let rest ← emitOps row selector rank ops (values ++ first.outputs) (column + first.used)
    return { rest with
      equations := first.equations ++ rest.equations
      queries := first.queries ++ rest.queries
      calls := first.calls ++ rest.calls }

theorem rowValues_append (left right : Array RowValue) :
    rowValues (left ++ right) = rowValues left ++ rowValues right := by
  simp only [rowValues, Array.map_append]

theorem emitOps_run {tables : LookupTables} {width : Nat} {queries : List (List G)}
    (global : GlobalLookups tables width queries)
    (memoryValid : ∀ size, MemoryRowsValid size (tables.memory size))
    (canonical : ∀ size ∈ tables.memoryWidths, size < gSize.toNat)
    {program : Toplevel} {ops : List Op} (shapes : ∀ op ∈ ops, op.lookupShape program = true)
    {row : Nat → G} {selector rank : G} {values : Array RowValue} {column : Nat}
    {emission : OpsEmission} (emitted : emitOps row selector rank ops values column = some emission)
    (active : selector = 1) (satisfied : ∀ equation ∈ emission.equations, equation = 0)
    (queried : emission.queries ⊆ queries) :
    Bytecode.AIR.RunOps (memoryFacts tables.memory) ops (rowValues values)
      (rowValues emission.values) (emission.calls.map Prod.fst) := by
  induction ops generalizing values column emission with
  | nil =>
    simp only [emitOps, Option.some.injEq] at emitted
    subst emission
    exact Bytecode.AIR.RunOps.nil
  | cons op ops ih =>
    simp only [emitOps, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    · rename_i first firstEmitted
      dsimp only at emitted
      split at emitted
      · cases emitted
      · rename_i rest restEmitted
        have equal := Option.some.inj emitted
        subst emission
        have firstStep := emitOp_step global memoryValid canonical (shapes op List.mem_cons_self)
          firstEmitted active
          (fun equation member => satisfied equation (List.mem_append_left _ member))
          (fun message member => queried (List.mem_append_left _ member))
        have restRun := ih (fun op member => shapes op (List.mem_cons_of_mem _ member))
          restEmitted (fun equation member => satisfied equation (List.mem_append_right _ member))
          (fun message member => queried (List.mem_append_right _ member))
        rw [rowValues_append] at restRun
        simpa only [List.map_append] using Bytecode.AIR.RunOps.cons firstStep restRun

end Aiur.AIR
