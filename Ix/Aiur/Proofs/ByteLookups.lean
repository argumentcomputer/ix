/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ByteArithmetic

/-!
Extraction of byte operations from fixed byte-table lookup messages.

The three unary and ten binary channels, row order, output columns and
arities match the native byte chips. Providers range over the complete
fixed tables with arbitrary field multiplicities. Exact balance and a
query-count bound force each requested input and output to match one row.
The step theorems include virtual carry/borrow outputs omitted by lookups.

Native preprocessed rows and lookup expressions are compared exhaustively
against these definitions by the component gate. That executable comparison
does not prove native refinement. Extracting balance for these exact tuples
from the global padded/compressed lookup argument remains a separate task.
-/

namespace Aiur.AIR

inductive Byte1Kind where
  | bits | shiftLeft | shiftRight
  deriving DecidableEq

def Byte1Kind.all : List Byte1Kind := [.bits, .shiftLeft, .shiftRight]

def Byte1Kind.channel : Byte1Kind → G
  | .bits => 2
  | .shiftLeft => 3
  | .shiftRight => 4

theorem Byte1Kind.channel_injective {left right : Byte1Kind}
    (same : left.channel = right.channel) : left = right := by
  revert same
  cases left <;> cases right <;> decide +kernel

def Byte1Kind.result : Byte1Kind → G → Array G
  | .bits, input => Array.ofFn (G.u8BitDecomposition input)
  | .shiftLeft, input => #[G.u8ShiftLeft input]
  | .shiftRight, input => #[G.u8ShiftRight input]

def byte1Outputs (kind : Byte1Kind) (row : Fin 256) : Array G :=
  match kind with
  | .bits => Array.ofFn fun bit : Fin 8 => G.ofNat ((row.val >>> bit.val) &&& 1)
  | .shiftLeft => #[G.ofNat ((row.val * 2) % 256)]
  | .shiftRight => #[G.ofNat (row.val / 2)]

def byte1Request (kind : Byte1Kind) (input : G) (outputs : Array G) : List G :=
  kind.channel :: input :: outputs.toList

def byte1Providers (weights : Byte1Kind → Fin 256 → G) : List (Provider (List G)) :=
  Byte1Kind.all.flatMap fun kind => List.ofFn fun row =>
    (byte1Request kind (G.ofNat row.val) (byte1Outputs kind row), weights kind row)

theorem byte1Outputs_correct (kind : Byte1Kind) (row : Fin 256) :
    byte1Outputs kind row = kind.result (G.ofNat row.val) := by
  have below : row.val < gSize.toNat := Nat.lt_trans row.isLt (by decide)
  cases kind <;>
    simp only [byte1Outputs, Byte1Kind.result, G.u8ShiftLeft,
      G.u8ShiftRight, G.n_ofNat, Nat.mod_eq_of_lt below]
  apply congrArg Array.ofFn
  funext bit
  simp only [G.u8BitDecomposition, G.n_ofNat, Nat.mod_eq_of_lt below]

theorem exactLookupBalance_byte1 {queries : List (List G)}
    (weights : Byte1Kind → Fin 256 → G)
    (balanced : ExactLookupBalance queries (byte1Providers weights))
    (bounded : queries.length < gSize.toNat)
    {kind : Byte1Kind} {input : G} {outputs : Array G}
    (queried : byte1Request kind input outputs ∈ queries) :
    input.n < 256 ∧ outputs = kind.result input := by
  obtain ⟨provider, member, same, _⟩ := exactLookupBalance_provider balanced bounded queried
  obtain ⟨providerKind, _, rowMember⟩ := List.mem_flatMap.mp member
  obtain ⟨row, equal⟩ := List.mem_ofFn.mp rowMember
  subst provider
  change byte1Request providerKind (G.ofNat row.val) (byte1Outputs providerKind row) =
    byte1Request kind input outputs at same
  obtain ⟨sameChannel, sameTail⟩ := List.cons.inj same
  have equalKind := Byte1Kind.channel_injective sameChannel
  subst providerKind
  obtain ⟨sameInput, sameOutputs⟩ := List.cons.inj sameTail
  have below : row.val < gSize.toNat := Nat.lt_trans row.isLt (by decide)
  constructor
  · rw [← sameInput, G.n_ofNat, Nat.mod_eq_of_lt below]
    exact row.isLt
  · rw [← sameInput]
    exact (Array.toList_inj.mp sameOutputs).symm.trans (byte1Outputs_correct kind row)

inductive Byte2Kind where
  | xor | add | sub | and | or | lessThan | range | mul | split7 | split4
  deriving DecidableEq

def Byte2Kind.all : List Byte2Kind :=
  [.xor, .add, .sub, .and, .or, .lessThan, .range, .mul, .split7, .split4]

def Byte2Kind.channel : Byte2Kind → G
  | .xor => 5
  | .add => 6
  | .sub => 7
  | .and => 8
  | .or => 9
  | .lessThan => 10
  | .range => 11
  | .mul => 12
  | .split7 => 13
  | .split4 => 14

theorem Byte2Kind.channel_injective {left right : Byte2Kind}
    (same : left.channel = right.channel) : left = right := by
  revert same
  cases left <;> cases right <;> decide +kernel

def Byte2Kind.result : Byte2Kind → G → G → Array G
  | .xor, x, y => #[G.u8Xor x y]
  | .add, x, y => #[(G.u8Add x y).1]
  | .sub, x, y => #[(G.u8Sub x y).1]
  | .and, x, y => #[G.u8And x y]
  | .or, x, y => #[G.u8Or x y]
  | .lessThan, x, y => #[G.u8LessThan x y]
  | .range, _, _ => #[]
  | .mul, x, y => Bytecode.AIR.pairValues (G.u8Mul x y)
  | .split7, x, y => #[G.ofNat ((x.n ^^^ y.n) / 128), G.ofNat (((x.n ^^^ y.n) * 2) % 256)]
  | .split4, x, y => #[G.ofNat ((x.n ^^^ y.n) / 16), G.ofNat (((x.n ^^^ y.n) * 16) % 256)]

def byte2Outputs (kind : Byte2Kind) (row : Fin 65536) : Array G :=
  let x := row.val / 256
  let y := row.val % 256
  match kind with
  | .xor => #[G.ofNat (x ^^^ y)]
  | .add => #[G.ofNat ((x + y) % 256)]
  | .sub => #[G.ofNat ((x + 256 - y) % 256)]
  | .and => #[G.ofNat (x &&& y)]
  | .or => #[G.ofNat (x ||| y)]
  | .lessThan => #[if x < y then 1 else 0]
  | .range => #[]
  | .mul => #[G.ofNat ((x * y) % 256), G.ofNat ((x * y) / 256)]
  | .split7 => #[G.ofNat ((x ^^^ y) / 128), G.ofNat (((x ^^^ y) * 2) % 256)]
  | .split4 => #[G.ofNat ((x ^^^ y) / 16), G.ofNat (((x ^^^ y) * 16) % 256)]

def byte2Request (kind : Byte2Kind) (x y : G) (outputs : Array G) : List G :=
  kind.channel :: x :: y :: outputs.toList

def byte2Providers (weights : Byte2Kind → Fin 65536 → G) : List (Provider (List G)) :=
  Byte2Kind.all.flatMap fun kind => List.ofFn fun row =>
    let inputs := byteRangeMessage row
    (byte2Request kind inputs.1 inputs.2 (byte2Outputs kind row), weights kind row)

theorem byte2Outputs_correct (kind : Byte2Kind) (row : Fin 65536) :
    byte2Outputs kind row = kind.result (byteRangeMessage row).1 (byteRangeMessage row).2 := by
  have left : row.val / 256 < gSize.toNat :=
    Nat.lt_trans (show row.val / 256 < 256 by omega) (by decide)
  have right : row.val % 256 < gSize.toNat := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)
  cases kind <;>
    simp only [byte2Outputs, Byte2Kind.result, byteRangeMessage, G.u8Xor, G.u8Add,
      G.u8Sub, G.u8And, G.u8Or, G.u8LessThan, G.u8Mul, Bytecode.AIR.pairValues,
      G.n_ofNat, Nat.mod_eq_of_lt left, Nat.mod_eq_of_lt right]

theorem exactLookupBalance_byte2 {queries : List (List G)}
    (weights : Byte2Kind → Fin 65536 → G)
    (balanced : ExactLookupBalance queries (byte2Providers weights))
    (bounded : queries.length < gSize.toNat)
    {kind : Byte2Kind} {x y : G} {outputs : Array G}
    (queried : byte2Request kind x y outputs ∈ queries) :
    x.n < 256 ∧ y.n < 256 ∧ outputs = kind.result x y := by
  obtain ⟨provider, member, same, _⟩ := exactLookupBalance_provider balanced bounded queried
  obtain ⟨providerKind, _, rowMember⟩ := List.mem_flatMap.mp member
  obtain ⟨row, equal⟩ := List.mem_ofFn.mp rowMember
  subst provider
  change byte2Request providerKind (byteRangeMessage row).1 (byteRangeMessage row).2
    (byte2Outputs providerKind row) = byte2Request kind x y outputs at same
  obtain ⟨sameChannel, sameTail⟩ := List.cons.inj same
  have equalKind := Byte2Kind.channel_injective sameChannel
  subst providerKind
  obtain ⟨sameX, sameTail⟩ := List.cons.inj sameTail
  obtain ⟨sameY, sameOutputs⟩ := List.cons.inj sameTail
  rw [← sameX, ← sameY]
  refine ⟨(byteRangeMessage_bounded row).1, (byteRangeMessage_bounded row).2, ?_⟩
  exact (Array.toList_inj.mp sameOutputs).symm.trans (byte2Outputs_correct kind row)

def Byte1Kind.op : Byte1Kind → Bytecode.ValIdx → Bytecode.Op
  | .bits => .u8BitDecomposition
  | .shiftLeft => .u8ShiftLeft
  | .shiftRight => .u8ShiftRight

theorem byte1_primitive {kind : Byte1Kind} {values : Array G} {index : Bytecode.ValIdx}
    {input : G} (read : values[index]? = some input) (bounded : input.n < 256) :
    Bytecode.AIR.primitive (kind.op index) values #[] = some (kind.result input) := by
  cases kind <;>
    simp only [Byte1Kind.op, Byte1Kind.result, Bytecode.AIR.primitive,
      Bytecode.AIR.unaryByte, read, bind, Option.bind, if_pos bounded, Function.comp_apply]

theorem exactLookupBalance_byte1_step {queries : List (List G)}
    (weights : Byte1Kind → Fin 256 → G)
    (balanced : ExactLookupBalance queries (byte1Providers weights))
    (bounded : queries.length < gSize.toNat)
    (memory : Bytecode.AIR.Memory) {kind : Byte1Kind} {values : Array G}
    {index : Bytecode.ValIdx} {input : G} {outputs : Array G}
    (read : values[index]? = some input)
    (queried : byte1Request kind input outputs ∈ queries) :
    Bytecode.AIR.Step memory (kind.op index) values (values ++ outputs) [] := by
  obtain ⟨range, correct⟩ := exactLookupBalance_byte1 weights balanced bounded queried
  apply Bytecode.AIR.Step.primitive (advice := #[])
  rw [correct]
  exact byte1_primitive read range

def Byte2Kind.op : Byte2Kind → Bytecode.ValIdx → Bytecode.ValIdx → Bytecode.Op
  | .xor => .u8Xor
  | .add => .u8Add
  | .sub => .u8Sub
  | .and => .u8And
  | .or => .u8Or
  | .lessThan => .u8LessThan
  | .range => .u8RangeCheck
  | .mul => .u8Mul
  | .split7 => .u8XorSplit7
  | .split4 => .u8XorSplit4

def Byte2Kind.extendOutputs (kind : Byte2Kind) (x y : G) (outputs : Array G) : Array G :=
  match kind with
  | .add => outputs.push ((x + y - outputs[0]?.getD 0) * inverse256)
  | .sub => outputs.push ((outputs[0]?.getD 0 + y - x) * inverse256)
  | _ => outputs

theorem byte2_primitive {kind : Byte2Kind} {values : Array G} {left right : Bytecode.ValIdx}
    {x y : G} (readX : values[left]? = some x) (readY : values[right]? = some y)
    (hx : x.n < 256) (hy : y.n < 256) :
    Bytecode.AIR.primitive (kind.op left right) values #[] =
      some (kind.extendOutputs x y (kind.result x y)) := by
  cases kind <;>
    simp only [Byte2Kind.op, Byte2Kind.result, Byte2Kind.extendOutputs,
      Bytecode.AIR.primitive, Bytecode.AIR.binaryByte, readX, readY,
      bind, Option.bind, if_pos (And.intro hx hy)]
  · simp only [G.u8Add, Bytecode.AIR.pairValues, Array.getElem?_singleton, ite_true, Option.getD_some]
    rw [byte_add_carry hx hy rfl]
    rfl
  · simp only [G.u8Sub, Bytecode.AIR.pairValues, Array.getElem?_singleton, ite_true, Option.getD_some]
    rw [byte_sub_borrow hx hy rfl]
    rfl

theorem exactLookupBalance_byte2_step {queries : List (List G)}
    (weights : Byte2Kind → Fin 65536 → G)
    (balanced : ExactLookupBalance queries (byte2Providers weights))
    (bounded : queries.length < gSize.toNat)
    (memory : Bytecode.AIR.Memory) {kind : Byte2Kind} {values : Array G}
    {left right : Bytecode.ValIdx} {x y : G} {outputs : Array G}
    (readX : values[left]? = some x) (readY : values[right]? = some y)
    (queried : byte2Request kind x y outputs ∈ queries) :
    Bytecode.AIR.Step memory (kind.op left right) values
      (values ++ kind.extendOutputs x y outputs) [] := by
  obtain ⟨rangeX, rangeY, correct⟩ := exactLookupBalance_byte2 weights balanced bounded queried
  apply Bytecode.AIR.Step.primitive (advice := #[])
  rw [correct]
  exact byte2_primitive readX readY rangeX rangeY

theorem active_u32_less_than_step (memory : Bytecode.AIR.Memory)
    {selector a b : G} {values : Array G} {left right : Bytecode.ValIdx}
    (active : selector = 1) (readA : values[left]? = some a) (readB : values[right]? = some b)
    (x y z : Fin 4 → G)
    (hx : ∀ i, (x i).n < 256) (hy : ∀ i, (y i).n < 256) (hz : ∀ i, (z i).n < 256)
    (decomposeA : selector * (a - pack4 x) = 0)
    (decomposeB : selector * (b - pack4 z) = 0)
    (carries : ∀ i : Fin 4, selector * booleanConstraint (u32Carries x y z i.succ) = 0) :
    Bytecode.AIR.Step memory (.u32LessThan left right) values
      (values ++ #[1 - u32Carries x y z 4]) [] := by
  obtain ⟨rangeA, rangeB, correct⟩ := active_u32_less_than active x y z hx hy hz decomposeA decomposeB carries
  apply Bytecode.AIR.Step.primitive (advice := #[])
  simp only [Bytecode.AIR.primitive, readA, readB, bind, Option.bind, if_pos (And.intro rangeA rangeB), correct]

def byte1Preprocessed (row : Fin 256) : Array G :=
  #[G.ofNat row.val] ++ byte1Outputs .bits row ++
    byte1Outputs .shiftLeft row ++ byte1Outputs .shiftRight row

def byte2Preprocessed (row : Fin 65536) : Array G :=
  let inputs := byteRangeMessage row
  #[inputs.1, inputs.2] ++ byte2Outputs .xor row ++ byte2Outputs .add row ++
    byte2Outputs .sub row ++ byte2Outputs .and row ++ byte2Outputs .or row ++
    byte2Outputs .lessThan row ++ byte2Outputs .mul row ++ byte2Outputs .split7 row ++
    byte2Outputs .split4 row

end Aiur.AIR
