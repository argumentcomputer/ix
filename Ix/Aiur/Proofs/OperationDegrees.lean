/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationSequences

/-!
Tracked degree zero implies a constant frontend expression. Positive tracked
degrees may still accompany folded constants; no converse is imposed. This
invariant is needed to identify equality-test allocation with compiler layout.
-/

namespace Aiur.NativeAIR

def RowExpr.ZeroConstant (row : RowExpr) : Prop :=
  row.degree = 0 → ∃ value, row.expr = .konst value

theorem RowExpr.ZeroConstant.konst (value : G) : (RowExpr.konst value).ZeroConstant :=
  fun _ => ⟨value, rfl⟩

theorem RowExpr.ZeroConstant.variable (column : ColRef) : (RowExpr.variable column).ZeroConstant := by
  intro zero
  cases zero

theorem RowExpr.ZeroConstant.add {left right : RowExpr} (a : left.ZeroConstant) (b : right.ZeroConstant) :
    (left.add right).ZeroConstant := by
  intro zero
  change max left.degree right.degree = 0 at zero
  obtain ⟨x, hx⟩ := a (by omega)
  obtain ⟨y, hy⟩ := b (by omega)
  exact ⟨x + y, by simp only [RowExpr.add, hx, hy, Expr.frontAdd, Expr.constantValue]⟩

theorem RowExpr.ZeroConstant.sub {left right : RowExpr} (a : left.ZeroConstant) (b : right.ZeroConstant) :
    (left.sub right).ZeroConstant := by
  intro zero
  change max left.degree right.degree = 0 at zero
  obtain ⟨x, hx⟩ := a (by omega)
  obtain ⟨y, hy⟩ := b (by omega)
  exact ⟨x - y, by simp only [RowExpr.sub, hx, hy, Expr.frontSub, Expr.constantValue]⟩

theorem RowExpr.ZeroConstant.mul {left right : RowExpr} (a : left.ZeroConstant) (b : right.ZeroConstant) :
    (left.mul right).ZeroConstant := by
  intro zero
  change left.degree + right.degree = 0 at zero
  obtain ⟨x, hx⟩ := a (by omega)
  obtain ⟨y, hy⟩ := b (by omega)
  exact ⟨x * y, by simp only [RowExpr.mul, hx, hy, Expr.frontMul, Expr.constantValue]⟩

namespace OpEmitter

def DegreeValid (rows : Array RowExpr) : Prop := ∀ row ∈ rows, row.ZeroConstant

theorem DegreeValid.empty : DegreeValid #[] := by
  intro row member
  exact False.elim (Array.not_mem_empty row member)

theorem DegreeValid.singleton {row : RowExpr} (valid : row.ZeroConstant) : DegreeValid #[row] := by
  intro expr member
  have equal := Array.mem_singleton.mp member
  subst expr
  exact valid

theorem DegreeValid.append {left right : Array RowExpr} (a : DegreeValid left) (b : DegreeValid right) :
    DegreeValid (left ++ right) := by
  intro row member
  rcases Array.mem_append.mp member with member | member
  · exact a row member
  · exact b row member

theorem DegreeValid.push {rows : Array RowExpr} {row : RowExpr} (valid : DegreeValid rows)
    (added : row.ZeroConstant) : DegreeValid (rows.push row) := by
  intro expr member
  rcases Array.mem_push.mp member with member | rfl
  · exact valid expr member
  · exact added

theorem DegreeValid.read {rows : Array RowExpr} (valid : DegreeValid rows) {index : Nat} {row : RowExpr}
    (present : rows[index]? = some row) : row.ZeroConstant := valid row (Array.mem_of_getElem? present)

theorem DegreeValid.getD {rows : Array RowExpr} (valid : DegreeValid rows) (index : Nat) :
    (rows[index]?.getD (.konst 0)).ZeroConstant := by
  cases present : rows[index]? with
  | none => exact RowExpr.ZeroConstant.konst 0
  | some row => exact valid.read present

theorem DegreeValid.select {rows : Array RowExpr} (valid : DegreeValid rows)
    {indices : Array Nat} {selected : Array RowExpr} (read : select rows indices = some selected) :
    DegreeValid selected := by
  intro row member
  obtain ⟨index, bound, equal⟩ := Array.mem_iff_getElem.mp member
  have selectedRead : selected[index]? = some row := Array.getElem?_eq_some_iff.mpr ⟨bound, equal⟩
  have input := array_mapM_read read index
  rw [selectedRead] at input
  cases indexRead : indices[index]? with
  | none => rw [indexRead] at input; cases input
  | some actual =>
    simp only [indexRead, bind, Option.bind_some] at input
    exact valid.read input

theorem advice_degreeValid (first count : Nat) : DegreeValid (advice first count) := by
  intro row member
  obtain ⟨index, rfl⟩ := Array.mem_ofFn.mp member
  exact RowExpr.ZeroConstant.variable _

theorem packFour_degreeValid (bytes : Fin 4 → RowExpr) (valid : ∀ index, (bytes index).ZeroConstant) :
    (packFour bytes).ZeroConstant := by
  exact ((((RowExpr.ZeroConstant.konst 0).add ((valid 0).mul (RowExpr.ZeroConstant.konst _))).add
    ((valid 1).mul (RowExpr.ZeroConstant.konst _))).add
    ((valid 2).mul (RowExpr.ZeroConstant.konst _))).add
    ((valid 3).mul (RowExpr.ZeroConstant.konst _))

theorem readWord_degreeValid {rows : Array RowExpr} (valid : DegreeValid rows)
    {indices : Array Nat} {word : RowExpr} (read : readWord rows indices = some word) : word.ZeroConstant := by
  simp only [readWord] at read
  split at read
  · cases read
  · simp only [bind, Option.bind] at read
    split at read
    · cases read
    rename_i selected selectedRead
    cases read
    exact packFour_degreeValid _ (fun index => (valid.select selectedRead).getD index.val)

theorem fromScalar_degreeValid {scalar : ScalarEmission} (valid : scalar.output.ZeroConstant) :
    DegreeValid (fromScalar scalar).outputs := DegreeValid.singleton valid

theorem emitMul_degreeValid (selector : Expr) (first : Nat) {left right : RowExpr}
    (a : left.ZeroConstant) (b : right.ZeroConstant) : (emitMul selector first left right).output.ZeroConstant := by
  dsimp only [emitMul]
  split
  · exact a.mul b
  · exact RowExpr.ZeroConstant.variable _

theorem emitEqZero_degreeValid (selector : Expr) (first : Nat) (input : RowExpr) :
    (emitEqZero selector first input).output.ZeroConstant := by
  unfold emitEqZero
  split
  · exact RowExpr.ZeroConstant.konst _
  · exact RowExpr.ZeroConstant.variable _

theorem emitByte2_degreeValid (first : Nat) (kind : AIR.Byte2Kind) (left right : RowExpr) :
    DegreeValid (emitByte2 first kind left right).outputs := by
  have carry (subtract : Bool) : (byteCarry first subtract left right).ZeroConstant := by
    intro zero
    change max (max left.degree right.degree) 1 = 0 at zero
    omega
  cases kind <;> first
    | exact advice_degreeValid _ _
    | exact (advice_degreeValid _ _).push (carry _)

theorem emitWordSum_degreeValid (first : Nat) {sum : RowExpr} (valid : sum.ZeroConstant) :
    DegreeValid (emitWordSum first sum).outputs :=
  (advice_degreeValid _ _).push ((valid.sub
    (packFour_degreeValid _ (fun _ => RowExpr.ZeroConstant.variable _))).mul (RowExpr.ZeroConstant.konst _))

theorem emitU32LessThan_degreeValid (selector : Expr) (first : Nat) (left right : RowExpr) :
    DegreeValid (emitU32LessThan selector first left right).outputs := by
  apply DegreeValid.singleton
  intro zero
  cases zero

theorem emitByte1_dispatch_degreeValid (selector rank : Expr) (first : Nat) (kind : AIR.Byte1Kind) (index : Nat)
    {rows : Array RowExpr} {emission : Emission}
    (emitted : emitOp selector rank first (kind.op index) rows callRanks = some emission) : DegreeValid emission.outputs := by
  rw [emitOp_byte1] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  cases emitted
  exact advice_degreeValid _ _

theorem emitByte2_dispatch_degreeValid (selector rank : Expr) (first : Nat) (kind : AIR.Byte2Kind) (a b : Nat)
    {rows : Array RowExpr} {emission : Emission}
    (emitted : emitOp selector rank first (kind.op a b) rows callRanks = some emission) : DegreeValid emission.outputs := by
  rw [emitOp_byte2] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  dsimp only at emitted
  split at emitted
  · cases emitted
  cases emitted
  exact emitByte2_degreeValid _ _ _ _

theorem emitOp_degreeValid {selector rank : Expr} {first : Nat} {op : Bytecode.Op}
    {rows : Array RowExpr} {emission : Emission} (valid : DegreeValid rows)
    (emitted : emitOp selector rank first op rows callRanks = some emission) :
    DegreeValid emission.outputs := by
  cases op with
  | const value =>
    cases emitted
    exact DegreeValid.singleton (RowExpr.ZeroConstant.konst _)
  | add a b | sub a b | mul a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    apply DegreeValid.singleton
    first
    | exact RowExpr.ZeroConstant.add (valid.read readA) (valid.read readB)
    | exact RowExpr.ZeroConstant.sub (valid.read readA) (valid.read readB)
    | exact emitMul_degreeValid selector first (valid.read readA) (valid.read readB)
  | eqZero index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact DegreeValid.singleton (emitEqZero_degreeValid _ _ _)
  | call function indices size unconstrained =>
    cases unconstrained with
    | true =>
      cases emitted
      exact advice_degreeValid _ _
    | false =>
      simp only [emitOp, Bool.false_eq_true, if_false, bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      cases emitted
      exact advice_degreeValid _ _
  | store indices | load size index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact advice_degreeValid _ _
  | assertEq xs ys message =>
    simp only [emitOp] at emitted
    split at emitted
    · cases emitted
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact DegreeValid.empty
  | ioGetInfo | ioRead | unconstrainedBigUintDivMod | unconstrainedGToBytes | unconstrainedGInverse =>
    cases emitted
    exact advice_degreeValid _ _
  | ioSetInfo | ioWrite | debug =>
    cases emitted
    exact DegreeValid.empty
  | u8BitDecomposition index => exact emitByte1_dispatch_degreeValid selector rank first .bits index emitted
  | u8ShiftLeft index => exact emitByte1_dispatch_degreeValid selector rank first .shiftLeft index emitted
  | u8ShiftRight index => exact emitByte1_dispatch_degreeValid selector rank first .shiftRight index emitted
  | u8Xor a b => exact emitByte2_dispatch_degreeValid selector rank first .xor a b emitted
  | u8Add a b => exact emitByte2_dispatch_degreeValid selector rank first .add a b emitted
  | u8Sub a b => exact emitByte2_dispatch_degreeValid selector rank first .sub a b emitted
  | u8And a b => exact emitByte2_dispatch_degreeValid selector rank first .and a b emitted
  | u8Or a b => exact emitByte2_dispatch_degreeValid selector rank first .or a b emitted
  | u8LessThan a b => exact emitByte2_dispatch_degreeValid selector rank first .lessThan a b emitted
  | u8RangeCheck a b => exact emitByte2_dispatch_degreeValid selector rank first .range a b emitted
  | u8Mul a b => exact emitByte2_dispatch_degreeValid selector rank first .mul a b emitted
  | u8XorSplit7 a b => exact emitByte2_dispatch_degreeValid selector rank first .split7 a b emitted
  | u8XorSplit4 a b => exact emitByte2_dispatch_degreeValid selector rank first .split4 a b emitted
  | u32LessThan a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact emitU32LessThan_degreeValid _ _ _ _
  | unconstrainedU32Add a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    exact emitWordSum_degreeValid _ (RowExpr.ZeroConstant.add
      (readWord_degreeValid valid readA) (readWord_degreeValid valid readB))
  | unconstrainedU32Add3 a b c =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i third readC
    cases emitted
    exact emitWordSum_degreeValid _ (RowExpr.ZeroConstant.add
      (RowExpr.ZeroConstant.add (readWord_degreeValid valid readA) (readWord_degreeValid valid readB))
      (readWord_degreeValid valid readC))
  | u32ToField indices =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i word read
    cases emitted
    exact DegreeValid.singleton (readWord_degreeValid valid read)

theorem emitOps_degreeValid {selector rank : Expr} {ops : List Bytecode.Op} {rows : Array RowExpr}
    {column : Nat} {emission : OpsEmission} (valid : DegreeValid rows)
    (emitted : emitOps selector rank ops rows column callRanks = some emission) : DegreeValid emission.values := by
  induction ops generalizing rows column emission with
  | nil =>
    cases emitted
    exact valid
  | cons op ops ih =>
    simp only [emitOps, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i first firstEmitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i rest restEmitted
    cases emitted
    exact ih (emission := rest) (valid.append (emitOp_degreeValid valid firstEmitted)) restEmitted

theorem emitEqZero_allocation (selector : Expr) (first : Nat) {input : RowExpr}
    (valid : input.ZeroConstant) :
    ((emitEqZero selector first input).used, (emitEqZero selector first input).output.degree) =
      if input.degree = 0 then (0, 0) else (2, 1) := by
  by_cases zero : input.degree = 0
  · obtain ⟨value, constant⟩ := valid zero
    simp only [emitEqZero, constant, Expr.constantValue, zero, if_true, RowExpr.konst]
  · cases constant : input.expr.constantValue <;>
      simp only [emitEqZero, constant, zero, if_false, eqZeroRegular, mainCurrent, RowExpr.variable]
    split
    · rename_i impossible
      exact False.elim (zero impossible)
    · rfl

end OpEmitter
end Aiur.NativeAIR
