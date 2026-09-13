/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationExpressions

/-!
Reflection of complete symbolic operation emission into the valued AIR.
Successful incoming evaluations and reads of the allocated fresh columns
derive all output values, metadata, equations, raw queries and call records.
-/

namespace Aiur.NativeAIR.OpEmitter

theorem fromScalar_eval (values : Values G) (emission : ScalarEmission) :
    (fromScalar emission).eval values = emission.eval values := by
  have singleton : evalRows values #[emission.output] = do
      let output ← emission.output.eval values
      return #[output] := by
    change ((#[] : Array RowExpr).push emission.output).mapM _ = _
    rw [array_mapM_push, Array.mapM_empty]
    rfl
  simp only [fromScalar, Emission.eval, singleton, ScalarEmission.eval, List.mapM_nil,
    bind, Option.bind, pure]
  cases emission.output.eval values <;> simp only

theorem empty_eval (values : Values G) : ({} : Emission).eval values = some {} := by
  exact Emission.eval_of (evalRows_empty values) rfl rfl rfl rfl

theorem normal_empty : Normal #[] := by
  intro row member
  exact False.elim (Array.not_mem_empty row member)

theorem normal_singleton {row : RowExpr} (normal : row.expr.noConstantNegs = true) :
    Normal #[row] := by
  intro item member
  have equal := Array.mem_singleton.mp member
  subst item
  exact normal

theorem Normal.read {rows : Array RowExpr} (normal : Normal rows)
    {index : Nat} {row : RowExpr} (read : rows[index]? = some row) :
    row.expr.noConstantNegs = true := normal row (Array.mem_of_getElem? read)

theorem emitOp_byte1 (selector rank : Expr) (first : Nat) (kind : AIR.Byte1Kind)
    (index : Nat) (rows : Array RowExpr) :
    emitOp selector rank first (kind.op index) rows = do
      return emitByte1 first kind (← rows[index]?) := by
  cases kind <;> rfl

theorem emitOp_byte2 (selector rank : Expr) (first : Nat) (kind : AIR.Byte2Kind)
    (left right : Nat) (rows : Array RowExpr) :
    emitOp selector rank first (kind.op left right) rows = do
      return emitByte2 first kind (← rows[left]?) (← rows[right]?) := by
  cases kind <;> rfl

theorem emitByte1_dispatch (values : Values G) (row : Nat → G) (selector rank : Expr)
    (s r : G) (first : Nat) (kind : AIR.Byte1Kind) (index : Nat)
    {rows : Array RowExpr} {inputs : Array AIR.RowValue} {emission : Emission}
    (inputEval : evalRows values rows = some inputs)
    (emitted : emitOp selector rank first (kind.op index) rows = some emission)
    (reads : ∀ index < emission.used,
      (values.columns .main .current)[first + index]? = some (row index)) :
    ∃ result, AIR.emitOp row s r (kind.op index) inputs = some result ∧
      emission.eval values = some result := by
  rw [emitOp_byte1] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i input read
  cases emitted
  obtain ⟨value, readValue, reflected⟩ := evalRows_read inputEval read
  refine ⟨_, ?_, emitByte1_reflects values row first kind reflected reads⟩
  cases kind <;> simp only [AIR.Byte1Kind.op, AIR.emitOp, AIR.emitByte1,
    readValue, bind, Option.bind_some, pure]

theorem emitByte2_dispatch (values : Values G) (row : Nat → G) (selector rank : Expr)
    (s r : G) (first : Nat) (kind : AIR.Byte2Kind) (left right : Nat)
    {rows : Array RowExpr} {inputs : Array AIR.RowValue} {emission : Emission}
    (inputEval : evalRows values rows = some inputs) (normal : Normal rows)
    (emitted : emitOp selector rank first (kind.op left right) rows = some emission)
    (reads : ∀ index < emission.used,
      (values.columns .main .current)[first + index]? = some (row index)) :
    ∃ result, AIR.emitOp row s r (kind.op left right) inputs = some result ∧
      emission.eval values = some result := by
  rw [emitOp_byte2] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i a readA
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i b readB
  cases emitted
  obtain ⟨x, readX, refX⟩ := evalRows_read inputEval readA
  obtain ⟨y, readY, refY⟩ := evalRows_read inputEval readB
  refine ⟨_, ?_, emitByte2_reflects values row first kind refX refY (normal.read readA) reads⟩
  cases kind <;> simp only [AIR.Byte2Kind.op, AIR.emitOp, AIR.emitByte2,
    readX, readY, bind, Option.bind_some, pure]

theorem list_ofFn_getD_pair {α β γ : Type} (left : Array α) (right : Array β)
    (leftDefault : α) (rightDefault : β) (f : α → β → γ) {count : Nat}
    (size : left.size = count) :
    (List.ofFn fun index : Fin count =>
      f (left[index.val]?.getD leftDefault) (right[index.val]?.getD rightDefault)) =
      List.ofFn fun index : Fin left.size => f left[index] (right[index.val]?.getD rightDefault) := by
  subst count
  congr 1
  funext index
  rw [getElem?_pos left index.val index.isLt, Option.getD_some]
  rfl

theorem emitOp_reflects (values : Values G) (row : Nat → G)
    {selector rank : Expr} {s r : G} {first : Nat} {op : Bytecode.Op}
    {rows : Array RowExpr} {inputs : Array AIR.RowValue} {emission : Emission}
    (selectorEval : evalExpr values selector = some s) (rankEval : evalExpr values rank = some r)
    (inputEval : evalRows values rows = some inputs) (normal : Normal rows)
    (emitted : emitOp selector rank first op rows = some emission)
    (reads : ∀ index < emission.used,
      (values.columns .main .current)[first + index]? = some (row index)) :
    ∃ result, AIR.emitOp row s r op inputs = some result ∧ emission.eval values = some result := by
  cases op with
  | const value =>
    cases emitted
    refine ⟨_, rfl, ?_⟩
    rw [fromScalar_eval]
    exact ScalarEmission.eval_of values (RowExpr.konst_reflects values value) rfl
  | add a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    obtain ⟨x, readX, refX⟩ := evalRows_read inputEval readA
    obtain ⟨y, readY, refY⟩ := evalRows_read inputEval readB
    refine ⟨{ outputs := #[x.add y] }, ?_, ?_⟩
    · simp only [AIR.emitOp, readX, readY, bind, Option.bind_some, pure]
    · rw [fromScalar_eval]
      exact ScalarEmission.eval_of values (RowExpr.add_reflects values refX refY) rfl
  | sub a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    obtain ⟨x, readX, refX⟩ := evalRows_read inputEval readA
    obtain ⟨y, readY, refY⟩ := evalRows_read inputEval readB
    refine ⟨{ outputs := #[x.sub y] }, ?_, ?_⟩
    · simp only [AIR.emitOp, readX, readY, bind, Option.bind_some, pure]
    · rw [fromScalar_eval]
      exact ScalarEmission.eval_of values
        (RowExpr.sub_reflects values refX refY (normal.read readB)) rfl
  | mul a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    obtain ⟨x, readX, refX⟩ := evalRows_read inputEval readA
    obtain ⟨y, readY, refY⟩ := evalRows_read inputEval readB
    have reflected := NativeAIR.emitMul_reflects values row selectorEval refX refY reads
    have indexed : AIR.emitOp row s r (.mul a b) inputs = AIR.emitOp row s 0 (.mul 0 1) #[x, y] := by
      simp only [AIR.emitOp, readX, readY, show #[x, y][0]? = some x from rfl,
        show #[x, y][1]? = some y from rfl, bind, Option.bind_some]
    rw [indexed]
    have total : ∃ result, AIR.emitOp row s 0 (.mul 0 1) #[x, y] = some result := by
      simp only [AIR.emitOp, show #[x, y][0]? = some x from rfl,
        show #[x, y][1]? = some y from rfl, bind, Option.bind_some]
      split <;> exact ⟨_, rfl⟩
    obtain ⟨result, resultEq⟩ := total
    exact ⟨result, resultEq, (fromScalar_eval _ _).trans (reflected.trans resultEq)⟩
  | eqZero index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i input read
    cases emitted
    obtain ⟨value, readValue, refValue⟩ := evalRows_read inputEval read
    have reflected := NativeAIR.emitEqZero_reflects values row selectorEval refValue reads
    have indexed : AIR.emitOp row s r (.eqZero index) inputs = AIR.emitOp row s 0 (.eqZero 0) #[value] := by
      simp only [AIR.emitOp, readValue, show #[value][0]? = some value from rfl, bind, Option.bind_some]
    rw [indexed]
    have total : ∃ result, AIR.emitOp row s 0 (.eqZero 0) #[value] = some result := by
      simp only [AIR.emitOp, show #[value][0]? = some value from rfl, bind, Option.bind_some]
      split <;> exact ⟨_, rfl⟩
    obtain ⟨result, resultEq⟩ := total
    exact ⟨result, resultEq, (fromScalar_eval _ _).trans (reflected.trans resultEq)⟩
  | call function indices size unconstrained =>
    cases unconstrained with
    | true =>
      cases emitted
      exact ⟨_, rfl, emitAdvice_reflects values row first size reads⟩
    | false =>
      simp only [emitOp, Bool.false_eq_true, if_false, bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      rename_i arguments selected
      cases emitted
      obtain ⟨args, argsRead, argsEval⟩ := select_reflects inputEval selected
      refine ⟨_, ?_, emitCall_reflects values row first function size selectorEval rankEval argsEval reads⟩
      simp only [AIR.emitOp, Bool.false_eq_true, if_false, select_values argsRead,
        bind, Option.bind_some, pure]
  | store indices =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i contents selected
    cases emitted
    obtain ⟨stored, storedRead, storedEval⟩ := select_reflects inputEval selected
    have size : contents.size = indices.size := array_mapM_size selected
    have read : (values.columns .main .current)[first]? = some (row 0) := by
      simpa only [Nat.add_zero] using reads 0 (by change 0 < 1; decide)
    refine ⟨_, ?_, emitStore_reflects values row first storedEval read⟩
    simp only [AIR.emitOp, select_values storedRead, bind, Option.bind_some, pure, size]
    rfl
  | load size index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i pointer read
    cases emitted
    obtain ⟨address, addressRead, addressRef⟩ := evalRows_read inputEval read
    refine ⟨_, ?_, emitLoad_reflects values row first size addressRef reads⟩
    simp only [AIR.emitOp, addressRead, bind, Option.bind_some, pure]
  | assertEq xs ys message =>
    simp only [emitOp] at emitted
    split at emitted
    · cases emitted
    rename_i size
    have same : xs.size = ys.size := Classical.not_not.mp size
    simp only [bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left selectedLeft
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right selectedRight
    cases emitted
    obtain ⟨a, readA, evalA⟩ := select_reflects inputEval selectedLeft
    obtain ⟨b, readB, evalB⟩ := select_reflects inputEval selectedRight
    have leftSize := array_mapM_size selectedLeft
    have rightSize := array_mapM_size selectedRight
    have resultSize : (AIR.rowValues a).size = left.size := by
      simpa only [AIR.rowValues, Array.size_map] using array_mapM_size evalA
    refine ⟨_, ?_, emitAssert_reflects selectorEval evalA evalB (by omega)⟩
    simp only [AIR.emitOp, same, ne_eq, not_true_eq_false, if_false,
      select_values readA, select_values readB, bind, Option.bind_some, pure]
    rw [list_ofFn_getD_pair (AIR.rowValues a) (AIR.rowValues b) 0 0 (fun x y => s * (x - y)) resultSize]
  | ioGetInfo | ioRead | unconstrainedBigUintDivMod | unconstrainedGToBytes | unconstrainedGInverse =>
    cases emitted
    exact ⟨_, rfl, emitAdvice_reflects values row first _ reads⟩
  | ioSetInfo | ioWrite | debug =>
    cases emitted
    exact ⟨_, rfl, empty_eval values⟩
  | u8BitDecomposition index => exact emitByte1_dispatch values row selector rank s r first .bits index inputEval emitted reads
  | u8ShiftLeft index => exact emitByte1_dispatch values row selector rank s r first .shiftLeft index inputEval emitted reads
  | u8ShiftRight index => exact emitByte1_dispatch values row selector rank s r first .shiftRight index inputEval emitted reads
  | u8Xor a b => exact emitByte2_dispatch values row selector rank s r first .xor a b inputEval normal emitted reads
  | u8Add a b => exact emitByte2_dispatch values row selector rank s r first .add a b inputEval normal emitted reads
  | u8Sub a b => exact emitByte2_dispatch values row selector rank s r first .sub a b inputEval normal emitted reads
  | u8And a b => exact emitByte2_dispatch values row selector rank s r first .and a b inputEval normal emitted reads
  | u8Or a b => exact emitByte2_dispatch values row selector rank s r first .or a b inputEval normal emitted reads
  | u8LessThan a b => exact emitByte2_dispatch values row selector rank s r first .lessThan a b inputEval normal emitted reads
  | u8RangeCheck a b => exact emitByte2_dispatch values row selector rank s r first .range a b inputEval normal emitted reads
  | u8Mul a b => exact emitByte2_dispatch values row selector rank s r first .mul a b inputEval normal emitted reads
  | u8XorSplit7 a b => exact emitByte2_dispatch values row selector rank s r first .split7 a b inputEval normal emitted reads
  | u8XorSplit4 a b => exact emitByte2_dispatch values row selector rank s r first .split4 a b inputEval normal emitted reads
  | u32LessThan a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i left readA
    dsimp only at emitted
    split at emitted
    · cases emitted
    rename_i right readB
    cases emitted
    obtain ⟨x, readX, refX⟩ := evalRows_read inputEval readA
    obtain ⟨y, readY, refY⟩ := evalRows_read inputEval readB
    refine ⟨_, ?_, emitU32LessThan_reflects values row first selectorEval refX refY reads⟩
    simp only [AIR.emitOp, AIR.emitU32LessThan, readX, readY, bind, Option.bind_some, pure]
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
    obtain ⟨x, readX, refX⟩ := readWord_reflects inputEval readA
    obtain ⟨y, readY, refY⟩ := readWord_reflects inputEval readB
    refine ⟨_, ?_, emitWordSum_reflects values row first (RowExpr.add_reflects values refX refY) reads⟩
    simp only [AIR.emitOp, AIR.emitU32Add, readX, readY, bind, Option.bind_some, pure]
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
    obtain ⟨x, readX, refX⟩ := readWord_reflects inputEval readA
    obtain ⟨y, readY, refY⟩ := readWord_reflects inputEval readB
    obtain ⟨z, readZ, refZ⟩ := readWord_reflects inputEval readC
    refine ⟨_, ?_, emitWordSum_reflects values row first
      (RowExpr.add_reflects values (RowExpr.add_reflects values refX refY) refZ) reads⟩
    simp only [AIR.emitOp, AIR.emitU32Add, readX, readY, readZ,
      Option.map_some, bind, Option.bind_some, pure]
  | u32ToField indices =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i word read
    cases emitted
    obtain ⟨value, readValue, refValue⟩ := readWord_reflects inputEval read
    refine ⟨{ outputs := #[value] }, ?_, ?_⟩
    · simp only [AIR.emitOp, readValue, bind, Option.bind_some, pure]
    · rw [fromScalar_eval]
      exact ScalarEmission.eval_of values refValue rfl

theorem emitByte1_dispatch_normal (selector rank : Expr) (first : Nat)
    (kind : AIR.Byte1Kind) (index : Nat) {rows : Array RowExpr} {emission : Emission}
    (emitted : emitOp selector rank first (kind.op index) rows = some emission) :
    Normal emission.outputs := by
  rw [emitOp_byte1] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  cases emitted
  exact advice_normal _ _

theorem emitByte2_dispatch_normal (selector rank : Expr) (first : Nat)
    (kind : AIR.Byte2Kind) (a b : Nat) {rows : Array RowExpr} {emission : Emission}
    (normal : Normal rows)
    (emitted : emitOp selector rank first (kind.op a b) rows = some emission) :
    Normal emission.outputs := by
  rw [emitOp_byte2] at emitted
  simp only [bind, Option.bind] at emitted
  split at emitted
  · cases emitted
  rename_i left readA
  dsimp only at emitted
  split at emitted
  · cases emitted
  rename_i right readB
  cases emitted
  exact emitByte2_normal _ _ (normal.read readA) (normal.read readB)

theorem emitOp_normal {selector rank : Expr} {first : Nat} {op : Bytecode.Op}
    {rows : Array RowExpr} {emission : Emission} (normal : Normal rows)
    (emitted : emitOp selector rank first op rows = some emission) :
    Normal emission.outputs := by
  cases op with
  | const value =>
    cases emitted
    exact normal_singleton rfl
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
    apply normal_singleton
    first
    | exact Expr.frontAdd_noConstantNegs (normal.read readA) (normal.read readB)
    | exact Expr.frontSub_noConstantNegs (normal.read readA) (normal.read readB)
    | exact NativeAIR.emitMul_noConstantNegs selector first (normal.read readA) (normal.read readB)
  | eqZero index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact normal_singleton (NativeAIR.emitEqZero_noConstantNegs _ _ _)
  | call function indices size unconstrained =>
    cases unconstrained with
    | true =>
      cases emitted
      exact advice_normal _ _
    | false =>
      simp only [emitOp, Bool.false_eq_true, if_false, bind, Option.bind] at emitted
      split at emitted
      · cases emitted
      cases emitted
      exact advice_normal _ _
  | store indices | load size index =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact advice_normal _ _
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
    exact normal_empty
  | ioGetInfo | ioRead | unconstrainedBigUintDivMod | unconstrainedGToBytes | unconstrainedGInverse =>
    cases emitted
    exact advice_normal _ _
  | ioSetInfo | ioWrite | debug =>
    cases emitted
    exact normal_empty
  | u8BitDecomposition index => exact emitByte1_dispatch_normal selector rank first .bits index emitted
  | u8ShiftLeft index => exact emitByte1_dispatch_normal selector rank first .shiftLeft index emitted
  | u8ShiftRight index => exact emitByte1_dispatch_normal selector rank first .shiftRight index emitted
  | u8Xor a b => exact emitByte2_dispatch_normal selector rank first .xor a b normal emitted
  | u8Add a b => exact emitByte2_dispatch_normal selector rank first .add a b normal emitted
  | u8Sub a b => exact emitByte2_dispatch_normal selector rank first .sub a b normal emitted
  | u8And a b => exact emitByte2_dispatch_normal selector rank first .and a b normal emitted
  | u8Or a b => exact emitByte2_dispatch_normal selector rank first .or a b normal emitted
  | u8LessThan a b => exact emitByte2_dispatch_normal selector rank first .lessThan a b normal emitted
  | u8RangeCheck a b => exact emitByte2_dispatch_normal selector rank first .range a b normal emitted
  | u8Mul a b => exact emitByte2_dispatch_normal selector rank first .mul a b normal emitted
  | u8XorSplit7 a b => exact emitByte2_dispatch_normal selector rank first .split7 a b normal emitted
  | u8XorSplit4 a b => exact emitByte2_dispatch_normal selector rank first .split4 a b normal emitted
  | u32LessThan a b =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    dsimp only at emitted
    split at emitted
    · cases emitted
    cases emitted
    exact emitU32LessThan_normal _ _ _ _
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
    exact emitWordSum_normal _ (Expr.frontAdd_noConstantNegs
      (readWord_normal normal readA) (readWord_normal normal readB))
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
    exact emitWordSum_normal _ (Expr.frontAdd_noConstantNegs
      (Expr.frontAdd_noConstantNegs (readWord_normal normal readA) (readWord_normal normal readB))
      (readWord_normal normal readC))
  | u32ToField indices =>
    simp only [emitOp, bind, Option.bind] at emitted
    split at emitted
    · cases emitted
    rename_i word read
    cases emitted
    exact normal_singleton (readWord_normal normal read)

end Aiur.NativeAIR.OpEmitter
