import Ix.CompileCert.ExpressionLeaves

/-! Source-index preservation from the executed expression guards. Bound
variables, projection fields and mutual-reference slots cannot silently wrap
to a different UInt64. The actual successful runs supply their own range
proofs. Overflowing fresh variables/projections fail before mutating state. -/

namespace Ix.CompileCert.ExpressionIndices

open Ix.CompileM Ix.CompileCert.HeadWriterFrame

theorem bvar_step_refuses (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (index : Nat) (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (large : UInt64.size ≤ index) :
    rawRun (compileExprTotalStep compile (.bvar index hash)) context before =
      (.error (.resourceLimit s!"bound variable table index {index} exceeds the Ixon UInt64 range"), before) := by
  simp only [compileExprTotalStep, checkedTableIndex, Nat.not_lt.mpr large, ↓reduceIte, rawRun_bind]
  rfl

theorem projection_step_refuses (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) (large : UInt64.size ≤ field) :
    rawRun (compileExprTotalStep compile (.proj name field source hash)) context before =
      (.error (.resourceLimit s!"projection field table index {field} exceeds the Ixon UInt64 range"), before) := by
  simp only [compileExprTotalStep, checkedTableIndex, Nat.not_lt.mpr large, ↓reduceIte, rawRun_bind]
  rfl

theorem bvar_step_bound (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (index : Nat) (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    {value : Ixon.Expr × UInt64}
    (success : (rawRun (compileExprTotalStep compile (.bvar index hash)) context before).1 = .ok value) :
    index < UInt64.size := by
  by_contra large
  rw [bvar_step_refuses compile index hash context before (Nat.le_of_not_gt large)] at success
  cases success

theorem projection_step_bound (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState) {value : Ixon.Expr × UInt64}
    (success : (rawRun (compileExprTotalStep compile (.proj name field source hash)) context before).1 = .ok value) :
    field < UInt64.size := by
  by_contra large
  rw [projection_step_refuses compile name field source hash context before (Nat.le_of_not_gt large)] at success
  cases success

/-- A successful actual bound-variable step reads as its full source index.
The range premise used by the earlier leaf lemma now follows from execution. -/
theorem bvar_step_read (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (index : Nat) (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    {value : Ixon.Expr × UInt64} {after : BlockState}
    (ran : rawRun (compileExprTotalStep compile (.bvar index hash)) context before = (.ok value, after))
    (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name) :
    (ExpressionRead.blockReader reader base param self after).read value.1 = .ok (.bvar index) ∧
      ExpressionLeaves.withoutExprMetadata after = ExpressionLeaves.withoutExprMetadata before := by
  have bounded := bvar_step_bound compile index hash context before (congrArg Prod.fst ran)
  obtain ⟨actual, state, emitted, reading, frame⟩ :=
    ExpressionLeaves.bvar_step_total_read compile index hash context before bounded reader base param self
  have equal := Prod.mk.inj (emitted.symm.trans ran)
  have sameValue := Except.ok.inj equal.1
  cases sameValue
  cases equal.2
  exact ⟨reading, frame⟩

theorem bind_success {action : CompileM α} {next : α → CompileM β}
    {context : CompileEnv × BlockEnv} {before : BlockState} {value : β}
    (success : (rawRun (action >>= next) context before).1 = .ok value) :
    ∃ first middle, rawRun action context before = (.ok first, middle) ∧
      (rawRun (next first) context middle).1 = .ok value := by
  rw [rawRun_bind] at success
  cases ran : rawRun action context before with
  | mk outcome middle =>
    rw [ran] at success
    cases outcome with
    | error error => cases success
    | ok first => exact ⟨first, middle, rfl, success⟩

/-- A successful recursive constant occurrence has a representable mutual
slot. Earlier universe/name effects may fail first; success cannot bypass
the actual slot check. -/
theorem mutual_slot_bound (name : Ix.Name) (levels : Array Ix.Level) (context : CompileEnv × BlockEnv)
    (before : BlockState) {index : Nat} (found : context.2.mutCtx.get? name = some index)
    {value : Ixon.Expr × UInt64}
    (success : (rawRun (compileConstExprRaw name levels) context before).1 = .ok value) : index < UInt64.size := by
  unfold compileConstExprRaw at success
  obtain ⟨block, state, readBlock, success⟩ := bind_success success
  have same : block = context.2 := by
    rw [UniverseMeaning.rawRun_readBlock] at readBlock
    exact (Except.ok.inj (Prod.mk.inj readBlock).1).symm
  have sameState : state = before := by
    rw [UniverseMeaning.rawRun_readBlock] at readBlock
    exact (Prod.mk.inj readBlock).2.symm
  subst block
  subst state
  obtain ⟨compiled, middle, _, success⟩ := bind_success success
  obtain ⟨_done, named, _, success⟩ := bind_success success
  dsimp only at success
  rw [found] at success
  obtain ⟨slot, afterCheck, checked, _⟩ := bind_success success
  exact (Interning.checkedTableIndex_value "mutual reference" index context named (congrArg Prod.fst checked)).2

theorem constant_step_eq (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (levels : Array Ix.Level) (hash : Address) :
    compileExprTotalStep compile (.const name levels hash) = compileConstExprRaw name levels := rfl

theorem mutual_step_bound (compile : Ix.Expr → CompileM (Ixon.Expr × UInt64))
    (name : Ix.Name) (levels : Array Ix.Level) (hash : Address) (context : CompileEnv × BlockEnv)
    (before : BlockState) {index : Nat} (found : context.2.mutCtx.get? name = some index)
    {value : Ixon.Expr × UInt64}
    (success : (rawRun (compileExprTotalStep compile (.const name levels hash)) context before).1 = .ok value) :
    index < UInt64.size := by
  rw [constant_step_eq] at success
  exact mutual_slot_bound name levels context before found success

theorem partial_step_error (source : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState)
    (missing : before.exprCache.get? source = none) {error : CompileError} {after : BlockState}
    (failed : rawRun (compileExprTotalStep compileExprPartial source) context before = (.error error, after)) :
    rawRun (compileExprPartial source) context before = (.error error, after) := by
  rw [ExpressionRuntime.partial_unfold]
  simp only [ExpressionRuntime.cached, rawRun_bind, rawRun_get, missing, failed]

theorem bvar_miss_refuses (index : Nat) (hash : Address) (context : CompileEnv × BlockEnv) (before : BlockState)
    (missing : before.exprCache.get? (Ix.Expr.bvar index hash) = none) (large : UInt64.size ≤ index) :
    rawRun (compileExprPartial (.bvar index hash)) context before =
      (.error (.resourceLimit s!"bound variable table index {index} exceeds the Ixon UInt64 range"), before) :=
  partial_step_error _ context before missing (bvar_step_refuses compileExprPartial index hash context before large)

theorem projection_miss_refuses (name : Ix.Name) (field : Nat) (source : Ix.Expr) (hash : Address)
    (context : CompileEnv × BlockEnv) (before : BlockState)
    (missing : before.exprCache.get? (Ix.Expr.proj name field source hash) = none) (large : UInt64.size ≤ field) :
    rawRun (compileExprPartial (.proj name field source hash)) context before =
      (.error (.resourceLimit s!"projection field table index {field} exceeds the Ixon UInt64 range"), before) :=
  partial_step_error _ context before missing (projection_step_refuses compileExprPartial name field source hash context before large)

end Ix.CompileCert.ExpressionIndices

