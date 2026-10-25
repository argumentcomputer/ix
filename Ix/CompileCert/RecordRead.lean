import Ix.CompileCert.RecordState

/-! The ordinary subrun of the actual record-bearing expression compiler.
Its source remains literally e or substRecords records e; no source-form
erasure, admitted prefix or baseline origin is asserted. -/
namespace Ix.CompileCert.RecordRead
open Ix.CompileM Ix.CompileCert ExpressionState UniversePipeline
open Ix.Kernel (Mode LevelParam)
open Ix.Kernel.Reader (Ctx CName CExpr ReadM)

private def guardBody (records : Std.HashMap Nat (Nat × UInt64)) (n : Nat) (_ : PUnit) :
    CompileM (ForInStep PUnit) :=
  if records.contains n then pure (.yield PUnit.unit) else do
    let _ ← (throw (.invalidMutualBlock s!"Pass 3: call-site record {n} was not compiled") : CompileM Unit)
    pure (.yield PUnit.unit)

private theorem guardList (records : Std.HashMap Nat (Nat × UInt64)) (xs : List Nat)
    (context : CompileEnv × BlockEnv) : ∀ {before after : BlockState},
    rawRun (forIn xs PUnit.unit (guardBody records)) context before = (.ok PUnit.unit, after) →
    after = before ∧ ∀ n ∈ xs, records.contains n = true := by
  induction xs with
  | nil => intro before after ran; cases ran; exact ⟨rfl, by simp⟩
  | cons n ns ih =>
    intro before after ran
    rw [List.forIn_cons] at ran
    cases hit : records.contains n
    · simp [guardBody, hit, rawRun_bind, rawRun_throw] at ran
    · have tail : rawRun (forIn ns PUnit.unit (guardBody records)) context before = (.ok PUnit.unit, after) := by
        simpa [guardBody, hit] using ran
      obtain ⟨rfl, rest⟩ := ih tail
      exact ⟨rfl, by intro q h; rcases List.mem_cons.mp h with rfl | h; exact hit; exact rest q h⟩

inductive RecordInput (e : Ix.Expr) (context : CompileEnv × BlockEnv) (before : BlockState) :
    Ix.Expr → BlockState → Prop where
  | plain (empty : (p3Placeholders e).isEmpty = true) : RecordInput e context before e before
  | recorded (nonempty : (p3Placeholders e).isEmpty = false)
      (records : Std.HashMap Nat (Nat × UInt64)) (middle : BlockState)
      (ran : rawRun (compileRecords (p3Placeholders e)) context before = (.ok records, middle))
      (ready : ∀ n ∈ p3Placeholders e, records.contains n = true) :
      RecordInput e context before (substRecords records e) middle

/-- Invert the same run, including the actual complete-record guard. -/
theorem ordinary_subrun (e : Ix.Expr) (context : CompileEnv × BlockEnv)
    {before after : BlockState} {value : Ixon.Expr × UInt64}
    (ran : rawRun (compileExprWithRecords e) context before = (.ok value, after)) :
    ∃ lowered middle, RecordInput e context before lowered middle ∧
      rawRun (compileExprNoSurgery lowered) context middle = (.ok value, after) := by
  unfold compileExprWithRecords at ran
  dsimp only at ran
  split at ran
  · exact ⟨e, before, .plain (by assumption), ran⟩
  · rename_i notEmpty
    obtain ⟨records, middle, compiled, rest⟩ := bind_ok ran
    obtain ⟨u, same, checked, ordinary⟩ := bind_ok rest
    cases u
    have guarded : rawRun (forIn (p3Placeholders e).toList PUnit.unit (guardBody records)) context middle =
        (.ok PUnit.unit, same) := by
      unfold guardBody
      simpa only [Array.forIn_toList] using checked
    obtain ⟨sameEq, ready⟩ := guardList records _ context guarded
    subst same
    exact ⟨_, middle, .recorded (by simpa using notEmpty) records middle compiled
      (fun n h => ready n (by simpa using h)), ordinary⟩

/-- Read the literal source passed to the ordinary compiler through its own
final tables. Intermediate Good is derived from the actual record producer. -/
theorem withRecords_read {md : Mode} (cx : Ctx md) (param : Nat → LevelParam)
    (self : Nat → Option (ReadM (CName md))) (names : Ix.Name → CName md → Prop)
    (σ : Ix.Name → LevelParam) (bindings : Bindings) (context : CompileEnv × BlockEnv)
    (aligned : ∀ a, cx.blob a = context.1.blobs.get? a)
    (external : BindingsCorrect context.1 bindings cx names) (selfSound : SelfCorrect context.2 self names)
    (e : Ix.Expr) (before : BlockState)
    (good : Good cx param self (Related names (LevelMeaning context.2.univCtx σ param)) bindings before)
    {value : Ixon.Expr × UInt64} {after : BlockState}
    (ran : rawRun (compileExprWithRecords e) context before = (.ok value, after)) :
    ∃ lowered middle target, RecordInput e context before lowered middle ∧
      rawRun (compileExprNoSurgery lowered) context middle = (.ok value, after) ∧
      Related names (LevelMeaning context.2.univCtx σ param) lowered target ∧
      (ExpressionRead.blockReader cx param self after).read value.1 = .ok target := by
  obtain ⟨lowered, middle, input, ordinary⟩ := ordinary_subrun e context ran
  have middleGood : Good cx param self (Related names (LevelMeaning context.2.univCtx σ param))
      bindings middle := by
    cases input with
    | plain => exact good
    | recorded _ records middle compiled _ =>
      have kept := (RecordState.compileRecords_preserves aligned (p3Placeholders e)).good
        context.2 before good
      rw [compiled] at kept
      exact kept.1
  obtain ⟨target, rel, read⟩ := compileExprNoSurgery_read cx param self names σ bindings context
    aligned external selfSound lowered middle middleGood ordinary
  exact ⟨lowered, middle, target, input, ordinary, rel, read⟩

end Ix.CompileCert.RecordRead
