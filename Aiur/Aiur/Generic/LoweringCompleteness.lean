import Aiur.Generic.BuiltinFacts
import Aiur.Generic.UpdateFacts
import Aiur.Generic.PatternLoweringFacts
import Aiur.Generic.OpenSource
import Aiur.Generic.ArrayFacts
import Aiur.Generic.SliceFacts
import Aiur.Generic.StructFacts

namespace Aiur.Generic
open SourceSemantics PatternLowering

/-- Expression lowering preserves native evaluation with function calls left
as premises. Recursion is handled separately by induction on the finite source
derivation; this lemma does not assume that recursive calls terminate. -/
theorem lowering_complete [Field F] [DecidableEq F]
    {source : SourceSemantics.World F} {core : Engine.World F} {calls : CallRelation F}
    (typed : core.typed = source.typed)
    (evaluated : OpenSource.EvalExpr source calls types locals expr before result after)
    (safe : expr.lowerSafe types) :
    OpenCore.EvalExpr core calls locals (expr.lower types) before result after := by
  induction evaluated using OpenSource.EvalExpr.rec
    (motive_2 := fun types locals exprs before values after _ =>
      (∀ e ∈ exprs, e.lowerSafe types) →
        OpenCore.EvalArgs core calls locals (exprs.map (Expr.lower types)) before values after)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ => True) with
  | block | blockExit => simp [Expr.lowerSafe] at safe
  | literal => simpa only [Expr.lower] using (OpenCore.EvalExpr.literal (world := core) (calls := calls))
  | var found => rw [Expr.lower]; exact OpenCore.EvalExpr.var found
  | global => simp [Expr.lowerSafe] at safe
  | tuple _ ih | array _ ih =>
      rw [Expr.lower]
      exact OpenCore.EvalExpr.tuple (ih (by simpa only [Expr.lowerSafe] using safe))
  | «repeat» _ ih =>
      rw [Expr.lower]
      exact ArrayLowering.repeatValue_iff.mpr ⟨_, ih (by simpa only [Expr.lowerSafe] using safe), rfl⟩
  | index _ projected ih | project _ projected ih =>
      rw [Expr.lower]
      exact OpenCore.EvalExpr.project (ih (by simpa only [Expr.lowerSafe] using safe)) projected
  | @slice types locals expr before input after start stop result _ sliced ih =>
      cases stop with
      | none => simp [Expr.lowerSafe] at safe
      | some stop =>
          rw [Expr.lowerSafe] at safe
          obtain ⟨values, projected, rfl⟩ := ArrayLowering.projects_of_source_slice sliced
          rw [Expr.lower]
          exact ArrayLowering.sliceValue_iff.mpr
            ⟨input, values, ih safe.2, projected, rfl⟩
  | builtin _ builtind ih =>
      rw [Expr.lower]
      exact BuiltinLowering.expression_iff.mpr ⟨_, ih (by simpa only [Expr.lowerSafe] using safe), builtind⟩
  | update _ updated ih =>
      rw [Expr.lower]
      exact UpdateLowering.expression_iff.mpr ⟨_, ih (by simpa only [Expr.lowerSafe] using safe), updated⟩
  | record _ ih =>
      rw [Expr.lower]
      exact StructLowering.record_iff.mpr ⟨_, ih (by simpa only [Expr.lowerSafe] using safe), rfl⟩
  | member _ projected ih =>
      rw [Expr.lowerSafe] at safe
      rw [Expr.lower]
      exact (StructLowering.member_iff safe.2).mpr ⟨_, ih safe.1, projected⟩
  | construct _ ih =>
      rw [Expr.lower]
      exact OpenCore.EvalExpr.construct (ih (by simpa only [Expr.lowerSafe] using safe))
  | constructAs _ ih =>
      rw [Expr.lower]
      exact OpenCore.EvalExpr.construct (ih (by simpa only [Expr.lowerSafe] using safe))
  | letValue _ matched _ valueIH bodyIH =>
      rw [Expr.lowerSafe] at safe
      obtain ⟨valueSafe, bodySafe, patternSafe⟩ := safe
      rw [Expr.lower]
      exact (lowerLet_open_iff _ _ _ _ patternSafe source.constant source.constDepth _ _ _ _).mpr
        ⟨_, _, _, valueIH valueSafe, matched, bodyIH bodySafe⟩
  | store _ ih => rw [Expr.lower]; exact OpenCore.EvalExpr.store (ih (by simpa only [Expr.lowerSafe] using safe))
  | load _ loaded ih => rw [Expr.lower]; exact OpenCore.EvalExpr.load (ih (by simpa only [Expr.lowerSafe] using safe)) loaded
  | hint _ formed ih =>
      rw [Expr.lower]
      exact OpenCore.EvalExpr.hint (ih (by simpa only [Expr.lowerSafe] using safe)) (by rw [typed]; exact formed)
  | neg _ operation ih => rw [Expr.lower]; exact OpenCore.EvalExpr.neg (ih (by simpa only [Expr.lowerSafe] using safe)) operation
  | binary _ _ operation leftIH rightIH =>
      rw [Expr.lowerSafe] at safe
      rw [Expr.lower]
      exact OpenCore.EvalExpr.binary (leftIH safe.1) (rightIH safe.2) operation
  | call _ callee argsIH =>
      rw [Expr.lower]
      exact OpenCore.EvalExpr.call (argsIH (by simpa only [Expr.lowerSafe] using safe)) callee
  | @matchValue types locals expr before input middle arms bindings body result after _ selected _ valueIH bodyIH =>
      rw [Expr.lowerSafe] at safe
      obtain ⟨valueSafe, armsSafe, patternSafe⟩ := safe
      have chosen : choose source.constant source.constDepth types middle input arms = .ok (some (bindings, body)) := by
        rw [choose_source]; exact selected
      obtain ⟨pat, member⟩ := choose_member chosen
      rw [Expr.lower]
      apply (lowerMatch_open_iff _ _ _ patternSafe source.constant source.constDepth _ _ _ _).mpr
      refine ⟨input, middle, bindings, body.lower types, valueIH valueSafe, ?_, bodyIH (armsSafe _ member)⟩
      rw [choose_map, chosen]
      rfl
  | nil => exact .nil
  | cons _ _ headIH tailIH =>
      rename_i safe
      exact .cons (headIH (safe _ (by simp))) (tailIH (fun e he => safe e (by simp [he])))
  | _ => trivial

end Aiur.Generic
