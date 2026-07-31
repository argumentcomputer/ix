import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts

/-!
# Structure-eta field comparison

This module verifies the named left-to-right field loop used by final-WHNF
structure eta.  Its inputs describe exactly the finitely many generated
projection nodes and constructor arguments selected by that loop.  A `true`
result retains a Theory equality for every compared field; malformed
structure metadata is not assumed here and remains the responsibility of the
outer constructor/classifier proof.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- The recursive field loop compares every requested projection with its
corresponding constructor field.  Projection existence is explicit because
`TrProjOK` provides closure and uniqueness, not construction of the concrete
projection relation. -/
theorem tryEtaStructFields_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {inductId : KId .anon} {numParams field fuel : Nat}
    {base : KExpr .anon} {args : Array (KExpr .anon)} {baseV : VExpr}
    (hcollision : support.CollisionFree)
    (hbase : TrKExprS world.venv uvars world.nameOf trProj Delta base baseV)
    (structName : Lean.Name)
    (hname : world.nameOf inductId.addr = some structName)
    (projectedV fieldV : Nat → VExpr)
    (hprojectionSupport : ∀ offset, offset < fuel →
      support (KExpr.mkPrj inductId (field + offset).toUInt64 base))
    (hfieldSupport : ∀ offset, offset < fuel →
      support args[numParams + field + offset]!)
    (hprojection : ∀ offset, offset < fuel →
      trProj Delta.toCtx structName (field + offset).toUInt64.toNat
        baseV (projectedV offset))
    (hfield : ∀ offset, offset < fuel →
      TrKExprS world.venv uvars world.nameOf trProj Delta
        args[numParams + field + offset]! (fieldV offset)) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryEtaStructFields inductId numParams base args fuel field)
      (fun answer _ => answer = true →
        ∀ offset, offset < fuel →
          world.venv.IsDefEqU uvars Delta.toCtx
            (projectedV offset) (fieldV offset)) := by
  induction fuel generalizing field state projectedV fieldV with
  | zero =>
      simp only [tryEtaStructFields]
      exact RecM.WF.pure fun _ _ offset hlt => by omega
  | succ remaining ih =>
      simp only [tryEtaStructFields]
      have hzero : 0 < remaining + 1 := by omega
      have hprojectionNode :
          KExpr.mkPrj inductId field.toUInt64 base =
            KExpr.mkPrj inductId (field + 0).toUInt64 base := by
        simp
      apply RecM.WF.bind <| RecM.WF.withInv <| RecM.WF.liftTcM <|
        TcM.intern_whnf_wf hcollision
          (hprojectionNode ▸ hprojectionSupport 0 hzero)
      intro projection afterIntern hprojectionPost
      rcases hprojectionPost with ⟨hIIntern, hprojectionEq, _⟩
      subst projection
      have hprojectionTr :
          TrKExprS world.venv uvars world.nameOf trProj Delta
            (KExpr.mkPrj inductId field.toUInt64 base) (projectedV 0) := by
        rw [KExpr.mkPrj_shape]
        exact .prj hname hbase (by simpa using hprojection 0 hzero)
      have hfieldNode : args[numParams + field]! =
          args[numParams + field + 0]! := by simp
      apply RecM.WF.bind <|
        RecM.isDefEqCall_wf
          (hprojectionNode ▸ hprojectionSupport 0 hzero)
          (hfieldNode ▸ hfieldSupport 0 hzero)
          hprojectionTr
          (hfieldNode ▸ hfield 0 hzero)
      intro equal afterEqual hequal
      cases equal with
      | false =>
          simp only [Bool.not_false, if_true]
          exact RecM.WF.pure fun _ htrue => by contradiction
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          apply RecM.WF.mono <|
            ih (state := afterEqual) (field := field + 1)
              (projectedV := fun offset => projectedV (offset + 1))
              (fieldV := fun offset => fieldV (offset + 1))
              (fun offset hlt => by
                simpa only [Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using
                    hprojectionSupport (offset + 1) (by omega))
              (fun offset hlt => by
                simpa only [Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using hfieldSupport (offset + 1) (by omega))
              (fun offset hlt => by
                simpa only [Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using hprojection (offset + 1) (by omega))
              (fun offset hlt => by
                simpa only [Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm] using hfield (offset + 1) (by omega))
          · intro answer final htail htrue offset hlt
            cases offset with
            | zero => exact hequal rfl
            | succ offset =>
                simpa only [Nat.succ_eq_add_one] using
                  htail htrue offset (by omega)
          · intro _ _ _
            trivial

end RecM

end Ix.Tc
