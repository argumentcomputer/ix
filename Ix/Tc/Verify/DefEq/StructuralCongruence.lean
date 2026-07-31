import Ix.Tc.Verify.DefEq.SameHeadSpine

/-!
# Post-delta structural congruence

This helper recognizes equal constant instances and de Bruijn variables
directly.  Matching projections delegate to the bounded projection-delta
loop through an exact contract over the concrete projected sources.  All
other shapes and all failed guards return `false` without a completeness
claim.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Finite universe support for constant nodes selected by structural
congruence. -/
structure StructuralCongruenceResources (support : RunSupport) : Prop where
  universes : ∀ {id : KId .anon} {levels : Array (KUniv .anon)}
      {info : ExprInfo .anon},
    support (.const id levels info) →
      ∀ level, level ∈ levels.toList →
        support.univ level ∧ level.size < UInt64.size

namespace RecM

/-- Soundness boundary for the exact bounded projection-delta helper.  The
contract is indexed by translations of the two concrete projection nodes;
it cannot authorize an unrelated projection or field. -/
def LazyDeltaProjReduction.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state id field left right leftInfo rightInfo leftV rightV},
    support (.prj id field left leftInfo) →
    support (.prj id field right rightInfo) →
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj id field left leftInfo) leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.prj id field right rightInfo) rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (lazyDeltaProjReduction id field left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Exact positive-result contract for `tryStructuralCongruence`. -/
def TryStructuralCongruence.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryStructuralCongruence left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Exhaustive execution proof of post-delta structural congruence. -/
theorem tryStructuralCongruence_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (collision : support.CollisionFree)
    (resources : StructuralCongruenceResources support)
    (projection : LazyDeltaProjReduction.WFAt layer semantics trProj world
      support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryStructuralCongruence left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  cases left <;> cases right <;> simp only [tryStructuralCongruence]
  all_goals
    first
    | exact RecM.WF.pure fun _ h => by contradiction
    | skip
  · rename_i leftIdx leftName leftInfo rightIdx rightName rightInfo
    exact RecM.WF.pure fun hI hanswer => by
      have hidx : leftIdx = rightIdx := eq_of_beq hanswer
      subst rightIdx
      have hleftWF := hleft.wf world.venvWF.ordered theory.literalWF
        theory.projections.wf hI.2.1.wf
      cases hleft with
      | var hleftLookup =>
          cases hright with
          | var hrightLookup =>
              have hp := Option.some.inj
                (hleftLookup.symm.trans hrightLookup)
              have hvalue : leftV = rightV := congrArg Prod.fst hp
              subst rightV
              exact Lean4Lean.VEnv.IsDefEqU.refl hleftWF
  · rename_i leftId leftLevels leftInfo rightId rightLevels rightInfo
    exact RecM.WF.pure fun _ hanswer => by
      obtain ⟨hid, hlevels⟩ := Bool.and_eq_true_iff.mp hanswer
      exact constantHeadsDefEq collision
        (resources.universes hleftSupport)
        (resources.universes hrightSupport)
        hleft hright hid hlevels
  · rename_i leftId leftField leftValue leftInfo rightId rightField
      rightValue rightInfo
    cases hguard :
        (leftId.addr != rightId.addr || leftField != rightField) with
    | true =>
        simp only [if_true]
        exact RecM.WF.pure fun _ h => by contradiction
    | false =>
        simp only [Bool.false_eq_true, if_false]
        obtain ⟨hid, hfield⟩ := Bool.or_eq_false_iff.mp hguard
        have hid' : leftId = rightId :=
          KId.anon_eq_of_addr_eq <| eq_of_beq
            (show (leftId.addr == rightId.addr) = true by simpa using hid)
        have hfield' : leftField = rightField := eq_of_beq
          (show (leftField == rightField) = true by simpa using hfield)
        subst rightId
        subst rightField
        exact projection hleftSupport hrightSupport hleft hright

namespace TryStructuralCongruence

/-- Package the exhaustive helper proof for the stopped lazy-delta
continuation. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (collision : support.CollisionFree)
    (resources : StructuralCongruenceResources support)
    (projection : LazyDeltaProjReduction.WFAt layer semantics trProj world
      support uvars) :
    TryStructuralCongruence.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryStructuralCongruence_wf theory collision resources projection
    hleftSupport hrightSupport hleft hright

end TryStructuralCongruence

end RecM

end Ix.Tc
