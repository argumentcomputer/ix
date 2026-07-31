import Ix.Tc.Verify.DefEq.FinalWhnf.Application
import Ix.Tc.Verify.DefEq.FinalWhnf.LetDeclaration

/-!
# Final-WHNF structural prefix

This module covers every constructor pair in `tryDefEqWhnfStructural`.
Sorts, variables, constants, applications, binders, and literal pairs are
proved directly.  The let-declaration scope is kept as its exact lower
contract so its allocation and dual-body opening proof can be discharged in
isolation.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Concrete resources for the constructor-directed final comparison. -/
structure FinalWhnfStructuralResources
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) : Prop where
  theory : WhnfTheory trProj world uvars
  collision : support.CollisionFree
  sorts : SortComponentResources support
  quick : QuickDefEqResources support
  constants : StructuralCongruenceResources support
  applications : FinalWhnfApplicationResources support
  lets : FinalWhnfLetResources support

/-- Exhaustive constructor-prefix proof. -/
theorem tryDefEqWhnfStructural_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (resources : FinalWhnfStructuralResources layer semantics trProj world
      support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfStructural left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  cases left <;> cases right <;>
    simp only [tryDefEqWhnfStructural]
  all_goals
    first
    | exact RecM.WF.pure fun _ => trivial
    | skip
  · rename_i leftIdx leftName leftInfo rightIdx rightName rightInfo
    cases hidx : leftIdx == rightIdx with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact RecM.WF.pure fun _ => trivial
    | true =>
        simp only [if_true]
        exact RecM.WF.pure fun hI _ => by
          have hsameIdx : leftIdx = rightIdx := eq_of_beq hidx
          subst rightIdx
          have hleftWF := hleft.wf world.venvWF.ordered
            resources.theory.literalWF
            resources.theory.projections.wf hI.2.1.wf
          cases hleft with
          | var hleftLookup =>
              cases hright with
              | var hrightLookup =>
                  have hp := Option.some.inj
                    (hleftLookup.symm.trans hrightLookup)
                  have hvalue : leftV = rightV := congrArg Prod.fst hp
                  subst rightV
                  exact Lean4Lean.VEnv.IsDefEqU.refl hleftWF
  · rename_i leftU leftInfo rightU rightInfo
    cases hleft with
    | sort hleftWF =>
        cases hright with
        | sort hrightWF =>
            obtain ⟨hleftSize, hleftSubterms⟩ :=
              resources.sorts hleftSupport
            obtain ⟨hrightSize, hrightSubterms⟩ :=
              resources.sorts hrightSupport
            exact RecM.WF.pure fun _ heq =>
              ⟨_, .sortDF hleftWF hrightWF <|
                univEq_sound
                  (resources.collision.univ.addrFaithful
                    (hleftSubterms leftU .refl)
                    (hrightSubterms rightU .refl))
                  hleftSize hrightSize heq⟩
  · rename_i leftId leftLevels leftInfo rightId rightLevels rightInfo
    cases hguard :
        (leftId.addr == rightId.addr &&
          sameDefEqUniverses leftLevels rightLevels) with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact RecM.WF.pure fun _ => trivial
    | true =>
        simp only [if_true]
        exact RecM.WF.pure fun _ _ => by
          obtain ⟨hid, hlevels⟩ := Bool.and_eq_true_iff.mp hguard
          exact constantHeadsDefEq resources.collision
            (resources.constants.universes hleftSupport)
            (resources.constants.universes hrightSupport)
            hleft hright hid hlevels
  · rename_i leftFn leftArg leftInfo rightFn rightArg rightInfo
    simpa only [bind_pure] using
      (TryDefEqWhnfApp.ofResources resources.applications
        hleftSupport hrightSupport hleft hright)
  · apply RecM.WF.bind <| by
      simpa only [quickDefEq] using
        (quickDefEq_wf resources.theory resources.collision resources.sorts
          resources.quick hleftSupport hrightSupport hleft hright)
    intro answer after hanswer
    cases answer with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact RecM.WF.pure fun _ => trivial
    | true =>
        simp only [if_true]
        exact RecM.WF.pure fun _ => hanswer
  · apply RecM.WF.bind <| by
      simpa only [quickDefEq] using
        (quickDefEq_wf resources.theory resources.collision resources.sorts
          resources.quick hleftSupport hrightSupport hleft hright)
    intro answer after hanswer
    cases answer with
    | false =>
        simp only [Bool.false_eq_true, if_false]
        exact RecM.WF.pure fun _ => trivial
    | true =>
        simp only [if_true]
        exact RecM.WF.pure fun _ => hanswer
  · rename_i leftName leftTy leftVal leftBody leftNondep leftInfo
      rightName rightTy rightVal rightBody rightNondep rightInfo
    simpa only [bind_pure] using
      (TryDefEqWhnfLet.ofResources resources.theory resources.collision
        resources.lets hleftSupport hrightSupport hleft hright)
  · rename_i leftNat leftBlob leftInfo rightNat rightBlob rightInfo
    cases hvalue : leftNat == rightNat with
    | false =>
        exact RecM.WF.pure fun _ h => by contradiction
    | true =>
        exact RecM.WF.pure fun hI _ => by
          have hsame : leftNat = rightNat := eq_of_beq hvalue
          subst rightNat
          have hleftWF := hleft.wf world.venvWF.ordered
            resources.theory.literalWF resources.theory.projections.wf
            hI.2.1.wf
          cases hleft
          cases hright
          exact Lean4Lean.VEnv.IsDefEqU.refl hleftWF
  · rename_i leftString leftBlob leftInfo rightString rightBlob rightInfo
    cases hvalue : leftString == rightString with
    | false =>
        exact RecM.WF.pure fun _ h => by contradiction
    | true =>
        exact RecM.WF.pure fun hI _ => by
          have hsame : leftString = rightString := eq_of_beq hvalue
          subst rightString
          have hleftWF := hleft.wf world.venvWF.ordered
            resources.theory.literalWF resources.theory.projections.wf
            hI.2.1.wf
          cases hleft
          cases hright
          exact Lean4Lean.VEnv.IsDefEqU.refl hleftWF

namespace TryDefEqWhnfStructural

/-- Package the constructor-prefix proof. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (resources : FinalWhnfStructuralResources layer semantics trProj world
      support uvars) :
    TryDefEqWhnfStructural.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqWhnfStructural_wf resources hleftSupport hrightSupport hleft
    hright

end TryDefEqWhnfStructural

end RecM

end Ix.Tc
