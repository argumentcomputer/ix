import Ix.Tc.Verify.DefEq.FinalWhnf.Contracts
import Ix.Tc.Verify.DefEq.StringLiteral

/-!
# Final-WHNF String-literal expansion

This module verifies the ordered, bidirectional String-expansion phase in the
final-WHNF comparator.  Each compact literal is expanded by the exact K1 plan,
whose result translates to the same Theory literal as the source syntax.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Once the syntax guard has found a String literal, both ordered expansion
attempts are sound.  A successful reverse attempt is flipped semantically. -/
theorem tryDefEqWhnfStringAfterGuard_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (context : DefEqStringContext trProj world support)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfStringAfterGuard left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryDefEqWhnfStringAfterGuard
  apply RecM.WF.bind <|
    tryStringLitExpansion_wf context hcanonical hleftSupport hrightSupport
      hleft hright
  intro accepted afterFirst hfirst
  cases accepted with
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => hfirst rfl
  | false =>
      simp only [Bool.false_eq_true, if_false]
      apply RecM.WF.bind <|
        tryStringLitExpansion_wf context hcanonical hrightSupport
          hleftSupport hright hleft
      intro reverseAccepted afterSecond hsecond
      cases reverseAccepted with
      | true =>
          simp only [if_true]
          exact RecM.WF.pure fun _ _ => (hsecond rfl).symm
      | false =>
          simp only [Bool.false_eq_true, if_false]
          exact RecM.WF.pure fun _ => trivial

/-- Exhaust the outer "either operand is a String literal" guard. -/
theorem tryDefEqWhnfString_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (context : DefEqStringContext trProj world support)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfString left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryDefEqWhnfString
  split
  · exact tryDefEqWhnfStringAfterGuard_wf context hcanonical hleftSupport
      hrightSupport hleft hright
  · exact RecM.WF.pure fun _ => trivial

namespace TryDefEqWhnfString

/-- Package the concrete String-literal phase. -/
theorem ofContext
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (context : DefEqStringContext trProj world support)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars) :
    TryDefEqWhnfString.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqWhnfString_wf context hcanonical hleftSupport hrightSupport
    hleft hright

end TryDefEqWhnfString

/-- Compose the optional String phase with the remaining final-WHNF tail. -/
theorem isDefEqWhnfAfterEta_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (hstring : TryDefEqWhnfString.WFAt layer semantics trProj world support
      uvars)
    (htail : IsDefEqWhnfAfterString.WFAt layer semantics trProj world support
      uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterEta left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqWhnfAfterEta
  apply RecM.WF.bind <|
    hstring hleftSupport hrightSupport hleft hright
  intro result afterString hresult
  cases result with
  | none => exact htail hleftSupport hrightSupport hleft hright
  | some answer => exact RecM.WF.pure fun _ => hresult

namespace IsDefEqWhnfAfterEta

/-- Package the String phase and its post-String continuation. -/
theorem ofString
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hstring : TryDefEqWhnfString.WFAt layer semantics trProj world support
      uvars)
    (htail : IsDefEqWhnfAfterString.WFAt layer semantics trProj world support
      uvars) :
    IsDefEqWhnfAfterEta.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact isDefEqWhnfAfterEta_wf hstring htail hleftSupport hrightSupport
    hleft hright

end IsDefEqWhnfAfterEta

end RecM

end Ix.Tc
