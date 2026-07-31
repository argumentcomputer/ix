import Ix.Tc.Verify.DefEq.StoppedContinuation

/-!
# Final-WHNF comparison contracts

The final DefEq tier has two production-owned phases: a constructor-directed
structural prefix and the Nat/eta/String/structural fallback chain.  These
contracts let their exhaustive proofs be developed independently and then
compose them back into `isDefEqWhnf`.
-/

namespace Ix.Tc

namespace RecM

/-- Exact positive-result contract for the let-declaration helper. -/
def TryDefEqWhnfLet.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state leftName rightName ty1 val1 body1 ty2 val2 body2}
      {leftNondep rightNondep : Bool}
      {leftInfo rightInfo : ExprInfo .anon} {leftV rightV : Lean4Lean.VExpr},
    support (.letE leftName ty1 val1 body1 leftNondep leftInfo) →
    support (.letE rightName ty2 val2 body2 rightNondep rightInfo) →
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.letE leftName ty1 val1 body1 leftNondep leftInfo) leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (.letE rightName ty2 val2 body2 rightNondep rightInfo) rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfLet leftName ty1 val1 body1 ty2 val2 body2)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the optional Nat bridge. -/
def TryDefEqWhnfNat.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfNat left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the fallback chain after the Nat bridge
returns `none`. -/
def IsDefEqWhnfAfterNat.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterNat left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the optional lambda-eta phase. -/
def TryDefEqWhnfEta.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfEta left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the fallback chain after lambda eta
returns `none`. -/
def IsDefEqWhnfAfterEta.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterEta left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the optional String-literal expansion
phase. -/
def TryDefEqWhnfString.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfString left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the fallback chain after String expansion
returns `none`. -/
def IsDefEqWhnfAfterString.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterString left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the optional bidirectional structure-eta
phase. -/
def TryDefEqWhnfStructEta.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfStructEta left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the concrete unit-like shortcut. -/
def TryDefEqUnit.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqUnit left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the unit-like/proof-irrelevance tail after
structure eta returns `none`. -/
def IsDefEqWhnfAfterStructEta.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterStructEta left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the final proof-irrelevance fallback. -/
def IsDefEqWhnfAfterUnit.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterUnit left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the constructor-directed prefix.  `none`
is deliberately only a control-flow result. -/
def TryDefEqWhnfStructural.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqWhnfStructural left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result soundness for the fallback chain after the structural
prefix returns `none`. -/
def IsDefEqWhnfAfterStructural.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnfAfterStructural left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- The two exact production phases close the final WHNF comparator. -/
theorem isDefEqWhnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : Lean4Lean.VExpr}
    (hstructural : TryDefEqWhnfStructural.WFAt layer semantics trProj world
      support uvars)
    (htail : IsDefEqWhnfAfterStructural.WFAt layer semantics trProj world
      support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (isDefEqWhnf left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold isDefEqWhnf
  apply RecM.WF.bind <|
    hstructural hleftSupport hrightSupport hleft hright
  intro result afterStructural hresult
  cases result with
  | none => exact htail hleftSupport hrightSupport hleft hright
  | some answer => exact RecM.WF.pure fun _ => hresult

namespace IsDefEqWhnf

/-- Package the phase composition as the contract used by the stopped
continuation. -/
theorem ofPhases
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hstructural : TryDefEqWhnfStructural.WFAt layer semantics trProj world
      support uvars)
    (htail : IsDefEqWhnfAfterStructural.WFAt layer semantics trProj world
      support uvars) :
    IsDefEqWhnf.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact isDefEqWhnf_wf hstructural htail hleftSupport hrightSupport hleft
    hright

end IsDefEqWhnf

end RecM

end Ix.Tc
