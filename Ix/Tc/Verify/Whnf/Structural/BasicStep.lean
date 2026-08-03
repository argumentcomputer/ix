import Ix.Tc.Verify.Whnf.Structural.CacheShell

/-!
# Basic structural-step closure

CacheShell verifies the public structural cache shell once one exhaustive local
step contract is available.  This slice starts that local assembly with the
state-pure leaves, the complete fvar branch, and explicit-let substitution.

The fvar premise is intentionally stronger than `CtxRecon`: production
returns an `.ldecl` value without lifting it, so soundness requires that the
stored value be constructed, closed with respect to the legacy de Bruijn
stack, and within the current weakening bound.  Naming this state obligation
prevents a translated-but-stale local value from being accepted silently.
-/

namespace Ix.Tc
namespace RecM

/-- Runtime safety needed by production's unchanged let-fvar return.  This
property is indexed by every state satisfying the fixed K1 invariant so it
can be consumed by the uniform `WhnfStep.WF` contract rather than by one
hand-picked execution fixture. -/
def FVarZetaSafety (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) : Prop :=
  ∀ {s : TcState .anon} {fv : FVarId} {declName : Mode.anon.F Name}
      {ty val : KExpr .anon},
    WhnfStateInv layer semantics trProj world support uvars Delta s →
    s.lctx.find? fv = some (.ldecl declName ty val) →
    support val ∧ KExpr.Constructed val ∧ val.lbr = 0 ∧
      Delta.bvars + val.size < UInt64.size

/-- Finite request census for every supported explicit let that can become a
current structural-loop state.  The support guard keeps the obligation
finite; it does not require global closure under arbitrary let syntax. -/
def LetSubstRequestCensus (requests : List WalkerRequest)
    (support : RunSupport) : Prop :=
  ∀ {name : Mode.anon.F Name} {ty val body : KExpr .anon}
      {nondep : Bool} {info : ExprInfo .anon},
    support (.letE name ty val body nondep info) →
      WalkerRequest.subst body val 0 ∈ requests

/-- Exhaustive fvar step closure.  Missing and ordinary local declarations
are reflexive, while an `.ldecl` uses the exact state-safety facts needed by
`WhnfMeaning.zetaFVar`.  The branch is state-pure and cannot raise an error. -/
theorem whnfCoreWithFlagsStep_fvar_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {fv : FVarId}
    {name : Mode.anon.F Name} {info : ExprInfo .anon} {flags : WhnfFlags}
    {stepError : TcError .anon → TcState .anon → Prop}
    (theory : WhnfTheory trProj world uvars)
    (hsafe : FVarZetaSafety layer semantics trProj world support uvars
      Delta) :
    ∀ s,
      WhnfStep.Source trProj world support uvars Delta id
        (.fvar fv name info) →
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep (.fvar fv name info) flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          (.fvar fv name info) action)
        stepError := by
  intro s hsource methods hmethods hI
  obtain ⟨hsourceSupport, sourceV, hsourceTr⟩ := hsource
  cases hfind : s.lctx.find? fv with
  | none =>
      have hnot : ∀ declName ty val,
          s.lctx.find? fv ≠ some (.ldecl declName ty val) := by
        intro declName ty val hbad
        rw [hfind] at hbad
        contradiction
      rw [whnfCoreWithFlagsStep_fvarDone hnot]
      exact ⟨hI, hsourceSupport,
        WhnfMeaning.refl hsourceTr (theory.exprWF hI.2.1 hsourceTr)⟩
  | some decl =>
      cases decl with
      | cdecl declName bi ty =>
          have hnot : ∀ declName' ty' val,
              s.lctx.find? fv ≠ some (.ldecl declName' ty' val) := by
            intro declName' ty' val hbad
            rw [hfind] at hbad
            cases hbad
          rw [whnfCoreWithFlagsStep_fvarDone hnot]
          exact ⟨hI, hsourceSupport,
            WhnfMeaning.refl hsourceTr (theory.exprWF hI.2.1 hsourceTr)⟩
      | ldecl declName ty val =>
          rw [whnfCoreWithFlagsStep_fvarZeta hfind]
          obtain ⟨hvalSupport, hconstructed, hclosed, hbound⟩ :=
            hsafe hI hfind
          exact ⟨hI, hvalSupport,
            WhnfMeaning.zetaFVar hI.2.1 theory.projections hfind hconstructed
              hclosed hbound⟩

/-- Every supported explicit-let branch satisfies the local step contract
from its one request-certified substitution.  Request bounds supply the
constructedness and no-wrap facts; request coverage supplies finite result
support and the walker preserves the complete invariant. -/
theorem whnfCoreWithFlagsStep_letE_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hcensus : LetSubstRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {name : Mode.anon.F Name}
    {ty val body : KExpr .anon} {nondep : Bool} {info : ExprInfo .anon}
    {flags : WhnfFlags}
    {stepError : TcError .anon → TcState .anon → Prop}
    (theory : WhnfTheory trProj world uvars) :
    ∀ s,
      WhnfStep.Source trProj world support uvars Delta id
        (.letE name ty val body nondep info) →
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep (.letE name ty val body nondep info) flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          (.letE name ty val body nondep info) action)
        stepError := by
  intro s hsource methods hmethods hI
  have hmem : WalkerRequest.subst body val 0 ∈ requests :=
    hcensus hsource.1
  obtain ⟨s', hstep, hI', hmeaning⟩ :=
    whnfCoreWithFlagsStep_letE_acceptance hrun theory hmem hsource hI
  rw [hstep]
  exact ⟨hI', hmeaning⟩

/-- The structural forms closed by this slice.  Keeping a proof-relevant
classifier makes later exhaustive assembly a simple constructor case split
and prevents a syntax branch from disappearing behind a Boolean test. -/
inductive WhnfCoreBasic : KExpr .anon → Prop
  | leaf {e} : WhnfCoreLeaf e → WhnfCoreBasic e
  | fvar {fv name info} : WhnfCoreBasic (.fvar fv name info)
  | letE {name ty val body nondep info} :
      WhnfCoreBasic (.letE name ty val body nondep info)

/-- Uniform local-step contract for all basic forms: immediate leaves,
fvars, and explicit lets. -/
theorem whnfCoreWithFlagsStep_basic_wf
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    (hcensus : LetSubstRequestCensus requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source : KExpr .anon} {flags : WhnfFlags}
    {stepError : TcError .anon → TcState .anon → Prop}
    (theory : WhnfTheory trProj world uvars)
    (hsafe : FVarZetaSafety layer semantics trProj world support uvars
      Delta)
    (hbasic : WhnfCoreBasic source) :
    ∀ s,
      WhnfStep.Source trProj world support uvars Delta id source →
      RecM.WF layer semantics trProj world support uvars Delta s
        (whnfCoreWithFlagsStep source flags)
        (fun action _ => WhnfStep.Meaning trProj world support uvars Delta id
          source action)
        stepError := by
  cases hbasic with
  | leaf hleaf => exact whnfCoreWithFlagsStep_leaf_wf theory hleaf
  | fvar => exact whnfCoreWithFlagsStep_fvar_wf theory hsafe
  | letE => exact whnfCoreWithFlagsStep_letE_wf hrun hcensus theory

end RecM
end Ix.Tc
