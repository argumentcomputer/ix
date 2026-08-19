import Init.Data.Range.Lemmas
import Ix.Tc.Verify.Infer.Constants
import Ix.Tc.Verify.Infer.ProjectionTelescope
import Ix.Tc.Verify.Whnf.StructEta.RecursionClassifier

/-!
# Projection result-sort classification

`inductiveAppIsProp` scans a declaration telescope without pushing its
binders into the runtime local context.  Successive bodies can therefore
contain loose de Bruijn variables even though the original declaration type
is closed.  This module proves the helper's state and finite-walker closure
against an explicit state-only WHNF callback contract; it does not pretend
those intermediate bodies have a structural translation in the caller's
context.
-/

namespace Ix.Tc

/-- The exact universe-instantiation request selected when the classifier's
lookup returns the catalogued inductive declaration.  Other declaration
kinds reject before invoking the walker. -/
def ProjectionInductiveInstantiationRequest
    (world : VerifyWorld) (requests : List WalkerRequest)
    (indId : KId .anon) (levels : Array (KUniv .anon)) : Prop :=
  ∀ {c}, world.catalog indId = some c →
    match c with
    | .indc (ty := ty) .. =>
        WalkerRequest.instUniv ty levels ∈ requests
    | _ => True

namespace RecM

/-- State-only WHNF authority for the loose declaration bodies traversed by
the classifier.  This is intentionally separate from `DirectWhnf.WFAt`,
whose semantic contract requires a translation in the runtime context. -/
def ProjectionWhnfPreservesAt
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) : Prop :=
  ∀ (input : KExpr .anon) (s : TcState .anon),
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnf input) (fun _ _ => True)

/-- One exact declaration-binder callback preserves the checker invariant on
success and error. -/
theorem inductiveAppBinderStep_state_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hwhnf : ProjectionWhnfPreservesAt layer semantics trProj world support
      uvars Delta)
    (current : KExpr .anon) (s : TcState .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inductiveAppBinderStep current) (fun _ _ => True) := by
  unfold inductiveAppBinderStep
  apply RecM.WF.bind (hwhnf current s)
  intro reduced after _
  cases reduced <;> simp only
  case all => exact RecM.WF.pure fun _ => trivial
  all_goals exact RecM.WF.throw fun _ => trivial

/-- List-normalized declaration-binder scan. -/
theorem inductiveAppBindersList_state_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hwhnf : ProjectionWhnfPreservesAt layer semantics trProj world support
      uvars Delta) :
    ∀ (indices : List Nat) (current : KExpr .anon) (s : TcState .anon),
      RecM.WF layer semantics trProj world support uvars Delta s
        (forIn (m := RecM .anon) indices current
          (fun _ current => inductiveAppBinderStep current))
        (fun _ _ => True)
  | [], current, s => by
      rw [List.forIn_nil]
      exact RecM.WF.pure fun _ => trivial
  | _ :: indices, current, s => by
      rw [List.forIn_cons]
      apply RecM.WF.bind
        (inductiveAppBinderStep_state_wf hwhnf current s)
      intro action after _
      cases action with
      | done result => exact RecM.WF.pure fun _ => trivial
      | yield next =>
          exact inductiveAppBindersList_state_wf hwhnf indices next after

/-- The production range wrapper has the same state closure as its
list-normalized traversal. -/
theorem inductiveAppBinders_state_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hwhnf : ProjectionWhnfPreservesAt layer semantics trProj world support
      uvars Delta)
    (binders : Nat) (current : KExpr .anon) (s : TcState .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inductiveAppBinders binders current) (fun _ _ => True) := by
  unfold inductiveAppBinders
  rw [_root_.Std.Legacy.Range.forIn_eq_forIn_range']
  exact inductiveAppBindersList_state_wf hwhnf _ current s

/-- `ensureSortDirect` needs only the state-only callback contract when no
semantic result is requested.  Its syntactic sort path is pure; every other
path delegates once to WHNF and then either returns the exposed level or
rejects. -/
private theorem ensureSortDirect_state_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hwhnf : ProjectionWhnfPreservesAt layer semantics trProj world support
      uvars Delta)
    (input : KExpr .anon) (s : TcState .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (ensureSortDirect input) (fun _ _ => True) := by
  cases input <;> simp only [ensureSortDirect]
  case sort => exact RecM.WF.pure fun _ => trivial
  all_goals
    unfold ensureSortWhnf
    apply RecM.WF.bind (hwhnf _ s)
    intro reduced after _
    cases reduced <;> simp only
    case sort => exact RecM.WF.pure fun _ => trivial
    all_goals exact RecM.WF.throw fun _ => trivial

/-- The post-telescope sort classifier preserves state across both WHNF
calls, direct-sort success, non-sort rejection, and the final Boolean test. -/
theorem inductiveAppResultIsProp_state_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hwhnf : ProjectionWhnfPreservesAt layer semantics trProj world support
      uvars Delta)
    (resultTy : KExpr .anon) (s : TcState .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inductiveAppResultIsProp resultTy) (fun _ _ => True) := by
  unfold inductiveAppResultIsProp
  apply RecM.WF.bind (hwhnf resultTy s)
  intro sortTy afterWhnf _
  apply RecM.WF.bind
    (ensureSortDirect_state_wf hwhnf sortTy afterWhnf)
  intro level afterSort _
  exact RecM.WF.pure fun _ => trivial

/-- Complete state/resource closure of `inductiveAppIsProp`: lazy lookup is
tied to the immutable catalog, universe instantiation is request-certified,
the declaration telescope is scanned exhaustively, and every partial error
preserves the caller's invariant. -/
theorem inductiveAppIsProp_state_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {indId : KId .anon} {levels : Array (KUniv .anon)} {binders : Nat}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hwhnf : ProjectionWhnfPreservesAt layer semantics trProj world support
      uvars Delta)
    (hrequest : ProjectionInductiveInstantiationRequest world requests indId
      levels) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inductiveAppIsProp indId levels binders) (fun _ _ => True) := by
  unfold inductiveAppIsProp
  apply RecM.WF.bind
    (RecM.WF.withInv <| RecM.WF.liftTcM <|
      TcM.tryGetConst_loaded_wf hfault indId s)
  intro found afterLookup hfound
  rcases hfound with ⟨hI, hloaded⟩
  cases found with
  | none => exact RecM.WF.throw fun _ => trivial
  | some c =>
      cases c <;> simp only
      case indc name levelParams lvls params indices isUnsafe block memberIdx
          ty ctors leanAll =>
        have hcatalog : world.catalog indId = some
            (.indc name levelParams lvls params indices isUnsafe block
              memberIdx ty ctors leanAll) :=
          hI.1.core.loaded (hloaded _ rfl)
        have hmem : WalkerRequest.instUniv ty levels ∈ requests := by
          simpa [ProjectionInductiveInstantiationRequest] using
            hrequest hcatalog
        apply RecM.WF.bind
          (RecM.WF.liftTcM <|
            TcM.instantiateUnivParams_whnf_wf hrun.collisionFree
              (hrun.coverage.instUniv hmem))
        intro instantiated afterInst _
        apply RecM.WF.bind
          (inductiveAppBinders_state_wf hwhnf binders instantiated afterInst)
        intro resultTy afterBinders _
        exact inductiveAppResultIsProp_state_wf hwhnf resultTy afterBinders
      all_goals exact RecM.WF.throw fun _ => trivial

end RecM

end Ix.Tc
