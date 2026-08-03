import Ix.Tc.Verify.DefEq.ProjectionDeltaLoop
import Ix.Tc.Verify.Whnf.Projection.NoAccelTail

/-!
# Direct projection reduction inside DefEq

The projection-directed DefEq loop invokes `tryProjReduce` on values that
already carry a Theory projection witness.  The production helper's
state/support behavior is proved by the no-acceleration WHNF development;
the remaining semantic fact is deliberately indexed by the exact successful
helper execution.  It therefore cannot authorize a different projection,
input, result, method table, or pair of states.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Semantic reflection for one successful direct projection-helper run.

This record has no state authority: both endpoint invariants are premises,
and the result is tied to the exact production execution equation. -/
structure DirectProjectionReflection (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  success : ∀ {uvars : Nat} {Delta : KVLCtx}
      {methods : Methods .anon} {before after : TcState .anon}
      {id : KId .anon} {field : UInt64} {source result : KExpr .anon}
      {sourceV projectedV : VExpr} {structName : Lean.Name},
    Methods.WFAt .noAccel semantics trProj world support uvars methods →
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    world.nameOf id.addr = some structName →
    trProj Delta.toCtx structName field.toNat sourceV projectedV →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta before →
    WhnfStateInv .noAccel semantics trProj world support uvars Delta after →
    (tryProjReduce id field source).run methods before =
      .ok (some result) after →
    WhnfPost trProj world uvars Delta projectedV result

/-- The already-proved helper invariant plus exact semantic reflection are
the complete resources needed by the projection-directed DefEq loop. -/
structure DirectProjectionReductionResources (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  helper : ProjectionHelper.WF .noAccel semantics trProj world support
  reflection : DirectProjectionReflection semantics trProj world support

/-- A direct production projection attempt preserves the complete recursive
state invariant on hits, misses, and errors.  Only an exact successful hit is
sent to semantic reflection. -/
theorem tryProjReduce_direct_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {id : KId .anon} {field : UInt64} {source : KExpr .anon}
    {sourceV projectedV : VExpr} {structName : Lean.Name}
    (resources : DirectProjectionReductionResources semantics trProj world
      support)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hname : world.nameOf id.addr = some structName)
    (hprojection :
      trProj Delta.toCtx structName field.toNat sourceV projectedV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (tryProjReduce id field source)
      (fun result _ => match result with
        | none => True
        | some reduced => support reduced ∧
            WhnfPost trProj world uvars Delta projectedV reduced) := by
  intro methods hmethods hI
  have hhelper := resources.helper (id := id) (field := field) hmethods
    hsourceSupport hI
  cases hrun : (tryProjReduce id field source).run methods state with
  | error err after =>
      rw [hrun] at hhelper
      exact hhelper
  | ok result after =>
      rw [hrun] at hhelper
      cases result with
      | none => exact ⟨hhelper.1, trivial⟩
      | some reduced =>
          exact ⟨hhelper.1, hhelper.2,
            resources.reflection.success hmethods hsourceSupport hsource
              hname hprojection hI hhelper.1 hrun⟩

namespace TryProjReduce

/-- Construct the exact lower-helper contract consumed by the bounded
projection loop. -/
theorem ofDirectResources
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (resources : DirectProjectionReductionResources semantics trProj world
      support) :
    TryProjReduce.WFAt .noAccel semantics trProj world support uvars := by
  intro Delta state id field source sourceV structName projectedV
    hsourceSupport hsource hname hprojection
  exact tryProjReduce_direct_wf resources hsourceSupport hsource hname
    hprojection

end TryProjReduce

end RecM

end Ix.Tc
