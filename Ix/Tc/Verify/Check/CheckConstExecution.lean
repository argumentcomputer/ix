import Ix.Tc.Verify.Check.BlockRouteFrame
import Ix.Tc.Verify.Check.BlockTransaction

/-!
# Production `checkConst` dispatch traces

The top-level recursive driver first loads the requested declaration, routes
it, and then executes exactly one of two branches.  The coordinated branch
ends at `checkCoordinatedBlock`; the standalone branch ends at
`checkConstMemberFresh`.  Keeping these equations explicit prevents a proof
for one branch from being reused for the other.
-/

namespace Ix.Tc

namespace RecM

/-- Exhaustive successful execution of the production recursive driver. -/
inductive CheckConstSuccessTrace
    (methods : Methods .anon) (id : KId .anon)
    (before after : TcState .anon) : Prop
  | coordinated (concrete : KConst .anon) (loaded : TcState .anon)
      (block : KId .anon) (routed : TcState .anon) :
      TcM.getConst id before = .ok concrete loaded →
      (coordinatedBlockFor concrete).run methods loaded =
        .ok (some block) routed →
      (checkCoordinatedBlock block id).run methods routed = .ok () after →
      CheckConstSuccessTrace methods id before after
  | standalone (concrete : KConst .anon) (loaded routed : TcState .anon) :
      TcM.getConst id before = .ok concrete loaded →
      (coordinatedBlockFor concrete).run methods loaded = .ok none routed →
      (checkConstMemberFresh id).run methods routed = .ok () after →
      CheckConstSuccessTrace methods id before after

/-- Invert a successful production `checkConst` run into its exact and
exclusive coordinated/standalone branch. -/
theorem checkConst_success_trace
    {methods : Methods .anon} {id : KId .anon}
    {before after : TcState .anon}
    (hrun : (checkConst id).run methods before = .ok () after) :
    CheckConstSuccessTrace methods id before after := by
  unfold checkConst at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  change EStateM.bind (TcM.getConst id) _ before = .ok () after at hrun
  unfold EStateM.bind at hrun
  cases hget : TcM.getConst id before with
  | error err failed =>
      rw [hget] at hrun
      contradiction
  | ok concrete loaded =>
      rw [hget] at hrun
      change EStateM.bind ((coordinatedBlockFor concrete).run methods) _
        loaded = .ok () after at hrun
      unfold EStateM.bind at hrun
      cases hroute : (coordinatedBlockFor concrete).run methods loaded with
      | error err failed =>
          rw [hroute] at hrun
          contradiction
      | ok selected routed =>
          rw [hroute] at hrun
          cases selected with
          | none => exact .standalone concrete loaded routed hget hroute hrun
          | some block =>
              exact .coordinated concrete loaded block routed hget hroute hrun

end RecM

end Ix.Tc
