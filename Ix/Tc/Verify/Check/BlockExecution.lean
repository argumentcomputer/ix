import Ix.Tc.Verify.Check.BlockAcceptance

/-!
# Coordinated block execution traces

This module follows the production `checkCoordinatedBlock` cache shell
exactly.  It separates a stable cache hit from a fresh `checkBlockBody` run
and proves that the sole subsequent mutation is insertion of the captured
verdict.  In particular:

* a returned success cannot be manufactured after a body error;
* a returned error cannot publish a successful block verdict;
* neither result insertion changes constants, block identity, interning, or
  the ghost verification world.

The semantic admission theorem remains in `BlockAcceptance`; this module is
the operational half needed to join that transaction to production.
-/

namespace Ix.Tc

namespace TcM

/-- A physical block already present in the checker environment takes the
fast path, returning the exact array without changing state or invoking lazy
ingress. -/
theorem tryGetBlock_of_loaded
    {state : TcState .anon} {block : KId .anon}
    {members : Array (KId .anon)}
    (hloaded : state.env.getBlock? block = some members) :
    TcM.tryGetBlock block state = .ok (some members) state := by
  unfold TcM.tryGetBlock
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ state = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) state =
    .ok state state by rfl]
  simp only
  rw [hloaded]
  rfl

/-- Every successful `some` result of the production block lookup is
physically installed in its post-state, on either the eager or lazy-ingress
path. -/
theorem tryGetBlock_success_loaded
    {block : KId .anon} {members : Array (KId .anon)}
    {before after : TcState .anon}
    (hrun : TcM.tryGetBlock block before = .ok (some members) after) :
    after.env.getBlock? block = some members := by
  unfold TcM.tryGetBlock at hrun
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before = _ at hrun
  unfold EStateM.bind at hrun
  rw [show (get : TcM .anon (TcState .anon)) before =
    .ok before before by rfl] at hrun
  simp only at hrun
  cases hget : before.env.getBlock? block with
  | some found =>
      rw [hget] at hrun
      simp only at hrun
      rcases hrun with ⟨rfl, rfl⟩
      exact hget
  | none =>
      rw [hget] at hrun
      simp only at hrun
      change EStateM.bind (TcM.lazyIngressAddr block.addr) _ before = _ at hrun
      unfold EStateM.bind at hrun
      cases hfault : TcM.lazyIngressAddr block.addr before with
      | error err failed =>
          rw [hfault] at hrun
          contradiction
      | ok value faulted =>
          rw [hfault] at hrun
          simp only at hrun
          change EStateM.bind (get : TcM .anon (TcState .anon)) _ faulted = _
            at hrun
          unfold EStateM.bind at hrun
          rw [show (get : TcM .anon (TcState .anon)) faulted =
            .ok faulted faulted by rfl] at hrun
          simp only at hrun
          cases hretry : faulted.env.getBlock? block with
          | none =>
              rw [hretry] at hrun
              cases hrun
          | some found =>
              rw [hretry] at hrun
              rcases hrun with ⟨rfl, rfl⟩
              exact hretry

end TcM

namespace RecM

/-- Capturing a successful body is exactly a successful outer action carrying
`Except.ok`. -/
theorem captureBlockCheckResult_success_iff
    {methods : Methods .anon} {block requested : KId .anon}
    {before after : TcState .anon} :
    (captureBlockCheckResult block requested).run methods before =
        .ok (.ok ()) after ↔
      (checkBlockBody block requested).run methods before = .ok () after := by
  unfold captureBlockCheckResult
  change EStateM.tryCatch
    (EStateM.bind ((checkBlockBody block requested).run methods)
      (fun _ state => EStateM.Result.ok (Except.ok ()) state))
    (fun err state => EStateM.Result.ok (Except.error err) state) before =
      EStateM.Result.ok (Except.ok ()) after ↔ _
  unfold EStateM.bind EStateM.tryCatch
  cases hbody : (checkBlockBody block requested).run methods before <;>
    simp only [hbody] <;> simp

/-- The capture shell handles both body outcomes and therefore cannot return
an outer checker error. -/
theorem captureBlockCheckResult_ne_error
    {methods : Methods .anon} {block requested : KId .anon}
    {before after : TcState .anon} {err : TcError .anon} :
    (captureBlockCheckResult block requested).run methods before ≠
      .error err after := by
  intro hrun
  unfold captureBlockCheckResult at hrun
  change EStateM.tryCatch
    (EStateM.bind ((checkBlockBody block requested).run methods)
      (fun _ state => EStateM.Result.ok (Except.ok ()) state))
    (fun caught state => EStateM.Result.ok (Except.error caught) state) before =
      EStateM.Result.error err after at hrun
  unfold EStateM.bind EStateM.tryCatch at hrun
  cases hbody : (checkBlockBody block requested).run methods before <;>
    simp only [hbody] at hrun <;> contradiction

/-- A captured error came from an actual error of `checkBlockBody` in the
same state.  `TcM` is deliberately non-backtracking, so writes performed
before the throw survive the catch exactly. -/
theorem captureBlockCheckResult_error_has_body_error
    {methods : Methods .anon} {block requested : KId .anon}
    {before captured : TcState .anon} {err : TcError .anon}
    (hrun : (captureBlockCheckResult block requested).run methods before =
      .ok (.error err) captured) :
    (checkBlockBody block requested).run methods before =
      .error err captured := by
  unfold captureBlockCheckResult at hrun
  change EStateM.tryCatch
    (EStateM.bind ((checkBlockBody block requested).run methods)
      (fun _ state => EStateM.Result.ok (Except.ok ()) state))
    (fun caught state => EStateM.Result.ok (Except.error caught) state) before =
      EStateM.Result.ok (Except.error err) captured at hrun
  unfold EStateM.bind EStateM.tryCatch at hrun
  cases hbody : (checkBlockBody block requested).run methods before with
  | ok value after =>
      simp only [hbody] at hrun
      cases value
      cases hrun
  | error bodyErr failed =>
      have hrestore : EStateM.Backtrackable.restore failed
          (EStateM.Backtrackable.save before) = failed := rfl
      simp only [hbody, hrestore] at hrun
      cases hrun
      rfl

/-- A successful body exposes the production lookup, classification, and
classified-block execution as three consecutive equations.  The lookup
post-state is explicit, so the trace covers both eager and lazy ingress.  The
classified kind is an index, so semantic admission evidence cannot later be
paired with a different production branch. -/
inductive ExactBlockBodySuccessTrace
    (methods : Methods .anon) (block requested : KId .anon)
    (members : Array (KId .anon)) (kind : CheckBlockKind)
    (before after : TcState .anon) : Prop
  | run (loaded classified : TcState .anon) :
      TcM.tryGetBlock block before = .ok (some members) loaded →
      (classifyBlock members).run methods loaded = .ok kind classified →
      (checkClassifiedBlock kind block members).run methods classified =
        .ok () after →
      ExactBlockBodySuccessTrace methods block requested members kind before
        after

/-- Invert successful `checkBlockBody` execution.  Production now fails
closed on a missing coordinated array, so every success contains an actual
`some members` lookup and there is no fallback singleton case. -/
theorem checkBlockBody_success_trace
    {methods : Methods .anon} {block requested : KId .anon}
    {before after : TcState .anon}
    (hrun : (checkBlockBody block requested).run methods before =
      .ok () after) :
    ∃ members kind,
      ExactBlockBodySuccessTrace methods block requested members kind before
        after := by
  unfold checkBlockBody at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift] at hrun
  change EStateM.bind (TcM.tryGetBlock block) _ before = .ok () after at hrun
  unfold EStateM.bind at hrun
  cases hlookup : TcM.tryGetBlock block before with
  | error err failed =>
      rw [hlookup] at hrun
      contradiction
  | ok found loaded =>
      rw [hlookup] at hrun
      cases found with
      | none =>
          simp only [throw] at hrun
          contradiction
      | some members =>
          simp only at hrun
          change EStateM.bind ((classifyBlock members).run methods) _ loaded =
            .ok () after at hrun
          unfold EStateM.bind at hrun
          cases hclass : (classifyBlock members).run methods loaded with
          | error err failed =>
              rw [hclass] at hrun
              contradiction
          | ok kind classified =>
              rw [hclass] at hrun
              exact ⟨members, kind,
                .run loaded classified hlookup hclass hrun⟩

/-- Exhaustive successful execution of the coordinated cache shell. -/
inductive CoordinatedBlockSuccessTrace
    (methods : Methods .anon) (block requested : KId .anon)
    (before after : TcState .anon) : Prop
  | cached :
      before.env.blockCheckResults[block]? = some (.ok ()) →
      after = before →
      CoordinatedBlockSuccessTrace methods block requested before after
  | fresh {bodyAfter : TcState .anon} :
      before.env.blockCheckResults[block]? = none →
      (checkBlockBody block requested).run methods before =
        .ok () bodyAfter →
      after = bodyAfter.withBlockCheckResult block (.ok ()) →
      CoordinatedBlockSuccessTrace methods block requested before after

/-- Exhaustive failing execution of the coordinated cache shell. -/
inductive CoordinatedBlockErrorTrace
    (methods : Methods .anon) (block requested : KId .anon)
    (before : TcState .anon) (err : TcError .anon)
    (after : TcState .anon) : Prop
  | cached :
      before.env.blockCheckResults[block]? = some (.error err) →
      after = before →
      CoordinatedBlockErrorTrace methods block requested before err after
  | fresh {failed : TcState .anon} :
      before.env.blockCheckResults[block]? = none →
      (captureBlockCheckResult block requested).run methods before =
        .ok (.error err) failed →
      (checkBlockBody block requested).run methods before =
        .error err failed →
      after = failed.withBlockCheckResult block (.error err) →
      CoordinatedBlockErrorTrace methods block requested before err after

/-- Invert a successful production execution into the two exhaustive paths.
The fresh constructor exposes the actual successful block-body equation and
the exact result-insertion state. -/
theorem checkCoordinatedBlock_success_trace
    {methods : Methods .anon} {block requested : KId .anon}
    {before after : TcState .anon}
    (hrun : (checkCoordinatedBlock block requested).run methods before =
      .ok () after) :
    CoordinatedBlockSuccessTrace methods block requested before after := by
  unfold checkCoordinatedBlock at hrun
  simp only [ReaderT.run_bind] at hrun
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before =
    .ok () after at hrun
  unfold EStateM.bind at hrun
  rw [show (get : TcM .anon (TcState .anon)) before =
    .ok before before by rfl] at hrun
  dsimp only at hrun
  cases hcache : before.env.blockCheckResults[block]? with
  | some result =>
      rw [hcache] at hrun
      dsimp only at hrun
      cases result with
      | ok value =>
          cases value
          exact .cached hcache (EStateM.Result.ok.inj hrun |>.2.symm)
      | error err =>
          simp only [throw] at hrun
          contradiction
  | none =>
      rw [hcache] at hrun
      dsimp only at hrun
      change EStateM.bind
        ((captureBlockCheckResult block requested).run methods) _ before =
          .ok () after at hrun
      unfold EStateM.bind at hrun
      cases hcapture :
          (captureBlockCheckResult block requested).run methods before with
      | error err failed =>
          exact False.elim (captureBlockCheckResult_ne_error hcapture)
      | ok result captured =>
          rw [hcapture] at hrun
          cases result with
          | error err =>
              simp only [modify, throw] at hrun
              contradiction
          | ok value =>
              cases value
              have hbody := captureBlockCheckResult_success_iff.mp hcapture
              simp only [modify] at hrun
              exact .fresh hcache hbody
                (EStateM.Result.ok.inj hrun |>.2.symm)

/-- Invert a failing production execution into a cached error or an actual
body error followed by an error-only result insertion. -/
theorem checkCoordinatedBlock_error_trace
    {methods : Methods .anon} {block requested : KId .anon}
    {before after : TcState .anon} {err : TcError .anon}
    (hrun : (checkCoordinatedBlock block requested).run methods before =
      .error err after) :
    CoordinatedBlockErrorTrace methods block requested before err after := by
  unfold checkCoordinatedBlock at hrun
  simp only [ReaderT.run_bind] at hrun
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ before =
    .error err after at hrun
  unfold EStateM.bind at hrun
  rw [show (get : TcM .anon (TcState .anon)) before =
    .ok before before by rfl] at hrun
  dsimp only at hrun
  cases hcache : before.env.blockCheckResults[block]? with
  | some result =>
      rw [hcache] at hrun
      dsimp only at hrun
      cases result with
      | ok value =>
          cases value
          contradiction
      | error cachedErr =>
          cases hrun
          exact .cached hcache rfl
  | none =>
      rw [hcache] at hrun
      dsimp only at hrun
      change EStateM.bind
        ((captureBlockCheckResult block requested).run methods) _ before =
          .error err after at hrun
      unfold EStateM.bind at hrun
      cases hcapture :
          (captureBlockCheckResult block requested).run methods before with
      | error outerErr failed =>
          exact False.elim (captureBlockCheckResult_ne_error hcapture)
      | ok result captured =>
          rw [hcapture] at hrun
          cases result with
          | ok value =>
              cases value
              simp only [modify] at hrun
              contradiction
          | error capturedErr =>
              have hbody :=
                captureBlockCheckResult_error_has_body_error hcapture
              simp only [modify, throw] at hrun
              cases hrun
              exact .fresh hcache hcapture hbody rfl

end RecM

namespace TcState

/-- The production verdict update installs exactly the requested entry. -/
@[simp] theorem withBlockCheckResult_self
    (state : TcState .anon) (block : KId .anon)
    (result : Except (TcError .anon) Unit) :
    (state.withBlockCheckResult block result).env.blockCheckResults[block]? =
      some result := by
  simp [TcState.withBlockCheckResult]

end TcState

namespace BlockStateWF

/-- Publishing a captured block verdict cannot change semantic trust or the
concrete/world representation boundary. -/
theorem withBlockCheckResult {trProj : RawProjRel}
    {state : TcState .anon} {world : VerifyWorld}
    (h : BlockStateWF trProj state world) (block : KId .anon)
    (result : Except (TcError .anon) Unit) :
    BlockStateWF trProj (state.withBlockCheckResult block result) world := by
  refine ⟨h.core.of_consts_eq ?_ ?_, ?_⟩
  · rfl
  · exact h.core.intern
  · intro loadedBlock members hget
    apply h.loadedBlocks
    change state.env.blocks[loadedBlock]? = some members at hget
    exact hget

end BlockStateWF

end Ix.Tc
