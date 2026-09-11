import Ix.Compiler.IxIR1.Optimizer
import Ix.Compiler.IxIR1.NoReuseAddressed

/-!
# Reclamation through the fail-soft IxIR₁ optimizer

The optimizer's successful-run theorem is intentionally one-way, but that is
enough for closed-main reclamation once the source has one successful run.
The forwarded run supplies a target witness, evaluator determinism identifies
every other successful target run with that witness, allocation-history
isomorphism transports deep release, and the final exact rebuild transports
the released heap through its certified address map.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address Owned)

namespace LowerSim

/-- Releasing a result does not inspect the declaration environment or
oracle. -/
theorem releaseResult_ctx_eq (before after : Ctx) (world : Owned)
    (fuel : Nat) (store : Store) (value : RVal) :
    releaseResult after world fuel store value =
      releaseResult before world fuel store value := by
  cases world with
  | shared =>
      exact Sim.dropVal_ctx_eq before after fuel store value
  | unique =>
      exact Sim.dropUVal_ctx_eq before after fuel store value

end LowerSim

namespace Sim.RunHistoryIso

/-- A related successful result can be released whenever its source result
can, and absence of live nodes survives the allocation-history relation. -/
theorem releaseResult_live_eq_zero
    {left right : Store} {before : HeapHistoryIso left right}
    {sourceOut targetOut : Store × RVal}
    (hresult : RunHistoryIso before sourceOut targetOut)
    (ctx : Ctx) (world : Owned) {fuel : Nat} {released : Store}
    (hrelease : LowerSim.releaseResult ctx world fuel sourceOut.1 sourceOut.2 =
      .ok released)
    (hlive : released.live = 0) :
    ∃ targetReleased,
      LowerSim.releaseResult ctx world fuel targetOut.1 targetOut.2 =
          .ok targetReleased ∧
        targetReleased.live = 0 := by
  obtain ⟨heap, _, hvalue⟩ := hresult
  cases world with
  | shared =>
      have hsource : dropVal ctx fuel sourceOut.1 sourceOut.2 =
          .ok released := by
        simpa [LowerSim.releaseResult] using hrelease
      obtain ⟨targetReleased, htarget, hstores⟩ :=
        dropVal_historyIso heap hvalue hsource
      exact ⟨targetReleased, by
        simpa [LowerSim.releaseResult] using htarget,
        hstores.right_live_eq_zero hlive⟩
  | unique =>
      have hsource : dropUVal ctx fuel sourceOut.1 sourceOut.2 =
          .ok released := by
        simpa [LowerSim.releaseResult] using hrelease
      obtain ⟨targetReleased, htarget, hstores⟩ :=
        dropUVal_historyIso heap hvalue hsource
      exact ⟨targetReleased, by
        simpa [LowerSim.releaseResult] using htarget,
        hstores.right_live_eq_zero hlive⟩

end Sim.RunHistoryIso

namespace Readdress

/-- A release witness commutes with a certified declaration-address image;
the address map changes no location liveness. -/
theorem releaseResult_mapAddresses
    {rename : Address → Address} {before after : Ctx}
    (hcontexts : Ctx.Renames rename before after)
    (world : Owned) {fuel : Nat} {store released : Store} {value : RVal}
    (hrelease : LowerSim.releaseResult before world fuel store value =
      .ok released)
    (hlive : released.live = 0) :
    LowerSim.releaseResult after world fuel (Store.mapAddresses rename store)
        value = .ok (Store.mapAddresses rename released) ∧
      (Store.mapAddresses rename released).live = 0 := by
  constructor
  · cases world with
    | shared =>
        have hsource : dropVal before fuel store value = .ok released := by
          simpa [LowerSim.releaseResult] using hrelease
        simp only [LowerSim.releaseResult]
        rw [(evalTransportAt hcontexts fuel).dropVal, hsource]
        rfl
    | unique =>
        have hsource : dropUVal before fuel store value = .ok released := by
          simpa [LowerSim.releaseResult] using hrelease
        simp only [LowerSim.releaseResult]
        rw [(evalTransportAt hcontexts fuel).dropUVal, hsource]
        rfl
  · simpa using hlive

end Readdress

namespace Optimizer.Outcome

/-- A selected optimizer result inherits reclamation from one successful
source run.  `hselected` exposes the exact rebuild only in the rebuilt branch;
the skipped branch is literal source equality. -/
theorem reclamation_of_witness
    {outcome : Optimizer.Outcome} {policy : Optimizer.Policy}
    {program : List ReaddressAll.Artifact} {summaries : HPT.SummaryEnv}
    {main : Code} {oracle : Address → List RVal → Option RVal}
    {world : Owned} {fuel : Nat} {sourceOut targetOut : Store × RVal}
    (hselected : ∀ {result}, outcome.rebuilt = some result →
      ∃ optimized,
        HPT.OptimizeProgram.rebuildProgram policy.passes [] program summaries
            main = .ok optimized ∧
          optimized.result = result)
    (hsource : runMain
      (outcome.sourceCtx policy program summaries main oracle) main fuel =
        .ok sourceOut)
    (htarget : runMain (outcome.targetCtx program oracle)
      (outcome.main main) fuel = .ok targetOut)
    (hrefines : outcome.RunRefines policy program summaries main sourceOut
      targetOut)
    (hreclamation : LowerSim.Reclamation
      (outcome.sourceCtx policy program summaries main oracle) main world) :
    LowerSim.Reclamation (outcome.targetCtx program oracle)
      (outcome.main main) world := by
  intro runFuel runStore runValue hrun
  have htargetRelease :
      ∃ releaseFuel released,
        LowerSim.releaseResult (outcome.targetCtx program oracle) world
            releaseFuel targetOut.1 targetOut.2 = .ok released ∧
          released.live = 0 := by
    cases hrebuilt : outcome.rebuilt with
    | none =>
        have hout : targetOut = sourceOut := by
          simpa [Optimizer.Outcome.RunRefines, hrebuilt] using hrefines
        subst targetOut
        simpa [Optimizer.Outcome.sourceCtx, Optimizer.Outcome.sourceOracle,
          Optimizer.Outcome.targetCtx, Optimizer.Outcome.main, hrebuilt] using
          hreclamation hsource
    | some result =>
        obtain ⟨optimized, hrebuild, hresult⟩ := hselected hrebuilt
        subst result
        obtain ⟨logicalOut, htargetOut, hhistory⟩ := by
          simpa only [Optimizer.Outcome.RunRefines, hrebuilt] using hrefines
        subst targetOut
        obtain ⟨releaseFuel, released, hrelease, hlive⟩ :=
          hreclamation hsource
        obtain ⟨logicalReleased, hlogicalRelease, hlogicalLive⟩ :=
          hhistory.releaseResult_live_eq_zero
            (outcome.sourceCtx policy program summaries main oracle) world
            hrelease hlive
        have hrebuildRaw :=
          HPT.OptimizeProgram.rebuild_of_rebuildProgram_eq_ok hrebuild
        have haudit :=
          ReaddressAll.rebuildSemanticAudit_of_rebuild_eq_ok hrebuildRaw
        let entries := policy.rebuildEntries program summaries main
        have hlogicalRelease' :
            LowerSim.releaseResult
                (optimized.result.rebuildSourceCtx entries oracle) world
                releaseFuel logicalOut.1 logicalOut.2 =
              .ok logicalReleased := by
          rw [LowerSim.releaseResult_ctx_eq
            (outcome.sourceCtx policy program summaries main oracle)
            (optimized.result.rebuildSourceCtx entries oracle)]
          exact hlogicalRelease
        have hmapped := Readdress.releaseResult_mapAddresses
          (optimized.result.renames_rebuildSourceCtx
            (raw := entries)
            (main := (HPT.OptimizeProgram.rewriteMain policy.passes
              (HPT.programDeclEnv program) summaries main).code)
            (by simpa [entries, Optimizer.Policy.rebuildEntries] using haudit)
            oracle)
          world hlogicalRelease' hlogicalLive
        refine ⟨releaseFuel,
          Readdress.Store.mapAddresses
            (optimized.result.rebuildRename entries) logicalReleased, ?_, ?_⟩
        · simpa [Optimizer.Outcome.targetCtx, Optimizer.Outcome.main,
            hrebuilt, entries] using hmapped.1
        · exact hmapped.2
  have houtput : (runStore, runValue) = targetOut :=
    LowerSim.runMain_success_unique hrun htarget
  cases houtput
  exact htargetRelease

end Optimizer.Outcome

namespace Optimizer

/-- Directly produced checked HPT results preserve reclamation through the
fail-soft optimizer selection. -/
theorem reclamation_of_runWithProducedHPT_eq
    {policy : Policy} {program : List ReaddressAll.Artifact} {main : Code}
    {limits : HPT.Limits} {production : HPT.Production limits program}
    {outcome : Outcome}
    (houtcome : runWithProducedHPT policy program main production = outcome)
    (oracle : Address → List RVal → Option RVal) (world : Owned)
    (hprogress : ∃ fuel sourceOut,
      runMain
        (outcome.sourceCtx policy program production.certificate.summaryEnv
          main oracle)
        main fuel = .ok sourceOut)
    (hreclamation : LowerSim.Reclamation
      (outcome.sourceCtx policy program production.certificate.summaryEnv
        main oracle)
      main world) :
    LowerSim.Reclamation (outcome.targetCtx program oracle)
      (outcome.main main) world := by
  obtain ⟨fuel, sourceOut, hsource⟩ := hprogress
  obtain ⟨targetOut, htarget, hrefines⟩ :=
    runMain_of_runWithProducedHPT_eq houtcome oracle fuel hsource
  exact outcome.reclamation_of_witness
    (hselected := by
      intro result hrebuilt
      apply rebuilt_eq_some_of_runWithProducedHPT
      rw [houtcome]
      exact hrebuilt)
    hsource htarget hrefines hreclamation

/-- Cached checked HPT results expose the same reclamation contract. -/
theorem reclamation_of_runWithCachedHPT_eq
    {policy : Policy} {program : List ReaddressAll.Artifact} {main : Code}
    {limits : HPT.Cache.Limits}
    {production : HPT.Cache.Production limits program} {outcome : Outcome}
    (houtcome : runWithCachedHPT policy program main production = outcome)
    (oracle : Address → List RVal → Option RVal) (world : Owned)
    (hprogress : ∃ fuel sourceOut,
      runMain
        (outcome.sourceCtx policy program production.certificate.summaryEnv
          main oracle)
        main fuel = .ok sourceOut)
    (hreclamation : LowerSim.Reclamation
      (outcome.sourceCtx policy program production.certificate.summaryEnv
        main oracle)
      main world) :
    LowerSim.Reclamation (outcome.targetCtx program oracle)
      (outcome.main main) world := by
  obtain ⟨fuel, sourceOut, hsource⟩ := hprogress
  obtain ⟨targetOut, htarget, hrefines⟩ :=
    runMain_of_runWithCachedHPT_eq houtcome oracle fuel hsource
  exact outcome.reclamation_of_witness
    (hselected := by
      intro result hrebuilt
      apply rebuilt_eq_some_of_runWithCachedHPT
      rw [houtcome]
      exact hrebuilt)
    hsource htarget hrefines hreclamation

end Optimizer

end Ix.Compiler.IxIR1
