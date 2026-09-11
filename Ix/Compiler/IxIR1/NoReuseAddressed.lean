import Ix.Compiler.IxIR1.NoReuse
import Ix.Compiler.IxIR1.LowerFullyAddressedSim

/-!
# Reclamation across IxIR₁ address normalization

Address normalization rewrites only declaration identities stored in code and
pap/constructor nodes. Locations, ownership counts, release behavior, and the
live-node metric are unchanged. This module transports the transient
lowerer's reclamation theorem to both content-addressed production boundaries.
-/

namespace Ix.Compiler.IxIR1.NoReuse

open Ix.Compiler.IxIR1

@[simp] theorem storeMapAddresses_live
    (rename : Ixon.Address → Ixon.Address) (store : Store) :
    (Readdress.Store.mapAddresses rename store).live = store.live := by
  simp only [Store.live, Readdress.Store.mapAddresses]
  rw [Array.foldl_map]
  simp

/-- Reclamation is equivariant under every address renaming accepted by the
evaluator context relation.  Address normalization changes declaration
identities beneath code and heap nodes, but leaves locations, result values,
release behavior, and the live-node count intact. -/
theorem reclamation_mapAddresses
    {rename : Ixon.Address → Ixon.Address}
    {before after : Ctx} {code : Code} {world : Ixon.Owned}
    (hcontexts : Readdress.Ctx.Renames rename before after)
    (hreclamation : LowerSim.Reclamation before code world) :
    LowerSim.Reclamation after
      (Readdress.Code.mapAddresses rename code) world := by
  intro runFuel mappedStore value hmappedRun
  have htransport :=
    Readdress.runMain_mapAddresses hcontexts code runFuel
  rw [hmappedRun] at htransport
  cases hraw : runMain before code runFuel with
  | error error =>
      rw [hraw] at htransport
      contradiction
  | ok output =>
      rcases output with ⟨rawStore, rawValue⟩
      rw [hraw] at htransport
      have hresult :
          mappedStore = Readdress.Store.mapAddresses rename rawStore ∧
            value = rawValue := by
        simpa only [Readdress.mapRunResult_ok, Except.ok.injEq,
          Prod.mk.injEq] using htransport
      rcases hresult with ⟨hstore, hvalue⟩
      subst mappedStore
      subst value
      obtain ⟨releaseFuel, released, hrelease, hlive⟩ :=
        hreclamation hraw
      refine ⟨releaseFuel,
        Readdress.Store.mapAddresses rename released, ?_, ?_⟩
      · cases world with
        | shared =>
            have hrelease' :
                dropVal before releaseFuel rawStore rawValue =
                  .ok released := by
              simpa [LowerSim.releaseResult] using hrelease
            simp only [LowerSim.releaseResult]
            rw [(Readdress.evalTransportAt hcontexts releaseFuel).dropVal,
              hrelease']
            rfl
        | unique =>
            have hrelease' :
                dropUVal before releaseFuel rawStore rawValue =
                  .ok released := by
              simpa [LowerSim.releaseResult] using hrelease
            simp only [LowerSim.releaseResult]
            rw [(Readdress.evalTransportAt hcontexts releaseFuel).dropUVal,
              hrelease']
            rfl
      · simpa using hlive

/-- Every result-independent counter invariant survives a compatible address
renaming.  The successful addressed run has the exact mapped raw store, and
`costObservation` ignores the address-bearing contents of its nodes. -/
theorem runCostInvariant_mapAddresses
    {rename : Ixon.Address → Ixon.Address}
    {before after : Ctx} {code : Code}
    {spec : LowerSim.CostObservation → Prop}
    (hcontexts : Readdress.Ctx.Renames rename before after)
    (hcost : LowerSim.RunCostInvariant before code spec) :
    LowerSim.RunCostInvariant after
      (Readdress.Code.mapAddresses rename code) spec := by
  intro targetFuel mappedStore value hmappedRun
  have htransport :=
    Readdress.runMain_mapAddresses hcontexts code targetFuel
  rw [hmappedRun] at htransport
  cases hraw : runMain before code targetFuel with
  | error error =>
      rw [hraw] at htransport
      contradiction
  | ok output =>
      rcases output with ⟨rawStore, rawValue⟩
      rw [hraw] at htransport
      have hresult :
          mappedStore = Readdress.Store.mapAddresses rename rawStore ∧
            value = rawValue := by
        simpa only [Readdress.mapRunResult_ok, Except.ok.injEq,
          Prod.mk.injEq] using htransport
      rcases hresult with ⟨hstore, hvalue⟩
      subst mappedStore
      subst value
      simpa using hcost hraw

/-- The SCC-aware production boundary preserves any reclamation theorem
established for its certified pre-address execution context. -/
theorem lowerAllFullyAddressed_reclamation_of_raw
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : Lower.LowSt} {result : ReaddressAll.Result}
    (hlower :
      (Lower.lowerAllAction declarations main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      Lower.lowerAllFullyAddressed declarations main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw : LowerSim.Reclamation
      (result.preAddressCtx raw oracle) mainCode mainWorld) :
    LowerSim.Reclamation (result.addressedCtx oracle) result.main
      mainWorld := by
  have hrun :=
    Lower.readdressAll_run_of_lowerAllFullyAddressed_eq_ok
      hlower haddressed
  have haudit := ReaddressAll.semanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_mapAddresses haudit]
  apply reclamation_mapAddresses
    (result.renames_preAddressCtx haudit oracle)
  exact hraw

/-- Indexed-production analogue of
`lowerAllFullyAddressed_reclamation_of_raw`. -/
theorem lowerAllIndexedFullyAddressed_reclamation_of_raw
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : Lower.LowSt} {result : ReaddressAll.Result}
    (hlower :
      (Lower.lowerAllIndexedAction declarations main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      Lower.lowerAllIndexedFullyAddressed declarations main mainWorld
        compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw : LowerSim.Reclamation
      (result.preAddressCtx raw oracle) mainCode mainWorld) :
    LowerSim.Reclamation (result.addressedCtx oracle) result.main
      mainWorld := by
  have hrun :=
    Lower.readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      hlower haddressed
  have haudit := ReaddressAll.semanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_mapAddresses haudit]
  apply reclamation_mapAddresses
    (result.renames_preAddressCtx haudit oracle)
  exact hraw

/-- Alias-free indexed-production reclamation transport. The raw theorem is
stated against the literal declaration-list context and crosses the final SCC
pass through its certified rebuild renaming. -/
theorem lowerAllIndexedFullyAddressed_reclamation_of_exact_raw
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : Lower.LowSt} {result : ReaddressAll.Result}
    (hlower :
      (Lower.lowerAllIndexedAction declarations main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      Lower.lowerAllIndexedFullyAddressed declarations main mainWorld
        compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw : LowerSim.Reclamation
      (result.rebuildSourceCtx raw oracle) mainCode mainWorld) :
    LowerSim.Reclamation (result.addressedCtx oracle) result.main
      mainWorld := by
  have hrun :=
    Lower.readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      hlower haddressed
  have haudit := ReaddressAll.rebuildSemanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_rebuildMapAddresses haudit]
  apply reclamation_mapAddresses
    (result.renames_rebuildSourceCtx haudit oracle)
  exact hraw

/-- The indexed SCC-aware production boundary preserves every target-only
counter invariant already established for its certified raw execution
context. -/
theorem lowerAllIndexedFullyAddressed_runCostInvariant_of_raw
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : Lower.LowSt} {result : ReaddressAll.Result}
    {spec : LowerSim.CostObservation → Prop}
    (hlower :
      (Lower.lowerAllIndexedAction declarations main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      Lower.lowerAllIndexedFullyAddressed declarations main mainWorld
        compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw : LowerSim.RunCostInvariant
      (result.preAddressCtx raw oracle) mainCode spec) :
    LowerSim.RunCostInvariant (result.addressedCtx oracle) result.main
      spec := by
  have hrun :=
    Lower.readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      hlower haddressed
  have haudit := ReaddressAll.semanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_mapAddresses haudit]
  intro targetFuel targetStore targetValue htarget
  exact runCostInvariant_mapAddresses
    (spec := spec) (result.renames_preAddressCtx haudit oracle)
    hraw htarget

/-- Alias-free transport of target-only counter invariants through complete
SCC addressing. -/
theorem lowerAllIndexedFullyAddressed_runCostInvariant_of_exact_raw
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : Lower.LowSt} {result : ReaddressAll.Result}
    {spec : LowerSim.CostObservation → Prop}
    (hlower :
      (Lower.lowerAllIndexedAction declarations main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      Lower.lowerAllIndexedFullyAddressed declarations main mainWorld
        compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw : LowerSim.RunCostInvariant
      (result.rebuildSourceCtx raw oracle) mainCode spec) :
    LowerSim.RunCostInvariant (result.addressedCtx oracle) result.main
      spec := by
  have hrun :=
    Lower.readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      hlower haddressed
  have haudit := ReaddressAll.rebuildSemanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_rebuildMapAddresses haudit]
  intro targetFuel targetStore targetValue htarget
  exact runCostInvariant_mapAddresses
    (spec := spec) (result.renames_rebuildSourceCtx haudit oracle)
    hraw htarget

/-- The actual indexed, fully-addressed compiler output satisfies the first
concrete `CostRefinement` equation, `reuses = 0`, whenever its certified
pre-address context is reuse-free.  This premise is explicit because the
semantic transport context also contains stable aliases, not just the raw
declaration list returned by lowering. -/
theorem lowerAllIndexedFullyAddressed_reuseCostRefinement
    {sourceCtx : IxIR0.Ctx} {funRel : Sim.FunctionRel}
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : Lower.LowSt} {result : ReaddressAll.Result}
    (hlower :
      (Lower.lowerAllIndexedAction declarations main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      Lower.lowerAllIndexedFullyAddressed declarations main mainWorld
        compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hctx : CtxNoReuse (result.preAddressCtx raw oracle)) :
    LowerSim.CostRefinement sourceCtx (result.addressedCtx oracle)
      main result.main funRel
      (fun _ observation => ReuseFreeCostSpec observation) := by
  apply LowerSim.RunCostInvariant.costRefinement
  have hlower' :
      (Lower.lowerAllAction declarations main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState := by
    simpa only [Lower.lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have hrawCost : LowerSim.RunCostInvariant
      (result.preAddressCtx raw oracle) mainCode ReuseFreeCostSpec := by
    intro targetFuel targetStore targetValue htarget
    exact runCostInvariant_of_noReuse hctx
      (lowerAllAction_noReuse hlower').2.1 htarget
  intro targetFuel targetStore targetValue htarget
  exact lowerAllIndexedFullyAddressed_runCostInvariant_of_raw
    (spec := ReuseFreeCostSpec) hlower haddressed oracle hrawCost htarget

/-- The indexed fully-addressed production output satisfies the complete
current-lowerer counter contract `reuses = 0 ∧ frees ≤ allocs`. -/
theorem lowerAllIndexedFullyAddressed_costRefinement
    {sourceCtx : IxIR0.Ctx} {funRel : Sim.FunctionRel}
    {declarations : List (Ixon.Address × IxIR0.Decl)}
    {main : IxIR0.Expr} {mainWorld : Ixon.Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : Lower.LowSt} {result : ReaddressAll.Result}
    (hlower :
      (Lower.lowerAllIndexedAction declarations main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      Lower.lowerAllIndexedFullyAddressed declarations main mainWorld
        compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hctx : CtxNoReuse (result.preAddressCtx raw oracle)) :
    LowerSim.CostRefinement sourceCtx (result.addressedCtx oracle)
      main result.main funRel
      (fun _ observation => CurrentLowererCostSpec observation) := by
  have hreuses : LowerSim.CostRefinement sourceCtx
      (result.addressedCtx oracle) main result.main funRel
      (fun _ observation => ReuseFreeCostSpec observation) :=
    lowerAllIndexedFullyAddressed_reuseCostRefinement
      (sourceCtx := sourceCtx) (funRel := funRel)
      hlower haddressed oracle hctx
  have hallocFree : LowerSim.CostRefinement sourceCtx
      (result.addressedCtx oracle) main result.main funRel
      (fun _ observation => LowerSim.AllocationFreeCostSpec observation) :=
    LowerSim.allocationFreeCostRefinement
  change LowerSim.CostRefinement sourceCtx (result.addressedCtx oracle)
    main result.main funRel (fun _ observation =>
      ReuseFreeCostSpec observation ∧
        LowerSim.AllocationFreeCostSpec observation)
  apply LowerSim.CostRefinement.and
  · exact hreuses
  · exact hallocFree

end Ix.Compiler.IxIR1.NoReuse
