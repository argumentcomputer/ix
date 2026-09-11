import Ix.Compiler.EraseAddressedSim
import Ix.Compiler.IxIR1.LowerAddressedSim
import Ix.Compiler.IxIR1.LowerFullyAddressedSim

/-!
# Composing IxIR₀ mutual-block and IxIR₁ generated-code addressing

The production pipeline now crosses two independent address maps:

1. cycle-safe IxIR₀ mutual blocks replace legacy member keys and map every
   address retained in source values; and
2. IxIR₁ lowering preserves those source-backed keys while content-addressing
   generated functions and mapping identities retained in the target heap.

This module composes the two existing evaluator transports.  It deliberately
keeps the maps separate: their domains and runtime actions differ, and
collapsing them into an untyped provenance list would obscure which value or
heap layer each map acts on.
-/

namespace Ix.Compiler.IxIR1.LowerSim

open Ix.Compiler.Ixon (Address Constant Owned)
open Ix.Compiler.IxIR1.Lower

/-- A final target heap realizes the IxIR₀ address image of a legacy source
value, modulo the independent IxIR₁ generated-declaration address image. -/
def MutualAddressedValueGraph
    (sourceRename targetRename : Address → Address)
    (funRel : Sim.FunctionRel) (store : Store)
    (legacyValue : IxIR0.Value) (targetValue : RVal) : Prop :=
  AddressedValueGraph targetRename funRel store
    (IxIR0.Readdress.Value.mapAddresses sourceRename legacyValue)
    targetValue

/-- Forward simulation spanning both production address maps. -/
def MutualAddressedSemanticForwardSimulation
    (legacyCtx : IxIR0.Ctx) (targetCtx : Ctx)
    (legacyMain : IxIR0.Expr) (targetMain : Code)
    (sourceRename targetRename : Address → Address)
    (funRel : Sim.FunctionRel) : Prop :=
  ∀ {sourceFuel sourceValue},
    IxIR0.eval legacyCtx sourceFuel [] legacyMain = .ok sourceValue →
    ∃ targetFuel targetStore targetValue,
      runMain targetCtx targetMain targetFuel =
          .ok (targetStore, targetValue) ∧
        MutualAddressedValueGraph sourceRename targetRename funRel
          targetStore sourceValue targetValue

/-- Precompose an addressed IxIR₀→IxIR₁ simulation with the generic IxIR₀
evaluator-renaming theorem. -/
theorem AddressedSemanticForwardSimulation.precomposeIxIR0
    {sourceRename targetRename : Address → Address}
    {legacyCtx addressedCtx : IxIR0.Ctx} {targetCtx : Ctx}
    {legacyMain addressedMain : IxIR0.Expr} {targetMain : Code}
    {funRel : Sim.FunctionRel}
    (contexts : IxIR0.Readdress.Ctx.Renames sourceRename
      legacyCtx addressedCtx)
    (hmain : addressedMain =
      IxIR0.MutualBlock.Concrete.Expr.mapAddresses sourceRename legacyMain)
    (hsim : AddressedSemanticForwardSimulation addressedCtx targetCtx
      addressedMain targetMain targetRename funRel) :
    MutualAddressedSemanticForwardSimulation legacyCtx targetCtx
      legacyMain targetMain sourceRename targetRename funRel := by
  intro sourceFuel sourceValue hsource
  have htransport := IxIR0.Readdress.eval_mapAddresses contexts
    sourceFuel [] legacyMain
  rw [hsource] at htransport
  simp only [IxIR0.Readdress.mapResult] at htransport
  rw [← hmain] at htransport
  have htransport' :
      IxIR0.eval addressedCtx sourceFuel [] addressedMain =
        .ok (IxIR0.Readdress.Value.mapAddresses sourceRename sourceValue) := by
    simpa only [IxIR0.Readdress.ValueList.mapAddresses_nil] using htransport
  obtain ⟨targetFuel, targetStore, targetValue, htarget, hgraph⟩ :=
    hsim htransport'
  exact ⟨targetFuel, targetStore, targetValue, htarget, hgraph⟩

/-- A successful addressed erasure supplies the concrete precomposition data
for any downstream addressed IxIR₀→IxIR₁ simulation. -/
theorem AddressedSemanticForwardSimulation.precomposeAddressedErasure
    {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {legacyMain : IxIR0.Expr}
    {eraseFuel : Nat} {erased : EraseAddressed.Result}
    (herase : EraseAddressed.run eraseCtx constants legacyMain eraseFuel =
      .ok erased)
    (beforeOracle afterOracle : IxIR0.Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    {targetRename : Address → Address} {targetCtx : Ctx}
    {targetMain : Code} {funRel : Sim.FunctionRel}
    (hsim : AddressedSemanticForwardSimulation
      (erased.addressed.addressedCtx afterOracle) targetCtx
      erased.main targetMain targetRename funRel) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      targetCtx legacyMain targetMain
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      targetRename funRel := by
  have haudit := EraseAddressed.semanticAudit_of_run_eq_ok herase
  have haddressed := erased.addressed_audit haudit
  have hmain := erased.addressed.main_eq_mapAddresses haddressed
  apply AddressedSemanticForwardSimulation.precomposeIxIR0
    (erased.addressed.renames_preAddressCtx haddressed
      beforeOracle afterOracle horacle)
  · simpa only [EraseAddressed.Result.main] using hmain
  · exact hsim

/-- Full production composition: a successful cycle-safe erasure, a
successful indexed lowerer/readdresser, and the existing raw lowering
simulation yield one forward simulation across both address maps. -/
theorem lowerAllIndexedAddressed_after_addressedErasure
    {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {legacyMain : IxIR0.Expr}
    {eraseFuel : Nat} {erased : EraseAddressed.Result}
    (herase : EraseAddressed.run eraseCtx constants legacyMain eraseFuel =
      .ok erased)
    (beforeOracle afterOracle : IxIR0.Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : Readdress.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    {funRel : Sim.FunctionRel}
    (hlowering : SemanticForwardSimulation
      (erased.addressed.addressedCtx afterOracle)
      (lowered.preAddressCtx raw targetOracle)
      erased.main mainCode funRel) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      (lowered.addressedCtx targetOracle)
      legacyMain lowered.main
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      (Readdress.Renaming.apply lowered.addressMap) funRel := by
  have hsim : AddressedSemanticForwardSimulation
      (erased.addressed.addressedCtx afterOracle)
      (lowered.addressedCtx targetOracle) erased.main lowered.main
      (Readdress.Renaming.apply lowered.addressMap) funRel :=
    lowerAllIndexedAddressed_semanticForwardSimulation
      hlower haddressed targetOracle hlowering
  intro sourceFuel sourceValue hsource
  exact AddressedSemanticForwardSimulation.precomposeAddressedErasure
    (targetRename := Readdress.Renaming.apply lowered.addressMap)
    (targetCtx := lowered.addressedCtx targetOracle)
    (targetMain := lowered.main) (funRel := funRel)
    herase beforeOracle afterOracle horacle hsim hsource

/-- Full production composition for the SCC-aware target boundary.  The
second map is now complete: it rekeys source and generated IxIR₁ functions,
while its audited reserved set fixes constructor identities. -/
theorem lowerAllIndexedFullyAddressed_after_addressedErasure
    {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {legacyMain : IxIR0.Expr}
    {eraseFuel : Nat} {erased : EraseAddressed.Result}
    (herase : EraseAddressed.run eraseCtx constants legacyMain eraseFuel =
      .ok erased)
    (beforeOracle afterOracle : IxIR0.Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    {funRel : Sim.FunctionRel}
    (hlowering : SemanticForwardSimulation
      (erased.addressed.addressedCtx afterOracle)
      (lowered.preAddressCtx raw targetOracle)
      erased.main mainCode funRel) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      (lowered.addressedCtx targetOracle)
      legacyMain lowered.main
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      (Readdress.Renaming.apply lowered.addressMap) funRel := by
  have hsim : AddressedSemanticForwardSimulation
      (erased.addressed.addressedCtx afterOracle)
      (lowered.addressedCtx targetOracle) erased.main lowered.main
      (Readdress.Renaming.apply lowered.addressMap) funRel :=
    lowerAllIndexedFullyAddressed_semanticForwardSimulation
      hlower haddressed targetOracle hlowering
  intro sourceFuel sourceValue hsource
  exact AddressedSemanticForwardSimulation.precomposeAddressedErasure
    (targetRename := Readdress.Renaming.apply lowered.addressMap)
    (targetCtx := lowered.addressedCtx targetOracle)
    (targetMain := lowered.main) (funRel := funRel)
    herase beforeOracle afterOracle horacle hsim hsource

/-- Alias-free production composition. The raw IxIR₁ simulation runs in
the literal lowering environment, and the final heap is related through the
certified exact-source `rebuildRename` rather than an alias-bearing adapter. -/
theorem lowerAllIndexedFullyAddressed_exact_after_addressedErasure
    {eraseCtx : Erase.EraseCtx}
    {constants : List (Address × Constant)} {legacyMain : IxIR0.Expr}
    {eraseFuel : Nat} {erased : EraseAddressed.Result}
    (herase : EraseAddressed.run eraseCtx constants legacyMain eraseFuel =
      .ok erased)
    (beforeOracle afterOracle : IxIR0.Oracle)
    (horacle : ∀ address arguments,
      afterOracle
          (IxIR0.MutualBlock.Renaming.apply erased.addressMap address)
          (IxIR0.Readdress.ValueList.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap) arguments) =
        (beforeOracle address arguments).map
          (IxIR0.Readdress.Value.mapAddresses
            (IxIR0.MutualBlock.Renaming.apply erased.addressMap)))
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {lowered : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction erased.declarations erased.main mainWorld
        compilerFuel).run {} = .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed erased.declarations erased.main mainWorld
        compilerFuel = .ok lowered)
    (targetOracle : Address → List RVal → Option RVal)
    {funRel : Sim.FunctionRel}
    (hlowering : SemanticForwardSimulation
      (erased.addressed.addressedCtx afterOracle)
      (lowered.rebuildSourceCtx raw targetOracle)
      erased.main mainCode funRel) :
    MutualAddressedSemanticForwardSimulation
      (erased.addressed.preAddressCtx erased.groups beforeOracle)
      (lowered.addressedCtx targetOracle)
      legacyMain lowered.main
      (IxIR0.MutualBlock.Renaming.apply erased.addressMap)
      (lowered.rebuildRename raw) funRel := by
  have hsim : AddressedSemanticForwardSimulation
      (erased.addressed.addressedCtx afterOracle)
      (lowered.addressedCtx targetOracle) erased.main lowered.main
      (lowered.rebuildRename raw) funRel :=
    lowerAllIndexedFullyAddressed_semanticForwardSimulation_exact
      hlower haddressed targetOracle hlowering
  intro sourceFuel sourceValue hsource
  exact AddressedSemanticForwardSimulation.precomposeAddressedErasure
    (targetRename := lowered.rebuildRename raw)
    (targetCtx := lowered.addressedCtx targetOracle)
    (targetMain := lowered.main) (funRel := funRel)
    herase beforeOracle afterOracle horacle hsim hsource

end Ix.Compiler.IxIR1.LowerSim
