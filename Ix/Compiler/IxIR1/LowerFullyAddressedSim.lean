import Ix.Compiler.IxIR1.LowerAddressedSim
import Ix.Compiler.IxIR1.LowerFullyAddressed
import Ix.Compiler.IxIR1.ReaddressAllSim

/-!
# Semantic boundary for fully content-addressed IxIR₁ lowering

The raw whole-pass compiler still uses transient producer labels internally.
`LowerFullyAddressed` sends the complete raw declaration graph through the
SCC-aware pass, rekeying source and generated functions together while fixing
constructor identities and stable extern ABI keys.  This module composes that
exact successful call with evaluator equivariance and the existing raw
lowering relations.
-/

namespace Ix.Compiler.IxIR1.LowerSim

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR1.Lower

/-- Exact evaluator-result transport for the transparent lowerer. -/
theorem lowerAllFullyAddressed_runMain
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllFullyAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Address → List RVal → Option RVal)
    (runFuel : Nat) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      Readdress.mapRunResult
        (Readdress.Renaming.apply result.addressMap)
        (runMain (result.preAddressCtx raw oracle) mainCode runFuel) := by
  exact ReaddressAll.runMain_of_run_eq_ok
    (readdressAll_run_of_lowerAllFullyAddressed_eq_ok hlower haddressed)
    oracle runFuel

/-- Exact evaluator-result transport for the indexed production lowerer. -/
theorem lowerAllIndexedFullyAddressed_runMain
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (runFuel : Nat) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      Readdress.mapRunResult
        (Readdress.Renaming.apply result.addressMap)
        (runMain (result.preAddressCtx raw oracle) mainCode runFuel) := by
  exact ReaddressAll.runMain_of_run_eq_ok
    (readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      hlower haddressed) oracle runFuel

/-- Alias-free evaluator-result transport for the indexed production
lowerer. The raw source context is literally `Env.ofList raw`; the certified
rebuild renaming supplies the total address action needed by the final graph. -/
theorem lowerAllIndexedFullyAddressed_runMain_exact
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (runFuel : Nat) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      Readdress.mapRunResult (result.rebuildRename raw)
        (runMain (result.rebuildSourceCtx raw oracle) mainCode runFuel) := by
  exact ReaddressAll.runMain_exact_of_run_eq_ok
    (readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
      hlower haddressed) oracle runFuel

/-- Successful raw execution gives the exact fully addressed heap image and
the same scalar/location result. -/
theorem lowerAllIndexedFullyAddressed_runMain_success
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel runFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    {store : Store} {value : RVal}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel =
        .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      .ok (Readdress.Store.mapAddresses
        (Readdress.Renaming.apply result.addressMap) store, value) := by
  rw [lowerAllIndexedFullyAddressed_runMain
    hlower haddressed oracle runFuel, hsource]
  rfl

/-- Successful execution in the exact raw context gives the corresponding
fully addressed heap under the certified rebuild renaming. -/
theorem lowerAllIndexedFullyAddressed_runMain_exact_success
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel runFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    {store : Store} {value : RVal}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hsource :
      runMain (result.rebuildSourceCtx raw oracle) mainCode runFuel =
        .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      .ok (Readdress.Store.mapAddresses
        (result.rebuildRename raw) store, value) := by
  rw [lowerAllIndexedFullyAddressed_runMain_exact
    hlower haddressed oracle runFuel, hsource]
  rfl

/-- Every original constructor identity is fixed by the complete target map.
Unlike the old generated-only boundary, source function identities are not
claimed fixed: they are deliberately content-addressed. -/
theorem lowerAllIndexedFullyAddressed_apply_constructorIdentity
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    {address : Address}
    (haddress : address ∈ constructorIdentities decls) :
    Readdress.Renaming.apply result.addressMap address = address := by
  have hrun := readdressAll_run_of_lowerAllIndexedFullyAddressed_eq_ok
    hlower haddressed
  have haudit := ReaddressAll.semanticAudit_of_run_eq_ok hrun
  apply result.apply_reserved haudit
  rw [ReaddressAll.reserved_of_run_eq_ok hrun]
  exact haddress

/-- Any raw IxIR₀→IxIR₁ forward simulation composes with complete
source/generated readdressing. -/
theorem lowerAllIndexedFullyAddressed_semanticForwardSimulation
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    {funRel : Sim.FunctionRel}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hraw : SemanticForwardSimulation sourceCtx
      (result.preAddressCtx raw oracle) main mainCode funRel) :
    AddressedSemanticForwardSimulation sourceCtx
      (result.addressedCtx oracle) main result.main
      (Readdress.Renaming.apply result.addressMap) funRel := by
  intro sourceFuel sourceValue hsource
  obtain ⟨targetFuel, rawStore, targetValue, htarget, hgraph⟩ :=
    hraw hsource
  refine ⟨targetFuel,
    Readdress.Store.mapAddresses
      (Readdress.Renaming.apply result.addressMap) rawStore,
    targetValue, ?_, rawStore, rfl, hgraph⟩
  exact lowerAllIndexedFullyAddressed_runMain_success
    hlower haddressed oracle htarget

/-- Exact-source form of complete readdressing. Unlike the generic transport,
this theorem needs no alias-completed raw context and records the certified
`rebuildRename` heap image in the addressed value graph. -/
theorem lowerAllIndexedFullyAddressed_semanticForwardSimulation_exact
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    {funRel : Sim.FunctionRel}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hraw : SemanticForwardSimulation sourceCtx
      (result.rebuildSourceCtx raw oracle) main mainCode funRel) :
    AddressedSemanticForwardSimulation sourceCtx
      (result.addressedCtx oracle) main result.main
      (result.rebuildRename raw) funRel := by
  intro sourceFuel sourceValue hsource
  obtain ⟨targetFuel, rawStore, targetValue, htarget, hgraph⟩ :=
    hraw hsource
  refine ⟨targetFuel,
    Readdress.Store.mapAddresses (result.rebuildRename raw) rawStore,
    targetValue, ?_, rawStore, rfl, hgraph⟩
  exact lowerAllIndexedFullyAddressed_runMain_exact_success
    hlower haddressed oracle htarget

/-- Complete readdressing cannot introduce a memory-discipline error. -/
theorem lowerAllIndexedFullyAddressed_memoryErrorUnreachable
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hraw : MemoryErrorUnreachable
      (result.preAddressCtx raw oracle) mainCode) :
    MemoryErrorUnreachable (result.addressedCtx oracle) result.main := by
  intro runFuel message htarget
  have htransport := lowerAllIndexedFullyAddressed_runMain
    hlower haddressed oracle runFuel
  rw [htarget] at htransport
  cases hsource : runMain (result.preAddressCtx raw oracle) mainCode runFuel with
  | ok output =>
      rcases output with ⟨store, value⟩
      simp [hsource] at htransport
  | error error =>
      cases error with
      | fuel => simp [hsource] at htransport
      | stuck sourceMessage => simp [hsource] at htransport
      | mem sourceMessage => exact hraw runFuel sourceMessage hsource
      | unknownRef address => simp [hsource] at htransport

/-- Complete readdressing cannot introduce ordinary stuckness. -/
theorem lowerAllIndexedFullyAddressed_ordinaryStuckUnreachable
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hraw : OrdinaryStuckUnreachable
      (result.preAddressCtx raw oracle) mainCode) :
    OrdinaryStuckUnreachable (result.addressedCtx oracle) result.main := by
  intro runFuel message htarget
  have htransport := lowerAllIndexedFullyAddressed_runMain
    hlower haddressed oracle runFuel
  rw [htarget] at htransport
  cases hsource : runMain (result.preAddressCtx raw oracle) mainCode runFuel with
  | ok output =>
      rcases output with ⟨store, value⟩
      simp [hsource] at htransport
  | error error =>
      cases error with
      | fuel => simp [hsource] at htransport
      | stuck sourceMessage => exact hraw runFuel sourceMessage hsource
      | mem sourceMessage => simp [hsource] at htransport
      | unknownRef address => simp [hsource] at htransport

/-- Complete readdressing cannot introduce a closed-world lookup failure. -/
theorem lowerAllIndexedFullyAddressed_unknownRefUnreachable
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hraw : UnknownRefUnreachable
      (result.preAddressCtx raw oracle) mainCode) :
    UnknownRefUnreachable (result.addressedCtx oracle) result.main := by
  intro runFuel address htarget
  have htransport := lowerAllIndexedFullyAddressed_runMain
    hlower haddressed oracle runFuel
  rw [htarget] at htransport
  cases hsource : runMain (result.preAddressCtx raw oracle) mainCode runFuel with
  | ok output =>
      rcases output with ⟨store, value⟩
      simp [hsource] at htransport
  | error error =>
      cases error with
      | fuel => simp [hsource] at htransport
      | stuck sourceMessage => simp [hsource] at htransport
      | mem sourceMessage => simp [hsource] at htransport
      | unknownRef sourceAddress => exact hraw runFuel sourceAddress hsource

/-- All four instruction-level store counters survive complete readdressing. -/
theorem lowerAllIndexedFullyAddressed_runMain_cost
    {decls : List (Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel runFuel : Nat}
    {raw : List (Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : ReaddressAll.Result}
    {store : Store} {value : RVal}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedFullyAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Address → List RVal → Option RVal)
    (hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel =
        .ok (store, value)) :
    ∃ addressedStore,
      runMain (result.addressedCtx oracle) result.main runFuel =
          .ok (addressedStore, value) ∧
        costObservation addressedStore = costObservation store := by
  refine ⟨Readdress.Store.mapAddresses
      (Readdress.Renaming.apply result.addressMap) store, ?_, ?_⟩
  · exact lowerAllIndexedFullyAddressed_runMain_success
      hlower haddressed oracle hsource
  · exact costObservation_mapAddresses _ _

end Ix.Compiler.IxIR1.LowerSim
