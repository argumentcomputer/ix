import Ix.Compiler.IxIR1.LowerAddressed
import Ix.Compiler.IxIR1.LowerSim
import Ix.Compiler.IxIR1.ReaddressSim

/-!
# Semantic boundary for content-addressed IxIR₁ lowering

The theorem-facing lowerer returns source-backed declarations followed by
the final generated-declaration suffix.  The production boundary rekeys that
suffix and all references into it.  This module connects those two successful
runs and transports exact evaluator results, the three public dynamic-error
exclusion properties, and instruction-level cost observations.

The raw side deliberately uses `Readdress.Result.preAddressCtx`.  It agrees
with every successful lookup in the raw list and supplies stable aliases at
new content keys, which is the total context required by evaluator
equivariance after deduplication.
-/

namespace Ix.Compiler.IxIR1.LowerSim

open Ix.Compiler.Ixon (Owned)
open Ix.Compiler.IxIR1.Lower

/-- A source value is realized by an addressed heap when that heap is the
address image of some raw heap carrying the existing `ValueGraph` witness.
This keeps locations, values, and graph structure exact while recording the
only representation change introduced by the post-pass. -/
def AddressedValueGraph (rename : Ixon.Address → Ixon.Address)
    (funRel : Sim.FunctionRel) (store : Store)
    (sourceValue : IxIR0.Value) (targetValue : RVal) : Prop :=
  ∃ rawStore,
    store = Readdress.Store.mapAddresses rename rawStore ∧
      Sim.ValueGraph funRel rawStore sourceValue targetValue

/-- Forward simulation whose target heap is compared modulo the declared
address image.  Unlike the ordinary `SemanticForwardSimulation`, this
relation does not silently require generated function keys or constructor
identities to remain textually unchanged. -/
def AddressedSemanticForwardSimulation
    (sourceCtx : IxIR0.Ctx) (targetCtx : Ctx)
    (source : IxIR0.Expr) (target : Code)
    (rename : Ixon.Address → Ixon.Address)
    (funRel : Sim.FunctionRel) : Prop :=
  ∀ {sourceFuel sourceValue},
    IxIR0.eval sourceCtx sourceFuel [] source = .ok sourceValue →
    ∃ targetFuel targetStore targetValue,
      runMain targetCtx target targetFuel = .ok (targetStore, targetValue) ∧
        AddressedValueGraph rename funRel targetStore sourceValue targetValue

private theorem estateBindRun_ok_inv_addressed
    {error state alpha beta : Type}
    {action : EStateM error state alpha}
    {next : alpha → EStateM error state beta}
    {initial finalState : state} {result : beta}
    (hrun : (action >>= next).run initial = .ok result finalState) :
    ∃ value middle,
      action.run initial = .ok value middle ∧
      (next value).run middle = .ok result finalState := by
  change
    (match action.run initial with
      | .ok value nextState => (next value).run nextState
      | .error error nextState => .error error nextState) =
        .ok result finalState at hrun
  cases haction : action.run initial with
  | ok value middle =>
      rw [haction] at hrun
      exact ⟨value, middle, rfl, hrun⟩
  | error error middle =>
      rw [haction] at hrun
      contradiction

private theorem lowerAllAction_run_of_indexed
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState) :
    (lowerAllAction decls main mainWorld compilerFuel).run {} =
      .ok (raw, mainCode) finalState := by
  simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower

private theorem lowerAllAddressed_eq_ok_of_indexed
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {result : Readdress.Result}
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result) :
    lowerAllAddressed decls main mainWorld compilerFuel = .ok result := by
  rw [lowerAllIndexedAddressed_eq_lowerAllAddressed] at haddressed
  exact haddressed

/-- A successful whole-program action returns some source-backed prefix
followed by exactly the generated declarations stored in its final state. -/
theorem lowerAllAction_result_split
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {initial finalState : LowSt}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run initial =
        .ok (raw, mainCode) finalState) :
    ∃ source, raw = source ++ finalState.extra := by
  simp only [lowerAllAction] at hlower
  obtain ⟨base, baseState, _hbase, hafterBase⟩ :=
    estateBindRun_ok_inv_addressed hlower
  obtain ⟨compiledMain, mainState, _hmain, hafterMain⟩ :=
    estateBindRun_ok_inv_addressed hafterBase
  obtain ⟨observed, getState, hget, hpure⟩ :=
    estateBindRun_ok_inv_addressed hafterMain
  have hget' : mainState = observed ∧ mainState = getState := by
    simpa using hget
  obtain ⟨hobserved, hgetState⟩ := hget'
  subst observed
  subst getState
  have hpure' :
      (base ++ mainState.extra, compiledMain) = (raw, mainCode) ∧
        mainState = finalState := by
    simpa using hpure
  obtain ⟨hresult, hstate⟩ := hpure'
  subst finalState
  exact ⟨base, (congrArg Prod.fst hresult).symm⟩

/-- A successful addressed result and its successful raw compiler run expose
one exact, certified readdressing call over the raw result split. -/
theorem lowerAllAddressed_readdress_run
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result) :
    ∃ source,
      raw = source ++ finalState.extra ∧
      Readdress.run source finalState.extra mainCode = .ok result := by
  obtain ⟨source, hraw⟩ := lowerAllAction_result_split hlower
  refine ⟨source, hraw, ?_⟩
  have hprotected :=
    readdress_run_of_lowerAllAddressed_eq_ok hlower haddressed
  have hprotected' :
      Readdress.runProtected (decls.map Prod.fst) source
          finalState.extra mainCode = .ok result := by
    simpa only [hraw, sourcePrefix_append] using hprotected
  exact (Readdress.run_and_protects_of_runProtected_eq_ok hprotected').1

/-- Production lowering fixes every original IxIR₀ declaration identity,
including constructor keys omitted from the raw IxIR₁ environment. -/
theorem lowerAllAddressed_protectsSourceAddresses
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result) :
    result.protects (decls.map Prod.fst) = true :=
  (Readdress.run_and_protects_of_runProtected_eq_ok
    (readdress_run_of_lowerAllAddressed_eq_ok hlower haddressed)).2

/-- Pointwise form of `lowerAllAddressed_protectsSourceAddresses`. -/
theorem lowerAllAddressed_apply_source_address
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    {address : Ixon.Address} {sourceDecl : IxIR0.Decl}
    (hmember : (address, sourceDecl) ∈ decls) :
    Readdress.Renaming.apply result.addressMap address = address := by
  apply result.apply_eq_of_protects
    (lowerAllAddressed_protectsSourceAddresses hlower haddressed)
  exact List.mem_map.mpr ⟨(address, sourceDecl), hmember, rfl⟩

/-- Indexed production entry points carry the same source-identity
protection certificate. -/
theorem lowerAllIndexedAddressed_protectsSourceAddresses
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result) :
    result.protects (decls.map Prod.fst) = true :=
  lowerAllAddressed_protectsSourceAddresses
    (lowerAllAction_run_of_indexed hlower)
    (lowerAllAddressed_eq_ok_of_indexed haddressed)

/-- The compiled main before and after the production address pass has one
exact evaluator result at every fuel.  Values and heap locations are
unchanged; declaration identities retained in heap nodes are rekeyed. -/
theorem lowerAllAddressed_runMain
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (runFuel : Nat) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      Readdress.mapRunResult
        (Readdress.Renaming.apply result.addressMap)
        (runMain (result.preAddressCtx raw oracle) mainCode runFuel) := by
  obtain ⟨source, hraw, hrun⟩ :=
    lowerAllAddressed_readdress_run hlower haddressed
  subst raw
  exact Readdress.runMain_of_run_eq_ok hrun oracle runFuel

/-- Production indexed-entry analogue of `lowerAllAddressed_runMain`. -/
theorem lowerAllIndexedAddressed_runMain
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (runFuel : Nat) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      Readdress.mapRunResult
        (Readdress.Renaming.apply result.addressMap)
        (runMain (result.preAddressCtx raw oracle) mainCode runFuel) := by
  have hlower' :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState := by
    simpa only [lowerAllIndexedAction_eq_lowerAllAction] using hlower
  have haddressed' :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result := by
    rw [lowerAllIndexedAddressed_eq_lowerAllAddressed] at haddressed
    exact haddressed
  exact lowerAllAddressed_runMain hlower' haddressed' oracle runFuel

/-- Successful raw execution gives the exact addressed heap, the same
runtime value, and therefore the same observable result. -/
theorem lowerAllAddressed_runMain_success
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel runFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    {store : Store} {value : RVal}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel =
        .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      .ok
        (Readdress.Store.mapAddresses
          (Readdress.Renaming.apply result.addressMap) store,
        value) := by
  rw [lowerAllAddressed_runMain hlower haddressed oracle runFuel, hsource]
  rfl

/-- Successful-run form for the indexed production entry point. -/
theorem lowerAllIndexedAddressed_runMain_success
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel runFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    {store : Store} {value : RVal}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel =
        .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main runFuel =
      .ok
        (Readdress.Store.mapAddresses
          (Readdress.Renaming.apply result.addressMap) store,
        value) := by
  rw [lowerAllIndexedAddressed_runMain hlower haddressed oracle runFuel,
    hsource]
  rfl

/-- Every existing raw whole-program forward simulation composes with the
production address pass.  The resulting graph records the exact raw heap
witness whose address image is returned by the addressed evaluator. -/
theorem lowerAllAddressed_semanticForwardSimulation
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    {funRel : Sim.FunctionRel}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
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
  exact lowerAllAddressed_runMain_success hlower haddressed oracle htarget

/-- Direct composition theorem for the indexed production entry point. -/
theorem lowerAllIndexedAddressed_semanticForwardSimulation
    {sourceCtx : IxIR0.Ctx}
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    {funRel : Sim.FunctionRel}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
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
  exact lowerAllIndexedAddressed_runMain_success hlower haddressed oracle
    htarget

/-- Address rekeying cannot introduce a memory-discipline error. -/
theorem lowerAllAddressed_memoryErrorUnreachable
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw :
      MemoryErrorUnreachable (result.preAddressCtx raw oracle) mainCode) :
    MemoryErrorUnreachable (result.addressedCtx oracle) result.main := by
  intro runFuel message htarget
  have htransport :=
    lowerAllAddressed_runMain hlower haddressed oracle runFuel
  rw [htarget] at htransport
  cases hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel with
  | ok output =>
      rcases output with ⟨store, value⟩
      simp [hsource] at htransport
  | error error =>
      cases error with
      | fuel => simp [hsource] at htransport
      | stuck sourceMessage => simp [hsource] at htransport
      | mem sourceMessage => exact hraw runFuel sourceMessage hsource
      | unknownRef address => simp [hsource] at htransport

/-- Address rekeying cannot introduce an ordinary stuck result. -/
theorem lowerAllAddressed_ordinaryStuckUnreachable
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw :
      OrdinaryStuckUnreachable (result.preAddressCtx raw oracle) mainCode) :
    OrdinaryStuckUnreachable (result.addressedCtx oracle) result.main := by
  intro runFuel message htarget
  have htransport :=
    lowerAllAddressed_runMain hlower haddressed oracle runFuel
  rw [htarget] at htransport
  cases hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel with
  | ok output =>
      rcases output with ⟨store, value⟩
      simp [hsource] at htransport
  | error error =>
      cases error with
      | fuel => simp [hsource] at htransport
      | stuck sourceMessage => exact hraw runFuel sourceMessage hsource
      | mem sourceMessage => simp [hsource] at htransport
      | unknownRef address => simp [hsource] at htransport

/-- Address rekeying cannot introduce a closed-world lookup failure. -/
theorem lowerAllAddressed_unknownRefUnreachable
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw :
      UnknownRefUnreachable (result.preAddressCtx raw oracle) mainCode) :
    UnknownRefUnreachable (result.addressedCtx oracle) result.main := by
  intro runFuel address htarget
  have htransport :=
    lowerAllAddressed_runMain hlower haddressed oracle runFuel
  rw [htarget] at htransport
  cases hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel with
  | ok output =>
      rcases output with ⟨store, value⟩
      simp [hsource] at htransport
  | error error =>
      cases error with
      | fuel => simp [hsource] at htransport
      | stuck sourceMessage => simp [hsource] at htransport
      | mem sourceMessage => simp [hsource] at htransport
      | unknownRef sourceAddress =>
          exact hraw runFuel sourceAddress hsource

/-- Indexed production transport of memory-error exclusion. -/
theorem lowerAllIndexedAddressed_memoryErrorUnreachable
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw :
      MemoryErrorUnreachable (result.preAddressCtx raw oracle) mainCode) :
    MemoryErrorUnreachable (result.addressedCtx oracle) result.main :=
  lowerAllAddressed_memoryErrorUnreachable
    (lowerAllAction_run_of_indexed hlower)
    (lowerAllAddressed_eq_ok_of_indexed haddressed) oracle hraw

/-- Indexed production transport of ordinary-stuck exclusion. -/
theorem lowerAllIndexedAddressed_ordinaryStuckUnreachable
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw : OrdinaryStuckUnreachable
      (result.preAddressCtx raw oracle) mainCode) :
    OrdinaryStuckUnreachable (result.addressedCtx oracle) result.main :=
  lowerAllAddressed_ordinaryStuckUnreachable
    (lowerAllAction_run_of_indexed hlower)
    (lowerAllAddressed_eq_ok_of_indexed haddressed) oracle hraw

/-- Indexed production transport of closed-world lookup safety. -/
theorem lowerAllIndexedAddressed_unknownRefUnreachable
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hraw :
      UnknownRefUnreachable (result.preAddressCtx raw oracle) mainCode) :
    UnknownRefUnreachable (result.addressedCtx oracle) result.main :=
  lowerAllAddressed_unknownRefUnreachable
    (lowerAllAction_run_of_indexed hlower)
    (lowerAllAddressed_eq_ok_of_indexed haddressed) oracle hraw

@[simp] theorem costObservation_mapAddresses
    (rename : Ixon.Address → Ixon.Address) (store : Store) :
    costObservation (Readdress.Store.mapAddresses rename store) =
      costObservation store := by
  rfl

/-- The address pass preserves all four instruction-level counters on every
successful whole-main run. -/
theorem lowerAllAddressed_runMain_cost
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel runFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    {store : Store} {value : RVal}
    (hlower :
      (lowerAllAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllAddressed decls main mainWorld compilerFuel = .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel =
        .ok (store, value)) :
    ∃ addressedStore,
      runMain (result.addressedCtx oracle) result.main runFuel =
          .ok (addressedStore, value) ∧
        costObservation addressedStore = costObservation store := by
  refine ⟨Readdress.Store.mapAddresses
      (Readdress.Renaming.apply result.addressMap) store, ?_, ?_⟩
  · exact lowerAllAddressed_runMain_success hlower haddressed oracle hsource
  · exact costObservation_mapAddresses _ _

/-- Indexed production entry point preserves the same cost observation. -/
theorem lowerAllIndexedAddressed_runMain_cost
    {decls : List (Ixon.Address × IxIR0.Decl)} {main : IxIR0.Expr}
    {mainWorld : Owned} {compilerFuel runFuel : Nat}
    {raw : List (Ixon.Address × Decl)} {mainCode : Code}
    {finalState : LowSt} {result : Readdress.Result}
    {store : Store} {value : RVal}
    (hlower :
      (lowerAllIndexedAction decls main mainWorld compilerFuel).run {} =
        .ok (raw, mainCode) finalState)
    (haddressed :
      lowerAllIndexedAddressed decls main mainWorld compilerFuel =
        .ok result)
    (oracle : Ixon.Address → List RVal → Option RVal)
    (hsource :
      runMain (result.preAddressCtx raw oracle) mainCode runFuel =
        .ok (store, value)) :
    ∃ addressedStore,
      runMain (result.addressedCtx oracle) result.main runFuel =
          .ok (addressedStore, value) ∧
        costObservation addressedStore = costObservation store := by
  refine ⟨Readdress.Store.mapAddresses
      (Readdress.Renaming.apply result.addressMap) store, ?_, ?_⟩
  · exact lowerAllIndexedAddressed_runMain_success hlower haddressed oracle
      hsource
  · exact costObservation_mapAddresses _ _

end Ix.Compiler.IxIR1.LowerSim
