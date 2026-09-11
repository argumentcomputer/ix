import Ix.Compiler.IxIR1.ReaddressAll
import Ix.Compiler.IxIR1.ReaddressSim

/-!
# Semantic transport for whole-program IxIR₁ readdressing

`ReaddressAll.Result` retains richer stable/ordinary/block provenance than the
generated-only result, but its semantic core is the same exact address image.
This module projects that core into the already proved evaluator equivariance
interface and exposes concrete successful-run transport for the SCC pass.
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address)

namespace ReaddressAll

namespace Result

def addressedCtx (result : Result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) : Ctx :=
  result.asReaddressResult.addressedCtx oracle

def preAddressCtx (result : Result)
    (raw : List (Address × Decl))
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) : Ctx :=
  result.asReaddressResult.preAddressCtx raw oracle

/-- Exact old-keyed source context for a certified rebuild.  Unlike
`preAddressCtx`, its declaration environment contains no aliases. -/
def rebuildSourceCtx (result : Result)
    (raw : List (Address × Decl))
    (oracle : Address → List RVal → Option RVal := fun _ _ => none) : Ctx :=
  { decls := Env.ofList raw
    oracle := fun address arguments =>
      oracle (result.rebuildRename raw address) arguments }

theorem main_eq_mapAddresses {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.semanticAudit raw main = true) :
    result.main = Readdress.Code.mapAddresses
      (Readdress.Renaming.apply result.addressMap) main := by
  exact result.asReaddressResult.main_eq_mapAddresses
    (result.semanticAudit_asReaddressResult haudit)

theorem renames_preAddressCtx {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.semanticAudit raw main = true)
    (oracle : Address → List RVal → Option RVal) :
    Readdress.Ctx.Renames
      (Readdress.Renaming.apply result.addressMap)
      (result.preAddressCtx raw oracle) (result.addressedCtx oracle) := by
  exact result.asReaddressResult.renames_preAddressCtx
    (result.semanticAudit_asReaddressResult haudit) oracle

private theorem envOfList_some_mem
    {entries : List (Address × Decl)} {address : Address} {declaration : Decl}
    (hlookup : Env.ofList entries address = some declaration) :
    (address, declaration) ∈ entries := by
  unfold Env.ofList at hlookup
  obtain ⟨entry, hfind, hvalue⟩ := Option.map_eq_some_iff.mp hlookup
  rcases entry with ⟨entryAddress, entryDeclaration⟩
  have hbeq : entryAddress == address :=
    List.find?_some
      (p := fun entry : Address × Decl => entry.1 == address) hfind
  have haddress : entryAddress = address := Address.eq_of_beq hbeq
  have hdeclaration : entryDeclaration = declaration := by
    simpa using hvalue
  subst entryAddress
  subst entryDeclaration
  exact List.mem_of_find?_eq_some hfind

/-- The finite exact-source rebuild audit reflects into the total context
relation used by evaluator equivariance. -/
theorem renames_rebuildSourceCtx {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.rebuildSemanticAudit raw main = true)
    (oracle : Address → List RVal → Option RVal) :
    Readdress.Ctx.Renames (result.rebuildRename raw)
      (result.rebuildSourceCtx raw oracle) (result.addressedCtx oracle) := by
  simp only [Result.rebuildSemanticAudit, Bool.and_eq_true] at haudit
  constructor
  · intro address
    simp only [Result.addressedCtx, Result.rebuildSourceCtx,
      Readdress.Result.addressedCtx, Readdress.Result.declarations,
      Result.asReaddressResult, List.append_nil]
    change Env.ofList result.declarations (result.rebuildRename raw address) =
      (Env.ofList raw address).map
        (Readdress.Decl.mapAddresses (result.rebuildRename raw))
    cases horiginal : Env.ofList raw address with
    | some declaration =>
        have hmember : (address, declaration) ∈ raw :=
          envOfList_some_mem horiginal
        have hrow := (List.all_eq_true.mp haudit.1.1.2)
          (address, declaration) hmember
        simp only [Result.rebuildRename, horiginal] at hrow
        cases hemitted : Env.ofList result.declarations
            (Readdress.Renaming.apply result.addressMap address) with
        | none => simp [hemitted] at hrow
        | some emitted =>
            simp only [hemitted, Bool.and_eq_true] at hrow
            have hequal : emitted = Readdress.Decl.mapAddresses
                (result.rebuildRename raw) declaration :=
              (Readdress.Decl.structurallyEq_eq_true_iff _ _).mp (by
                simpa [horiginal, hemitted] using hrow.2)
            simp [Result.rebuildRename, horiginal, hemitted, hequal]
    | none =>
        cases hreverse : result.addressMap.find?
            (fun entry => entry.2 == address) with
        | some mapping =>
            rcases mapping with ⟨source, target⟩
            have htargetBeq : target == address :=
              List.find?_some
                (p := fun entry : Address × Address => entry.2 == address)
                hreverse
            have htarget : target = address := Address.eq_of_beq htargetBeq
            subst target
            have hmember : (source, address) ∈ result.addressMap :=
              List.mem_of_find?_eq_some hreverse
            have hpair := (List.all_eq_true.mp haudit.1.2)
              (source, address) hmember
            simp only [Bool.and_eq_true] at hpair
            have hsafe := hpair.1
            simp only [horiginal] at hsafe
            simp only [Result.rebuildRename, horiginal, hreverse,
              Option.map_none]
            simpa using hsafe
        | none =>
            simp only [Result.rebuildRename, horiginal, hreverse,
              Option.map_none]
            cases hemitted : Env.ofList result.declarations address with
            | none => rfl
            | some declaration =>
                have hmember : (address, declaration) ∈ result.declarations :=
                  envOfList_some_mem hemitted
                have hcovered := (List.all_eq_true.mp haudit.2)
                  (address, declaration) hmember
                obtain ⟨mapping, hmapping, hmaps⟩ :=
                  List.any_eq_true.mp hcovered
                have hmissing := (List.find?_eq_none.mp hreverse)
                  mapping hmapping
                exact (hmissing hmaps).elim
  · intro address arguments
    rfl

/-- Every literal raw row is selected by the exact source environment carried
by the rebuild audit.  Ordinary initial addressing and rebuilding both expose
this fact through their successful-run certificates. -/
theorem raw_lookup_of_mem_of_rebuildSemanticAudit {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.rebuildSemanticAudit raw main = true)
    {address : Address} {declaration : Decl}
    (hmember : (address, declaration) ∈ raw) :
    Env.ofList raw address = some declaration := by
  simp only [Result.rebuildSemanticAudit, Bool.and_eq_true] at haudit
  have hrow := (List.all_eq_true.mp haudit.1.1.2)
    (address, declaration) hmember
  cases hlookup : Env.ofList raw address with
  | none => simp [hlookup] at hrow
  | some selected =>
      cases hemitted : Env.ofList result.declarations
          (result.rebuildRename raw address) with
      | none => simp [hlookup, hemitted] at hrow
      | some emitted =>
          simp only [hlookup, hemitted, Bool.and_eq_true] at hrow
          have hselected : selected = declaration :=
            (Readdress.Decl.structurallyEq_eq_true_iff _ _).mp hrow.1
          simpa [hlookup, hselected]

/-- Every selected emitted declaration has an exact raw producer whose key
maps to the emitted key and whose declaration maps to the selected value.
This is the lookup-facing provenance needed to back-translate reachable
runtime heaps without requiring the rebuild map to be globally surjective. -/
theorem declaration_preimage_of_lookup_of_rebuildSemanticAudit
    {result : Result} {raw : List (Address × Decl)} {main : Code}
    (haudit : result.rebuildSemanticAudit raw main = true)
    {address : Address} {declaration : Decl}
    (hlookup : Env.ofList result.declarations address = some declaration) :
    ∃ sourceAddress sourceDeclaration,
      Env.ofList raw sourceAddress = some sourceDeclaration ∧
        result.rebuildRename raw sourceAddress = address ∧
        Readdress.Decl.mapAddresses (result.rebuildRename raw)
          sourceDeclaration = declaration := by
  have hrenames :=
    result.renames_rebuildSourceCtx haudit (fun _ _ => none)
  simp only [Result.rebuildSemanticAudit, Bool.and_eq_true] at haudit
  have hmember : (address, declaration) ∈ result.declarations :=
    envOfList_some_mem hlookup
  have hcovered := (List.all_eq_true.mp haudit.2)
    (address, declaration) hmember
  obtain ⟨mapping, mappingMember, mapsTo⟩ :=
    List.any_eq_true.mp hcovered
  obtain ⟨sourceAddress, targetAddress⟩ := mapping
  have targetEq : targetAddress = address := Address.eq_of_beq mapsTo
  subst targetAddress
  have hsourcePair := (List.all_eq_true.mp haudit.1.2)
    (sourceAddress, address) mappingMember
  simp only [Bool.and_eq_true] at hsourcePair
  have hsource := hsourcePair.2
  cases sourceLookup : Env.ofList raw sourceAddress with
  | none => simp [sourceLookup] at hsource
  | some sourceDeclaration =>
      have renameEq : result.rebuildRename raw sourceAddress = address := by
        exact Address.eq_of_beq (by simpa [sourceLookup] using hsource)
      have relation := hrenames.decls sourceAddress
      simp only [Result.addressedCtx, Result.rebuildSourceCtx,
        Readdress.Result.addressedCtx, Readdress.Result.declarations,
        Result.asReaddressResult, List.append_nil] at relation
      rw [renameEq, hlookup, sourceLookup] at relation
      simp only [Option.map_some, Option.some.injEq] at relation
      exact ⟨sourceAddress, sourceDeclaration, sourceLookup, renameEq,
        relation.symm⟩

theorem main_eq_rebuildMapAddresses {result : Result}
    {raw : List (Address × Decl)} {main : Code}
    (haudit : result.rebuildSemanticAudit raw main = true) :
    result.main = Readdress.Code.mapAddresses
      (result.rebuildRename raw) main := by
  simp only [Result.rebuildSemanticAudit, Bool.and_eq_true] at haudit
  exact (Readdress.Code.structurallyEq_eq_true_iff _ _).mp
    haudit.1.1.1.2

end Result

/-- A successful SCC pass transports the complete evaluator result, including
heap-retained constructor/PAP addresses, address-bearing errors, and counters. -/
theorem runMain_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : run reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain (result.addressedCtx oracle) result.main fuel =
      Readdress.mapRunResult
        (Readdress.Renaming.apply result.addressMap)
        (runMain (result.preAddressCtx raw oracle) main fuel) := by
  have haudit := semanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_mapAddresses haudit]
  exact Readdress.runMain_mapAddresses
    (result.renames_preAddressCtx haudit oracle) main fuel

theorem runMain_success_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : run reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal)
    {fuel : Nat} {store : Store} {value : RVal}
    (hsource : runMain (result.preAddressCtx raw oracle) main fuel =
      .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main fuel =
      .ok (Readdress.Store.mapAddresses
        (Readdress.Renaming.apply result.addressMap) store, value) := by
  rw [runMain_of_run_eq_ok hrun oracle fuel, hsource]
  rfl

/-- Exact-source transport for the ordinary SCC pass.  Successful initial
content addressing now certifies the same alias-free source view as rebuilds. -/
theorem runMain_exact_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : run reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain (result.addressedCtx oracle) result.main fuel =
      Readdress.mapRunResult (result.rebuildRename raw)
        (runMain (result.rebuildSourceCtx raw oracle) main fuel) := by
  have haudit := rebuildSemanticAudit_of_run_eq_ok hrun
  rw [result.main_eq_rebuildMapAddresses haudit]
  exact Readdress.runMain_mapAddresses
    (result.renames_rebuildSourceCtx haudit oracle) main fuel

/-- Successful-run specialization of ordinary exact-source transport. -/
theorem runMain_exact_success_of_run_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrun : run reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal)
    {fuel : Nat} {store : Store} {value : RVal}
    (hsource : runMain (result.rebuildSourceCtx raw oracle) main fuel =
      .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main fuel =
      .ok (Readdress.Store.mapAddresses
        (result.rebuildRename raw) store, value) := by
  rw [runMain_exact_of_run_eq_ok hrun oracle fuel, hsource]
  rfl

/-- The already-addressed rebuild adapter has the same complete evaluator
transport as the initial SCC pass.  Its source context contains the original
rows plus the stable aliases required by total address equivariance. -/
theorem runMain_of_rebuild_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrebuild : rebuild reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain (result.addressedCtx oracle) result.main fuel =
      Readdress.mapRunResult
        (Readdress.Renaming.apply result.addressMap)
        (runMain (result.preAddressCtx raw oracle) main fuel) := by
  have haudit := semanticAudit_of_rebuild_eq_ok hrebuild
  rw [result.main_eq_mapAddresses haudit]
  exact Readdress.runMain_mapAddresses
    (result.renames_preAddressCtx haudit oracle) main fuel

/-- Successful-run specialization for rebuilding an already-addressed graph. -/
theorem runMain_success_of_rebuild_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrebuild : rebuild reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal)
    {fuel : Nat} {store : Store} {value : RVal}
    (hsource : runMain (result.preAddressCtx raw oracle) main fuel =
      .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main fuel =
      .ok (Readdress.Store.mapAddresses
        (Readdress.Renaming.apply result.addressMap) store, value) := by
  rw [runMain_of_rebuild_eq_ok hrebuild oracle fuel, hsource]
  rfl

/-- Exact-source transport for rebuilding an already-addressed graph.  The
source declaration environment is precisely `Env.ofList raw`; no newly
emitted content key is installed as an alias. -/
theorem runMain_exact_of_rebuild_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrebuild : rebuild reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal := fun _ _ => none)
    (fuel : Nat := 100000) :
    runMain (result.addressedCtx oracle) result.main fuel =
      Readdress.mapRunResult (result.rebuildRename raw)
        (runMain (result.rebuildSourceCtx raw oracle) main fuel) := by
  have haudit := rebuildSemanticAudit_of_rebuild_eq_ok hrebuild
  rw [result.main_eq_rebuildMapAddresses haudit]
  exact Readdress.runMain_mapAddresses
    (result.renames_rebuildSourceCtx haudit oracle) main fuel

/-- Successful-run specialization of exact-source rebuild transport. -/
theorem runMain_exact_success_of_rebuild_eq_ok
    {reserved : List Address} {raw : List (Address × Decl)} {main : Code}
    {result : Result}
    (hrebuild : rebuild reserved raw main = .ok result)
    (oracle : Address → List RVal → Option RVal)
    {fuel : Nat} {store : Store} {value : RVal}
    (hsource : runMain (result.rebuildSourceCtx raw oracle) main fuel =
      .ok (store, value)) :
    runMain (result.addressedCtx oracle) result.main fuel =
      .ok (Readdress.Store.mapAddresses
        (result.rebuildRename raw) store, value) := by
  rw [runMain_exact_of_rebuild_eq_ok hrebuild oracle fuel, hsource]
  rfl

end ReaddressAll

end Ix.Compiler.IxIR1
