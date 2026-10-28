import Ix.Cert.SourceContext.Observations
import Ix.Cert.SourceContext.Rows

namespace Ix.Cert.SourceContext
open Ix.Kernel Ix.Kernel.Reader Ix.Kernel.Admission

private theorem lookup_origin {α : Type} {xs : List (Address × α)} {a : Address} {v : α}
    (hit : xs.lookup a = some v) : (a,v) ∈ xs := by
  obtain ⟨left,right,rfl,_⟩ := List.lookup_eq_some_iff.mp hit
  exact List.mem_append.mpr (.inr List.mem_cons_self)

theorem recordMap_agrees {old next : Ingress.Constants}
    (unique : (old.map Prod.fst).Nodup) (same : old.Perm next) :
    Maps.Agrees (recordMap old.toArray) (recordMap next.toArray) := by
  have nextUnique := (same.map Prod.fst).nodup unique
  intro address
  rw [ReaderClosureKeys.recordMap_get,ReaderClosureKeys.recordMap_get]
  cases previous : old.lookup address with
  | some value =>
    exact (ReaderClosureKeys.lookup_of_nodup nextUnique (same.mem_iff.mp (lookup_origin previous))).symm
  | none =>
    cases found : next.lookup address with
    | none => rfl
    | some value =>
      have earlier := ReaderClosureKeys.lookup_of_nodup unique (same.mem_iff.mpr (lookup_origin found))
      rw [previous] at earlier
      cases earlier

section ActualContext
variable (hash : ByteArray → Address) (table : RoleTable) (pre : Prelude .anon)
  (blobs : Ingress.Blobs) (hint : ConstRef Address → Option ReducibilityHint)
local notation "context" cs => streamContext hash table pre cs blobs hint

theorem stream_store_agrees {old next : Ingress.Constants}
    (unique : (old.map Prod.fst).Nodup) (same : old.Perm next) :
    (context old).store = (context next).store := by
  funext address
  change ((recordMap old.toArray)[address]? <|> ((recordMap (pre.records ++ pre.evidence))[address]? <|> none)) = _
  rw [recordMap_agrees unique same address]
  rfl

/-- Two stream contexts read blobs alike: by unfolding them, not by `rfl` between them, which has
the kernel compare the two contexts whole. -/
theorem stream_blob_agrees (old next : Ingress.Constants) : (context old).blob = (context next).blob := by
  simp only [streamContext, contextOf, contextWith]

/-- Two stream contexts carry one hint function (as `stream_blob_agrees`). -/
theorem stream_hint_agrees (old next : Ingress.Constants) : (context old).hint = (context next).hint := by
  simp only [streamContext, contextOf, contextWith]

/-- All non-table functions agree universally by actual construction and the
proved input-store equality, not by probing finitely many source addresses. -/
theorem stream_agrees {old next : Ingress.Constants}
    (unique : (old.map Prod.fst).Nodup) (same : old.Perm next)
    (tables : Tables (context old) (context next)) : Agrees (context old) (context next) := by
  have store := stream_store_agrees hash table pre blobs hint unique same
  refine { toTables := tables, store, blob := stream_blob_agrees hash table pre blobs hint old next,
           hint := stream_hint_agrees hash table pre blobs hint old next, reconstruct := ?_ }
  change projectionAddress hash (context old).store = projectionAddress hash (context next).store
  rw [store]

def storeDomain (constants : Ingress.Constants) : List Address :=
  Maps.domain (recordMap constants.toArray) ++ Maps.domain (recordMap (pre.records ++ pre.evidence))
def blobIndex : Std.HashMap Address ByteArray :=
  (blobs ++ pre.blobs).foldl (fun m (a,b) => if m.contains a then m else m.insert a b) {}
def blobDomain : List Address := Maps.domain (blobIndex pre blobs)

/-- Complete store coverage includes unshadowed fallback lookup as well as
inputs. It is independent of which addresses any candidate happened to use. -/
theorem store_domain_iff (constants : Ingress.Constants) (address : Address) :
    address ∈ storeDomain pre constants ↔ ∃ value, (context constants).store address = some value := by
  simp only [storeDomain,List.mem_append,Maps.domain_iff]
  change ((∃ value, (recordMap constants.toArray)[address]? = some value) ∨
    ∃ value, (recordMap (pre.records ++ pre.evidence))[address]? = some value) ↔
    ∃ value, ((recordMap constants.toArray)[address]? <|>
      ((recordMap (pre.records ++ pre.evidence))[address]? <|> none)) = some value
  cases first : (recordMap constants.toArray)[address]? <;>
    cases fallback : (recordMap (pre.records ++ pre.evidence))[address]? <;> simp

theorem store_none_outside (constants : Ingress.Constants) {address : Address}
    (outside : address ∉ storeDomain pre constants) : (context constants).store address = none := by
  cases hit : (context constants).store address with
  | none => rfl
  | some value => exact (outside ((store_domain_iff hash table pre blobs hint constants address).mpr ⟨value,hit⟩)).elim

theorem blob_domain_iff (constants : Ingress.Constants) (address : Address) :
    address ∈ blobDomain pre blobs ↔ ∃ value, (context constants).blob address = some value :=
  Maps.domain_iff (blobIndex pre blobs) address

theorem blob_none_outside (constants : Ingress.Constants) {address : Address}
    (outside : address ∉ blobDomain pre blobs) : (context constants).blob address = none :=
  Maps.none_outside (blobIndex pre blobs) outside

end ActualContext
end Ix.Cert.SourceContext
