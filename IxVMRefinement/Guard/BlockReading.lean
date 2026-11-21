import IxVMRefinement.Guard.BlockReach
import IxVMRefinement.Guard.LoadParents

/-! # The checked field loop's reading at a block over any store closed under what it uses

Every load of the classifier at a checked field loop of the block `B` is at an address
reachable from `B` by used constant references, projection blocks and member projections
(`Guard.BlockReach`): the constructor's telescope is read from `B`, and each declared type and
definition value the classifier reads at a reachable address names only reachable addresses
(`Guard.keysKept_reachStore`). So the reading at `B` holds over the run's records at the
reachable addresses alone, and over every store that holds those records and the run's blobs.

* `checkedSortsReadingAtBlock_reach`: **the reading at `B` over the run's records reachable
  from `B`** (`reachStore E₀ B`), from the two facts every step has of the run's store.
* `CheckedSortsReadingAtBlock.mono`: the reading moves to a store that holds more records and
  blobs.
* `reachStore_records_held`: a store that agrees with the run's store, is closed under what its
  records use (`UsedClosed`) and holds `B`, holds every record reachable from `B`.
* `checkedSortsReadingAtBlock_of_usedClosed`: **the reading at `B` over such a store** that also
  holds the run's blobs.
-/

namespace IxVM.Refinement.Guard

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- **The reading of the checked field loops at `B` holds over the run's records reachable from
`B`**: no record at an address unreachable from `B` is read. -/
theorem checkedSortsReadingAtBlock_reach {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (B : _root_.Address) : CheckedSortsReadingAtBlock calls (reachStore E₀ B) B := by
  intro c b i nP nF cty u sorts checked hB
  obtain ⟨sigs, fuel, raw, hraw, hsig, hzeros⟩ :=
    checkedSortsReadingAt_of_runStore hS hcov c checked
  subst hB
  refine ⟨sigs, fuel, raw, ?_, ?_, hzeros⟩
  · rw [ctorRaw_reachStore]
    exact hraw
  · exact fieldSignatures_keys (keysKept_reachStore E₀ _) nP nF [] raw sigs
      (fun _ h => nomatch h) (ctorRaw_keysIn hraw) hsig

/-- **The reading at a block moves to a store that holds more records and blobs.** -/
theorem CheckedSortsReadingAtBlock.mono {calls : List (Call F)} {E E' : Ixon.Env}
    {B : _root_.Address}
    (hrec : ∀ a c, recordOf E a = some c → recordOf E' a = some c)
    (hblob : ∀ x bs, E.blobs.get? x = some bs → E'.blobs.get? x = some bs)
    (reading : CheckedSortsReadingAtBlock calls E B) : CheckedSortsReadingAtBlock calls E' B := by
  intro c b i nP nF cty u sorts checked hB
  obtain ⟨sigs, fuel, raw, hraw, hsig, hzeros⟩ := reading c checked hB
  refine ⟨sigs, fuel, raw, ?_,
    Ix.Kernel.GuardClassifier.fieldSignatures_mono (GuardRaw.lookup_extends hrec hblob)
      (Nat.le_refl fuel) hsig, hzeros⟩
  unfold Guard.ctorRaw at hraw ⊢
  obtain ⟨root, hroot, hread⟩ := Option.bind_eq_some_iff.mp hraw
  exact Option.bind_eq_some_iff.mpr
    ⟨root, GuardRaw.memberRoot_mono hrec hroot, GuardRaw.readRoot_mono hblob hread⟩

/-- A store that agrees with `E₀`, is closed under what its records use and holds `B` holds a
record at every address reachable from `B` in `E₀`. -/
theorem blockReach_held {E₀ R : Ixon.Env} {B : _root_.Address}
    (hR : ∀ a c, recordOf R a = some c → recordOf E₀ a = some c) (hcl : UsedClosed R)
    (hB : (recordOf R B).isSome = true) {a : _root_.Address} (h : BlockReach E₀ B a) :
    (recordOf R a).isSome = true := by
  have held : ∀ {a c}, (recordOf R a).isSome = true → recordOf E₀ a = some c →
      recordOf R a = some c := by
    intro a c ha hc
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp ha
    have e : c' = c := Option.some.inj ((hR a c' hc').symm.trans hc)
    rw [hc', e]
  induction h with
  | seed => exact hB
  | @used a x c i _ hc hi hx ih => exact (hcl.1 a c (held ih hc)).2 i hi x hx
  | @owner a c _ hc ih => exact (hcl.1 a c (held ih hc)).1
  | @member a c ms i m _ hc hinfo hm ih =>
    rw [(hcl.2 a c ms (held ih hc) hinfo i m hm).1]
    rfl

/-- **A store that agrees with `E₀`, is closed under what its records use and holds `B` holds
every record of `E₀` reachable from `B`.** -/
theorem reachStore_records_held {E₀ R : Ixon.Env} {B : _root_.Address}
    (hR : ∀ a c, recordOf R a = some c → recordOf E₀ a = some c) (hcl : UsedClosed R)
    (hB : (recordOf R B).isSome = true) :
    ∀ a c, recordOf (reachStore E₀ B) a = some c → recordOf R a = some c := by
  intro a c h
  obtain ⟨hr, hE⟩ := recordOf_of_reachStore h
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (blockReach_held hR hcl hB hr)
  have e : c' = c := Option.some.inj ((hR a c' hc').symm.trans hE)
  rw [hc', e]

/-- **The reading of the checked field loops at `B` over a store closed under what its records
use.** `R` agrees with the run's store `E₀` on what it holds, is closed under used references,
projection blocks and member projections (`UsedClosed`), holds `B` and holds the run's blobs. -/
theorem checkedSortsReadingAtBlock_of_usedClosed {calls : List (Call F)} {E₀ R : Ixon.Env}
    {B : _root_.Address}
    (hS : LoadedReads.RunStore calls E₀) (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hR : ∀ a c, recordOf R a = some c → recordOf E₀ a = some c)
    (hcl : UsedClosed R) (hB : (recordOf R B).isSome = true)
    (hblobs : ∀ x bs, E₀.blobs.get? x = some bs → R.blobs.get? x = some bs) :
    CheckedSortsReadingAtBlock calls R B :=
  (checkedSortsReadingAtBlock_reach hS hcov B).mono (reachStore_records_held hR hcl hB) hblobs

end IxVM.Refinement.Guard
