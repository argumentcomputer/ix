import IxVMRefinement.Guard.BlockReading
import IxVMRefinement.Binding.RunStores

/-! # The checked field loop's reading at a block over the binding fold's stores

The binding fold's store before group `g` (`Binding.groupStore t E₀ Pay g`) is, above group 6, the
run's records at the addresses the groups below `g` admitted, with every blob of the run
(`Binding.groupStore_recordOf`, `Binding.groupStore_reads_blobs`). Where that store is closed
under what its records use (`Binding.groupStore_usedClosed_all`) and holds the block `B`, the
reading of the checked field loops at `B` holds over it.
-/

namespace IxVM.Refinement.Guard

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- **The reading of the checked field loops at `B` over a store of the binding fold above group
6** that holds `B` and is closed under what its records use. -/
theorem checkedSortsReadingAtBlock_groupStore {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : Binding.PayloadRel} {g : Nat}
    {B : _root_.Address}
    (hC : Binding.CollisionFreeRun calls E₀) (hb : Binding.BasisRowsLoaded E₀) (hg : 6 < g)
    (hcl : UsedClosed (Binding.groupStore t E₀ Pay g))
    (hB : (recordOf (Binding.groupStore t E₀ Pay g) B).isSome = true) :
    CheckedSortsReadingAtBlock calls (Binding.groupStore t E₀ Pay g) B :=
  checkedSortsReadingAtBlock_of_usedClosed hC.runStore hC.hashedStored
    (fun _ _ h => ((Binding.groupStore_recordOf hb (Nat.le_of_lt hg)).mp h).2) hcl hB
    (Binding.groupStore_reads_blobs hg)

end IxVM.Refinement.Guard
