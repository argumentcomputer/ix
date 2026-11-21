import IxVMRefinement.Binding.ReadsLocal
import IxVMRefinement.Binding.StoreClausesWalk
import IxVMRefinement.Binding.BasisAt

/-! # The reading clause of a group's admission

`AdmitsReads.reads` for the store sequence `groupStore t E₀`: a reading over the run's records of
a constant address of a record new in group `g` is a reading over the store after the group. The
store after the group is a sub-store of the run's records, closed under used references and
owners (`groupStore_usedClosed_all`), holding every blob, and it holds the constant addresses of
its records (a record itself, or a block's member and constructor projections); so
`reads_of_closed_sub` applies.
-/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-- **`AdmitsReads.reads` for one group of a run**, at a table that checks. -/
theorem groupStore_reads {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel} (ht : t.check = .ok ())
    (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀) (hbr : BasisRolesStored t)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ Pay)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) :
    ∀ A c x ci₀, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) A →
      recordOf (groupStore t E₀ Pay (g + 1)) A = some c → ConstAddrOf A c x →
      Reads t E₀ x ci₀ → Reads t (groupStore t E₀ Pay (g + 1)) x ci₀ := by
  intro A c x ci₀ _ hc hx hr
  have hcl := groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6)
  have hheld : (recordOf (groupStore t E₀ Pay (g + 1)) x).isSome = true := by
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, hm, hxm | ⟨ind, j, hmi, hj, hxc⟩⟩
    · rw [hxA, hc]
      rfl
    · rw [hxm]
      exact Option.isSome_iff_exists.mpr ⟨_, (hcl.2 A c ms hc hms i m hm).1⟩
    · rw [hxc]
      exact Option.isSome_iff_exists.mpr ⟨_, (hcl.2 A c ms hc hms i m hm).2 ind hmi j hj⟩
  exact reads_of_closed_sub ht (wf_of_check ht)
    (fun y c' hy => ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hy).2) hcl
    (groupStore_reads_blobs (Nat.lt_succ_of_le hg6)) hheld hr

end IxVM.Refinement.Binding
