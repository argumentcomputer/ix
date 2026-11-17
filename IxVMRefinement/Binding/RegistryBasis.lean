import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.Binding.GlueStore
import IxVMRefinement.Assembly.NativeBlockFinalRetHead

/-! # The registered-family clause at the pinned basis for every admitted table

The basis stores only prelude-role keys. A table that pins those roles therefore
has the same store-key clause as the committed table, even if its other bindings
differ. The empty native registry and the auxiliary/level clauses are independent
of the table and record store.
-/

universe u

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.TableInhabit (basisEnv basisRoleOrder)
open IxVM.Refinement.StoreInhabit (basisStore)

/-- Every address whose key the basis stores is a hash-sized address under a pinned table. -/
theorem hashKeyed_basis_at {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) (hpre : PreludePinned t) : HashKeyed t basisEnv := by
  intro ci hci y hy
  have hn : ci.name ∈ basisRoleOrder.map Ix.Kernel.Key.role := by
    rw [← basisEnv_names]
    exact List.mem_map_of_mem hci
  obtain ⟨r, hr, hname⟩ := List.mem_map.mp hn
  have hkey : Core.keyOf t y = .role r := hy.symm.trans hname.symm
  have hdefault : Core.keyOf ctab y = .role r := (keyOf_basis ht hpre hr).mp hkey
  exact hashKeyed_basisEnv ci hci y (hname.symm.trans hdefault.symm)

/-- The native registered-family clause at the basis under every table pinning the prelude. -/
theorem nativeBlockXR_basis_at {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) (hpre : PreludePinned t) (E : Ixon.Env) :
    NativeBlockXR.{u} t E basisEnv :=
  ⟨⟨⟨retHeadRegistry_basis t E, hashKeyed_basis_at ht hpre⟩, auxRootSynced_basisEnv⟩,
    lvClauses_basisEnv⟩

/-- The binding basis carries the registered-family clause at every store for its records. -/
theorem bnd_basis_registered {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) (hpre : PreludePinned t) (hall : AllBound t) :
    Bnd.{u} (StoreX NativeBlockXR.{u}) t (· < 6) basisStore basisEnv :=
  bnd_basis_at ht hpre hall (fun E _ => nativeBlockXR_basis_at ht hpre E)

/-- Only the concrete binding run's table and initial-store facts remain in the basis export. -/
theorem basisBase_registered
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (hrun : ∀ t ρ Rs, Run t ρ Rs →
      t.check = .ok () ∧ PreludePinned t ∧
        (∀ a, (Rs 6).consts.get? a = basisStore.consts.get? a) ∧
        ∀ a, (Rs 6).blobs.get? a = basisStore.blobs.get? a) :
    BasisBase.{u} (StoreX NativeBlockXR.{u}) Run :=
  basisBase_at hrun
    (fun _ _ hc hb hX E hE =>
      hX E (recordsFor_storeCongr (fun a => (hc a).symm) (fun a => (hb a).symm) hE))
    (fun _ ht hpre _ E _ => nativeBlockXR_basis_at ht hpre E)

end IxVM.Refinement.Binding
