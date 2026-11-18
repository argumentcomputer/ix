import IxVMRefinement.Assembly.NativeBlockFinal
import IxVMRefinement.Assembly.TypingBasisInv

/-! # The earlier native block step's clauses at the basis

* `hashKeyed_basisEnv`: the store-key clause at the environment of the pins under the committed
  table (every key there is a role key, and the table binds roles to 32-byte addresses);
* `nativeBlockX_basisEnv`: the step's whole carried clause at the environment of the pins;
* `prefixInv_basisEnv_of_le_six`: the prefix invariant there, at every limit at most six, for
  every record store of the basis (`basis_facts`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.TableInhabit (basisEnv basisRoleOrder)
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

universe u

/-- The committed table binds every role to a 32-byte address. -/
theorem ctab_bound_size : ∀ p ∈ ctab.bound.toList, p.2.hash.size = 32 := by
  decide +kernel

/-- **The store-key clause at the environment of the pins**, under the committed table. -/
theorem hashKeyed_basisEnv : HashKeyed ctab basisEnv := by
  intro ci hci y hy
  have hy' : ci.name = IxVM.Consistency.keyOf ctab y := hy
  rcases IxVM.Consistency.keyOf_cases ctab y with ⟨hk, -⟩ | ⟨r, hr, -⟩
  · exfalso
    have hn : basisEnv.consts.map (·.name) = basisRoleOrder.map Ix.Kernel.Key.role := rfl
    have hm : ci.name ∈ basisEnv.consts.map (·.name) := List.mem_map_of_mem hci
    rw [hn] at hm
    obtain ⟨r, -, hr⟩ := List.mem_map.mp hm
    rw [← hr, hk] at hy'
    cases hy'
  · exact ctab_bound_size (r, y) hr

/-- **The native block step's carried clause at the environment of the pins.** -/
theorem nativeBlockX_basisEnv (E : Ixon.Env) : NativeBlockX.{u} ctab E basisEnv :=
  ⟨⟨⟨lateRegistry_basis ctab E, hashKeyed_basisEnv⟩, auxRootSynced_basisEnv⟩, lvClauses_basisEnv⟩

/-- **The prefix invariant at the environment of the pins**, at every limit at most six, for every
record store of the basis. -/
theorem prefixInv_basisEnv_of_le_six {E : Ixon.Env} (hR : RecordsFor StoreInhabit.basisStore E)
    {n : Nat} (hn : n ≤ 6) : Decl.PrefixInv.{u} E ctab (some n) basisEnv :=
  basis_facts.inv E hR (some n) (limWithin_six hn)

end IxVM.Refinement.Typing
