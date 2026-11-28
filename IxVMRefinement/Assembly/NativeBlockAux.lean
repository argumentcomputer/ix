import IxVMRefinement.Assembly.NativeBlockRegister
import IxVMRefinement.Assembly.TypingBasisInv

/-! # The projection-name clause beside the registry

IxCK's install of a native family checks that the projection names of the family
(`projFnName T j`, `projTableName T`) are fresh (`checkNativeTable`), and the constructor stage
reads the absence of a projection at the family. The circuit does not check these names; the
prefix has their freshness from `Decl.AuxRootSynced` (every stored derived key has its root
stored) and the freshness of `T`. The fold's invariant holds `AuxRootSynced` only inside
`Decl.FullDeclInv V`, under the set-theory quantifier. The clause itself reads only the
environment, so it is carried as it is in the fold's extra clause, beside the registry and the
key clause `HashKeyed`:

* `keepsValuesKeyed_auxRoot`: a value step keeps it (the new key is the key of an address, a base
  key);
* `NativeNoRecFacts.auxRootSynced`: a native block's install keeps it (every declaration step on
  a non-derived declaration does, `Decl.auxRootSynced_step_declRunJ`);
* `auxRootSynced_basisEnv`: it holds at the environment of the pins (role keys are base keys);
* `keepsValuesKeyed_lateAux`: the registry, the key clause and this clause together, kept by a
  value step.
-/

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Ix.Kernel (ConstantInfo Key)
open IxVM.Refinement.TableInhabit (basisEnv)

universe u

/-- **A value step keeps the projection-name clause**: its key is the key of an address, whose
root is itself. -/
theorem keepsValuesKeyed_auxRoot (t : Ix.Kernel.RoleTable) :
    KeepsValuesKeyed t Decl.AuxRootSynced := by
  intro env ci d hX _ _ _ _ hkey
  obtain ⟨x, hx, -⟩ := hkey
  exact hX.cons_of_root_stored (Or.inl (by
    rw [hx]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t x)))

/-- **A native block's install keeps the projection-name clause.** -/
theorem NativeNoRecFacts.auxRootSynced {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    {fam : Ix.Kernel.Semantics.NativeFam .anon} (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : Decl.DeclNonAux (.indDecl blk nP)) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (haux : Decl.AuxRootSynced env) : Decl.AuxRootSynced env₂ :=
  Decl.auxRootSynced_step_declRunJ haux hna (h.declRunJ hpin)

/-- **The projection-name clause holds at the environment of the pins**: it stores only role
keys, each its own root. -/
theorem auxRootSynced_basisEnv : Decl.AuxRootSynced basisEnv := by
  intro k hk
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨r, -, rfl⟩ := basisEnv_find_role hci
  exact hk

/-- **The registry, the key clause and the projection-name clause together** are kept by a value
step whose key is the key of a 32-byte address. -/
theorem keepsValuesKeyed_lateAux {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) (E : Ixon.Env) :
    KeepsValuesKeyed t
      (fun env => (LateRegistry.{u} t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) :=
  (keepsValuesKeyed_late htwf E).and (keepsValuesKeyed_auxRoot t)

end IxVM.Refinement.Typing
