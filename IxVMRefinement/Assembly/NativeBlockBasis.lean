import IxVMRefinement.Assembly.NativeBlockFinal
import IxVMRefinement.Assembly.TypingBasisInv

/-! # The native block step: the hashed-projection input derived, and its clauses at the basis

* `unitStep_nativeBlock_held`: `unitStep_nativeBlock` without its input
  `HashedBlockProjectionsHeld E`, which every store whose records decode has
  (`hashedBlockProjectionsHeld_of_decoded`; the step's store decodes, `StepStore.decoded`);
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

/-- **`UnitStep` for a one-type native inductive block without its recursor, the hashed-projection
input derived from the step's store.** -/
theorem unitStep_nativeBlock_held {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n) (hlim : lim = some n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hkey : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hcov : L1.CanonicalHashCoverage E calls)
    (hread : Core.ProjGuardRunReading)
    (hcert : ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
      (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
      (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
      BlockCert t E ⟨new ++ env.consts⟩ B)
    (heta : ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
      (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
      (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
      Decl.PrefixInv.{u} E t (some n) env →
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
      BlockEta ⟨E, env, t, some n⟩ new) :
    UnitStep.{u} (NativeBlockX.{u} t E) t envT E₀ E lim B cb :=
  unitStep_nativeBlock ht hS hst hrec hchk hlim hnat htele hkey hinert hcover
    (hashedBlockProjectionsHeld_of_decoded hst.decoded) hcov hread hcert heta

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
