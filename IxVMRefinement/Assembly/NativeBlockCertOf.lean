import IxVMRefinement.Assembly.NativeBlockFire
import IxVMRefinement.Assembly.NativeBlockInstallOf
import IxVMRefinement.Guard.LoadParents

/-! # The certificate of a native block's new projection table, from the install's output

`BlockCert` (`NativeBlockFire.lean`) is what a native block step asks of the install: where the
new environment stores the family's projection table and its sort passes the zero test, the
table has its certificate over the step's store.

* `blockCert_of_reading_block`: at a block with one constructor and no index whose result sort
  passes the zero test, the install's output (`NativeInstallOut`) with the sorts of its table
  stage (`InstallSortsChecked`, both from `nativeInstallOut_of_member_checked`) gives `BlockCert`.
  The sorts are the ones the classifier's field loop checked; the reading of the loop at the
  block over the step's store (`Guard.CheckedSortsReadingAtBlock`) gives signatures with the same
  zero-sets, and `Guard.projGuardCert_of_checkNativeTable` the certificate of the table the stage
  stores. `blockCert_of_reading`: the same from the reading of every loop
  (`Guard.CheckedSortsReadingAt`).
* `blockCert_of_runStore`: the same from the facts a step has of its stores: the run's store,
  that it holds the run's hashed records, and that the step's store holds the run store's
  records and blobs. The reading is proved (`Guard.checkedSortsReadingAt_of_stepStore`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option linter.unusedVariables false

/-- **The new table's certificate, from the install's output, the sorts of its table stage and
the reading of the checked field loops at the block over the step's store**
(`Guard.CheckedSortsReadingAtBlock`: only the loop at `B` is read). The reading has no
alternative, so no goodness of the run is asked here. -/
theorem blockCert_of_reading_block
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    {caps : IndCaps .anon}
    (hfields : Guard.CheckedSortsReadingAtBlock calls E B)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hS : InstallSortsChecked calls t E n env B
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA)
    (h1 : ind.ctors.size = 1) (h0 : ind.indices.toNat = 0)
    (hz : Ix.Kernel.Level.isEquiv p.resSort .zero = some true) :
    BlockCert t E ⟨new ++ env.consts⟩ B := by
  intro tbl htbl hprop
  obtain ⟨isRec, sortss, hQ, htab, hres⟩ := hS
  have hlenP : p₀.ctors.length = 1 := by
    have h := congrArg List.length hO.ctorNames
    simp only [List.length_map] at h
    rw [h, hO.lenA]
    exact h1
  have hzero : ∀ φ : Ix.Kernel.LevelParam → Nat, Ix.Kernel.Level.eval φ p₀.resSort = 0 := by
    intro φ
    rw [← hres]
    exact Decl.eval_zero_of_isEquiv_zero (by rw [hz]; rfl) φ
  obtain ⟨b, u, cA, sorts, hbB, hcA, hsorts, hcS, hchk⟩ := hQ hlenP (hO.nIdx₀.trans h0) hzero
  subst hcA hsorts
  -- the loop's reading at the sorts the table stage ran at
  obtain ⟨sigs, fuel, raw, hraw, hsig, hzeros⟩ := hfields _ hchk hbB
  have hv0 : ZMod.val (0 : F) = 0 := ZMod.val_zero
  rw [hbB, hv0] at hraw
  rw [hO.nP₀, ← hO.nP] at hsig
  -- the table the stage stores, with its certificate
  obtain ⟨tbl', -, hfind', -, -, -, hlps', cert⟩ :=
    Guard.projGuardCert_of_checkNativeTable (hO.nIdx.trans h0) htab hsig hzeros
  rw [hO.cvT, hO.cvT₀.1] at hfind'
  rw [hfind'] at htbl
  injection htbl with htbl
  injection htbl with htbl
  subst htbl
  -- the stored constructor
  obtain ⟨ct, cty', -, -, -, hA0⟩ := hO.ctors 0 (by omega)
  have hcAeq : cA = (⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat, cty'⟩,
      ct.fields.toNat) := by
    have h : some cA = some ((⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat,
        cty'⟩, ct.fields.toNat) : ConstantVal .anon × Nat) := hA0
    exact Option.some.inj h
  have hctor := hO.ctorFind cA (List.mem_singleton.mpr rfl)
  have hname : cA.1.name = Core.keyOf t (Core.cprjAddr B 0 0) := by rw [hcAeq]
  rw [hname] at hctor
  refine ⟨cA.1, p.nP, cA.2, raw, hctor, hraw, ?_, cert⟩
  rw [hlps', hO.cvT, hO.cvT₀.2, List.length_range]

/-- **The new table's certificate, from the install's output, the sorts of its table stage and
the reading of every checked field loop over the step's store** (`Guard.CheckedSortsReadingAt`). -/
theorem blockCert_of_reading
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    {caps : IndCaps .anon}
    (hfields : Guard.CheckedSortsReadingAt calls E)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hS : InstallSortsChecked calls t E n env B
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA)
    (h1 : ind.ctors.size = 1) (h0 : ind.indices.toNat = 0)
    (hz : Ix.Kernel.Level.isEquiv p.resSort .zero = some true) :
    BlockCert t E ⟨new ++ env.consts⟩ B :=
  blockCert_of_reading_block (hfields.block B) hO hS h1 h0 hz

/-- **The new table's certificate at a step**: from the install's output with the sorts of its
table stage, and the three facts every walked unit's step has of its stores (the run's store,
that it holds the run's hashed records, and that the step's store holds the run store's
records and blobs). No reading is left as a premise. -/
theorem blockCert_of_runStore
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    {caps : IndCaps .anon}
    (hrun : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hst : StepStore calls t E₀ E)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hS : InstallSortsChecked calls t E n env B
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA)
    (h1 : ind.ctors.size = 1) (h0 : ind.indices.toNat = 0)
    (hz : Ix.Kernel.Level.isEquiv p.resSort .zero = some true) :
    BlockCert t E ⟨new ++ env.consts⟩ B :=
  blockCert_of_reading (Guard.checkedSortsReadingAt_of_stepStore hrun hcov hst) hO hS h1 h0 hz

end IxVM.Refinement.Typing
