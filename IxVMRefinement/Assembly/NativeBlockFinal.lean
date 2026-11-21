import IxVMRefinement.Assembly.NativeBlockInstallOf
import IxVMRefinement.Assembly.NativeBlockTableOf
import IxVMRefinement.Assembly.NativeBlockFire
import IxVMRefinement.Assembly.NativeBlockEta
import IxVMRefinement.Assembly.NativeBlockAux
import IxVMRefinement.Assembly.StoreArClauses
import IxVMRefinement.Assembly.LateValueStep

/-! # The carried clause of the earlier native block step, and the family it registers

What the earlier statements of a one-type native block's step share: the keys of the new
constants are resolved (`keyOf_ne_unresolvedKey`, `projTableName_keyOf_ne_unresolvedKey`), the
family the install names read off the store with its telescope constant the stored former
(`lateFamAt_of_install`), and the clause those statements carry beside the invariant
(`NativeBlockX t E`: the registry of native families, the store-key clause, the
projection-name clause and the level clauses).
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

universe u

/-! ## Keys -/

/-- A key of an address is resolved. -/
theorem keyOf_ne_unresolvedKey (t : Ix.Kernel.RoleTable) (x : _root_.Address) :
    Core.keyOf t x ≠ Core.unresolvedKey := by
  intro h
  have hb := Decl.isBaseKey_keyOf t x
  rw [h] at hb
  exact absurd hb (by decide)

/-- The projection table's name of the key of an address is resolved. -/
theorem projTableName_keyOf_ne_unresolvedKey (t : Ix.Kernel.RoleTable) (x : _root_.Address) :
    Ix.Kernel.projTableName (Core.keyOf t x) ≠ Core.unresolvedKey := by
  intro h
  unfold Ix.Kernel.projTableName Ix.Kernel.auxKey Core.unresolvedKey at h
  injection h with h1 _
  have hb := Decl.isBaseKey_keyOf t x
  rw [h1] at hb
  exact absurd hb (by decide)

/-! ## The family registered -/

/-- **The new family's registry entry**: the family the install names is read off the store at
the environment after the install. -/
theorem lateFamAt_of_install {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps) :
    LateFamAt t E ⟨new ++ env.consts⟩
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ := by
  have hI := hO.install
  have hnd₀ : (p₀.ctors.map (·.1.name)).Nodup := hO.facts.2.1
  have hpT : p.cvT.name = Core.keyOf t (Core.iprjAddr B 0) := by rw [hO.cvT]; exact hO.cvT₀.1
  have hpL : p.cvT.levelParams = List.range ind.lvls.toNat := by rw [hO.cvT]; exact hO.cvT₀.2
  have hctor : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
      cA.1.name = Core.keyOf t (Core.cprjAddr B 0 j) ∧
        cA.1.levelParams = List.range ind.lvls.toNat := by
    intro j cA hcA
    have hj : j < ind.ctors.size := by
      have := (List.getElem?_eq_some_iff.mp hcA).1
      rw [hO.lenA] at this
      exact this
    obtain ⟨ct, cty', -, hcl, -, hA⟩ := hO.ctors j hj
    rw [hA] at hcA
    injection hcA with hcA
    subst hcA
    exact ⟨rfl, by rw [hcl]⟩
  obtain ⟨-, -, isRec, cvS', cvTa, caps', p₁, q, ctorsB, sortss, kinds, tfvs, trest, isorts, hfam,
    hInd, hp, hCtors, hK, -, -, -, -, -, -⟩ := hO.facts
  injection hfam with h1 h2 h3 h4
  subst h2 h3
  rw [← h4] at hCtors hK
  rw [← h1] at hp hCtors hK
  obtain ⟨cvTa₀, s, bs, cvS'', -, -, hstrip, -, hp₁, -⟩ := hInd
  subst hp₁
  have hpnP : p.nP = p₀.nP := by rw [hp]; rfl
  have hpnIdx : p.nIdx = p₀.nIdx := by rw [hp]; rfl
  have hpres : p.resSort = s := by rw [hp]; rfl
  have hpk : p.kinds = kinds := by rw [hp]; rfl
  obtain ⟨hlA, -, hall⟩ := hCtors
  refine {
    stored := ?_
    tele := rfl
    lps := by rw [hpL]
    sort := ⟨bs, by rw [hpnP, hpnIdx, hpres]; exact hstrip⟩
    isProp := by rw [hp]; rfl
    kinds := by rw [hpk]; exact hK
    nodup := by rw [← hO.ctorNames]; exact hnd₀
    ctorFields := fun j c cA hc hcA => (hall j c cA hc hcA).1
    record := ?_ }
  · refine { former := ?_, ctor := ?_, lenA := hlA, lenK := ?_ }
    · rw [hpT, ← hO.caps_eq]
      exact hO.formerFind
    · intro j cA hcA
      replace hcA : ctorsA[j]? = some cA := hcA
      have hjc : j < p.ctors.length := by
        have := (List.getElem?_eq_some_iff.mp hcA).1
        omega
      obtain ⟨c, hc⟩ : ∃ c, p.ctors[j]? = some c :=
        ⟨p.ctors[j]'hjc, List.getElem?_eq_getElem hjc⟩
      obtain ⟨hf2, sorts, -, hrun⟩ := hall j c cA hc hcA
      obtain ⟨-, -, -, -, ⟨cbs, es, hst, hes⟩, -⟩ := Decl.sumCtorRunJ_struct_facts hrun
      refine ⟨hO.ctorFind cA (List.mem_of_getElem? hcA), ?_, cbs, es, ?_, hes⟩
      · rw [(hctor j cA hcA).2, hpL]
      · rw [hf2]
        exact hst
    · rw [hpk]
      exact (Ix.Kernel.classifyFixKinds_inv hK).2.2.2.symm
  · have hrecA : Ix.Cert.recordAt E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
      (recordOf_eq_recordAt_of_decoded hI.decoded _).symm.trans hI.formerRec
    have hrecB : Ix.Cert.recordAt E B = some cb :=
      (recordOf_eq_recordAt_of_decoded hI.decoded _).symm.trans hI.block
    have h0 : ((0 : Nat).toUInt64).toNat = 0 := by decide
    refine ⟨Core.iprjAddr B 0, memberProjection B 0 (.indc ind), ⟨(0 : Nat).toUInt64, B⟩, cb,
      #[.indc ind], ind, hpT, hrecA, rfl, hrecB, hI.muts, ?_, hO.nP, hO.nIdx, hO.lenA, ?_,
      hrec.logic, hpL⟩
    · show (#[Ixon.MutConst.indc ind])[((0 : Nat).toUInt64).toNat]? = some (.indc ind)
      rw [h0]
      rfl
    · intro j cA hcA
      show cA.1.name = Core.keyOf t (Core.cprjAddr B ((0 : Nat).toUInt64).toNat j)
      rw [h0]
      exact (hctor j cA hcA).1

/-! ## The carried clause -/

/-- **The clause the fold carries beside the invariant** (module docstring). -/
abbrev NativeBlockX (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  ((LateRegistry.{u} t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧ LvClauses env

end IxVM.Refinement.Typing
