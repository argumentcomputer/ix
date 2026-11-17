import IxVMRefinement.Assembly.NativeBlockFinal

/-! # The new table's guard clause off structure-like propositions

`BlockGuard` (`NativeBlockTableOf.lean`) speaks of a projection table found at the projection
table name of the new family, and only where the table's sort tests equal to zero. The install
puts a table in front only at one constructor and no index (`checkNativeTable`), with the
family's sort as the table's; the prefix stores no table at that name (the former's key is fresh,
and a stored auxiliary name has its root stored). So the clause holds vacuously unless the block
is a one-constructor, index-free family whose sort tests equal to zero:

* `checkNativeTable_cases`: the table check either keeps the environment or puts in front one
  table, at one constructor and no index, with the family's name and sort;
* `NativeInstallOut.table_struct`: a projection table among the new constants is that table;
* `blockGuard_of_install_off`: `BlockGuard` off one-constructor, index-free propositional
  families.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option linter.unusedVariables false

/-- **The table check's two outcomes**: the environment is kept, or one table is put in front, at
a single constructor and no index, with the family's name and sort. -/
theorem checkNativeTable_cases {p : Ix.Kernel.NativeParts .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List Ix.Kernel.Level)}
    {X env₂ : Ix.Kernel.Env .anon}
    (h : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    env₂ = X ∨ (ctorsA.length = 1 ∧ p.nIdx = 0 ∧ ∃ tbl : Ix.Kernel.ProjTable .anon,
      env₂ = ⟨.projInfo tbl :: X.consts⟩ ∧ tbl.structName = p.cvT.name ∧
      tbl.structSort = p.resSort) := by
  unfold Ix.Kernel.checkNativeTable at h
  split at h
  · split at h
    · rename_i hidx
      obtain ⟨bodies, -, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv h
      exact Or.inr ⟨rfl, by simpa using hidx, _, rfl, rfl, rfl⟩
    · injection h with hX
      exact Or.inl hX.symm
  · injection h with hX
    exact Or.inl hX.symm

/-- **A projection table among the new constants is the family's**: the block has one
constructor and no index, and the table's sort is the family's. -/
theorem NativeInstallOut.table_struct {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    {tbl : Ix.Kernel.ProjTable .anon} (hm : ConstantInfo.projInfo tbl ∈ new) :
    ind.ctors.size = 1 ∧ ind.indices.toNat = 0 ∧ tbl.structSort = p.resSort := by
  obtain ⟨-, -, isRec, cvS', cvTa, caps', p₁, q, ctorsB, sortss, kinds, tfvs, trest, isorts, hfam,
    -, -, -, -, -, -, -, -, -, hTbl⟩ := hO.facts
  injection hfam with h1 h2 h3 h4
  rw [← h4, ← h1] at hTbl
  have hX : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS' caps' :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS' caps']) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  rcases checkNativeTable_cases hTbl with heq | ⟨hlen, hidx, tbl', heq, -, hsort⟩
  · exfalso
    have hc : new ++ env.consts =
        (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS' caps' :: env.consts⟩).consts :=
      congrArg Ix.Kernel.Env.consts heq
    rw [hX] at hc
    have hn := List.append_cancel_right hc
    rw [hn] at hm
    simp at hm
  · have hc : new ++ env.consts = .projInfo tbl' ::
        (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS' caps' :: env.consts⟩).consts :=
      congrArg Ix.Kernel.Env.consts heq
    rw [hX] at hc
    have hc' : new ++ env.consts = (.projInfo tbl' ::
        ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
          [.indInfo cvS' caps'])) ++ env.consts := by
      rw [hc, List.cons_append]
    have hn := List.append_cancel_right hc'
    rw [hn] at hm
    simp at hm
    subst hm
    exact ⟨hO.lenA.symm.trans hlen, hO.nIdx.symm.trans hidx, hsort⟩

/-- **The guard clause off one-constructor, index-free propositional families**: where the
block has more or fewer than one constructor, or an index, or a sort that does not test equal to
zero, `BlockGuard` holds — no table at the family's table name meets its premises. Inputs: the
install read off the member check, the prefix's projection names (`AuxRootSynced`, the fold's
carried clause) and the freshness of the former's key. -/
theorem blockGuard_of_install_off {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)} {p₀ p : Ix.Kernel.NativeParts .anon}
    {new : List (ConstantInfo .anon)} {ty' : Ix.Kernel.Expr .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (haux : Decl.AuxRootSynced env)
    (hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hoff : ¬ (ind.ctors.size = 1 ∧ ind.indices.toNat = 0 ∧
      Ix.Kernel.Level.isEquiv p.resSort .zero = some true)) :
    BlockGuard ⟨E, env, t, some n⟩ new B := by
  unfold BlockGuard
  intro i hi j cvC nP nF tbl hC hTb hz
  exfalso
  have hκ : (appCtx ⟨E, env, t, some n⟩ new).stored.κ (Core.iprjAddr B 0) =
      Core.keyOf t (Core.iprjAddr B 0) :=
    appCtx_key_of_find (c := ⟨E, env, t, some n⟩) (new := new) hO.formerFind
  rw [hκ] at hTb
  rcases find?_append_cases (env := env) new hTb with hm | hold
  · obtain ⟨h1, h2, h3⟩ := hO.table_struct hm
    rw [h3] at hz
    exact hoff ⟨h1, h2, hz⟩
  · have hbaseT : (Core.keyOf t (Core.iprjAddr B 0)).base = Core.keyOf t (Core.iprjAddr B 0) :=
      Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
    have htbl : env.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) = none :=
      haux.fresh_of_base_none (by
        show env.find? (Core.keyOf t (Core.iprjAddr B 0)).base = none
        rw [hbaseT]; exact hfreshT)
    rw [htbl] at hold
    cases hold

end IxVM.Refinement.Typing
