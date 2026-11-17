import IxVMRefinement.Assembly.NativeBlockInstallOf
import IxVMRefinement.Assembly.NativeBlockTableOf
import IxVMRefinement.Assembly.NativeBlockEta
import IxVMRefinement.Assembly.NativeBlockAux
import IxVMRefinement.Assembly.StoreArClauses
import IxVMRefinement.Assembly.LateValueStep

/-! # The per-record step of a native inductive block without its recursor

`unitStep_nativeBlock`: `UnitStep` for a one-type native inductive block whose former is a
syntactic telescope, its type former and constructors as one unit, with the carried clause
`NativeBlockX t E` (the registry of native families, the store-key clause, the projection-name
clause and the level clauses).

The step at an environment `env` handed by the fold: the readings and the recogniser
(`blockReads_of_member`, `nativeParts_of_member`), the install read off the member check
(`nativeInstallOut_of_member`), the new projection table (`blockTable_of_install`), the load
contract after the install (`storedLoads_append` with `BlockInstall.newLoads`), the prefix
invariant there (`PrefixInv.nativeNoRec_eta`), and the carried clause there: the family registered
(`LateRegistry.nativeNoRec'` with `lateFamAt_of_install`), the store keys (`HashKeyed.append`),
the projection names (`NativeNoRecFacts.auxRootSynced`), the level clauses
(`NativeNoRecFacts.lvClauses`).

The level clauses are not read by this step; they are in the carried clause so that it is the
fold's one clause, which the value steps read for their front check
(`constantValCheckJ_of_prefix_lv`) and this step keeps.

Two inputs remain, each stated over the install read off the member check
(`NativeInstallOut`): the projection guard of the new table (`BlockGuard`, open: the circuit
recomputes the field sorts at each use, IxC reads them stored) and the two η fields of the load
contract at the new family (`BlockEta`).
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

/-! ## The step -/

/-- **The clause the fold carries beside the invariant** (module docstring). -/
abbrev NativeBlockX (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  ((LateRegistry.{u} t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧ LvClauses env

/-- **`UnitStep` for a one-type native inductive block without its recursor** (module
docstring). The unit is the block's record at `B`; it is checked at the limit `n` of the member
check, on the native route, with its former declared at a syntactic telescope. -/
theorem unitStep_nativeBlock {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n) (hlim : lim = some n)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hkey : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb)
    (hP : HashedBlockProjectionsHeld E) (hcov : L1.CanonicalHashCoverage E calls)
    (hguard : ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
      (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
      (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
      BlockGuard ⟨E, env, t, some n⟩ new B)
    (heta : ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
      (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
      (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
      Decl.PrefixInv.{u} E t (some n) env →
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
      BlockEta ⟨E, env, t, some n⟩ new) :
    UnitStep.{u} (NativeBlockX.{u} t E) t envT E₀ E lim B cb := by
  subst hlim
  intro env hext hnd hinv hXe href hfresh
  obtain ⟨⟨⟨hreg, hkeys⟩, haux⟩, hlv⟩ := hXe
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  obtain ⟨ty₀, cs, -, -, -, hall⟩ := blockReads_of_member ht hbound hS hrec hchk
  obtain ⟨hblk, hpin, hna⟩ := hall {}
  obtain ⟨p₀, hp₀, -⟩ := nativeParts_of_member ht hbound hS hrec hchk htele hblk hkey
  obtain ⟨new, p, ty', ctorsA, caps, hO⟩ := nativeInstallOut_of_member ht hS hst hrec hchk hnat
    htele hblk hp₀ hinv hstored hP hkeys hfresh hkey hcov haux hnd
  have hI := hO.install
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hcvT : p₀.cvT = ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat,
      p₀.cvT.type⟩ := by
    rw [← hO.cvT₀.1, ← hO.cvT₀.2]
  have hctorsA : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
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
  have hT : BlockTable ⟨E, env, t, some n⟩ new B ind :=
    blockTable_of_install hI hinv hpin hna hO.facts hcvT hO.nP₀ hO.nIdx₀ hO.lenA hctorsA hfreshT
      (hguard env new _ p₀ p ty' ctorsA caps hO)
  have hE := heta env new _ p₀ p ty' ctorsA caps hinv hO
  -- the names of the new constants
  have hnres : ∀ cn ∈ new, cn.name ≠ Core.unresolvedKey := by
    intro cn hcn
    rcases hI.newName cn hcn with h | ⟨j, -, h⟩ | ⟨tbl, rfl⟩
    · rw [h]; exact keyOf_ne_unresolvedKey t _
    · rw [h]; exact keyOf_ne_unresolvedKey t _
    · show Ix.Kernel.projTableName tbl.structName ≠ Core.unresolvedKey
      rw [hO.tableName tbl hcn]
      exact projTableName_keyOf_ne_unresolvedKey t _
  have hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon),
      (⟨new ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k = some ci → env.find? k = none →
      k ≠ Core.unresolvedKey := by
    intro k ci hf hnone
    rcases find?_append_cases new hf with hm | hold
    · rw [← Core.WhnfAux.name_of_find hf]
      exact hnres ci hm
    · rw [hnone] at hold
      cases hold
  -- the load contract and the invariant after the install
  have hloads := storedLoads_append (c := ⟨E, env, t, some n⟩) hinv.loads hO.facts.envExt hnres
    hinv.etaStable (hI.newLoads hT hE)
  have hinv₂ : Decl.PrefixInv.{u} E t (some n) ⟨new ++ env.consts⟩ :=
    PrefixInv.nativeNoRec_eta hinv hO.facts hpin hna hres hloads
  -- the carried clause after the install
  have hreg₂ : LateRegistry.{u} t E ⟨new ++ env.consts⟩ :=
    LateRegistry.nativeNoRec' hreg hO.facts (lateFamAt_of_install hrec hO)
  have hkeys₂ : HashKeyed t ⟨new ++ env.consts⟩ := by
    refine HashKeyed.append htwf hkeys fun ci hci => ?_
    rcases hI.newName ci hci with h | ⟨j, hj, h⟩ | ⟨tbl, rfl⟩
    · exact Or.inl ⟨Core.iprjAddr B 0, h, address_size_of_record hS hrec.former⟩
    · exact Or.inl ⟨Core.cprjAddr B 0 j, h, address_size_of_record hS (hrec.ctors j hj)⟩
    · exact Or.inr fun y h =>
        Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t y) h.symm
  have haux₂ : Decl.AuxRootSynced ⟨new ++ env.consts⟩ :=
    NativeNoRecFacts.auxRootSynced hpin hna hO.facts haux
  have hlv₂ : LvClauses ⟨new ++ env.consts⟩ := NativeNoRecFacts.lvClauses hpin hO.facts hlv
  exact ⟨new, hO.nodup, hO.fresh, hinv₂, ⟨⟨⟨hreg₂, hkeys₂⟩, haux₂⟩, hlv₂⟩, hO.reads, hO.named⟩

end IxVM.Refinement.Typing
