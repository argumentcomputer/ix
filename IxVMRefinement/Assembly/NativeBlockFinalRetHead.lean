import IxVMRefinement.Assembly.NativeBlockFinalStruct
import IxVMRefinement.Assembly.RetHeadRegistry
import IxVMRefinement.Assembly.NativeBlockNoProjOf

/-! # The native block step carrying the literal return of every registered family

`NativeBlockXR t E`: the native block step's carried clause `NativeBlockX t E` with the registry
replaced by `RetHeadRegistry t E` (the registry and, for each of its families, the entry facts
`LateEntryFacts`: the constructors' literal return and no projection of the family in a stored
constructor type). `NativeBlockXR.toX` forgets it.

* `nativeBlockXR_basisEnv`: the clause at the environment of the pins;
* `keepsValuesKeyed_nativeBlockXR`: a value step at the key of a 32-byte address keeps it;
* `unitStep_nativeBlock_struct_rh`: `unitStep_nativeBlock_struct` for the clause: the install
  registers its family with the family's entry facts, produced from the member check
  (`famIxonRetHead_of_member`, `blockFamCtorNoProj_of_member`);
* `unitStep_recLate_xr`: the late recursor's step for the clause: the second interface
  receives the matched family's entry facts (`FamIxonRetHead`, `BlockFamCtorNoProj`); the
  registry, its facts and the other clauses are kept.
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
open IxVM.Refinement.TableInhabit (basisEnv)

universe u

/-- **The clause the fold carries beside the invariant, with the registered families'
constructors' literal return** (module docstring). -/
abbrev NativeBlockXR (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (env : Ix.Kernel.Env .anon) :
    Prop :=
  ((RetHeadRegistry.{u} t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧ LvClauses env

/-- The clause forgets to the native block step's clause. -/
theorem NativeBlockXR.toX {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (h : NativeBlockXR.{u} t E env) : NativeBlockX.{u} t E env :=
  ⟨⟨⟨h.1.1.1.lateRegistry, h.1.1.2⟩, h.1.2⟩, h.2⟩

/-- **The clause at the environment of the pins.** -/
theorem nativeBlockXR_basisEnv (E : Ixon.Env) : NativeBlockXR.{u} ctab E basisEnv :=
  ⟨⟨⟨retHeadRegistry_basis ctab E, hashKeyed_basisEnv⟩, auxRootSynced_basisEnv⟩,
    lvClauses_basisEnv⟩

/-- **A value step at the key of a 32-byte address keeps the clause.** -/
theorem keepsValuesKeyed_nativeBlockXR {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    (E : Ixon.Env) : KeepsValuesKeyed t (NativeBlockXR.{u} t E) :=
  (((keepsValuesKeyed_retHeadKeyed htwf E).and (keepsValuesKeyed_auxRoot t)).and
    (keepsValuesKeyed_lvClauses t))

/-- **`UnitStep` for a one-type native inductive block without its recursor, carrying the
registered families' constructors' literal return**: `unitStep_nativeBlock_struct` for
`NativeBlockXR` (same inputs). -/
theorem unitStep_nativeBlock_struct_rh {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr B : _root_.Address}
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
    (hcert : ind.ctors.size = 1 → ind.indices.toNat = 0 →
      ∀ (env : Ix.Kernel.Env .anon) (new blk : List (ConstantInfo .anon))
        (p₀ p : Ix.Kernel.NativeParts .anon) (ty' : Ix.Kernel.Expr .anon)
        (ctorsA : List (ConstantVal .anon × Nat)) (caps : IndCaps .anon),
        NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps →
        Ix.Kernel.Level.isEquiv p.resSort .zero = some true →
        BlockCert t E ⟨new ++ env.consts⟩ B) :
    UnitStep.{u} (NativeBlockXR.{u} t E) t envT E₀ E lim B cb := by
  subst hlim
  have hP : HashedBlockProjectionsHeld E := hashedBlockProjectionsHeld_of_decoded hst.decoded
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
  have hG : BlockFire ⟨E, env, t, some n⟩ new B := by
    by_cases hs : ind.ctors.size = 1 ∧ ind.indices.toNat = 0 ∧
        Ix.Kernel.Level.isEquiv p.resSort .zero = some true
    · exact blockFire_of_cert hread hI
        (hcert hs.1 hs.2.1 env new _ p₀ p ty' ctorsA caps hO hs.2.2)
    · exact blockFire_of_install_off hO haux hfreshT hs
  have hT : BlockTable ⟨E, env, t, some n⟩ new B ind :=
    blockTable_of_install hI hinv hpin hna hO.facts hcvT hO.nP₀ hO.nIdx₀ hO.lenA hctorsA hfreshT
      hG
  have hE : BlockEta ⟨E, env, t, some n⟩ new :=
    blockEta_of_install hrec hinv hkeys hstored hpin hna hO
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
  -- the carried clause after the install: the family registered with its constructors' return
  have hrh := famIxonRetHead_of_member ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP
    hkeys hfresh hkey hcov haux hO
  have hreg₂ : RetHeadRegistry.{u} t E ⟨new ++ env.consts⟩ :=
    hreg.nativeNoRec hO.facts (lateFamAt_of_install hrec hO) hrh
      (blockFamCtorNoProj_of_member ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP hkeys
        hfresh hkey hcov haux hO)
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

/-- **The late recursor's step with the clause**: the parent's predicate `Q` produced by the
first interface; the second receives the level clauses at the step's environment and the
matched family's constructors' literal return. The step keeps the registry (unchanged), its
facts, the store keys (`HashKeyed.append` at the record's 32-byte address), the projection names
(`cons_of_root_stored` at a base key) and the level clauses (`lvClauses_lateRec`). -/
theorem unitStep_recLate_xr {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (Q : _root_.Address → Prop)
    (ht : t.check = .ok ()) (hinfo : c.info = .recr rc) (hsz : A.hash.size = 32)
    (hparent : ∀ env, StepAt.{u} t envT E₀ E lim A c env →
      ∃ P ip, RecParent t E env P ip ∧ Q P)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → LvClauses env →
      RecParent t E env P ip → Q P → MatchedAt t E env P ip fam → FamIxonRetHead t E fam →
      BlockFamCtorNoProj fam → RecLateOut t E₀ E A env fam) :
    UnitStep.{u} (NativeBlockXR.{u} t E) t envT E₀ E lim A c := by
  intro env hext hnd hinv hX href hfresh
  obtain ⟨⟨⟨⟨Reg, hR, hH⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hstep : StepAt.{u} t envT E₀ E lim A c env := ⟨hext, hnd, hinv, href, hfresh⟩
  obtain ⟨P, ip, hpar, hQ⟩ := hparent env hstep
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam, hReg, hat, hnameP, hmatch⟩ := hR.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep hlv ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ hQ
      ⟨hat, hnameP, hmatch⟩ (hH fam hReg).1 (hH fam hReg).2
  have hcomp := late_companions ht hinv.companions ⟨hat, hnameP, hmatch⟩ hcm hcmi hrun
  obtain ⟨hinv', hR'⟩ := late_prefixInv_step_rh hinv hR hH hReg hrun
    (hname.trans (LoadedReads.keyOf_eq t A).symm) hcomp hreload
  obtain ⟨hfreshN, -, -, -⟩ := late_head hrun
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  have htwf : t.wf = true := hinv.tableWf
  have hkeys' : HashKeyed t ⟨[cn] ++ env.consts⟩ :=
    HashKeyed.append htwf hkeys fun ci hci => by
      obtain rfl := List.mem_singleton.mp hci
      exact Or.inl ⟨A, hname.trans (LoadedReads.keyOf_eq t A).symm, hsz⟩
  have hbase : cn.name.base = cn.name := by
    rw [hname, ← LoadedReads.keyOf_eq t A]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t A)
  have haux' : Decl.AuxRootSynced ⟨cn :: env.consts⟩ := haux.cons_of_root_stored (Or.inl hbase)
  have hlv' : LvClauses ⟨cn :: env.consts⟩ := lvClauses_lateRec hat hlv hrun
  refine ⟨[cn], List.nodup_singleton _, ?_, hinv', ⟨⟨⟨hR', hkeys'⟩, haux'⟩, hlv'⟩, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshN
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hstored⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

end IxVM.Refinement.Typing
