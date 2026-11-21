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
