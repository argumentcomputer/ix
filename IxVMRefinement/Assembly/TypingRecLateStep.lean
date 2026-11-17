import IxVMRefinement.Assembly.TypingRecParentTie
import IxVMRefinement.Assembly.StoreArClauses
import IxVMRefinement.Assembly.NativeBlockAux
import IxVMRefinement.Decl.LateCtorRetHead

/-! # The late recursor step with the fold's carried clause

The fold carries, beside the invariant, the registry of native families, the store-key clause,
the projection-name clause and the level clauses:
`((LateRegistry t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧ LvClauses env`, the clause
of the native block's step. `unitStep_recLate_lv` is `unitStep_recLate_of_tied` for that clause:
the second interface also receives the level clauses at the step's environment (a large
eliminator's front check reads them, `constantValCheckJ_of_prefix_lv`), and the step keeps the
four clauses (`HashKeyed.append` at the record's 32-byte address, `cons_of_root_stored` at a base
key, `lvClauses_lateRec`).

`FamCtorRetHead t E fam` is the fact about a registry entry that the recursor comparison needs and
the recursor's own run does not check: at the member record the family's name is the key of, the
constructors' types return literally (`Decl.CtorRetHeadAt`). The native block's step has it from
`check_ctor_return_type` on its own loads.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (NativeFam)

/-- **The constructors of a registry entry return literally**: at the member record whose
address the family's name is the key of (its projection record at `P`, of member `ip.idx` of the
block record at `ip.block`), every constructor's type is, through the block record's sharing
table, the member's parameters and the constructor's fields as literal binders, then an
application spine over a reference (`Decl.CtorRetHeadAt`). -/
def FamCtorRetHead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (fam : NativeFam .anon) : Prop :=
  ∀ (P : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
    fam.p.cvT.name = keyOf t P → Ix.Cert.recordAt E P = some cm → cm.info = .iPrj ip →
    Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
    ms[ip.idx.toNat]? = some (.indc ind) → Decl.CtorRetHeadAt cb ind

/-- **`unitStep_recLate_of_tied` with the fold's carried clause** (module docstring). -/
theorem unitStep_recLate_lv {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (Q : _root_.Address → Prop)
    (ht : t.check = .ok ()) (hinfo : c.info = .recr rc) (hsz : A.hash.size = 32)
    (hparent : ∀ env, StepAt.{u} t envT E₀ E lim A c env →
      ∃ P ip, RecParent t E env P ip ∧ Q P)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → LvClauses env →
      RecParent t E env P ip → Q P → MatchedAt t E env P ip fam → RecLateOut t E₀ E A env fam) :
    UnitStep.{u}
      (fun env => ((LateRegistry.{u} t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧
        LvClauses env) t envT E₀ E lim A c := by
  intro env hext hnd hinv hX href hfresh
  obtain ⟨⟨⟨⟨Reg, hR⟩, hkeys⟩, haux⟩, hlv⟩ := hX
  have hstep : StepAt.{u} t envT E₀ E lim A c env := ⟨hext, hnd, hinv, href, hfresh⟩
  obtain ⟨P, ip, hpar, hQ⟩ := hparent env hstep
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam, hReg, hat, hnameP, hmatch⟩ := hR.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep hlv ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ hQ
      ⟨hat, hnameP, hmatch⟩
  have hcomp := late_companions ht hinv.companions ⟨hat, hnameP, hmatch⟩ hcm hcmi hrun
  obtain ⟨hinv', hR'⟩ := late_prefixInv_step hinv hR hReg hrun
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
  refine ⟨[cn], List.nodup_singleton _, ?_, hinv', ⟨⟨⟨⟨Reg, hR'⟩, hkeys'⟩, haux'⟩, hlv'⟩, ?_, ?_⟩
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
