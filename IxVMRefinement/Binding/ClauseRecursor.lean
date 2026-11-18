import IxVMRefinement.Binding.ClauseInhabit
import IxVMRefinement.Assembly.TypingRecLateRegistered

/-! # The binding fold's step of a standalone recursor record, from the circuit's check

The check of a standalone recursor record gives one output, with the recursor's reload at
every store that holds the record (`Typing.RecLateOutAll`, `Typing.recLateOutAll_of_arm`). The
typing fold reads it at its step's store; this module reads it at every record store of the
binding fold's witness store:

* `recLateOutOver_of_all`: where the witness store holds the record and the run's blobs, the
  output is the binding fold's (`RecLateOutOver`).
* `overUnitStep_recLate_tied`: the step over the fold's clause with a predicate on the parent,
  which the first interface produces and the second receives. The second interface cannot be
  asked at every parent the store reads as native: the check's output holds only at the parent
  that heads the record's own major premise.
* `overUnitStep_recLate_of_arm`: **the step of a standalone recursor record of a registered
  family, over the fold's clause at the recorded head traces**, from the circuit's check of
  the record at one record store and one carried limit. That the record's key is no
  operation's follows from its being free.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal RecRule)
open Ix.Kernel.Semantics (NativeFam DeclNativeRecLateRunJ)
open Ix.Kernel.Model (rulesJ)

/-- **The check's output at every record store of a witness store that holds the record and
the run's blobs.** -/
theorem recLateOutOver_of_all {t : Ix.Kernel.RoleTable} {R E₀ : Ixon.Env} {A : _root_.Address}
    {c : Ixon.Constant} {env : Ix.Kernel.Env .anon} {fam : NativeFam .anon}
    (h : RecLateOutAll t E₀ A c env fam) (hR : recordOf R A = some c)
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b) :
    RecLateOutOver t R E₀ A env fam := by
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ := h
  exact ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, fun E hE =>
    hreload E (recordOf_of_recordsFor hE hR) (blob_of_recordsFor hE hblobs)⟩

/-- **The step of a standalone recursor record over the fold's clause, with the parent tied to
the record.** `Ec` is a record store for `R` the parent is read at, at a carried limit `lim₀`
within `G`. The first interface produces the parent with `Q` and with `R` holding its
projection record; the second receives `Q`, the level clauses at the step's environment and the
family the registry reads at that parent. -/
theorem overUnitStep_recLate_tied {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {t : Ix.Kernel.RoleTable} {G : Nat → Prop} {R E₀ Ec : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim₀ : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (Q : _root_.Address → Prop) (ht : t.check = .ok ())
    (hinfo : c.info = .recr rc) (hsz : A.hash.size = 32) (hRc : RecordsFor R Ec)
    (hc₀ : Carried lim₀) (hl₀ : LimWithin G t lim₀) (hop : keyOf t A ∉ RoleOps.opNames)
    (hparent : ∀ env, StepAt.{u} t envT E₀ Ec lim₀ A c env →
      ∃ P ip, RecParent t Ec env P ip ∧ (recordOf R P).isSome = true ∧ Q P)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ Ec lim₀ A c env → LvClauses env →
      RecParent t Ec env P ip → Q P → FamReadAt L t Ec env P ip fam →
      RecLateOutOver t R E₀ A env fam) :
    OverUnitStep.{u} L t G R envT E₀ A c := by
  intro env Reg hext hnd hcl href hfresh
  have hC₀ := hcl Ec hRc lim₀ hc₀ hl₀
  have hstep : StepAt.{u} t envT E₀ Ec lim₀ A c env :=
    ⟨hext, hnd, hC₀.prefixInv, href, hfresh⟩
  obtain ⟨P, ip, hpar, hheld, hQ⟩ := hparent env hstep
  have hpar' := hpar
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar'
  -- The family, found once, at the store the parent was read at.
  obtain ⟨fam, hReg, hread₀⟩ := hC₀.registry.at_parent ht hfP hres hcm hcmi hnat
  have hnameP : fam.p.cvT.name = keyOf t P := hread₀.2.1
  obtain ⟨cmR, hcmR⟩ := Option.isSome_iff_exists.mp hheld
  have hcc : cmR = cm := Option.some.inj ((hRc.2.1 P cmR hcmR).symm.trans hcm)
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep hC₀.core.2 hpar hQ hread₀
  -- The clause with the recursor, at every store for `R` and every carried limit within `G`.
  have hall : ∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
      FoldClauseWith.{u} L t E lim ⟨cn :: env.consts⟩ Reg := by
    intro E hE lim hc hl
    have hC := hcl E hE lim hc hl
    have hcmE : Ix.Cert.recordAt E P = some cm := by
      rw [← hcc]
      exact hE.2.1 P cmR hcmR
    have hread : FamReadAt L t E env P ip fam := (hC.fams fam hReg).readAt ht hnameP hcmE hcmi
    have hcomp := late_companions_read ht hC.companions hread hcmE hcmi hrun
    exact hC.lateRec hL hReg hrun (hname.trans (LoadedReads.keyOf_eq t A).symm) hsz hcomp
      (hreload E hE)
  obtain ⟨hfreshN, -, -, -⟩ := late_head hrun
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  refine ⟨[cn], Reg, List.nodup_singleton _, ?_, hall, ?_, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshN
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    rw [hname]
    exact hop
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hstored⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

/-- **The step of a standalone recursor record of a registered family, over the fold's clause
at the recorded head traces** (module docstring). The record's check took the recursor arm at
the carried limit `lim₀` within `G`; `Ec` is a record store for `R` the run is good for; `R`
holds the record, only records the run loaded, every blob the run loaded, and the projection
record of the parent that heads the record's major premise. -/
theorem overUnitStep_recLate_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {G : Nat → Prop} {R E₀ Ec : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim₀ : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀)
    (hRc : RecordsFor R Ec) (hst : StepStore calls t E₀ Ec)
    (hR : recordOf R A = some c)
    (hloaded : ∀ a lc, R.consts.get? a = some lc → E₀.consts.get? a = some lc)
    (hblobs : ∀ x b, E₀.blobs.get? x = some b → R.blobs.get? x = some b)
    (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hnat : RecArmRun calls t A lim₀) (hc₀ : Carried lim₀) (hl₀ : LimWithin G t lim₀)
    (hkey : Decl.KeyFree (keyOf t A)) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hres : RecMajorFreshNotBasis.{u} t envT E₀ Ec lim₀ A c rc)
    (hparentHeld : ∀ P, RecMajorTie t E₀ A c rc P → (recordOf R P).isSome = true) :
    OverUnitStep.{u} FormerOpenTraceAt t G R envT E₀ A c := by
  have hc : recordOf E₀ A = some c := recordOf_of_loaded hloaded hR
  exact overUnitStep_recLate_tied linkLaws_formerOpenTrace (RecMajorTie t E₀ A c rc) ht hinfo
    (address_size_of_record hS hc) hRc hc₀ hl₀ (not_mem_opNames_of_keyFree hkey)
    (fun env hstep => by
      obtain ⟨P, ip, hpar, htie⟩ :=
        recParent_of_arm_tied ht hS hst hc hinfo hnat hinert hcover hres env hstep
      exact ⟨P, ip, hpar, hparentHeld P htie, htie⟩)
    (fun env P ip fam hstep hlv hpar htie hread =>
      recLateOutOver_of_all
        (recLateOutAll_of_arm ht hS hcov hst hc hinfo hlogic hnat hkey hinert hcover hstep hlv
          hpar htie hread)
        hR hblobs)

end IxVM.Refinement.Binding
