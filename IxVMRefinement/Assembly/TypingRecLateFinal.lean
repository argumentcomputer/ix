import IxVMRefinement.Assembly.TypingRecLateOut
import IxVMRefinement.Assembly.TypingRecLateRunBounds
import IxVMRefinement.Assembly.TypingRecLateRetHead
import IxVMRefinement.Assembly.TypingRecLateNative
import IxVMRefinement.Assembly.TypingRecLateNativeRaw
import IxVMRefinement.Assembly.TypingRecLateReading
import IxVMRefinement.Assembly.TypingRecLateFields
import IxVMRefinement.Assembly.TypingRecLatePinsAt
import IxVMRefinement.Assembly.TypingRecLateKStored

/-! # The check of a standalone recursor record at its parent's registered family

`recLateOutAll_of_arm`: what the circuit's check of a standalone recursor record gives at the
family the fold's registry holds at the recursor's own parent, at any validation limit and for
a family whose stored former need not be its telescope constant (the registry's link is the
recorded head traces, `FormerOpenTraceAt`). It is stated once, with the recursor's reload at
every store that holds the record (`RecLateOutAll`): the typing fold reads it at its step's
store and the binding fold at every record store.

* the late relation's conjuncts read off the arm (`rec_pins_of_arm`, `rec_elim_of_arm`,
  `rec_field_sorts_of_arm`, `rec_nativeRecJ_of_arm`, with the read rules' scoping from the member
  check, `rec_rules_scoped_of_arm`), the reading (`rec_reads_of_arm`), the K bit
  (`rec_k_stored_of_arm`), assembled by `rec_lateOut_of_parts`;
* the registry entry's two facts about its constructors (`FamRead.retHead`, `FamRead.noProj`)
  and its recorded result-sort walk (`formerSortReads_of_trace`), read at the step's
  environment.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantVal RecRule)
open Ix.Kernel.Semantics (NativeFam)

/-- Two rule readings of one rule list are one. -/
theorem ruleReads_unique {t : Ix.Kernel.RoleTable} {mr : Ix.Kernel.Reader.MemberReader .anon}
    {B : _root_.Address} {i : Nat} :
    ∀ {xs : List (Ixon.RecursorRule × Nat)} {r₁ r₂ : List (RecRule .anon)},
      List.Forall₂ (RuleReads t mr B i) xs r₁ → List.Forall₂ (RuleReads t mr B i) xs r₂ →
      r₁ = r₂
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons h₁ t₁, .cons h₂ t₂ => by
    obtain ⟨rhs₁, hr₁, e₁⟩ := h₁
    obtain ⟨rhs₂, hr₂, e₂⟩ := h₂
    rw [hr₁] at hr₂
    cases hr₂
    subst e₁ e₂
    rw [ruleReads_unique t₁ t₂]

/-- The level parameters of the recursor read at the matched member: the member's, behind one
more at a large eliminator. -/
abbrev lateRecLps (rc : Ixon.Recursor) (ind : Ixon.Inductive) : List Ix.Kernel.LevelParam :=
  Ix.Kernel.Reader.recLps (decide (rc.lvls.toNat = ind.lvls.toNat + 1)) (List.range ind.lvls.toNat)

/-- **The check's output at the recursor's own parent** (module docstring). The circuit's
evidence at the record: `hS`, `hcov`, `hst` (the run's store, its hashed records, the step's
store), `hc`, `hinfo`, `hlogic` (the record, a recursor, in Lean's logic), `hnat` (its check
took the recursor arm at the limit `lim`), `hkey`, `hinert`, `hcover` (its key free, no inert
axiom used, the cover clause). At a step environment: the level clauses, the parent the circuit
read with its tie to the record, and the family the registry reads off that parent's record. -/
theorem recLateOutAll_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hnat : RecArmRun calls t A lim)
    (hkey : Decl.KeyFree (keyOf t A)) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    (hlv : LvClauses env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} (hpar : RecParent t E env P ip)
    (htie : RecMajorTie t E₀ A c rc P) {fam : NativeFam .anon}
    (hm : FamReadAt FormerOpenTraceAt t E env P ip fam) :
    RecLateOutAll t E₀ A c env fam := by
  obtain ⟨-, -, ⟨cm, hcm, hcmi⟩, -⟩ := hpar
  have hm' := hm
  obtain ⟨hat, hname, cb, ms, ind, hcb, hms, hind, hnP, hnI, hlenC, hnames⟩ := hm'
  have hhd : Decl.CtorRetHeadAt cb ind :=
    famCtorRetHead_of_ixon hat.retHead P cm ip cb ms ind hname hcm hcmi hcb hms hind
  have hnoProj : FamCtorNoProj fam := hat.noProj
  obtain ⟨-, -, -, hpP, hiP, -, -⟩ :=
    recArmRunBounds_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb hms hind
  have hsr : FormerSortReads t E lim env fam :=
    formerSortReads_of_trace hstep.inv.scopedCoreFacts hstep.inv.store.store.wf
      (by rw [hnP, hnI]; omega) hat.link
  obtain ⟨ty, rules, tyC, rlsC, recTy, hty, hlbb, hdef, hrd, hrr, hcT, hcR, hnatJ, hgen, hwrap,
    hannT, hrs, hlen⟩ :=
    rec_nativeRecJ_of_arm ht hS hcov hst hc hinfo hlogic hnat hkey hinert hcover hstep hlv
      hcm hcmi htie hcb hms hind hm hhd hnoProj
      (rec_rules_scoped_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hcb
        hms hind)
  obtain ⟨rules', hrr', -, hmI, hrP, hrlen, hpins⟩ :=
    rec_pins_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hm
      (lateRecLps rc ind) ⟨keyOf t A, lateRecLps rc ind, ty⟩
      (if decide (rc.lvls.toNat = ind.lvls.toNat + 1) then ind.lvls.toNat else 0)
      (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
  have hreq : rules' = rules := ruleReads_unique hrr' hrr
  subst hreq
  have helim := rec_elim_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie
    hcb hms hind hat.stored hsr hname hnP hnI hlenC
  have hfs := rec_field_sorts_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi
    htie hcb hms hind hm hsr
  have hK := rec_k_stored_of_arm ht hS hst hc hinfo hnat hinert hcover hstep hcm hcmi htie hm
    hsr
  obtain ⟨hp, -, -, -, -⟩ := rec_counts_of_arm ht hS hst hc hinfo hnat hinert hcover hstep
    hcm hcmi htie hcb hms hind
  have hreads := rec_reads_of_arm ht hS hcov hst hc hinfo hlogic hnat hinert hcover hstep
    hcm hcmi htie hcb hms hind hm hty hrr' hannT hgen hwrap
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  exact rec_lateOut_of_parts ht hinfo hstored hlen hty hlbb hdef hrd hcT
    hcR hannT hrs hmI hrP hrlen hpins hat.stored helim hfs hnatJ hK (hnP.trans hp.symm) hreads

end IxVM.Refinement.Typing
