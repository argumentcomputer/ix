import IxVMRefinement.Assembly.TypingRecLateOut
import IxVMRefinement.Assembly.TypingRecLateRetHead
import IxVMRefinement.Assembly.TypingRecLateNative
import IxVMRefinement.Assembly.TypingRecLateReading
import IxVMRefinement.Assembly.TypingRecLateFields
import IxVMRefinement.Assembly.TypingRecLatePinsAt
import IxVMRefinement.Assembly.TypingRecLateKStored

/-! # The step of a standalone recursor record of a native family

`unitStep_recLate`: `UnitStep` for a top-walked, in-logic, standalone recursor record whose parent
is a registered native family, with the fold's carried clause (the native block step's: registry,
store keys, projection names, level clauses).

* `recLateOut_of_arm` (the second interface at the recursor's own parent): the late relation's
  conjuncts read off the arm (`rec_pins_of_arm`, `rec_elim_of_arm`, `rec_field_sorts_of_arm`,
  `rec_nativeRecJ_of_arm`), the reading (`rec_reads_of_arm`), the K bit (`rec_k_stored_of_arm`),
  assembled by `rec_lateOut_of_parts`;
* the parent with its tie (`recParent_of_arm_tied`);
* `unitStep_recLate_lv`.
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

/-- **The rules of the record, read at the matched member's level parameters, are closed and
their level parameters are among those** (the reading of `rc.rules` at `lateRecLps rc ind`). -/
def RecRulesScoped (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (A : _root_.Address)
    (c : Ixon.Constant) (rc : Ixon.Recursor) (ind : Ixon.Inductive) : Prop :=
  ∀ rules : List (RecRule .anon),
    List.Forall₂ (fun ru rl₀ => (exprReader t (fun x => E₀.blobs.get? x) c
        (Ix.Kernel.Reader.recParam (lateRecLps rc ind)) (soloSelf t A)).read ru.rhs =
          .ok rl₀.rhs) rc.rules.toList rules →
    ∀ rl₀ ∈ rules, rl₀.rhs.looseBVarsBounded 0 = true ∧
      rl₀.rhs.allLevelParamsDefined (lateRecLps rc ind) = true

/-- **The second interface at the recursor's own parent** (module docstring). -/
theorem recLateOut_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hlim : lim = some n) (hnat : NativeRecArm calls bAddr t A n)
    (hkey : Decl.KeyFree (keyOf t A)) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    (hlv : LvClauses env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} (hpar : RecParent t E env P ip)
    (htie : RecMajorTie t E₀ A c rc P) {fam : NativeFam .anon}
    (hm : MatchedAt t E env P ip fam) (hhead : FamCtorRetHead t E fam)
    (hnoProj : FamCtorNoProj fam)
    (hbounds : ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
      ms[ip.idx.toNat]? = some (.indc ind) → RecArmBounds ip ind fam)
    (hscoped : ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
      ms[ip.idx.toNat]? = some (.indc ind) → RecRulesScoped t E₀ A c rc ind) :
    RecLateOut t E₀ E A env fam := by
  obtain ⟨-, -, ⟨cm, hcm, hcmi⟩, -⟩ := hpar
  have hm' := hm
  obtain ⟨hat, hname, cb, ms, ind, hcb, hms, hind, hnP, hnI, hlenC, hnames⟩ := hm'
  have hhd : Decl.CtorRetHeadAt cb ind := hhead P cm ip cb ms ind hname hcm hcmi hcb hms hind
  obtain ⟨ty, rules, tyC, rlsC, recTy, hty, hlbb, hdef, hrd, hrr, hcT, hcR, hnatJ, hgen, hwrap,
    hannT, hrs, hlen⟩ :=
    rec_nativeRecJ_of_arm ht hS hcov hst hc hinfo hlogic hlim hnat hkey hinert hcover hstep hlv
      hcm hcmi htie hcb hms hind hm hhd hnoProj (hbounds cb ms ind hcb hms hind)
      (hscoped cb ms ind hcb hms hind)
  obtain ⟨rules', hrr', -, hmI, hrP, hrlen, hpins⟩ :=
    rec_pins_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie hm
      (lateRecLps rc ind) ⟨keyOf t A, lateRecLps rc ind, ty⟩
      (if decide (rc.lvls.toNat = ind.lvls.toNat + 1) then ind.lvls.toNat else 0)
      (decide (rc.lvls.toNat = ind.lvls.toNat + 1))
  have hreq : rules' = rules := ruleReads_unique hrr' hrr
  subst hreq
  have helim := rec_elim_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie
    hcb hms hind hat hname hnP hnI hlenC
  have hfs := rec_field_sorts_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi
    htie hcb hms hind hm
  have hK := rec_k_stored_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep hcm hcmi htie hm
  obtain ⟨hp, -, -, -, -⟩ := rec_counts_of_arm ht hS hst hc hinfo hlim hnat hinert hcover hstep
    hcm hcmi htie hcb hms hind
  have hreads := rec_reads_of_arm ht hS hcov hst hc hinfo hlogic hlim hnat hinert hcover hstep
    hcm hcmi htie hcb hms hind hm hty hrr' hannT hgen hwrap
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  exact rec_lateOut_of_parts ht (hst.held hc) hinfo hst.runBlob hstored hlen hty hlbb hdef hrd hcT
    hcR hannT hrs hmI hrP hrlen hpins hat.stored helim hfs hnatJ hK (hnP.trans hp.symm) hreads

/-- **The step of a top-walked, in-logic, standalone recursor record of a native family**, with
the fold's carried clause (the native block step's). The circuit's evidence at the record:
`hS`, `hcov`, `hst` (the run's store, its hashed records, the step's store), `hc`, `hinfo`,
`hlogic` (the record, a recursor, in Lean's logic), `hlim`, `hnat` (checked on the native recursor
route at the limit `n`), `hkey`, `hinert`, `hcover` (its key free, no inert axiom used, the cover
clause), `hres` (the major premise's head is no basis name). Named hypotheses about the matched
registry entry and the record, at every environment the fold hands the step: `hhead` (the
entry's constructors return literally, `FamIxonRetHead`: the native block step's, carried by the
fold), `hnoProj` (no stored constructor type projects out of the family: the native block step's
constructor stage), `hbounds` (the count bounds of the native recursor comparison's
specifications) and `hscoped` (the record's rules, read at the member's level parameters, are
closed). -/
theorem unitStep_recLate {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {bAddr A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlogic : InLogic c)
    (hlim : lim = some n) (hnat : NativeRecArm calls bAddr t A n)
    (hkey : Decl.KeyFree (keyOf t A)) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hres : RecMajorNotBasis t E₀ A c rc)
    (hhead : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → MatchedAt t E env P ip fam →
      FamIxonRetHead t E fam)
    (hnoProj : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env →
      MatchedAt t E env P ip fam → FamCtorNoProj fam)
    (hbounds : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env →
      MatchedAt t E env P ip fam →
      ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
        Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
        ms[ip.idx.toNat]? = some (.indc ind) → RecArmBounds ip ind fam)
    (hscoped : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env →
      MatchedAt t E env P ip fam →
      ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
        Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
        ms[ip.idx.toNat]? = some (.indc ind) → RecRulesScoped t E₀ A c rc ind) :
    UnitStep.{u}
      (fun env => ((LateRegistry.{u} t E env ∧ HashKeyed t env) ∧ Decl.AuxRootSynced env) ∧
        LvClauses env) t envT E₀ E lim A c :=
  unitStep_recLate_lv (RecMajorTie t E₀ A c rc) ht hinfo (address_size_of_record hS hc)
    (fun env hstep => recParent_of_arm_tied ht hS hst hc hinfo hlim hnat hinert hcover hres env
      hstep)
    (fun env P ip fam hstep hlv hpar htie hm =>
      recLateOut_of_arm ht hS hcov hst hc hinfo hlogic hlim hnat hkey hinert hcover hstep hlv hpar
        htie hm (famCtorRetHead_of_ixon (hhead env P ip fam hstep hm))
        (hnoProj env P ip fam hstep hm) (hbounds env P ip fam hstep hm)
        (hscoped env P ip fam hstep hm))

end IxVM.Refinement.Typing
