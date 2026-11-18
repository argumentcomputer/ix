import IxVMRefinement.Assembly.TypingRecLateFinal
import IxVMRefinement.Assembly.FoldClauseAlias

/-! # The step of a top-walked standalone recursor record, at the fold's clause

A standalone recursor record the walk checked, at the walk's limit (a validating limit or an
assumed binding), with the fold's clause at the recorded head traces (`FoldExtra
FormerOpenTraceAt`): the registry reads the parent's family off the store, whether its stored
former is a telescope or only head-reduces to one.

* `recArmRun_of_walk`: the walk's check of a top-walked recursor record took the recursor arm at
  the walk's limit (`Claim.TopWalkCore.recArm`, the role context read as the core reads it).
* `recLateOut_of_walk`: **the check's output at the family the registry reads at the recursor's
  own parent**, from what the walk hands every unit's step. This is the second interface of
  the late recursor step (`unitStep_recLate_foldExtra`).
* `unitStep_recLate_walked`: the step itself. Its first interface asks, at a fresh record, that
  a native parent heading the major premise is no basis family (`RecMajorFreshNotBasis`).
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel.Semantics (NativeFam)

/-- **The walk's check of a top-walked recursor record took the recursor arm**, at the walk's
limit. -/
theorem recArmRun_of_walk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank) {A : _root_.Address}
    {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) :
    RecArmRun calls t A lim :=
  recArmRun_of_limArm (hW.recArm hT hc hinfo)

/-- **The check's output at the family the registry reads at the recursor's own parent, for a
top-walked standalone recursor record** (module docstring). The premises are those the walk
hands every unit's step (the table's check, the run's store and its hashed records, the step's
store, the inert clause, the cover clause, the key of the record's address free) and, at a step
environment, the level clauses, the parent with its tie and the family read at the parent. -/
theorem recLateOut_of_walk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ E : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    {envT : Ix.Kernel.Env .anon} {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c) (hlogic : InLogic c) (hinfo : c.info = .recr rc)
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hkey : Decl.KeyFree (keyOf t A))
    {env : Ix.Kernel.Env .anon} (hstep : StepAt.{u} t envT E₀ E lim A c env)
    (hlv : LvClauses env)
    {P : _root_.Address} {ip : Ixon.InductiveProj} (hpar : RecParent t E env P ip)
    (htie : RecMajorTie t E₀ A c rc P) {fam : NativeFam .anon}
    (hm : FamReadAt FormerOpenTraceAt t E env P ip fam)
    (hbounds : ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
      ms[ip.idx.toNat]? = some (.indc ind) → RecArmBounds ip ind fam) :
    RecLateOut t E₀ E A env fam :=
  (recLateOutAll_of_arm ht hS hcov hst hc hinfo hlogic (recArmRun_of_walk hW hT hc hinfo) hkey
    hinert hcover hstep hlv hpar htie hm hbounds).at (hst.held hc) hst.runBlob

/-- **`UnitStep` for a top-walked standalone recursor record, keeping the fold's clause**, at
the walk's limit. `hres` is the basis exclusion at a fresh record. -/
theorem unitStep_recLate_walked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ E : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank)
    {envT : Ix.Kernel.Env .anon} {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c) (hlogic : InLogic c) (hinfo : c.info = .recr rc)
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hcov : LoadedReads.HashedRecordsStored calls E₀) (hst : StepStore calls t E₀ E)
    (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hkey : Decl.KeyFree (keyOf t A))
    (hres : RecMajorFreshNotBasis.{u} t envT E₀ E lim A c rc)
    (hbounds : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env →
      FamReadAt FormerOpenTraceAt t E env P ip fam →
      ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
        Ix.Cert.recordAt E ip.block = some cb → cb.info = .muts ms →
        ms[ip.idx.toNat]? = some (.indc ind) → RecArmBounds ip ind fam) :
    UnitStep.{u} (FoldExtra.{u} FormerOpenTraceAt t E) t envT E₀ E lim A c :=
  unitStep_recLate_foldExtra linkLaws_formerOpenTrace (RecMajorTie t E₀ A c rc) ht hinfo
    (address_size_of_record hS hc)
    (fun env hstep => recParent_of_arm_tied ht hS hst hc hinfo (recArmRun_of_walk hW hT hc hinfo)
      hinert hcover hres env hstep)
    (fun env P ip fam hstep hlv hpar htie hread =>
      recLateOut_of_walk hW hT hc hlogic hinfo ht hS hcov hst hinert hcover hkey hstep hlv hpar
        htie hread (hbounds env P ip fam hstep hread))

end IxVM.Refinement.Typing
