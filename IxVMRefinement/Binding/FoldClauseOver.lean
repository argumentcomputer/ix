import IxVMRefinement.Binding.Glue
import IxVMRefinement.Binding.RegistryBasis
import IxVMRefinement.Assembly.FoldClause

/-! # The fold's clause over every store for a witness store

The binding fold's invariant is stated for every record store for its own store `R` and every
limit a role context carries. `FoldClauseOver L t G R env` is the fold's clause
(`Typing.FoldClause`) in that form, with **one registry chosen before the store and the
limit**: the registered families are the same at every store, and only their reading
(`FamRead`), the completeness of the registry and the load contract are taken store by store.

* `FoldClauseOver.clauseAt`: at one store and limit it is the typing fold's clause.
* `xAllGroups_foldClauseOver`: on the 77 groups it is the clause on every group.
* `foldClauseOver_basis_at`, `foldClause_basis_at`: it holds at the environment of the pins,
  with the empty registry, for every well-formed table that pins the prelude and binds every
  role.
* `FoldClauseOver.parent_everywhere`: a recursor's parent family, found in the registry at the
  one store a run is good for, is registered and read off the parent's record at every store
  for `R` that holds the parent's projection record. No fact about the circuit's dispatch at
  the other stores is used.
* `typing_skeleton_clause`, `composed_skeleton_clause`: the typing half and the composed
  statement with this clause as the witness's extra part, from typing steps that keep
  `Typing.FoldExtra` and binding steps that keep `FoldClauseOver`.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.TableInhabit (basisEnv)
open IxVM.Refinement.StoreInhabit (basisStore)

/-- **The fold's clause at every record store for `R` and every carried limit within `G`**,
with one registry for all of them. -/
def FoldClauseOver (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (G : Nat → Prop) (R : Ixon.Env) (env : Ix.Kernel.Env .anon) : Prop :=
  ∃ Reg : NativeFam .anon → Prop, ∀ E, RecordsFor R E → ∀ lim, Carried lim →
    LimWithin G t lim → FoldClauseWith.{u} L t E lim env Reg

section Over

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {t : Ix.Kernel.RoleTable}
  {G : Nat → Prop} {R : Ixon.Env} {env : Ix.Kernel.Env .anon}

/-- At one store and limit, the clause the typing fold carries. -/
theorem FoldClauseOver.clauseAt (h : FoldClauseOver.{u} L t G R env) {E : Ixon.Env}
    (hE : RecordsFor R E) {lim : Option Nat} (hc : Carried lim) (hl : LimWithin G t lim) :
    FoldClause.{u} L t E lim env := by
  obtain ⟨Reg, hR⟩ := h
  exact ⟨Reg, hR E hE lim hc hl⟩

/-- **A recursor's parent family is registered and read off the parent's record at every
store.** The parent is read at one store `Ec` for `R` (the store the run is good for): a stored
former under no basis name whose record is an inductive projection of a block the circuit
treats as native there. The registry, chosen before the store, holds a family of the parent's
name; at every store for `R` that family is read off the store, and off the parent's record
when `R` holds it. -/
theorem FoldClauseOver.parent_everywhere (h : FoldClauseOver.{u} L t G R env)
    (ht : t.check = .ok ()) {Ec : Ixon.Env} (hEc : RecordsFor R Ec) {lim₀ : Option Nat}
    (hc₀ : Carried lim₀) (hl₀ : LimWithin G t lim₀) {P : _root_.Address}
    {ip : Ixon.InductiveProj} (hpar : RecParent t Ec env P ip)
    (hheld : (recordOf R P).isSome = true) :
    ∃ (Reg : NativeFam .anon → Prop) (fam : NativeFam .anon), Reg fam ∧
      ∀ E, RecordsFor R E → ∀ lim, Carried lim → LimWithin G t lim →
        FoldClauseWith.{u} L t E lim env Reg ∧ FamReadAt L t E env P ip fam := by
  obtain ⟨Reg, hR⟩ := h
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam, hReg, hread⟩ :=
    (hR Ec hEc lim₀ hc₀ hl₀).registry.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨cmR, hcmR⟩ := Option.isSome_iff_exists.mp hheld
  have hcmc : Ix.Cert.recordAt Ec P = some cmR := hEc.2.1 P cmR hcmR
  have hcc : cmR = cm := Option.some.inj (hcmc.symm.trans hcm)
  have hname : fam.p.cvT.name = keyOf t P := hread.2.1
  refine ⟨Reg, fam, hReg, fun E hE lim hc hl => ?_⟩
  have hC := hR E hE lim hc hl
  have hcmE : Ix.Cert.recordAt E P = some cm := by
    rw [← hcc]
    exact hE.2.1 P cmR hcmR
  exact ⟨hC, (hC.fams fam hReg).readAt ht hname hcmE hcmi⟩

end Over

/-- **The clause on the 77 groups is the clause on every group.** -/
theorem xAllGroups_foldClauseOver (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) :
    XAllGroups (FoldClauseOver.{u} L) := by
  intro t R env h
  obtain ⟨Reg, hR⟩ := h
  exact ⟨Reg, fun E hE lim hc _ => hR E hE lim hc (limWithin_77 t lim)⟩

/-! ## The environment of the pins -/

/-- **The clause at the environment of the pins**, with the empty registry, at every store of
the basis records and every limit within the six basis groups. -/
theorem foldClause_basis_at (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) (hpre : PreludePinned t)
    (hall : AllBound t) {E : Ixon.Env} (hE : RecordsFor basisStore E) {lim : Option Nat}
    (hlim : LimWithin (· < 6) t lim) :
    FoldClauseWith.{u} L t E lim basisEnv (fun _ => False) :=
  FoldClauseWith.of_prefix (prefixInv_basis_at ht hpre hall hE hlim)
    (famRegistryWith_basis L t E) (hashKeyed_basis_at ht hpre) auxRootSynced_basisEnv
    lvClauses_basisEnv

/-- **The binding fold's form of the clause at the environment of the pins.** -/
theorem foldClauseOver_basis_at (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) (hpre : PreludePinned t)
    (hall : AllBound t) : FoldClauseOver.{u} L t (· < 6) basisStore basisEnv :=
  ⟨fun _ => False, fun _ hE _ _ hlim => foldClause_basis_at L ht hpre hall hE hlim⟩

/-! ## The two halves at the one clause -/

/-- **The typing half with the clause as the witness's extra part.** The witness's clause is
read at the walk's limit, which a typing claim's context carries; the steps keep the part of
the clause beside the prefix invariant. -/
theorem typing_skeleton_clause {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {calls : List (Call F)} {d : Digest} (hb : Bounded calls)
    (hclaim : ClaimExport Walk calls d) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstep : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} calls t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) :
    TypingSpecOn.{u} (BW.{u} (FoldClauseOver.{u} L)) calls d := by
  intro bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT hW
  by_cases hnc : CollisionWith V (bytes :: tb :: committedFootprint) R calls
  · exact Or.inl hnc
  · refine Or.inr ?_
    have ht : t.check = .ok () :=
      ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
    have hextra : ∀ x ∈ committedFootprint, x ∈ bytes :: tb :: committedFootprint :=
      fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
    rcases hclaim bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm with
      hcol | ⟨E₀, lim, Top, rank, hS, hWalk⟩
    · exact (hnc (Or.inl hcol)).elim
    · have hF : BFacts.{u} t (fun _ => True) R envT := hW.facts.1
      have hO : FoldClauseOver.{u} L t (fun _ => True) R envT := hW.facts.2
      have hc : Carried lim := carried_of_typingLim (hlim t seeds E₀ lim Top rank hWalk)
      have hX : ∀ E, RecordsFor R E → FoldExtra.{u} L t E envT := by
        intro E hE
        obtain ⟨Reg, h⟩ := hO.clauseAt hE hc (limWithin_all t lim)
        exact h.extra
      exact typing_skeleton_core_lim (X := fun E => FoldExtra.{u} L t E) hW.shape
        (fun E hE => hF.inv E hE lim hc (limWithin_all t lim)) hF.whole hX ht hb hextra hnc hS
        (hgraph t seeds E₀ lim Top rank hWalk)
        (fun E hE => hstep t seeds E₀ lim Top rank hWalk R envT E hE)

/-- **The composed statement with the one clause on both sides**: the binding fold's
hypotheses with the clause in its every-store form, and the typing walk, its limit and the
steps keeping the part of the clause beside the prefix invariant. -/
theorem composed_skeleton_clause {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (hclaimB : BindingClaimExport Run callsB dB)
    (hbase : BasisBase.{u} (FoldClauseOver.{u} L) Run)
    (hadm : AdmitsChain Run) (hrd : AdmitsReadsChain Run)
    (hstepB : GroupStepsR.{u} (FoldClauseOver.{u} L) Run)
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepA : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      ∀ R envT E, StepCtx.{u} callsA t R envT E₀ E →
        ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
          UnitStep.{u} (FoldExtra.{u} L t E) t envT E₀ E lim A c) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_r hclaimB hbase hadm hrd hstepB (xAllGroups_foldClauseOver L))
    (typing_skeleton_clause hb hclaimA hlim hgraph hstepA)

end IxVM.Refinement.Binding
