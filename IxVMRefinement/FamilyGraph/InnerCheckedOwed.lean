import IxVMRefinement.FamilyGraph.InnerCheckedRow

/-! # What the row `innerChecked` is owed, at a walk and its family run

`InnerCheckedRow` asks `InnerChecked` of the records a family check of an accepted run checks,
at every walk and every `FamilyRun` of it. Two of its four fields are read off observations
already (`checked`, `blocks`; `InnerCheckedRow.lean`). The other two read the used references of
those records. This module states what the circuit owes of them at the walk and a family run,
and proves `InnerChecked` from it:

* `AdviceCheckOf`, `ContainerCheckOf`: a record an advice-record check (no projection record)
  or a container recursor's check checked, among the calls of the family check of a family
  record or of a twin, at the binding of the run's family checks and the walk's limit.
* `InnerGives`: what is owed of the used references of such a record that is inner and no twin,
  one field per source. The walk's own facts are not asked again: a record the walk reached has
  no inert reference (`TopWalkCore.refsNotInert`) and uses none of its own constant addresses
  except covered ones (`top_own_covered`: its own member's projection record would lie both
  above and below it in the walk). So the fields that read the record's own addresses, and the
  inert one, are asked only of records the walk did not reach.
* `innerChecked_of_gives`: `InnerChecked` at a walk and a family run from `InnerGives`. At the
  graph producer's choices `InnerGives` is proved up to two facts of the circuit
  (`ProducersInner.lean`).
* `InnerCheckedOwed`, `innerCheckedRow_of_owed`: the row over every family run from what it is
  owed there; `innerCheckedOwed_of_refs`: the earlier premise `InnerRefsChecked` gives it.

Over every family run, the own-address field (`ownRef`) is no assertion of the circuit (its
docstring); at the graph producer's choices it is proved. Lines are of `KernelModeled.lean`
unless named: "today" in the present source, "changed" in the text of the circuit's changes. -/

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open FamilyAlias (FamilyCallAtLim)

set_option linter.unusedVariables false

/-! ## The records a family check checks -/

/-- **An advice record a family check of the run checked**: an advice-record check of the record
at `a`, which is no projection record, among the calls of the family check of a family record or
of a twin, at the binding `bAddr` and the limit `lim`. -/
def AdviceCheckOf (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (lim : Option Nat) (fam twin : _root_.Address → Option _root_.Address)
    (a : _root_.Address) : Prop :=
  ∃ B rb cs, (fam B = some rb ∨ twin rb = some B) ∧ FamilyCallAtLim calls bAddr t B rb lim cs ∧
    AdviceCheckIn cs bAddr t lim a ∧ ∀ c, recordOf E₀ a = some c → ¬ IsProj c

/-- **A container's recursor a family check of the run checked**: a container recursor's check
of the record at `a` among the calls of the family check of a family record or of a twin, at the
binding `bAddr` and the limit `lim`. -/
def ContainerCheckOf (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (lim : Option Nat) (fam twin : _root_.Address → Option _root_.Address)
    (a : _root_.Address) : Prop :=
  ∃ B rb cs, (fam B = some rb ∨ twin rb = some B) ∧ FamilyCallAtLim calls bAddr t B rb lim cs ∧
    ContainerRecCheckIn cs bAddr t lim a

/-- **An inner record that is no twin was checked by a family check**, as an advice record or as
a container's recursor (`FamilyChecksAt.innerCall`; a twin reached through a container's
recursor projection is the twin step's). -/
theorem FamilyChecksAt.innerCheck {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hC : FamilyChecksAt calls bAddr t E₀ lim fam twin adv Inner) {a : _root_.Address}
    (hI : Inner a) (htw : twin a = none) :
    AdviceCheckOf calls bAddr t E₀ lim fam twin a ∨
      ContainerCheckOf calls bAddr t lim fam twin a := by
  obtain ⟨B, rb, cs, hor, hfc, hk⟩ := hC.innerCall a hI
  rcases hk with ⟨hadv, hnp⟩ | hk | ⟨B', cs', htw', -⟩
  · exact Or.inl ⟨B, rb, cs, hor, hfc, hadv, hnp⟩
  · exact Or.inr ⟨B, rb, cs, hor, hfc, hk⟩
  · rw [htw] at htw'
    cases htw'

/-! ## What the walk gives -/

/-- **A record the walk reached uses none of its own constant addresses except covered ones**:
the walk puts an uncovered used reference below the record, and a member's or constructor's
projection record above its block (`TopGraph.closed`, `TopGraph.owner`); a record that declares
one constant would lie below itself. -/
theorem top_own_covered {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {seeds : List _root_.Address}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} {envT : Ix.Kernel.Env .anon}
    {fam twin : _root_.Address → Option _root_.Address}
    {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}
    (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    {a x : _root_.Address} {c : Ixon.Constant} (hT : Top a) (hc : recordOf E₀ a = some c)
    (hu : UsedRef E₀ a x) (hx : ConstAddrOf a c x) : Covered t x := by
  rcases hG.closed a x hT hu with ⟨hTx, hlt⟩ | hcov
  · exfalso
    rcases walked_constAddr_cases hG hF (Or.inl hT) hc hx with ⟨hxa, -⟩ | ⟨-, P, hP, hpj, hown⟩
    · rw [hxa] at hlt
      exact Nat.lt_irrefl _ hlt
    · have hlt' := (hG.owner x P hTx hP hpj).2
      rw [hown] at hlt'
      omega
  · exact hcov

/-! ## What is owed -/

/-- **What is owed of the used references of an inner record a family check checked**, at the
binding `bAddr` of the run's family checks (premise; each field names its source). Every field
is asked of a record that is inner and no twin, checked as an advice record (no projection
record) or as a container's recursor (`AdviceCheckOf`, `ContainerCheckOf`); the fields the walk
gives at a record it reached (`top_own_covered`, `TopWalkCore.refsNotInert`) are asked only of
records it did not reach. -/
structure InnerGives (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env) (lim : Option Nat)
    (Top Inner : _root_.Address → Prop) (fam twin : _root_.Address → Option _root_.Address) :
    Prop where
  /-- The change that adds `assert_inner_refs_safe` (changed `:990-995`) to
  `check_advice_record` (changed `:921`) and `container_refs_check` (changed `:739`): its
  `assert_safe_used_refs` runs `assert_ref_allowed` (today `KernelRoles.lean:1259`) at every used
  reference. Today nothing in a family check asserts it of an inner record. -/
  notInert : ∀ a x, Inner a → ¬ Top a → twin a = none →
    (AdviceCheckOf calls bAddr t E₀ lim fam twin a ∨
      ContainerCheckOf calls bAddr t lim fam twin a) →
    UsedRef E₀ a x → ¬ InertAt t x
  /-- The same change: the uncovered branch of `assert_safe_used_refs` (today
  `KernelClaim.lean:600-615`: the referenced record and its owner are not unsafe) and
  `assert_used_not_block` with `assert_not_block_ref` (changed `:976-988`). Asked of every inner
  record: at a record the walk reached the walk gives it only from that record's own safety
  (`TopWalkCore.safeRefs`), which no check of a container's recursor asserts. -/
  needOk : ∀ a x, Inner a → twin a = none →
    (AdviceCheckOf calls bAddr t E₀ lim fam twin a ∨
      ContainerCheckOf calls bAddr t lim fam twin a) →
    UsedRef E₀ a x → Covered t x ∨ NeedOk E₀ x
  /-- A used reference that is one of the record's own constant addresses is stored by the
  witness's environment or covered. Over every family run no assertion of the circuit gives it:
  an advice block that uses one of its own member addresses passes `advice_refs_ok` when that
  address is a witnessed reference (a hash fixed point, not a collision), and a family check of a
  block the walk did not reach gives the walk nothing to compare. At the graph producer's
  choices it is proved from the walk and the changed `check_witness` and `walk_path`
  (`FamRunCtx.inner_ownRef`). -/
  ownRef : ∀ a c x, Inner a → ¬ Top a → twin a = none →
    (AdviceCheckOf calls bAddr t E₀ lim fam twin a ∨
      ContainerCheckOf calls bAddr t lim fam twin a) →
    recordOf E₀ a = some c → UsedRef E₀ a x → ConstAddrOf a c x →
    StoredAt t envT x ∨ Covered t x

/-- **What the row `innerChecked` is owed over every family run**: at every walk of an accepted
typing claim and every family run of it, `InnerGives` at the binding of the run's family
checks. -/
def InnerCheckedOwed : Prop :=
  ∀ (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address)
    (E₀ : Ixon.Env) (lim : Option Nat) (Top : _root_.Address → Prop)
    (rank : _root_.Address → Nat), Claim.TopWalk calls t seeds E₀ lim Top rank →
    ∀ (envT : Ix.Kernel.Env .anon) (fam twin : _root_.Address → Option _root_.Address)
      (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop),
      FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner →
      ∃ bAddr, FamilyChecksAt calls bAddr t E₀ lim fam twin adv Inner ∧
        InnerGives calls bAddr t envT E₀ lim Top Inner fam twin

/-! ## `InnerChecked` from what is owed -/

section Row

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
  {seeds : List _root_.Address} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
  {fam twin : _root_.Address → Option _root_.Address}
  {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}

/-- **An inner record that is no twin uses none of its own constant addresses except stored or
covered ones**: at a record the walk reached by the walk (`top_own_covered`), otherwise by
`ownRef`. -/
theorem InnerGives.own_kept (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hI : InnerGives calls bAddr t envT E₀ lim Top Inner fam twin) {a x : _root_.Address}
    {c : Ixon.Constant} (hIa : Inner a) (htw : twin a = none)
    (hk : AdviceCheckOf calls bAddr t E₀ lim fam twin a ∨
      ContainerCheckOf calls bAddr t lim fam twin a)
    (hc : recordOf E₀ a = some c) (hu : UsedRef E₀ a x) (hx : ConstAddrOf a c x) :
    StoredAt t envT x ∨ Covered t x := by
  by_cases hT : Top a
  · exact Or.inr (top_own_covered hG hF hT hc hu hx)
  · exact hI.ownRef a c x hIa hT htw hk hc hu hx

/-- **`InnerChecked` at a walk and a family run, from what is owed**: `checked` and `blocks`
from the observed checks (as `innerCheckedRow_of`); `notInert` from the walk at a record it
reached, else from `InnerGives.notInert`; `refsBelow` from `needOk`, the graph's `innerClosed`,
and `InnerGives.own_kept` for the record's own addresses. -/
theorem innerChecked_of_gives (hWalk : Claim.TopWalk calls t seeds E₀ lim Top rank)
    (hFR : FamilyRun calls t envT E₀ lim Top rank fam twin adv Inner)
    (hC : FamilyChecksAt calls bAddr t E₀ lim fam twin adv Inner)
    (hI : InnerGives calls bAddr t envT E₀ lim Top Inner fam twin) :
    InnerChecked calls bAddr t envT E₀ lim Top rank fam twin Inner := by
  obtain ⟨bW, hW, hG⟩ := hWalk
  have hS := hW.runStore
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a c hIa htw hc
    rcases hC.innerCheck hIa htw with
      ⟨B, rb, cs, -, hfc, ⟨h, h', rc, xa, seen, wset, r, cs₁, hrc, ⟨ab, hab, rfl⟩, ev, hsub₁⟩,
        hnp⟩ |
      ⟨B, rb, cs, -, hfc, h, h', rc, xa, ib, r, cs₁, hrc, haddr, ev, hsub₁⟩
    · have hcs : ∀ cl ∈ cs, cl ∈ calls := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsub⟩ := hfc
        exact hsub
      rcases kind_cases c with hsa | hpr | ⟨ms, hms⟩
      · exact Or.inr (Decl.adviceRecord_checked hS hrc hab ev (fun cl h => hcs cl (hsub₁ cl h))
          hc hsa)
      · exact absurd hpr (hnp c hc)
      · exact Or.inl ⟨ms, hms, (Decl.adviceBlock_checked hS hrc hab ev
          (fun cl h => hcs cl (hsub₁ cl h)) hc hms).1⟩
    · have hcs : ∀ cl ∈ cs, cl ∈ calls := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsub⟩ := hfc
        exact hsub
      exact Or.inr (Decl.containerRec_checked hS hrc haddr ev
        (fun cl h => hcs cl (hsub₁ cl h))).1
  · intro a x hIa htw hu
    by_cases hT : Top a
    · exact hW.refsNotInert a x hT hu
    · exact hI.notInert a x hIa hT htw (hC.innerCheck hIa htw) hu
  · intro a x hIa htw hu
    have hk := hC.innerCheck hIa htw
    rcases hI.needOk a x hIa htw hk hu with hcov | hok
    · exact Or.inr (Or.inl hcov)
    · rcases hFR.graph.innerClosed a x hIa hu hok with hst | hcov | ⟨c, hc, hx⟩ | hob
      · exact Or.inl hst
      · exact Or.inr (Or.inl hcov)
      · rcases hI.own_kept hG hFR.graph hIa htw hk hc hu hx with hst | hcov
        · exact Or.inl hst
        · exact Or.inr (Or.inl hcov)
      · exact Or.inr (Or.inr ⟨hok, hob⟩)
  · intro a c ms hIa hU htw hc hms hnd h0
    rcases hC.innerCheck hIa htw with
      ⟨B, rb, cs, -, hfc, hadv, hnp⟩ |
      ⟨B, rb, cs, -, hfc, h, h', rc, xa, ib, r, cs₁, hrc, haddr, ev, hsub₁⟩
    · have hcs : ∀ cl ∈ cs, cl ∈ calls := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsub⟩ := hfc
        exact hsub
      refine ⟨adviceBlockShape_holds calls cs t E₀ lim bAddr a c ms hS hcs hadv hc hms h0, ?_⟩
      obtain ⟨h, h', rc, xa, seen, wset, r, cs₁, hrc, ⟨ab, hab, rfl⟩, ev, hsub₁⟩ := hadv
      exact (Decl.adviceBlock_checked hS hrc hab ev (fun cl h => hcs cl (hsub₁ cl h)) hc hms).2
    · have hcs : ∀ cl ∈ cs, cl ∈ calls := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsub⟩ := hfc
        exact hsub
      exact absurd hms ((Decl.containerRec_checked hS hrc haddr ev
        (fun cl h => hcs cl (hsub₁ cl h))).2 c hc ms)

end Row

/-- **Row `innerChecked`, from what it is owed over every family run.** -/
theorem innerCheckedRow_of_owed (h : InnerCheckedOwed) : InnerCheckedRow := by
  intro calls t seeds E₀ lim Top rank hWalk R envT fam twin adv Inner hFR
  obtain ⟨bAddr, hC, hI⟩ := h calls t seeds E₀ lim Top rank hWalk envT fam twin adv Inner hFR
  exact ⟨bAddr, innerChecked_of_gives hWalk hFR hC hI⟩

/-- **The earlier premise gives what the row is owed over every family run**: `InnerRefsChecked`
asks its three facts of every record any family check at any binding checked, in any run with a
run store, and of the record's own addresses with no exception; `InnerCheckedOwed` asks less. -/
theorem innerCheckedOwed_of_refs (refs : InnerRefsChecked) : InnerCheckedOwed := by
  intro calls t seeds E₀ lim Top rank hWalk envT fam twin adv Inner hFR
  obtain ⟨bW, hW, hG⟩ := hWalk
  have hS := hW.runStore
  obtain ⟨bAddr, hC⟩ := hFR.checks
  have hr : ∀ a, (AdviceCheckOf calls bAddr t E₀ lim fam twin a ∨
      ContainerCheckOf calls bAddr t lim fam twin a) → ∀ x, UsedRef E₀ a x →
      ¬ InertAt t x ∧ (Covered t x ∨ NeedOk E₀ x) ∧
        ∀ c, recordOf E₀ a = some c → ¬ ConstAddrOf a c x := by
    intro a hk x hu
    rcases hk with ⟨B, rb, cs, -, hfc, hadv, hnp⟩ | ⟨B, rb, cs, -, hfc, hcont⟩
    · exact refs calls t E₀ lim bAddr B rb cs a hS hfc (Or.inl ⟨hadv, hnp⟩) x hu
    · exact refs calls t E₀ lim bAddr B rb cs a hS hfc (Or.inr hcont) x hu
  refine ⟨bAddr, hC, ⟨?_, ?_, ?_⟩⟩
  · intro a x hIa hT htw hk hu
    exact (hr a hk x hu).1
  · intro a x hIa htw hk hu
    exact (hr a hk x hu).2.1
  · intro a c x hIa hT htw hk hc hu hx
    exact absurd hx ((hr a hk x hu).2.2 c hc)

end IxVM.Refinement.Typing
