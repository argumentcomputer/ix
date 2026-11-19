import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Core.Rep
import IxVMRefinement.Obs.KernelModeled3

/-! # The advice records a family check lists itself

`check_family` walks the advice addresses its payload lists with
`check_advice_records(rc, advice, Nil, wset)` under its own role context `rc`. That walk, and not
the advice walk of a family check nested in its calls (a container's recursor's check runs one, and
so may the check of a basis role's record and its closure), is the family check's own advice
list. Recorded calls do not mark which call made which, so the walk is read off the family check's
unfolding, `«KernelModeled::check_family».Path.run` (generated, `Obs/KernelModeled3.lean`), using
named binders for the advice list (`x_advice`) and the walk's heap (`m423`).

* `FamilyOwnAdvice`, `FamilyOwnAdvice.path`: the family check's unfolding with its own advice list;
* `FamilyCallOwn`: the observed family check of `B` with the record at `rb` at the limit `lim`, its
  calls `cs` among the run's, with its own advice list;
* `AdviceListedIn`: an address of that list. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Obs
open IxVM (F)

set_option linter.unusedVariables false

/-- **The family check's unfolding with its own advice list**: `«KernelModeled::check_family».Path`
whose own advice walk (`ev465`) reads the list `advAs` at its heap `m423` from its argument
`x_advice`. -/
def FamilyOwnAdvice (x_rc x_block x_rec_block : SourceValue F) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) (calls : List (Call F)) (advAs : List Bytes.Address) :
    Prop :=
  ∃ p : «KernelModeled::check_family».Path x_rc x_block x_rec_block h r h' calls,
    match p with
    | .run (m423 := m423) (x_advice := x_advice) .. =>
      RepList addrListEnum (Bytes.RepAddressRef addrTy) m423 advAs x_advice

/-- The family check's unfolding with its own advice list is the family check's unfolding. -/
theorem FamilyOwnAdvice.path {x_rc x_block x_rec_block : SourceValue F} {h : Heap F}
    {r : SourceValue F} {h' : Heap F} {calls : List (Call F)} {advAs : List Bytes.Address}
    (w : FamilyOwnAdvice x_rc x_block x_rec_block h r h' calls advAs) :
    «KernelModeled::check_family».Path x_rc x_block x_rec_block h r h' calls :=
  w.1

/-- **The family check of the block at `B` with the family record at `rb`, with its own advice
list**: `check_family [rc, B, rb]` observed with calls `cs` under a role context at `lim` with the
table at `bAddr`, the call and its calls in the run, and the list `advAs` its own advice walk
reads (`FamilyOwnAdvice`). -/
def FamilyCallOwn (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (B rb : _root_.Address) (lim : Option Nat) (cs : List (Call F))
    (advAs : List Bytes.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ S0.addr h xb B ∧ S0.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    FamilyOwnAdvice rc xb xrb h r h' cs advAs ∧
    (⟨"KernelModeled::check_family", [rc, xb, xrb], h⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs, cl ∈ calls)

/-- **The family check's own advice walk**: a `check_advice_records` call under the family check's
role context, at an extension of the family check's heap where the list is read, with its calls
among the family check's. -/
theorem FamilyOwnAdvice.walk {x_rc x_block x_rec_block : SourceValue F} {h : Heap F}
    {r : SourceValue F} {h' : Heap F} {calls : List (Call F)} {advAs : List Bytes.Address}
    (w : FamilyOwnAdvice x_rc x_block x_rec_block h r h' calls advAs) :
    ∃ (m m' : Heap F) (xadv seen wset v : SourceValue F) (cs₁ : List (Call F)),
      Heap.Extends h m ∧ RepList addrListEnum (Bytes.RepAddressRef addrTy) m advAs xadv ∧
      ObsFn Obs.W "KernelModeled::check_advice_records" [x_rc, xadv, seen, wset] m v m' cs₁ ∧
      ∀ cl ∈ cs₁, cl ∈ calls := by
  obtain ⟨p, hadv⟩ := w
  match p, hadv with
  | .run (m105 := m105) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := evo) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309) (ev344 := ev344)
      (ev403 := ev403) (ev435 := ev435) (ev465 := ev465) (hc1474 := hc) .., hadv =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. =>
        rw [he33]
        exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    refine ⟨_, _, _, _, _, _, _, e0.trans (ev126.heap_extends.trans (ev148.heap_extends.trans
      (ev194.heap_extends.trans (evo.heap_extends.trans (ev231.heap_extends.trans
      (ev266.heap_extends.trans (ev309.heap_extends.trans (ev344.heap_extends.trans
      (ev403.heap_extends.trans ev435.heap_extends))))))))), hadv, ev465, fun cl hcl => ?_⟩
    rw [hc]
    simp [hcl]

/-- **An advice record listed by a family check itself**: an address of the family check's own
advice list. -/
def AdviceListedIn (advAs : List Bytes.Address) (a : _root_.Address) : Prop :=
  ∃ b ∈ advAs, ixAddr b = a

end IxVM.Refinement.Typing
