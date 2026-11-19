import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Core.Rep
import IxVMRefinement.Obs.KernelModeled3

/-! # The advice records a family check lists itself

`check_family` walks the advice addresses its payload lists with
`check_advice_records(rc, advice, Nil, wset)` under its own role context `rc`. That walk, and not
the advice walk of a family check nested in its calls (a container's recursor's check runs one, and
so may the check of a basis role's record and its closure), is the family check's own advice
list. Recorded calls do not mark which call made which, so the walk is read off the family check's
unfolding, `«KernelModeled::check_family».Path.run` (generated, `Obs/KernelModeled3.lean`).

* `FamilyOwnAdvice`: the family check's unfolding paired with its own witness walk, witness set
  build, and advice walk reading `advAs`;
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
together with its witness walk (`ev_ws`), witness-set build (`ev_asb`), and own advice walk
(`ev_adv`) reading the list `advAs` from `x_advice` at `m_adv`. -/
structure FamilyOwnAdvice (x_rc x_block x_rec_block : SourceValue F) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) (calls : List (Call F)) (advAs : List Bytes.Address) :
    Prop where
  path : «KernelModeled::check_family».Path x_rc x_block x_rec_block h r h' calls
  m_ws : Heap F
  x_s4 : SourceValue F
  x_nw : SourceValue F
  x_outside : SourceValue F
  x_s5 : SourceValue F
  m_ws' : Heap F
  cs_ws : List (Call F)
  ev_ws : ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_block, x_s4, x_nw]
    m_ws (.tuple [x_outside, x_s5]) m_ws' cs_ws
  wset : SourceValue F
  m_asb : Heap F
  cs_asb : List (Call F)
  ev_asb : ObsFn Obs.W "KernelClaim::addr_set_build"
    [x_outside, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []]
    m_ws' wset m_asb cs_asb
  m_adv : Heap F
  m_adv' : Heap F
  x_advice : SourceValue F
  v_adv : SourceValue F
  cs_adv : List (Call F)
  ev_adv : ObsFn Obs.W "KernelModeled::check_advice_records"
    [x_rc, x_advice, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [], wset]
    m_adv v_adv m_adv' cs_adv
  ext_h_ws : Heap.Extends h m_ws
  ext_asb_adv : Heap.Extends m_asb m_adv
  advRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) m_adv advAs x_advice
  sub_ws : ∀ cl ∈ cs_ws, cl ∈ calls
  sub_asb : ∀ cl ∈ cs_asb, cl ∈ calls
  sub_adv : ∀ cl ∈ cs_adv, cl ∈ calls

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
  obtain ⟨_, _, _, _, _, _, _, _, ev_ws, wset, _, _, ev_asb, m_adv, m_adv', x_advice, v_adv, cs_adv,
    ev_adv, ext_h_ws, ext_asb_adv, advRep, _, _, sub_adv⟩ := w
  exact ⟨m_adv, m_adv', x_advice, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [],
    wset, v_adv, cs_adv,
    ext_h_ws.trans (ev_ws.heap_extends.trans (ev_asb.heap_extends.trans ext_asb_adv)),
    advRep, ev_adv, sub_adv⟩

/-- **An advice record listed by a family check itself**: an address of the family check's own
advice list. -/
def AdviceListedIn (advAs : List Bytes.Address) (a : _root_.Address) : Prop :=
  ∃ b ∈ advAs, ixAddr b = a

end IxVM.Refinement.Typing
