import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Core.Rep
import IxVM.Obs.KernelModeled

/-! # The advice records a family check lists itself

`check_family` walks the advice addresses its payload lists with
`check_advice_records(rc, advice, Nil, wset)` under its own role context `rc`. That walk, and not
the advice walk of a family check nested in its calls (a container's recursor's check runs one, and
so may the check of a basis role's record and its closure), is the family check's own advice
list. Recorded calls do not mark which call made which, so the walk is read off the family check's
unfolding, `«KernelModeled::check_family».Path.run` (derived, `IxVM.Obs.KernelModeled`).

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
inductive FamilyOwnAdvice (x_rc x_block x_rec_block : SourceValue F) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) (calls : List (Call F)) (advAs : List Bytes.Address) :
    Prop where
  | mk
      (path : «KernelModeled::check_family».Path x_rc x_block x_rec_block h r h' calls)
      (m_ws : Heap F) (x_s4 x_nw x_outside x_s5 : SourceValue F) (m_ws' : Heap F)
      (cs_ws : List (Call F))
      (stream_s4 : ∃ bs : List UInt8, Bytes.RepByteStream byteListEnum m_ws bs x_s4)
      (ev_ws : ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_block, x_s4, x_nw]
        m_ws (.tuple [x_outside, x_s5]) m_ws' cs_ws)
      (wset : SourceValue F) (m_asb : Heap F) (cs_asb : List (Call F))
      (ev_asb : ObsFn Obs.W "KernelClaim::addr_set_build"
        [x_outside, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []]
        m_ws' wset m_asb cs_asb)
      (m_adv m_adv' : Heap F) (x_advice v_adv : SourceValue F) (cs_adv : List (Call F))
      (ev_adv : ObsFn Obs.W "KernelModeled::check_advice_records"
        [x_rc, x_advice, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [], wset]
        m_adv v_adv m_adv' cs_adv)
      (ext_h_ws : Heap.Extends h m_ws)
      (ext_asb_adv : Heap.Extends m_asb m_adv)
      (advRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) m_adv advAs x_advice)
      (sub_ws : ∀ cl ∈ cs_ws, cl ∈ calls)
      (sub_asb : ∀ cl ∈ cs_asb, cl ∈ calls)
      (sub_adv : ∀ cl ∈ cs_adv, cl ∈ calls)
      (v_pl : SourceValue F) (m_pl : Heap F) (bytes_pl : List UInt8)
      (pl_stream : Bytes.RepByteStream byteListEnum m_pl bytes_pl v_pl)
      (pl_first : calls.find? (fun cl => cl.name == "IxonDeserialize::get_address") =
        some ⟨"IxonDeserialize::get_address", [v_pl], m_pl⟩)
      (x_rb x_s1 : SourceValue F) (m_s1 : Heap F) (cs_rb : List (Call F))
      (ev_rb : ObsFn Obs.W "IxonDeserialize::get_address" [v_pl] m_pl (.tuple [x_rb, x_s1])
        m_s1 cs_rb)
      (m_na : Heap F) (x_na x_s2 : SourceValue F) (m_s2 : Heap F) (cs_na : List (Call F))
      (ext_s1_na : Heap.Extends m_s1 m_na)
      (ev_na : ObsFn Obs.W "KernelModeled::get_count" [x_s1] m_na (.tuple [x_na, x_s2])
        m_s2 cs_na)
      (x_s3 : SourceValue F) (m_s3 : Heap F) (cs_ga : List (Call F))
      (ev_ga : ObsFn Obs.W "KernelModeled::get_addrs" [x_s2, x_na] m_s2 (.tuple [x_advice, x_s3])
        m_s3 cs_ga)
      (ext_s3_adv : Heap.Extends m_s3 m_adv)

/-- The family check's unfolding with its own advice list is the family check's unfolding. -/
theorem FamilyOwnAdvice.path {x_rc x_block x_rec_block : SourceValue F} {h : Heap F}
    {r : SourceValue F} {h' : Heap F} {calls : List (Call F)} {advAs : List Bytes.Address}
    (w : FamilyOwnAdvice x_rc x_block x_rec_block h r h' calls advAs) :
    «KernelModeled::check_family».Path x_rc x_block x_rec_block h r h' calls := by
  match w with
  | .mk (path := p) .. => exact p

/-- **The family check of the block at `B` with the family record at `rb`, with its own advice
list**: `check_family [rc, B, rb]` observed with calls `cs` under a role context at `lim` with the
table at `bAddr`, the call and its calls in the run, and the list `advAs` its own advice walk
reads (`FamilyOwnAdvice`). -/
def FamilyCallOwn (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (B rb : _root_.Address) (lim : Option Nat) (cs : List (Call F))
    (advAs : List Bytes.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ BaseSeams.addr h xb B ∧ BaseSeams.addr h xrb rb ∧
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
  match w with
  | .mk (ev_ws := ev_ws) (wset := wset) (ev_asb := ev_asb) (m_adv := m_adv) (m_adv' := m_adv')
      (x_advice := x_advice) (v_adv := v_adv) (cs_adv := cs_adv) (ev_adv := ev_adv)
      (ext_h_ws := ext_h_ws) (ext_asb_adv := ext_asb_adv) (advRep := advRep)
      (sub_adv := sub_adv) .. =>
    exact ⟨m_adv, m_adv', x_advice, .construct Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [],
      wset, v_adv, cs_adv,
      ext_h_ws.trans (ev_ws.heap_extends.trans (ev_asb.heap_extends.trans ext_asb_adv)),
      advRep, ev_adv, sub_adv⟩

/-- **An advice record listed by a family check itself**: an address of the family check's own
advice list. -/
def AdviceListedIn (advAs : List Bytes.Address) (a : _root_.Address) : Prop :=
  ∃ b ∈ advAs, ixAddr b = a

end IxVM.Refinement.Typing
