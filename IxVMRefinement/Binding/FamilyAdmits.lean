import IxVMRefinement.Binding.FamilyOf
import IxVMRefinement.Binding.Defs
import IxVMRefinement.FamilyAlias.Target
import IxVMRefinement.Binding.FamilyFlat
import IxVMRefinement.Binding.FamilyRecon
import IxVMRefinement.Binding.StoreLevelsDef
import IxVMRefinement.Assembly.AdviceListed
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Ingress.Stream

/-! # A group's admission with modeled blocks: the family checks and the store

The run's admission of group `g` (`Admits`) describes the records the group adds by reference:
the walk of the group's roots, used references and projection blocks. A block the circuit
routes as modeled is checked together with records that no reference reaches: the family record
the claim's payload names, the advice records, and the container recursors its witnesses name
(`KernelModeled::check_family`, under the group's validation context). This module states what
the binding fold's family form needs of a group beside `Admits`:

* `ContainerRecIn cs x`: a check of the container recursor at `x` among the calls `cs`;
* `GroupFamilyChecks calls bAddr t E₀ g R R' famOf adv cont`: what the run's family checks give at
  group `g`: every new block of inductive types in Lean's logic that the run routes as modeled,
  where a member's check at the group's limit ran the dispatch, has a selected family record
  `famOf B`,
  the one its family check accepted at the group's validation limit, with that check's advice
  `adv B` and container recursors `cont B`; the selected record is the block's family, position by
  position over the flattened family (`FamilyOfBlock`: complete, since the binding's family check
  refuses an empty record under a group's validation); and a new non-empty
  block of recursors is a selected family record or was checked as a second family record of a
  block (a twin);
* `FamilyAdmits ρ t g R R' famOf adv cont`: what the group's store holds and in what order: the
  family record of a new block is new, ranked after its block (the block's unit owns it); the
  advice records and container recursors are in the store, and those new in the group are ranked
  before the block (their own units come first); and a new unit is checked by the run's check
  of a unit at the group's limit, or is a selected family record (checked by its block's family
  check, which is no check of a unit). This is the only check clause of a group's admission:
  `Admits` has none, since a check of every new unit as a unit is false of a selected family
  record. -/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option linter.unusedVariables false

/-- **A container recursor's check of the record at `x`**: a call of
`KernelModeled::check_container_rec` at `x` among the calls `cs`. -/
def ContainerRecIn (cs : List (Call F)) (x : _root_.Address) : Prop :=
  ∃ (rc xa ib : SourceValue F) (h : Heap F),
    (⟨"KernelModeled::check_container_rec", [rc, xa, ib], h⟩ : Call F) ∈ cs ∧
    Core.BaseSeams.addr h xa x

/-- **A container recursor witnessed directly by a `KernelModeled::check_witnesses` walk**:
some step of this walk checked `x` under `KernelModeled::check_witness` with kind `2` (rather than
appearing only in a nested family check inside a witness's check). -/
inductive DirectContWitness (x_rc x_block : SourceValue F) (x : _root_.Address) :
    SourceValue F → SourceValue F → SourceValue F → SourceValue F →
    Heap F → Heap F → List (Call F) → Prop where
  | head {x_s x_n x_out x_s' : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {m47 m82 m_ord m157 m117 m184 m256 : Heap F}
      {x_x x_s2 x_kind x_s3 v_ord v_ns x_rest v200 : SourceValue F}
      {cs57 cs92 cs_ord cs165 cs127 cs194 : List (Call F)}
      (hne : x_n ≠ .field 0)
      (ev59 : ObsFn Obs.W "IxonDeserialize::get_address" [x_s] h (.tuple [x_x, x_s2]) m47 cs57)
      (ev94 : ObsFn Obs.W "IxonDeserialize::read_byte" [x_s2] m47 (.tuple [x_kind, x_s3]) m82 cs92)
      (ev_ord : ObsFn Obs.W "KernelRoles::assert_in_order" [x_rc, x_x] m82 v_ord m_ord cs_ord)
      (ev167 : ObsFn Obs.W "UInt8::to_field" [x_kind] m_ord (.field 2) m157 cs165)
      (ev129 : ObsFn Obs.W "KernelModeled::check_witness" [x_rc, x_block, x_x, .field 2, x_s3]
        m157 v_ns m117 cs127)
      (op235 : evalBinOp .sub x_n (.field 1) = .ok v200)
      (ev196 : ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_block, v_ns, v200]
        m117 (.tuple [x_rest, x_s']) m184 cs194)
      (hx : Core.BaseSeams.addr m157 x_x x)
      (hr : x_out = .ptr (.enum Obs.Names.«Lists::Node<&[Field; 32]>») m184.length)
      (hm : m256 = m184 ++ [.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [x_x, x_rest]])
      (hh : h' = m256)
      (hcs : cs = (⟨"IxonDeserialize::get_address", [x_s], h⟩ : Call F) ::
        (cs57 ++ (⟨"IxonDeserialize::read_byte", [x_s2], m47⟩ : Call F) ::
        (cs92 ++ (⟨"KernelRoles::assert_in_order", [x_rc, x_x], m82⟩ : Call F) ::
        (cs_ord ++ (⟨"UInt8::to_field", [x_kind], m_ord⟩ : Call F) ::
        (cs165 ++ (⟨"KernelModeled::check_witness", [x_rc, x_block, x_x, .field 2, x_s3], m157⟩ : Call F) ::
        (cs127 ++ (⟨"KernelModeled::check_witnesses", [x_rc, x_block, v_ns, v200], m117⟩ : Call F) ::
          cs194)))))) :
      DirectContWitness x_rc x_block x x_s x_n x_out x_s' h h' cs
  | tail {x_s x_n x_out x_s' : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {m47 m82 m_ord m157 m117 m184 m256 : Heap F}
      {x_x x_s2 x_kind x_s3 v_ord v_kf v_ns x_rest v200 : SourceValue F}
      {cs57 cs92 cs_ord cs165 cs127 cs194 : List (Call F)}
      (hne : x_n ≠ .field 0)
      (ev59 : ObsFn Obs.W "IxonDeserialize::get_address" [x_s] h (.tuple [x_x, x_s2]) m47 cs57)
      (ev94 : ObsFn Obs.W "IxonDeserialize::read_byte" [x_s2] m47 (.tuple [x_kind, x_s3]) m82 cs92)
      (ev_ord : ObsFn Obs.W "KernelRoles::assert_in_order" [x_rc, x_x] m82 v_ord m_ord cs_ord)
      (ev167 : ObsFn Obs.W "UInt8::to_field" [x_kind] m_ord v_kf m157 cs165)
      (ev129 : ObsFn Obs.W "KernelModeled::check_witness" [x_rc, x_block, x_x, v_kf, x_s3]
        m157 v_ns m117 cs127)
      (op235 : evalBinOp .sub x_n (.field 1) = .ok v200)
      (ev196 : ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_block, v_ns, v200]
        m117 (.tuple [x_rest, x_s']) m184 cs194)
      (htail : DirectContWitness x_rc x_block x v_ns v200 x_rest x_s' m117 m184 cs194)
      (hr : x_out = .ptr (.enum Obs.Names.«Lists::Node<&[Field; 32]>») m184.length)
      (hm : m256 = m184 ++ [.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [x_x, x_rest]])
      (hh : h' = m256)
      (hcs : cs = (⟨"IxonDeserialize::get_address", [x_s], h⟩ : Call F) ::
        (cs57 ++ (⟨"IxonDeserialize::read_byte", [x_s2], m47⟩ : Call F) ::
        (cs92 ++ (⟨"KernelRoles::assert_in_order", [x_rc, x_x], m82⟩ : Call F) ::
        (cs_ord ++ (⟨"UInt8::to_field", [x_kind], m_ord⟩ : Call F) ::
        (cs165 ++ (⟨"KernelModeled::check_witness", [x_rc, x_block, x_x, v_kf, x_s3], m157⟩ : Call F) ::
        (cs127 ++ (⟨"KernelModeled::check_witnesses", [x_rc, x_block, v_ns, v200], m117⟩ : Call F) ::
          cs194)))))) :
      DirectContWitness x_rc x_block x x_s x_n x_out x_s' h h' cs

/-- **Payload-stream anchor tying a family check's advice walk to the first
`IxonDeserialize::get_address` call in `calls`** (mirrors the anchor fields of `FamilyOwnAdvice`). -/
inductive AdviceChainAnchor (calls : List (Call F)) (m_adv : Heap F) (x_advice : SourceValue F) :
    Prop where
  | mk
      (v_pl : SourceValue F) (m_pl : Heap F) (bytes_pl : List UInt8)
      (pl_stream : Bytes.RepByteStream Core.byteListEnum m_pl bytes_pl v_pl)
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

/-- **The witness, advice, container, and family reference guards extracted from a single unfolding
of `KernelModeled::check_family`**: packs `path`, the `assert_in_order` on `rec_block`, the
`Ingress.Stream` feeding `check_witnesses`, `ev_ws`, `ev_asb`, `ev_crr`, `ev_adv` (with `advRep` for
`advAs`), `ev_fro` (`family_refs_ok` on the same witness set), call memberships in `cs`, and an
optional `DirectContWitness` for `optCont`. -/
inductive CheckFamilyGuards (x_rc x_block x_rec_block : SourceValue F) (h : Heap F)
    (r : SourceValue F) (h' : Heap F) (cs : List (Call F)) (advAs : List Bytes.Address)
    (optCont : Option _root_.Address) : Prop where
  | mk
      (path : Obs.«KernelModeled::check_family».Path x_rc x_block x_rec_block h r h' cs)
      (m_ord0 m_ord1 : Heap F) (v_ord : SourceValue F) (cs_ord : List (Call F))
      (ext_h_ord : Heap.Extends h m_ord0)
      (ev_ord : ObsFn Obs.W "KernelRoles::assert_in_order" [x_rc, x_rec_block]
        m_ord0 v_ord m_ord1 cs_ord)
      (m_ws m_ws' : Heap F) (nw : Nat) (bytes4 : List UInt8)
      (x_s4 x_outside x_s5 : SourceValue F) (cs_ws : List (Call F))
      (ext_h_ws : Heap.Extends h m_ws)
      (hs4 : Ingress.Stream m_ws bytes4 x_s4)
      (ev_ws : ObsFn Obs.W "KernelModeled::check_witnesses" [x_rc, x_block, x_s4, .field (nw : F)]
        m_ws (.tuple [x_outside, x_s5]) m_ws' cs_ws)
      (x_wset : SourceValue F) (m_asb : Heap F) (cs_asb : List (Call F))
      (ev_asb : ObsFn Obs.W "KernelClaim::addr_set_build"
        [x_outside, .construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" []]
        m_ws' x_wset m_asb cs_asb)
      (v_crr : SourceValue F) (m_crr : Heap F) (cs_crr : List (Call F))
      (ev_crr : ObsFn Obs.W "KernelModeled::container_recs_refs" [x_rc, x_outside, x_wset]
        m_asb v_crr m_crr cs_crr)
      (x_advice v_adv : SourceValue F) (m_adv' : Heap F) (cs_adv : List (Call F))
      (ev_adv : ObsFn Obs.W "KernelModeled::check_advice_records"
        [x_rc, x_advice, .construct Obs.Names.«RBTreeMap::RBTreeMap<Field>» "Nil" [], x_wset]
        m_crr v_adv m_adv' cs_adv)
      (advRep : Aiur.Library.List.RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy)
        m_crr advAs x_advice)
      (m_fro0 m_fro1 : Heap F) (v_fro : SourceValue F) (cs_fro : List (Call F))
      (ext_asb_fro : Heap.Extends m_asb m_fro0)
      (ev_fro : ObsFn Obs.W "KernelModeled::family_refs_ok" [x_rc, x_rec_block, x_block, x_wset]
        m_fro0 v_fro m_fro1 cs_fro)
      (sub_ws : ∀ cl ∈ cs_ws, cl ∈ cs)
      (len_ws : cs_ws.length < cs.length)
      (sub_asb : ∀ cl ∈ cs_asb, cl ∈ cs)
      (sub_crr : ∀ cl ∈ cs_crr, cl ∈ cs)
      (sub_adv : ∀ cl ∈ cs_adv, cl ∈ cs)
      (sub_fro : ∀ cl ∈ cs_fro, cl ∈ cs)
      (hcont : ∀ x, optCont = some x →
        DirectContWitness x_rc x_block x x_s4 (.field (nw : F)) x_outside x_s5 m_ws m_ws' cs_ws)
      (anchor : AdviceChainAnchor cs m_crr x_advice)

/-- **A family check with its exact own advice list and reference guards** (`CheckFamilyGuards`). -/
def FamilyCallExact (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (B rb : _root_.Address) (lim : Option Nat)
    (cs : List (Call F)) (advAs : List Bytes.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ Core.BaseSeams.addr h xb B ∧ Core.BaseSeams.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    CheckFamilyGuards rc xb xrb h r h' cs advAs none ∧
    (⟨"KernelModeled::check_family", [rc, xb, xrb], h⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs, cl ∈ calls)

/-- **A container recursor witnessed directly by an observed family check**: the family check's
own `check_witnesses` walk took kind `2` on `x` (`CheckFamilyGuards ... (some x)`). -/
def DirectContOwn (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (B rb : _root_.Address) (lim : Option Nat)
    (cs : List (Call F)) (advAs : List Bytes.Address) (x : _root_.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ Core.BaseSeams.addr h xb B ∧ Core.BaseSeams.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    CheckFamilyGuards rc xb xrb h r h' cs advAs (some x) ∧
    (⟨"KernelModeled::check_family", [rc, xb, xrb], h⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs, cl ∈ calls)

theorem FamilyCallOwn.toCall {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address}
    (hown : FamilyCallOwn calls bAddr t B rb lim cs advAs) :
    FamilyCallAtLim calls bAddr t B rb lim cs := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, -, hmem, hsub⟩ := hown
  exact ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, hmem, hsub⟩

theorem FamilyCallExact.toOwn {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address}
    (hex : FamilyCallExact calls bAddr t B rb lim cs advAs) :
    FamilyCallOwn calls bAddr t B rb lim cs advAs := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, g, hmem, hsub⟩ := hex
  obtain ⟨path, _, _, _, _, _, _, m_ws, m_ws', nw, bytes4, x_s4, x_outside, x_s5, cs_ws,
    ext_h_ws, hs4, ev_ws, x_wset, m_asb, cs_asb, ev_asb, _, m_crr, _, ev_crr,
    x_advice, v_adv, m_adv', cs_adv, ev_adv, advRep, _, _, _, _, _, _,
    sub_ws, _, sub_asb, _, sub_adv, _, _, anchor⟩ := g
  obtain ⟨v_pl, m_pl, bytes_pl, pl_stream, pl_first, x_rb, x_s1, m_s1, cs_rb, ev_rb,
    m_na, x_na, x_s2, m_s2, cs_na, ext_s1_na, ev_na, x_s3, m_s3, cs_ga, ev_ga, ext_s3_adv⟩ := anchor
  exact ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev,
    FamilyOwnAdvice.mk path m_ws x_s4 (.field (nw : F)) x_outside x_s5 m_ws' cs_ws ⟨bytes4, hs4⟩
      ev_ws x_wset m_asb cs_asb ev_asb m_crr m_adv' x_advice v_adv cs_adv ev_adv
      ext_h_ws ev_crr.heap_extends advRep sub_ws sub_asb sub_adv
      v_pl m_pl bytes_pl pl_stream pl_first x_rb x_s1 m_s1 cs_rb ev_rb
      m_na x_na x_s2 m_s2 cs_na ext_s1_na ev_na x_s3 m_s3 cs_ga ev_ga ext_s3_adv,
    hmem, hsub⟩

theorem FamilyCallExact.toCall {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address}
    (hex : FamilyCallExact calls bAddr t B rb lim cs advAs) :
    FamilyCallAtLim calls bAddr t B rb lim cs :=
  FamilyCallOwn.toCall (FamilyCallExact.toOwn hex)

theorem DirectContOwn.toExact {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address} {x : _root_.Address}
    (hdc : DirectContOwn calls bAddr t B rb lim cs advAs x) :
    FamilyCallExact calls bAddr t B rb lim cs advAs := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, g, hmem, hsub⟩ := hdc
  obtain ⟨path, m_ord0, m_ord1, v_ord, cs_ord, ext_h_ord, ev_ord, m_ws, m_ws', nw, bytes4,
    x_s4, x_outside, x_s5, cs_ws, ext_h_ws, hs4, ev_ws, x_wset, m_asb, cs_asb, ev_asb,
    v_crr, m_crr, cs_crr, ev_crr, x_advice, v_adv, m_adv', cs_adv, ev_adv, advRep,
    m_fro0, m_fro1, v_fro, cs_fro, ext_asb_fro, ev_fro, sub_ws, len_ws, sub_asb, sub_crr, sub_adv,
    sub_fro, _, anchor⟩ := g
  exact ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev,
    ⟨path, m_ord0, m_ord1, v_ord, cs_ord, ext_h_ord, ev_ord, m_ws, m_ws', nw, bytes4,
      x_s4, x_outside, x_s5, cs_ws, ext_h_ws, hs4, ev_ws, x_wset, m_asb, cs_asb, ev_asb,
      v_crr, m_crr, cs_crr, ev_crr, x_advice, v_adv, m_adv', cs_adv, ev_adv, advRep,
      m_fro0, m_fro1, v_fro, cs_fro, ext_asb_fro, ev_fro, sub_ws, len_ws, sub_asb, sub_crr, sub_adv,
      sub_fro, (fun _ hc => nomatch hc), anchor⟩, hmem, hsub⟩

theorem DirectContOwn.toOwn {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address} {x : _root_.Address}
    (hdc : DirectContOwn calls bAddr t B rb lim cs advAs x) :
    FamilyCallOwn calls bAddr t B rb lim cs advAs :=
  FamilyCallExact.toOwn (DirectContOwn.toExact hdc)

/-- **What a binding run's family checks give at group `g`** (module docstring). -/
structure GroupFamilyChecks (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) : Prop where
  /-- Every block of inductive types in Lean's logic, new in the group, that the run routes as
  modeled has a selected family record, where a member's check at the group's validation limit
  shows the dispatch ran on it. (`ModeledRouteAt` reads the run's observations of the dispatch,
  so it holds of a record the dispatch never saw: the field is asked of blocks of inductive
  types in Lean's logic, the records the modeled arm of `check_const` reaches, and only where
  the check of a member at the group's limit ran that arm's dispatch.) -/
  modeled : ∀ B cb (ms : Array Ixon.MutConst), New R R' B → recordOf E₀ B = some cb →
    InLogic cb → cb.info = .muts ms → (∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) →
    ModeledRouteAt calls B →
    (∃ k, k < ms.size ∧ Claim.MemberCheckedLimAt calls bAddr t B ms k (some (valLimit g))) →
    ∃ rb, famOf B = some rb
  /-- The selected record is the one the family check of the new block accepted, under the
  group's validation context; `adv B` and `cont B` hold the check's own advice records and
  directly witnessed container recursors. -/
  famCall : ∀ B rb, famOf B = some rb → New R R' B ∧ ModeledRouteAt calls B ∧
    ∃ cs advAs, FamilyCallOwn calls bAddr t B rb (some (valLimit g)) cs advAs ∧
      (∀ a, AdviceListedIn advAs a → adv B a) ∧
      (∀ x, DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs x → cont B x)
  /-- The selected record is the block's family, position by position over the flattened family,
  in the run's store. -/
  family : ∀ B rb, famOf B = some rb →
    ∃ cb ms crb rs flat, FamilyOfBlock E₀ B cb ms rb crb rs flat
  /-- The selected record's flattened family, entry by entry: derived from the block's
  constructors and read off the record. `check_family`'s `check_nested_aux` with the changed
  `aux_all_in` (the record's entries, `build_flat_block`, are the derived ones, `nested_walk`,
  in order) and `check_recs` (entry `k` at recursor `k`), at the offset `block_elim` computes
  (every term read off the store in the canonical reading, `FamilyFlat.loadedAt`: the binder
  data of the record's binder blocks at the expression's root, as `get_ci` loads it). -/
  familyFlat : ∀ B rb, famOf B = some rb → ∃ (cb crb : Ixon.Constant)
      (ms rs : Array Ixon.MutConst) (es : List FamilyFlat.FlatEntry) (off : Nat),
    FamilyOfBlock E₀ B cb ms rb crb rs (es.map FamilyFlat.FlatEntry.addr) ∧
    FamilyFlat.RecordFlat t E₀ rb crb rs es ∧ FamilyFlat.BlockDerivedFlat t E₀ B off es
  /-- The selected record's reconstruction form: the record is the block's family over the
  flattened family derived from the block, and each of its recursors is the block's reconstruction
  at its position, its type the reconstructed type (`build_rec_type`) and each rule following the
  reconstructed body (`populate_rules`), up to the semantic equality of levels. `check_family`'s
  `check_recs` under the group's validation: `canonical_rules_at_pos` refuses the full-consumption
  arm in a context that validates a group (`rc_validates_group`), so every member's declared type
  is structurally the reconstruction; `compare_rules` checks every rule (every term read off the
  store in the canonical reading, `FamilyFlat.loadedAt`: the binder data of the record's binder
  blocks at the expression's root, as `get_ci` loads it). -/
  familyForm : ∀ B rb, famOf B = some rb → FamilyRecon.RFormS t E₀ B rb
  /-- Every recursor of the selected family record has level count equal to the block's first
  inductive's level count plus the block's elimination offset `off`. -/
  familyRecLvls : ∀ B rb cb crb (ms rs : Array Ixon.MutConst),
    famOf B = some rb → recordOf E₀ B = some cb → recordOf E₀ rb = some crb →
    cb.info = .muts ms → crb.info = .muts rs →
    ∃ off : Nat, FamilyFlat.BlockElim t E₀ B off ∧
      ∀ (ind₀ : Ixon.Inductive) (k : Nat) (rc : Ixon.Recursor),
        ms[0]? = some (.indc ind₀) → rs[k]? = some (.recr rc) →
        rc.lvls.toNat = ind₀.lvls.toNat + off
  /-- A new non-empty block of recursors is a selected family record, or was checked as a
  second family record of a block (a twin). -/
  claimed : ∀ (A : _root_.Address) (c : Ixon.Constant) (rs' : Array Ixon.MutConst),
    New R R' A → recordOf E₀ A = some c → c.info = .muts rs' → 0 < rs'.size →
    (∀ m ∈ rs'.toList, ∃ r, m = Ixon.MutConst.recr r) →
    (∃ B, famOf B = some A) ∨ ∃ B cs, FamilyCallAtLim calls bAddr t B A (some (valLimit g)) cs

/-- **What the group's store holds for its modeled blocks, and in what order** (module
docstring). -/
structure FamilyAdmits (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv cont : _root_.Address → _root_.Address → Prop) : Prop where
  /-- The family record of a block new in the group is new, after the block. -/
  famNew : ∀ B rb, famOf B = some rb → New R R' B → New R R' rb ∧ ρ.rank g B < ρ.rank g rb
  /-- The advice of a new block's family check is in the store; a new advice record comes
  before the block. -/
  advice : ∀ B rb a, famOf B = some rb → New R R' B → adv B a →
    (recordOf R' a).isSome = true ∧ (New R R' a → ρ.rank g a < ρ.rank g B)
  /-- The container recursors of a new block's family check are in the store; a new one comes
  before the block. -/
  container : ∀ B rb x, famOf B = some rb → New R R' B → cont B x →
    (recordOf R' x).isSome = true ∧ (New R R' x → ρ.rank g x < ρ.rank g B)
  /-- A new unit of no twin's shape (no non-empty block of recursors only: `IsTwinShape`, written
  out, whose definition comes later in the import order) was checked at the group's limit by a
  check of a unit, or is the selected family record of a block new in the group: installed with
  that block by its step, checked by the block's family check (`GroupFamilyChecks.famCall`),
  which is no check of a unit. A unit of a twin's shape is a family record (`claimed`). -/
  checked : ∀ a c, New R R' a → recordOf R' a = some c → UnitKind c →
    ¬ (∃ rs : Array Ixon.MutConst, c.info = .muts rs ∧ 0 < rs.size ∧
      ∀ m ∈ rs.toList, ∃ r, m = Ixon.MutConst.recr r) →
    ρ.checked a (valLimit g) ∨ ∃ B, famOf B = some a ∧ New R R' B
  /-- Blob-independent level-parameter well-scopedness and inductive parameter coherence on the
  group's store `R'`. -/
  levelsParams : StoreLevelsParams t R'

/-- **The family record of a new block is held by the group's store, with its member
projections**: from `famNew` and the store's closure under block members. -/
theorem FamilyAdmits.famRecord_held {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat}
    {R R' : Ixon.Env} {famOf : _root_.Address → Option _root_.Address}
    {adv cont : _root_.Address → _root_.Address → Prop}
    (h : FamilyAdmits ρ t g R R' famOf adv cont) (hc : UsedClosed R')
    {B rb : _root_.Address} (hrb : famOf B = some rb) (hB : New R R' B) :
    ∃ crb, recordOf R' rb = some crb ∧ ∀ rs, crb.info = .muts rs → ∀ i m, rs[i]? = some m →
      recordOf R' (memberAddr rb i m) = some (memberProjection rb i m) := by
  obtain ⟨⟨hsome, -⟩, -⟩ := h.famNew B rb hrb hB
  cases hr : recordOf R' rb with
  | none => simp [hr] at hsome
  | some crb => exact ⟨crb, rfl, fun rs hmuts i m hm => (hc.2 rb crb rs hr hmuts i m hm).1⟩

end IxVM.Refinement.Binding
