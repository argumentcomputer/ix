import IxVMRefinement.Binding.FamilyOf
import IxVMRefinement.Binding.Defs
import IxVMRefinement.FamilyAlias.Target
import IxVMRefinement.Binding.FamilyFlat
import IxVMRefinement.Binding.FamilyRecon
import IxVMRefinement.Assembly.AdviceListed
import IxVMRefinement.Obs.KernelModeled1

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
  position over the flattened family (`FamilyOfBlock`: complete, so the binding's family check must
  refuse an empty record under a group's validation, batch candidate B1″); and a new non-empty
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
    Core.S0.addr h xa x

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
      (hx : Core.S0.addr m157 x_x x)
      (hr : x_out = .ptr (.enum Obs.Names.«Lists::Node<&[Field; 32]>») m184.length)
      (hm : m256 = m184 ++ [.construct Obs.Names.«Lists::Node<&[Field; 32]>» "Cons" [x_x, x_rest]])
      (hh : h' = m256)
      (hcs : cs = (⟨"IxonDeserialize::get_address", [x_s], h⟩ : Call F) ::
        (cs57 ++ (⟨"IxonDeserialize::read_byte", [x_s2], m47⟩ : Call F) ::
        (cs92 ++ (⟨"KernelRoles::assert_in_order", [x_rc, x_x], m82⟩ : Call F) ::
        (cs_ord ++ (⟨"UInt8::to_field", [x_kind], m_ord⟩ : Call F) ::
        (cs165 ++ (⟨"KernelModeled::check_witness", [x_rc, x_block, x_x, .field 2, x_s3], m157⟩ : Call F) ::
        (cs127 ++ (⟨"KernelModeled::check_witnesses", [x_rc, x_block, v_ns, v200], m117⟩ : Call F) ::
          cs194))))))))) :
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
          cs194))))))))) :
      DirectContWitness x_rc x_block x x_s x_n x_out x_s' h h' cs

/-- **The advice list read directly from a `check_family.Path` unfolding** at the advice walk's
heap `m423`. -/
def OwnAdviceOfPath {rc xb xrb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (p : Obs.«KernelModeled::check_family».Path rc xb xrb h r h' cs)
    (advAs : List Bytes.Address) : Prop :=
  match p with
  | .run (x_advice := x_advice) (m423 := m423) .. =>
    Aiur.Library.List.RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m423 advAs x_advice

/-- **A container recursor witnessed directly by a `check_family.Path` unfolding** on its own
`check_witnesses` step (`ev344`). -/
def DirectContOfPath {rc xb xrb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (p : Obs.«KernelModeled::check_family».Path rc xb xrb h r h' cs) (x : _root_.Address) : Prop :=
  match p with
  | .run (m297 := m297) (x_n_w := x_nw) (x_s4 := x_s4) (m332 := m332) (cs342 := cs342)
      (x_outside := x_outside) (x_s5 := x_s5) .. =>
    DirectContWitness rc xb x x_s4 x_nw x_outside x_s5 m297 m332 cs342

/-- **A family check with its exact own advice list** read directly from its `check_family.Path`
unfolding (`OwnAdviceOfPath`). -/
def FamilyCallExact (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (B rb : _root_.Address) (lim : Option Nat)
    (cs : List (Call F)) (advAs : List Bytes.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ Core.S0.addr h xb B ∧ Core.S0.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    (∃ p : Obs.«KernelModeled::check_family».Path rc xb xrb h r h' cs,
      OwnAdviceOfPath p advAs) ∧
    (⟨"KernelModeled::check_family", [rc, xb, xrb], h⟩ : Call F) ∈ calls ∧
    (∀ cl ∈ cs, cl ∈ calls)

/-- **A container recursor witnessed directly by an observed family check**: the family check's
own `check_witnesses` walk (`DirectContOfPath` on the same `check_family.Path` unfolding as
`OwnAdviceOfPath`) took kind `2` on `x`. -/
def DirectContOwn (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (B rb : _root_.Address) (lim : Option Nat)
    (cs : List (Call F)) (advAs : List Bytes.Address) (x : _root_.Address) : Prop :=
  ∃ (h h' : Heap F) (rc xb xrb r : SourceValue F),
    Claim.RCLimRep t bAddr lim h rc ∧ Core.S0.addr h xb B ∧ Core.S0.addr h xrb rb ∧
    ObsFn Obs.W "KernelModeled::check_family" [rc, xb, xrb] h r h' cs ∧
    (∃ p : Obs.«KernelModeled::check_family».Path rc xb xrb h r h' cs,
      OwnAdviceOfPath p advAs ∧ DirectContOfPath p x) ∧
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
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, ⟨p, hadv⟩, hmem, hsub⟩ := hex
  refine ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, ?_, hmem, hsub⟩
  match p with
  | .run (m105 := m105) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := ev_ord) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309)
      (ev344 := ev344) (ev403 := ev403) (ev435 := ev435) (ev465 := ev465)
      (hc1474 := hc) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. => rw [he33]; exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have e_ws : Heap.Extends h _ :=
      e0.trans (ev126.heap_extends.trans (ev148.heap_extends.trans
        (ev194.heap_extends.trans (ev_ord.heap_extends.trans
          (ev231.heap_extends.trans (ev266.heap_extends.trans ev309.heap_extends))))))
    exact FamilyOwnAdvice.mk (path := p) (ev_ws := ev344) (ev_asb := ev403) (ev_adv := ev465)
      (ext_h_ws := e_ws) (ext_asb_adv := ev435.heap_extends) (advRep := hadv)
      (sub_ws := fun cl hcl => by rw [hc]; simp [hcl])
      (sub_asb := fun cl hcl => by rw [hc]; simp [hcl])
      (sub_adv := fun cl hcl => by rw [hc]; simp [hcl])

theorem FamilyCallExact.toCall {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address}
    (hex : FamilyCallExact calls bAddr t B rb lim cs advAs) :
    FamilyCallAtLim calls bAddr t B rb lim cs :=
  hex.toOwn.toCall

theorem DirectContOwn.toExact {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address} {x : _root_.Address}
    (hdc : DirectContOwn calls bAddr t B rb lim cs advAs x) :
    FamilyCallExact calls bAddr t B rb lim cs advAs := by
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, ⟨p, hadv, -⟩, hmem, hsub⟩ := hdc
  exact ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, ⟨p, hadv⟩, hmem, hsub⟩

theorem DirectContOwn.toOwn {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} {advAs : List Bytes.Address} {x : _root_.Address}
    (hdc : DirectContOwn calls bAddr t B rb lim cs advAs x) :
    FamilyCallOwn calls bAddr t B rb lim cs advAs :=
  hdc.toExact.toOwn

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
