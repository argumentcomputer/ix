import IxVMRefinement.Assembly.PointRecord
import IxVMRefinement.Assembly.NativeBlockFormer

/-! # The type former of a block member on the modeled route, typed at the prefix

A block of any number of inductive members (a mutual or nested block) whose circuit dispatch is
the modeled branch (`ModeledAt`) installs each member's type former with the one-point model.
Its front door is the former's check at the prefix: `k_ensure_sort` in the prelude of
`check_const`'s `Induct` arm, read the same way on every route
(`Decl.native_prelude_calls`), and the modeled branch's syntactic telescope test
`former_is_tele(ty, n_params + n_indices) = 1`.

* `peer_zero_not_member`, `mentions_block_cells_of`: a cell of a term the circuit's scan
  `expr_mentions_block(ty, [B]) = 0` passed is no member's projection address `iprjAddr B k`, or
  heads a projection;
* `induct_native_or_tele`: a successful `Induct` check either observed `block_is_modeled`
  answering `0` (the native branch) or passed `former_is_tele` at `n_params + n_indices`;
* `resultSort_piArity_of_stripPis`: a telescope of `k` binders into a sort has that result sort
  and arity `k`;
* `pointFormer_of_member`: for member `i` of the block, the canonical former is checked at the
  prefix (`ConstantValCheckJ`), its type is typed there as a sort, and it is a telescope of
  `n_params + n_indices` binders into a sort.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency

private theorem toUInt64_toNat_pf {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

private theorem lt_uint64_of_size {ms : Array Ixon.MutConst} {k : Nat} {m : Ixon.MutConst}
    (hsize : ms.size < 2 ^ 39) (hm : ms[k]? = some m) : k < UInt64.size := by
  have hk := (Array.getElem?_eq_some_iff.mp hm).1
  have e : UInt64.size = 18446744073709551616 := rfl
  omega

/-- **The walked block has fewer than `2 ^ 39` members**: the walk's projection-address call
received the member list, and the run is bounded. -/
theorem mutsMemberAt_size_lt {calls : List (Call F)} (hbound : Bounded calls)
    {bAddr B : _root_.Address} {t : Ix.Kernel.RoleTable} {ms : Array Ixon.MutConst}
    {k lim : Nat} (hm : MutsMemberCheckedAtFullAt calls bAddr t B ms k lim) :
    ms.size < 2 ^ 39 := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hcl_pa, -⟩ := hm
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem
  simpa using hlen

/-! ## The scan excludes every member of the block -/

section Scan

variable {c : Core.Ctx} {B : _root_.Address} {cb : Ixon.Constant}

/-- **A constant the peer test answers `0` for is not member `k` of the block**, where the store
holds the block and member `k`'s projection record. -/
theorem peer_zero_not_member {ms : Array Ixon.MutConst} {k : Nat} {ind : Ixon.Inductive}
    (hdec : L1.EnvDecoded c.E)
    (hblock : recordOf c.E B = some cb) (hmuts : cb.info = .muts ms)
    (hk : k < UInt64.size) (hmem : ms[k]? = some (.indc ind))
    (hproj : recordOf c.E (Core.iprjAddr B k) = some (memberProjection B k (.indc ind)))
    {b₀ : Bytes.Address} (hb₀ : Core.ixAddr b₀ = B)
    {a : Bytes.Address} {ca bas : SourceValue F} {m m' : Heap F} {cs : List (Call F)}
    (ha : Bytes.RepAddressRef Core.addrTy m a ca)
    (hbas : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m [b₀] bas)
    (ev : ObsFn Core.W "KernelCheck::caddr_is_peer" [ca, bas] m (.field 0) m' cs)
    (hg : Core.Good c cs) : Core.ixAddr a ≠ Core.iprjAddr B k := by
  intro hx
  have hrecA : Ix.Cert.recordAt c.E (Core.ixAddr a) = some (memberProjection B k (.indc ind)) := by
    rw [hx]
    exact recordAt_of_recordOf hdec hproj
  have hdecA : ∀ lc, c.E.consts.get? (Core.ixAddr a) = some lc →
      Ixon.deConstantExact lc.rawBytes = .ok (memberProjection B k (.indc ind)) := by
    rw [hx]
    exact decoded_at_of_recordOf hproj
  have hk' : (⟨k.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = k := toUInt64_toNat_pf hk
  have hmemk : ms[(⟨k.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat]? = some (.indc ind) := by
    rw [hk']
    exact hmem
  match Obs.«KernelCheck::caddr_is_peer».obs ev with
  | .Induct (m2 := m2) (p9 := p9) (cs15 := cs15) (ev17 := ev_ci) (ld11 := ld) (ev94 := ev_in)
      (hc111 := hc) .. =>
    subst hc
    have hg1 : Core.Good c cs15 := hg.sub (fun x hx => by simp [hx])
    obtain ⟨nl', ty', u', blk', b', hld', hb', hbB', -, -⟩ :=
      L1.indRecord_of_deConstantExact (c := c) (p := ⟨k.toUInt64, B⟩) hdecA
        (decoded_at_of_recordOf hblock) ev_ci hg1 ha hrecA rfl
        (recordAt_of_recordOf hdec hblock) hmuts hmemk
    rw [hld'] at ld
    have same := Except.ok.inj ld
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at same
    obtain ⟨-, -, -, -, -, -, hblkEq, -⟩ := same
    rw [← hblkEq] at ev_in
    have hbas' := repList_heapMono₂ Core.addrListEnum (Bytes.repAddressRef_heapMono₂ Core.addrTy)
      ev_ci.heap_extends hbas
    obtain ⟨-, hres⟩ := Decl.addr_list_contains_singleton_spec hbas' hb' ev_in
    rcases hres with ⟨hr1, -⟩ | ⟨-, hne⟩
    · exact nomatch hr1
    · exact hne (hbB'.trans hb₀.symm)
  | .other (m2 := m2) (p9 := p9) (cs15 := cs15) (ev17 := ev_ci) (ld11 := ld)
      (hne112 := hne_ind) (hc118 := hc) .. =>
    subst hc
    have hg1 : Core.Good c cs15 := hg.sub (fun x hx => by simp [hx])
    obtain ⟨nl', ty', u', blk', b', hld', -, -, -, -⟩ :=
      L1.indRecord_of_deConstantExact (c := c) (p := ⟨k.toUInt64, B⟩) hdecA
        (decoded_at_of_recordOf hblock) ev_ci hg1 ha hrecA rfl
        (recordAt_of_recordOf hdec hblock) hmuts hmemk
    rw [ld] at hld'
    injection hld' with hv1
    exact hne_ind [_, _, _, _, _, _, _, _] rfl hv1

/-- **A cell of a term the scan answers `0` for is not `X`, or heads a projection**, wherever
the peer test answering `0` excludes `X`. The scan runs on the heap term (every `let`'s type,
value and body). -/
theorem mentions_block_cells_of {X : _root_.Address} {b₀ : Bytes.Address}
    (hpeer : ∀ {a : Bytes.Address} {ca bas : SourceValue F} {m m' : Heap F} {cs : List (Call F)},
      Bytes.RepAddressRef Core.addrTy m a ca →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m [b₀] bas →
      ObsFn Core.W "KernelCheck::caddr_is_peer" [ca, bas] m (.field 0) m' cs →
      Core.Good c cs → Core.ixAddr a ≠ X)
    {h : Heap F} :
    ∀ {pe : SourceValue F} {a : Bytes.Address}, Core.AddrIn h pe a →
    ∀ {m m' : Heap F} {bas : SourceValue F} {cs : List (Call F)},
      Heap.Extends h m → RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) m [b₀] bas →
      ObsFn Core.W "KernelCheck::expr_mentions_block" [pe, bas] m (.field 0) m' cs →
      Core.Good c cs → Core.ProjIn h pe a ∨ Core.ixAddr a ≠ X := by
  intro pe a hin
  induction hin with
  | const cell ra =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Const (cs66 := cs66) (ld12 := ld) (ev68 := ev_peer) (hc85 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      injection hargs with hap _
      subst hap
      exact Or.inr (hpeer (Bytes.repAddressRef_heapMono₂ Core.addrTy ext ra) hbas ev_peer
        (hg.sub (fun x hx => by simp [hc, hx])))
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) .. | .Let_other_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | projHead cell ra =>
    intro _ _ _ _ _ _ _ _
    exact Or.inl (.head cell ra)
  | projArg cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Proj (cs516 := cs1) (ld12 := ld) (ev518 := ev1) (hc535 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, -, rfl⟩ := hargs
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.projArg cell hp)
      · exact Or.inr hne
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) .. | .Let_other_other (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | appFn cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .App_other (cs115 := cs1) (ld12 := ld) (ev117 := ev1) (hne141 := hne1) (hc167 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.appFn cell hp)
      · exact Or.inr hne
    | .App_n1 (he138 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .Lam_n1 (ld12 := ld) .. | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | appArg cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .App_other (cs148 := cs2) (ld12 := ld) (ev117 := ev1) (ev150 := ev2) (hc167 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl⟩ := hargs
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.appArg cell hp)
      · exact Or.inr hne
    | .App_n1 (he138 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .Lam_n1 (ld12 := ld) .. | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | lamTy cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Lam_other (cs203 := cs1) (ld12 := ld) (ev205 := ev1) (hne229 := hne1) (hc255 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.lamTy cell hp)
      · exact Or.inr hne
    | .Lam_n1 (he226 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | lamBody cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Lam_other (cs236 := cs2) (ld12 := ld) (ev205 := ev1) (ev238 := ev2) (hc255 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.lamBody cell hp)
      · exact Or.inr hne
    | .Lam_n1 (he226 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) ..
    | .Forall_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | forallTy cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Forall_other (cs291 := cs1) (ld12 := ld) (ev293 := ev1) (hne317 := hne1)
        (hc343 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.forallTy cell hp)
      · exact Or.inr hne
    | .Forall_n1 (he314 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | forallBody cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Forall_other (cs324 := cs2) (ld12 := ld) (ev293 := ev1) (ev326 := ev2)
        (hc343 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.forallBody cell hp)
      · exact Or.inr hne
    | .Forall_n1 (he314 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Let_n1 (ld12 := ld) .. | .Let_other_n1 (ld12 := ld) ..
    | .Let_other_other (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | letTy cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Let_other_other (cs378 := cs1) (ld12 := ld) (ev380 := ev1) (hne404 := hne1)
        (hc472 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, -, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev1).resolve_right hne1] at ev1
      rcases ih ext hbas ev1 (hg.sub (fun x hx => by simp [hc, hx])) with hp | hne
      · exact Or.inl (.letTy cell hp)
      · exact Or.inr hne
    | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | letVal cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Let_other_other (cs420 := cs2) (ld12 := ld) (ev380 := ev1) (ev422 := ev2)
        (hne446 := hne2) (hc472 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      rw [(Decl.expr_mentions_block_ret_bit ev2).resolve_right hne2] at ev2
      have hbas2 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ev1.heap_extends hbas
      rcases ih (ext.trans ev1.heap_extends) hbas2 ev2 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.letVal cell hp)
      · exact Or.inr hne
    | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim
  | letBody cell sub ih =>
    intro m m' bas cs ext hbas ev hg
    have cellm := ext.getElem?_eq cell
    match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .Let_other_other (cs453 := cs3) (ld12 := ld) (ev380 := ev1) (ev422 := ev2)
        (ev455 := ev3) (hc472 := hc) .. =>
      obtain ⟨-, hargs⟩ := Core.load_cell cellm ld
      simp only [List.cons.injEq, and_true] at hargs
      obtain ⟨-, -, rfl⟩ := hargs
      have ext12 := ev1.heap_extends.trans ev2.heap_extends
      have hbas3 := repList_heapMono₂ Core.addrListEnum
        (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext12 hbas
      rcases ih (ext.trans ext12) hbas3 ev3 (hg.sub (fun x hx => by simp [hc, hx]))
        with hp | hne
      · exact Or.inl (.letBody cell hp)
      · exact Or.inr hne
    | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. => exact nomatch hr
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Lit (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App_n1 (ld12 := ld) .. | .App_other (ld12 := ld) .. | .Lam_n1 (ld12 := ld) ..
    | .Lam_other (ld12 := ld) .. | .Forall_n1 (ld12 := ld) .. | .Forall_other (ld12 := ld) ..
    | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cellm ld (by decide)).elim

end Scan

/-! ## The route of an `Induct` check -/

/-- **A successful `Induct` check took the native branch or passed the telescope test.** Either
`KernelModeled::block_is_modeled` was observed answering `0` on the record's block field, within
the check's calls (the native arm), or `KernelCheck::former_is_tele` was observed answering `1` on
the record's type at `n_params + n_indices` (both modeled arms), at a heap extending the check's
input heap. -/
theorem induct_native_or_tele {rc typePtr blockArg index safety addr result : SourceValue F}
    {params indices count levels : Nat} {h h' : Heap F} {calls : List (Call F)}
    (observed : ObsFn Core.W "KernelCheck::check_const"
      [rc, .construct Core.kciEnum "Induct"
        [.field (levels : F), typePtr, .field (params : F), .field (indices : F),
          .field (count : F), safety, blockArg, index], addr] h result h' calls) :
    (∃ (before after : Heap F) (cs : List (Call F)),
      ObsFn Core.W "KernelModeled::block_is_modeled" [blockArg] before (.field 0) after cs ∧
      Heap.Extends h before ∧ ∀ cl ∈ cs, cl ∈ calls) ∨
    ∃ (before after : Heap F) (cs : List (Call F)),
      ObsFn Core.W "KernelCheck::former_is_tele"
        [typePtr, .field ((params + indices : Nat) : F)] before (.field 1) after cs ∧
      Heap.Extends h before := by
  match Obs.«KernelCheck::check_const».obs observed with
  | .Axiom_n1 (hv37 := shape) ..
  | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) ..
  | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) ..
  | .Opaque (hv825 := shape) ..
  | .Quot (hv1076 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Ctor_n0_n0 (hne1984 := notInduct) ..
  | .Ctor_n0_other (hne1984 := notInduct) ..
  | .Ctor_other_n0 (hne1984 := notInduct) ..
  | .Ctor_other_other (hne1984 := notInduct) ..
  | .Rec_n0 (hne1984 := notInduct) ..
  | .Rec_other (hne1984 := notInduct) .. =>
    exact (notInduct [_, _, _, _, _, _, _, _] rfl rfl).elim
  | .Induct_n0 (m1470 := before) (m1492 := after) (cs1503 := children)
      (hv1240 := fields) (ev1505 := modeRun) (hc1634 := allCalls) .. =>
    injection fields with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    have member : (⟨"KernelModeled::block_is_modeled", [blockArg], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inl ⟨before, after, children, modeRun, (observed.call_heap_bounds member).1,
      fun cl inside => by rw [allCalls]; simp [inside]⟩
  | .Induct_other_n0 (m1701 := before) (m1749 := after) (cs1757 := children)
      (hv1240 := fields) (op1782 := sum) (ev1759 := teleRun) (heq1791 := teleOne)
      (hc1974 := allCalls) .. =>
    injection fields with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := fields
    subst teleOne
    obtain rfl := Decl.evalBinOp_add_nat params indices sum
    have member : (⟨"KernelCheck::former_is_tele",
        [typePtr, .field ((params + indices : Nat) : F)], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inr ⟨before, after, children, teleRun, (observed.call_heap_bounds member).1⟩
  | .Induct_other_other (m1701 := before) (m1749 := after) (cs1757 := children)
      (hv1240 := fields) (op1782 := sum) (ev1759 := teleRun) (heq1791 := teleOne)
      (hc1983 := allCalls) .. =>
    injection fields with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    subst teleOne
    obtain rfl := Decl.evalBinOp_add_nat params indices sum
    have member : (⟨"KernelCheck::former_is_tele",
        [typePtr, .field ((params + indices : Nat) : F)], before⟩ : Call F) ∈ calls := by
      rw [allCalls]; simp
    exact .inr ⟨before, after, children, teleRun, (observed.call_heap_bounds member).1⟩

/-! ## Telescopes -/

/-- **A telescope of `k` binders into a sort** has that sort as its result sort and arity `k`. -/
theorem resultSort_piArity_of_stripPis :
    ∀ (k : Nat) (e : Ix.Kernel.Expr .anon) {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)}
      {s : Ix.Kernel.Level},
      e.stripPis k = some (bs, .sort s) → e.resultSort = some s ∧ e.piArity = k
  | 0, e, bs, s, h => by
    simp only [Ix.Kernel.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | k + 1, .forallE ty b m, bs, s, h => by
    simp only [Ix.Kernel.Expr.stripPis] at h
    cases hb : b.stripPis k with
    | none => rw [hb] at h; cases h
    | some p =>
      rw [hb] at h
      obtain ⟨bs', e'⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := resultSort_piArity_of_stripPis k b hb
      refine ⟨?_, ?_⟩
      · simp only [Ix.Kernel.Expr.resultSort, ih1]
      · simp only [Ix.Kernel.Expr.piArity, ih2]
  | k + 1, .bvar _, _, _, h | k + 1, .fvar _ _, _, _, h | k + 1, .sort _, _, _, h
  | k + 1, .const _ _, _, _, h | k + 1, .app _ _, _, _, h | k + 1, .lam _ _ _, _, _, h
  | k + 1, .letE _ _ _ _, _, _, h | k + 1, .lit _, _, _, h | k + 1, .proj _ _ _, _, _, h => by
    simp [Ix.Kernel.Expr.stripPis] at h

/-! ## The former of member `i`, checked at the prefix -/

/-- **The type former of member `i` of a modeled block, checked at the prefix, a telescope.**
From the walked check of member `i` of the block `ms` at `B` (any number of inductive members)
under the walk's role context at the limit `n`, where the circuit's dispatch on the block is the
modeled branch (`hmod`): the canonical annotation `ty'` of the reading `ty₀` of the former's type
is checked against the prefix environment (`ConstantValCheckJ`, at the prefix's keying, where no
member's address resolves), it is typed there as a sort, and it is a telescope of
`n_params + n_indices` binders into a sort (`former_is_tele`).

The inputs about the store are the block's record, its members (all inductive, `hinds`) and
every member's projection record (`hproj`): the circuit's scan `expr_mentions_block(ty, [B]) = 0`
excludes a `Const` cell at any member's projection address only through that member's record.
The inputs about the prefix are the invariant, the references the block uses stored, every
member's key fresh (`hfresh`: a cell of the type at member `k`'s address heading a projection
would make that key stored) and the former's key free. -/
theorem pointFormer_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {i : Nat} {ind : Ixon.Inductive} {n : Nat}
    {env : Ix.Kernel.Env .anon}
    (hst : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i]? = some (.indc ind))
    (hproj : ∀ (k : Nat) (ind' : Ixon.Inductive), ms[k]? = some (.indc ind') →
      recordOf E (Core.iprjAddr B k) = some (memberProjection B k (.indc ind')))
    (hinds : ∀ (k : Nat) (m : Ixon.MutConst), ms[k]? = some m →
      ∃ ind' : Ixon.Inductive, m = .indc ind')
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B ms i n)
    (hmod : ModeledAt E B)
    {ty₀ : Ix.Kernel.Expr .anon} (hty : blockRead t E B cb ms ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hfv : ty₀.hasFvar = false)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : ∀ (k : Nat) (ind' : Ixon.Inductive), ms[k]? = some (.indc ind') →
      env.find? (Core.keyOf t (Core.iprjAddr B k)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B i))) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList i : Nat) : F) ind.typ ty₀ = some ty' ∧
      Annotates ty' ty₀ ∧
      Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env
        ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty₀⟩
        ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty'⟩ ∧
      (∃ sty u, Ix.Kernel.Rules.Infer env .full 0 ty' sty ∧
        Ix.Kernel.Rules.Red env 0 sty (.sort u)) ∧
      (∃ l, ty'.resultSort = some l) ∧ ty'.piArity = ind.params.toNat + ind.indices.toNat := by
  have hbound : Bounded calls := (hst.good env none).2
  have hsize : ms.size < 2 ^ 39 := mutsMemberAt_size_lt hbound hchk
  have hi64 : i < UInt64.size := lt_uint64_of_size hsize hmem
  have hchkA := mutsMemberAt_checkedAt hbound hchk hmem
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre,
    ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchkA
  obtain ⟨a, ha, hax⟩ := ha_pre
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hg_ld : Core.Good ⟨E, env, t, some n⟩ cs_load := hgood.sub hsub_ld
  have hg_chk : Core.Good ⟨E, env, t, some n⟩ cs_chk := hgood.sub hsub_chk
  have hi' : (⟨i.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = i := toUInt64_toNat_pf hi64
  -- the load of the member's projection record, traced
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrec : recordOf E (Core.ixAddr a) = some (memberProjection B i (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hproj i ind hmem
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B i (.indc ind) := by
    rw [hb, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B i (.indc ind)).info = .iPrj ⟨i.toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = ms := (Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts))
  rw [hmsEq] at hms planned hraw
  rw [hi'] at hms planned hraw
  have hiEq : ind' = ind := by
    rw [Array.getElem?_toList, hmem] at hms
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms)).symm
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst typePtr
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hg_ld.1 hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon_exact ht hlvls (LoadedReads.blockSelf_key t B ms)
      hagree rty built planned trace hty hty_lbb hty_def
  -- the prelude of the check
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  -- the references the block uses are stored in the prefix
  have hmem' : Ixon.MutConst.indc ind ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  have used : ∀ x, L1.RefUsed cb.refs.toList cb.sharing.toList ind.typ x →
      ∃ ci, env.find? (Core.keyOf t x) = some ci := by
    intro x hu
    obtain ⟨j, hj | ⟨s, hs, hjs⟩, hr⟩ := hu
    · refine hstored j ?_ x hr
      unfold usedRefIdxs
      rw [hmuts]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.indc ind, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hj⟩)
    · refine hstored j ?_ x hr
      unfold usedRefIdxs
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, hjs⟩)
  let κP := (Core.Ctx.stored ⟨E, env, t, some n⟩).κ
  have hextM : Heap.Extends m_chk prelude.mentionsBefore :=
    prelude.initialExtended.trans prelude.scope_to_mentions
  have hagreeP : ∀ a', Core.AddrIn m_chk tyPtr a' →
      κP (Core.ixAddr a') = Core.keyOf t (Core.ixAddr a') := by
    intro a' hin
    rcases rty.addrIn_used a' hin with hu | hr
    · obtain ⟨ci, hci⟩ := used _ hu
      exact Core.Ctx.stored_key_of_find (c := ⟨E, env, t, some n⟩) hci
    · exfalso
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨m, hm, hxm⟩ := LoadedReads.blockRecurAddrs_get hk
      obtain ⟨indk, rfl⟩ := hinds k m hm
      rw [LoadedReads.memberAddr_indc] at hxm
      have hxm' : Core.ixAddr a' = Core.iprjAddr B k := hxm
      have hk64 : k < UInt64.size := lt_uint64_of_size hsize hm
      have hscan := mentions_block_cells_of (c := ⟨E, env, t, some n⟩) (X := Core.iprjAddr B k)
        (b₀ := b)
        (fun ha' hbas' ev' hg' => peer_zero_not_member (c := ⟨E, env, t, some n⟩) hst.decoded
          hblock hmuts hk64 hm (hproj k indk hm) hb_eq ha' hbas' ev' hg')
        hin hextM (prelude.blocksRep hb_rep) prelude.mentionsRun
        (hg_chk.sub prelude.mentionsSubset)
      rcases hscan with hp | hne
      · obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
        rw [hxm', hfresh k indk hm] at hci
        cases hci
      · exact hne hxm'
  have hpermP : ∀ a', Core.ProjIn m_chk tyPtr a' →
      Core.ProjPermitted (Core.keyOf t) (Core.ixAddr a') →
        Core.ProjPermitted κP (Core.ixAddr a') := by
    intro a' hp _
    obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
    exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, some n⟩) hci
  have htmP : Decl.TmCExact κP m_chk (Core.posOf (List.range ind.lvls.toNat) ty') tyPtr :=
    TmCExact.rekey htmT hagreeP hpermP
  have hvP : Decl.ValRepExact κP m_chk (.field (ind.lvls.toNat : F)) tyPtr
      ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty'⟩ :=
    ⟨by simp, by simpa using hlvls, by simp, htmP⟩
  have hgS : Core.CoreGood (Core.Ctx.stored ⟨E, env, t, some n⟩) prelude.sortCalls :=
    Core.CoreGood.ofRaw (hg_chk.sub prelude.sortSubset) (fun _ _ => trivial)
  obtain ⟨checked, sty, u, ℓ, inferred, reduced, -, -⟩ :=
    Decl.constantValCheckJ_of_scoped (c := Core.Ctx.stored ⟨E, env, t, some n⟩)
      (cv := ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty₀⟩)
      (cv' := ⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty'⟩)
      ⟨rfl, rfl, hannT⟩ (hvP.mono prelude.initialExtended) hty_lbb hfv (hfresh i ind hmem)
      hfree.1 (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) hinv.store.store
      (Decl.PosSortLift.of_range rfl) prelude.scopeRun prelude.scope_to_sort
      (hrc_m.toRCRep.mono (prelude.initialExtended.trans prelude.scope_to_sort))
      (prelude.typesRep κP (fun _ => default)) hinv.scopedCoreFacts.1 hinv.loads hgS
      prelude.sortRun
  rw [Decl.posOf_range] at inferred
  -- the route: the native branch is excluded, the modeled branch passed the telescope test
  rcases induct_native_or_tele ev_chk with ⟨mb, ma, mcs, modeRun, hextN, hsubN⟩ |
      ⟨tb, ta, tcs, teleRun, hextT⟩
  · have hgN : Core.Good ⟨E, env, t, some n⟩ mcs := hg_chk.sub hsubN
    exact absurd (show NativeAt E B from ⟨blkPtr, mb, ma, mcs, b, modeRun, hgN.1, hgN.2,
      Bytes.repAddressRef_heapMono₂ Core.addrTy hextN hb_rep, hb_eq⟩) hmod
  · obtain ⟨-, bs, s, hstrip, hlen⟩ := Decl.former_is_tele_one_bounded_spec
      (ind.params.toNat + ind.indices.toNat) (by omega) ((htmT 0 (fun _ => default)).mono hextT)
      teleRun
    rw [Decl.posOf_range] at hstrip
    obtain ⟨hrs, har⟩ := resultSort_piArity_of_stripPis _ _ hstrip
    exact ⟨ty', hcT, hannT, checked, ⟨sty, u, inferred, reduced⟩, ⟨s, hrs⟩, har⟩

end IxVM.Refinement.Typing
