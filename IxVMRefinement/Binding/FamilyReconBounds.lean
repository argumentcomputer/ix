import IxVMRefinement.Binding.FamilyFlatBuild
import IxVMRefinement.Binding.FamilyReconRules
import IxVMRefinement.Binding.FamilyReconMinors
import IxVMRefinement.Binding.FamilyFlatWalk

/-! # Numeric side conditions of the family reconstruction

Four bounds the reconstruction and flat-family specs take as hypotheses, each traced to the
circuit's arithmetic.

* **The level offset of a block's types** (`FamilyFlatBuild.build_flat_block_spec`'s
  `off + ind.lvls < 2^32`). `build_param_lvls_range(off, nl, 0)` builds the parameters
  `off, …, off + nl - 1`, so the bound it needs is `off + nl ≤ 2^32`
  (`build_param_lvls_range_at_le`, `param_lvls_range_of_le`), which a loaded type (`nl < 2^32`)
  has at an elimination offset. `flat_originals_walk_of_le`, `build_flat_originals_of_le`,
  `build_flat_block_of_le`: the three specs with `off ≤ 1` in place of the bound;
  `blockElim_off_le`.
* **The cutoff of a lift** (`expr_lift_tmOExact`'s `cut < 2^32`, behind `list_lift_indices_spec`'s
  `i + Ds.length < 2^32`, an inductive's index count and a constructor's field count).
  `expr_lift` returns its argument at shift `0`, and at any other shift compares the cutoff with
  `UInt32::less_than_fields`, which range-checks it: an observed call has its cutoff below `2^32`
  (`expr_lift_cut_lt`). So the spec holds at every cutoff the field holds
  (`expr_lift_tmOExact_of_lt`, `list_lift_indices_of_le`), and the counts a load gives below
  `2^56` are enough.
* **A scan's binder depth** (`FamilyFlatWalk.ScanDepthIn`). `occ_scan` counts the binders it is
  under in a field element, one more at each scan of a binder's body, with `Let` cells re-entered
  on their instance. Two routes bound it. A count of the depths the scans of the derivation are
  called at (`ScanDepthsAtMost`, from a count of its distinct calls, `CallsAtMost`): scans at
  every depth up to `d` (`ScanChain`, threaded by `ScanChain.zero` and `ScanChain.succ`) are at
  `d + 1` depths (`ScanChain.lt`, `ScanChain.succ_val`), and `scanDepthIn_of_pred` gives
  `ScanDepthIn` where every scan under a binder has one a binder up. And the trace's memory: the
  terms a scan meets under successive binders are pairwise different, each read at a cell of the
  memory, so there are at most `2^39` of them (`distinct_terms_le`) where one cell reads terms of
  one key (`TermRomDet`, taken as a hypothesis).
* **A constructor's telescopes** (`CtorTeleSmall`, the fields half of `CtorFits`). Past the
  instantiated parameters the binders are the field domains the circuit lists, fewer than `2^39`
  (`fields_lt_of_call`); the count of the raw telescope's binders (`count_foralls_body`, through
  `Let` cells) is a count of pairwise different terms, as a scan's depth is.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace IxVM.Refinement.Binding.FamilyReconBounds

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat
open IxVM.Refinement.Binding.FamilyOf
open IxVM.Refinement.Binding.FamilyFlatRecord
open IxVM.Refinement.Binding.FamilyRecon
open IxVM.Refinement.Binding.FamilyFlatBuild
open IxVM.Refinement.Typing
open IxVM.Refinement.Core (W KExpr KLevel KKey kexprEnum kexprListEnum addrTy ixAddr)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM (F)
/-! ## The level offset of a block's types (`build_flat_block`) -/

section LevelRange

open IxVM.Refinement.Core
open Ix.Kernel (Level)

/-- `KernelCheck::build_param_lvls_range(start, count, idx)`: the level parameters
`start + idx, …, start + count - 1`. The largest index built is `start + count - 1`, so the
bound the parameters need is `start + count ≤ 2^32`. -/
theorem build_param_lvls_range_at_le (rem : Nat) :
    ∀ {start count idx : F} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ZMod.val count = ZMod.val idx + rem →
      ZMod.val start + ZMod.val count ≤ 4294967296 →
      ObsFn W "KernelCheck::build_param_lvls_range" [.field start, .field count, .field idx]
        h r h' cs →
      RepKLevelList h'
        ((List.range rem).map fun k => .param (ZMod.val start + ZMod.val idx + k)) r := by
  induction rem with
  | zero =>
    intro start count idx r h h' cs hrem _ ev
    rcases Obs.«KernelCheck::build_param_lvls_range».obs ev with ⟨_, rfl, rfl, _⟩ |
      ⟨v1, _, _, _, _, _, _, op17, hne, _, _, _, _, _, _, _⟩
    · obtain ⟨repN, _⟩ := RepKLevelList.allocNil h
      rw [IxVM.Refinement.Levels.klevelList_names] at repN
      simpa using repN
    · rw [SubstAux.sub_ok op17] at hne
      have hv : ZMod.val (count - idx) = 0 := by rw [SubstAux.val_sub (by omega)]; omega
      have hcz : count - idx = 0 := ZMod.val_injective _ (by simpa using hv)
      exact absurd (congrArg Value.field hcz) hne
  | succ rem ih =>
    intro start count idx r h h' cs hrem hlt ev
    rcases Obs.«KernelCheck::build_param_lvls_range».obs ev with ⟨op17, _, _, _⟩ |
      ⟨_, v46, m48, v60, m78, _, v91, op17, _, rfl, rfl, rfl, op74, op119, ev_rec, _⟩
    · have hsub := SubstAux.sub_ok op17
      injection hsub with h0
      have hv : ZMod.val (count - idx) = rem + 1 := by rw [SubstAux.val_sub (by omega)]; omega
      rw [← h0, ZMod.val_zero] at hv; omega
    · rw [SubstAux.add_ok op74] at ev_rec
      rw [SubstAux.add_ok op119] at ev_rec
      have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
      have hval1 : ZMod.val (1 : F) = 1 := rfl
      have hsi_val : ZMod.val (start + idx) = ZMod.val start + ZMod.val idx :=
        SubstAux.val_add (by omega)
      have hsi_cast : ((ZMod.val start + ZMod.val idx : Nat) : F) = start + idx := by
        rw [← hsi_val, ZMod.natCast_zmod_val]
      have hparam : RepKLevel (h ++ [.construct klevelEnum "Param" [.field (start + idx)]])
          (.param (ZMod.val start + ZMod.val idx)) (.ptr (.enum klevelEnum) h.length) :=
        .param (by omega) (by rw [hsi_cast]; simp)
      have hi1 : ZMod.val (idx + 1) = ZMod.val idx + 1 := SubstAux.val_add (by omega)
      have htail := ih (start := start) (count := count) (idx := idx + 1)

        (by omega) hlt ev_rec
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have htail_eq :
          ((List.range rem).map
            ((fun k => Level.param (ZMod.val start + ZMod.val idx + k)) ∘ (· + 1))) =
            (List.range rem).map (fun k => .param (ZMod.val start + ZMod.val (idx + 1) + k)) := by
        apply List.map_congr_left
        intro k _
        exact congrArg (fun n : Nat => Level.param n)
          (show (ZMod.val start + ZMod.val idx + (k + 1) : Nat) =
              ZMod.val start + ZMod.val (idx + 1) + k by
            rw [hi1]; omega)
      rw [Nat.add_zero, htail_eq]
      obtain ⟨repC, _⟩ := RepKLevelList.allocCons (hparam.mono ev_rec.heap_extends) htail
      rw [IxVM.Refinement.Levels.klevelList_names] at repC
      exact repC

end LevelRange

/-- **`KernelCheck::build_param_lvls_range(off, nl, 0)`**: the level parameters `off + j` for
`j < nl`, the levels `build_flat_originals` gives a type of the block. -/
theorem param_lvls_range_of_le {off nl : Nat} (hlt : off + nl ≤ 4294967296)
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::build_param_lvls_range"
      [.field (off : F), .field (nl : F), .field 0] h r h' cs) :
    RepKLevelList h' ((List.range nl).map fun j => Ix.Kernel.Level.param (off + j)) r := by
  have ho : ((off : F)).val = off := FamilyOfCall.val_cast_lt_u58 (by omega)
  have hn : ((nl : F)).val = nl := FamilyOfCall.val_cast_lt_u58 (by omega)
  have h1 := build_param_lvls_range_at_le nl (start := (off : F)) (count := (nl : F)) (idx := 0)
    (by rw [hn, ZMod.val_zero, Nat.zero_add]) (by rw [ho, hn]; exact hlt) ev
  rw [ho, ZMod.val_zero] at h1
  simpa using h1

section Offset

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}

/-- **`KernelCheck::flat_originals_walk`** over the members of a block of the store from position
`k` is `FamilyFlat.originals` of their addresses at the offset: each inductive type of the block
at the levels `param (off + j)`, with no parameters. The offset is an elimination offset
(`off ≤ 1`); a type's level count is below `2^32` by its load, so the largest parameter index
`off + nl - 1` is. -/
theorem flat_originals_walk_of_le (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP)
    (hsz : mP.size < 8589934592) {off : Nat} (hoff : off ≤ 1)
    {x_all x_blk : SourceValue F} :
    ∀ (cur : List Ixon.MutConst) (k : Nat) {x_cur r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      (∀ j m, cur[j]? = some m → mP[k + j]? = some m) →
      RepList L1.mutConstListEnum L1.RepMutConst h mP.toList x_all →
      RepList L1.mutConstListEnum L1.RepMutConst h cur x_cur →
      Bytes.RepAddressRef addrTy h bP x_blk →
      ObsFn W "KernelCheck::flat_originals_walk"
        [x_all, x_cur, x_blk, .field (off : F), .field (k : F)] h r h' cs →
      (∀ c ∈ cs, c ∈ calls) →
      Heap.Extends h h' ∧
      ∃ os, originals (FlatView.ofStore t E₀) off (indcAddrs (ixAddr bP) k cur) = some os ∧
        RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' os r := by
  intro cur
  induction cur with
  | nil =>
    intro k x_cur r h h' cs _ _ hcur _ ev _
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      rw [hr, hh]
      exact ⟨Heap.Extends.snoc _ _, [], rfl, Lib.rep_store_nil h⟩
    | .Cons_Indc (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hcur ld
      cases he
  | cons m rest ih =>
    intro k x_cur r h h' cs hsuf hall hcur hb ev hsub
    have hm0 : mP[k]? = some m := by simpa using hsuf 0 m rfl
    have hklt : k < mP.size := (Array.getElem?_eq_some_iff.mp hm0).1
    have hsuf' : ∀ j m', rest[j]? = some m' → mP[k + 1 + j]? = some m' := fun j m' hj => by
      have := hsuf (j + 1) m' (by simpa using hj)
      rwa [show k + (j + 1) = k + 1 + j by omega] at this
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hcur ld
    | .Cons_other (cs382 := cs382) (ld12 := ld) (hne375 := hne) (op431 := op) (ev384 := evR)
        (hc433 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      obtain rfl := binop_add_one_nat op
      have hrec := ih (k + 1) hsuf' hall hrest hb evR
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
      cases m with
      | indc ind =>
        obtain ⟨iv, hiv, -⟩ := hm
        exact absurd hiv (hne [iv] rfl)
      | defn d => simpa only [indcAddrs] using hrec
      | recr rc => simpa only [indcAddrs] using hrec
    | .Cons_Indc (v68 := v68) (cs79 := cs79) (v106 := v106) (m107 := m107) (cs120 := cs120)
        (v213 := v213) (m214 := m214) (v222 := v222) (m223 := m223) (v268 := v268)
        (m295 := m295) (m315 := m315) (cs323 := cs323)
        (ld12 := ld) (ev81 := e1) (ev122 := e2) (ld116 := ld116) (sg221 := sg) (ev235 := e3)
        (he263 := hr) (hm262 := hh) (hm303 := hm3) (op372 := op) (ev325 := evR)
        (hc374 := hc) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hcur ld
      injection he with h1 h2
      subst h1 h2
      cases m with
      | defn d => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
      | recr rc => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
      | indc ind =>
        have hkval : ((k : F)).val = k := FamilyOfCall.val_cast_lt_u58 (by omega)
        obtain ⟨ext1, -, -, mc, a, hget, ha_rep, ha_eq, hhash⟩ :=
          L1.projection_addr_hashed_spec (Route.membersRep_of_repMutConstList hall) hb e1
        rw [hkval, Array.getElem?_toList, hm0] at hget
        have hmc : mc = .indc ind := (Option.some.inj hget).symm
        subst hmc
        rw [hkval] at ha_eq hhash
        have hci : indInfoAt E₀ (memberAddr (ixAddr bP) k (.indc ind)) =
            some (some ⟨ind.lvls.toNat, ind.params.toNat, ind.ctors.size, ixAddr bP, k⟩) :=
          member_indInfo hH hcP hmP hm0 (Nat.lt_trans hklt (Nat.lt_trans hsz (by decide)))
            (IxVM.Refinement.Core.hashed_mono
              (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hhash)
        have hsub120 : ∀ c ∈ cs120, c ∈ calls := fun c hc' => hsub c (by rw [hc]; simp [hc'])
        obtain ⟨ext2, -, blkBytes, cb, ms, ind', blobs, v, hhB, haB, hexB, -, hcbi, hmem, -, hldv,
          hraw⟩ := L1.get_ci_iprj_spec (RomBound.bounded_mono hbd hsub120)
            (Bytes.repAddressRef_heapMono₂ addrTy ext1 hb) e2
        have hcb : cb = cP := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hcP)
          (IxVM.Refinement.Core.hashed_mono hsub120 hhB) haB hexB
        subst hcb
        have hms : ms = mP := Ixon.ConstantInfo.muts.inj (hcbi.symm.trans hmP)
        subst hms
        rw [hkval, Array.getElem?_toList, hm0] at hmem
        have hind : ind' = ind := (Ixon.MutConst.indc.inj (Option.some.inj hmem)).symm
        subst hind
        obtain ⟨hl, -, -, -, -, tyPtr, blkPtr, b, -, -, hv, -⟩ := hraw
        have hv106 : v106 = v := Except.ok.inj (ld116.symm.trans hldv)
        have hseg : v213 = .field (ind'.lvls.toNat : F) ∧ m214 = m107 := by
          match sg with
          | .Induct (hv153 := hvi) (he203 := hrs) (he204 := hhs) .. =>
            rw [hv106, hv] at hvi
            have hargs := (Value.construct.inj hvi).2.2
            simp only [List.cons.injEq, and_true] at hargs
            exact ⟨hrs.trans hargs.1.symm, hhs⟩
          | .other (hne206 := hnei) .. => exact (hnei _ rfl (hv106.trans hv)).elim
        obtain ⟨hv213, hm214⟩ := hseg
        subst hv213 hm214
        have hlv := param_lvls_range_of_le
          (show off + ind'.lvls.toNat ≤ 4294967296 by omega) e3
        subst hm3
        obtain rfl := binop_add_one_nat op
        have ext3 := e3.heap_extends
        have ext4 : Heap.Extends m223
            (m223 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) :=
          Heap.Extends.snoc _ _
        have extR := ext1.trans (ext2.trans (ext3.trans ext4))
        obtain ⟨ext5, os, hos, hrep⟩ := ih (k + 1) hsuf'
          (RepLinkedList.mono L1.repMutConst_heapMono₂ extR hall)
          (RepLinkedList.mono L1.repMutConst_heapMono₂ extR hrest)
          (Bytes.repAddressRef_heapMono₂ addrTy extR hb) evR
          (fun c hc' => hsub c (by rw [hc]; simp [hc']))
        rw [hr, hh]
        have hnil : RepList kexprListEnum (TmOExact (keyOf t))
            (m223 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KExprNode>» "Nil" []]) []
            (.ptr (.enum kexprListEnum) m223.length) := Lib.rep_store_nil m223
        have hentry : FlatEntryRepExact (keyOf t) m315
            (⟨memberAddr (ixAddr bP) k (.indc ind'), false, [],
              (List.range ind'.lvls.toNat).map fun j => .param (off + j)⟩ : FlatEntry)
            (.tuple [v68, .field 0,
              .ptr (.enum Obs.Names.«Lists::Node<&KernelTypes::KExprNode>») m223.length, v222]) :=
          ⟨v68, _, _, a, rfl,
            Bytes.repAddressRef_heapMono₂ addrTy (ext2.trans (ext3.trans (ext4.trans ext5))) ha_rep,
            by rw [ha_eq, LoadedReads.memberAddr_eq_projAddr],
            tmOExactList_mono ext5 hnil, hlv.mono (ext4.trans ext5)⟩
        refine ⟨extR.trans (ext5.trans (Heap.Extends.snoc _ _)), _ :: os, ?_,
          Lib.rep_store_cons flatEntryRepExact_heapMono₂ hentry hrep⟩
        have hci' : (FlatView.ofStore t E₀).ci (memberAddr (ixAddr bP) k (.indc ind')) =
            some (some ⟨ind'.lvls.toNat, ind'.params.toNat, ind'.ctors.size, ixAddr bP, k⟩) := hci
        simp only [indcAddrs, originals, hci', hos]

/-- **`KernelCheck::build_flat_originals`** on a block record of the store is
`FamilyFlat.originals` of the block's member addresses (`membersAt`) at an elimination offset. -/
theorem build_flat_originals_of_le (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    {bP : Bytes.Address} {cP : Ixon.Constant} {mP : Array Ixon.MutConst}
    (hcP : recordOf E₀ (ixAddr bP) = some cP) (hmP : cP.info = .muts mP) {off : Nat}
    (hoff : off ≤ 1)
    {x_blk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h bP x_blk)
    (ev : ObsFn W "KernelCheck::build_flat_originals" [x_blk, .field (off : F)] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ os, originals (FlatView.ofStore t E₀) off (indcAddrs (ixAddr bP) 0 mP.toList) = some os ∧
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' os r := by
  match Obs.«KernelCheck::build_flat_originals».obs ev with
  | .Muts (cs12 := csL) (cs92 := csW) (ev14 := evL) (ev94 := evW) (hc134 := hc) .. =>
    obtain ⟨msPtr, hxm, hlist, hlt⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
    subst hxe
    have extL := evL.heap_extends
    obtain ⟨ext, res⟩ := flat_originals_walk_of_le (t := t) hbd hS hH hcP hmP hlt hoff mP.toList 0
      (fun j m hj => by rw [Nat.zero_add, ← Array.getElem?_toList]; exact hj) hlist hlist
      (Bytes.repAddressRef_heapMono₂ addrTy extL hb) (by simpa using evW)
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    exact ⟨extL.trans ext, res⟩
  | .other_Induct (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc332 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)
  | .other_other (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc345 := hc) .. =>
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hb evL
      (fun c hc' => hsub c (by rw [hc]; simp [hc'])) hcP hmP
    exact absurd hxm (hne [msPtr] rfl)

/-- **`KernelCheck::build_flat_block(rb, B, off)`** on a family record of a bounded run's store is
its model `FamilyFlatRecord.recordFlatAt`, represented exactly. The list is the types of the
primary block `P` (`primaryAt`) at the offset (`FamilyFlat.originals` of the block's members)
followed by auxiliary entries only (`es = os ++ xs`), the walk's (`auxWalk`).

Taken: the fallback block `B` is a block record of the store (`hcB`, `hmB`); the recursors' types
mention only their own level parameters (`hlv`); and the offset is an elimination offset
(`hoff : off ≤ 1`), in place of `FamilyFlatBuild.build_flat_block_spec`'s bound
`off + ind.lvls < 2^32` on every type of the primary block. -/
theorem build_flat_block_of_le (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs) (hlv : RecLevelsDefined t E₀ rb crb rs)
    {bR bB : Bytes.Address} (hbR : ixAddr bR = rb)
    {cB : Ixon.Constant} {mB : Array Ixon.MutConst}
    (hcB : recordOf E₀ (ixAddr bB) = some cB) (hmB : cB.info = .muts mB) {off : Nat}
    (hoff : off ≤ 1)
    {x_rb x_b r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrb : Bytes.RepAddressRef addrTy h bR x_rb) (hb : Bytes.RepAddressRef addrTy h bB x_b)
    (ev : ObsFn W "KernelCheck::build_flat_block" [x_rb, x_b, .field (off : F)] h r h' cs)
    (hsub : ∀ c ∈ cs, c ∈ calls) :
    Heap.Extends h h' ∧
    ∃ (P : _root_.Address) (as : List _root_.Address) (os es xs : List FlatEntry),
      primaryAt t E₀ rb crb rs (ixAddr bB) = some P ∧
      membersAt E₀ P = some as ∧
      originals (FlatView.ofStore t E₀) off as = some os ∧
      auxWalk (contribAt t E₀ rb crb rs P) rs.size 0 os = some es ∧
      recordFlatAt t E₀ rb crb rs (ixAddr bB) off = some es ∧
      es = os ++ xs ∧ (∀ e ∈ xs, e.aux = true) ∧
      RepList flatListEnum (FlatEntryRepExact (keyOf t)) h' es r := by
  have hrec : recordOf E₀ (ixAddr bR) = some crb := by rw [hbR]; exact hR.record
  match Obs.«KernelCheck::build_flat_block».obs ev with
  | .n0 (cs73 := csM) (ev14 := evP) (ev44 := evO) (ev75 := evM) (hc91 := hc) .. =>
    have h1 := is_muts_block_of_muts hS
      (Bytes.repAddressRef_heapMono₂ addrTy (evP.heap_extends.trans evO.heap_extends) hrb)
      hrec hR.muts evM (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    exact absurd (Value.field.inj h1) (by decide)
  | .other (cs12 := csP) (cs42 := csO) (cs73 := csM) (cs99 := csD) (ev14 := evP) (ev44 := evO)
      (ev75 := evM) (ev101 := evD) (hc134 := hc) .. =>
    obtain ⟨ext1, P, cP, mP, hprim, rP, hcP, hmP⟩ :=
      primary_parent_block_of_spec ht hbd hS hH hR hlv hbR hcB hmB hrb hb evP
        (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    obtain ⟨ext2, os, hos, hrepO⟩ := build_flat_originals_of_le (t := t) hbd hS hH hcP hmP
      hoff rP evO
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    have ext3 := evM.heap_extends
    obtain ⟨ext4, es, hes, hrepE⟩ := detect_aux_from_recrs_ex_spec ht hbd hS hH hR hlv hbR
      (Bytes.repAddressRef_heapMono₂ addrTy (ext1.trans (ext2.trans ext3)) hrb)
      (Bytes.repAddressRef_heapMono₂ addrTy (ext2.trans ext3) rP) (flatList_mono ext3 hrepO) evD
      (fun c hc' => hsub c (by rw [hc]; simp [hc']))
    obtain ⟨xs, hxs, haux⟩ := auxWalk_aux _ (fun k e hk => contribAt_aux hk) _ _ _ _ hes
    refine ⟨ext1.trans (ext2.trans (ext3.trans ext4)), ixAddr P, _, os, es, xs, hprim,
      membersAt_of hcP hmP, hos, hes, ?_, hxs, haux, hrepE⟩
    simp only [recordFlatAt, hprim, membersAt_of hcP hmP, hos, hes]

/-- **An elimination offset is `0` or `1`.** -/
theorem blockElim_off_le {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address} {off : Nat}
    (h : BlockElim t E B off) : off ≤ 1 := by
  obtain ⟨t0, rest, nl, np, ni, ty, lvl, -, -, -, rfl⟩ := h
  split <;> omega

end Offset


/-! ## The cutoff of a lift (`expr_lift`, `list_lift_indices`) -/

section Lift

variable {κ : _root_.Address → KKey}

/-- **An observed `KernelSubst::expr_lift` at a non-zero shift has its cutoff below `2^32`**: the
circuit compares the cutoff against the term's loose-variable range with
`UInt32::less_than_fields`, which range-checks both operands. -/
theorem expr_lift_cut_lt {pe r : SourceValue F} {s c : F} {h h' : Heap F} {cs : List (Call F)}
    (hs : s ≠ 0)
    (ev : ObsFn Obs.W "KernelSubst::expr_lift" [pe, .field s, .field c] h r h' cs) :
    ZMod.val c < 4294967296 := by
  match Obs.«KernelSubst::expr_lift».obs ev with
  | .n0 (hv14 := hv) .. => exact absurd (Value.field.inj hv) hs
  | .other_n0 (ev59 := e) .. =>
    obtain ⟨a, b, ha, -, hla, -, -, -⟩ := IxVM.Refinement.Lib.less_than_fields_spec e
    injection ha with ha
    subst ha
    exact hla
  | .other_n1 (ev59 := e) .. =>
    obtain ⟨a, b, ha, -, hla, -, -, -⟩ := IxVM.Refinement.Lib.less_than_fields_spec e
    injection ha with ha
    subst ha
    exact hla

/-- **`KernelSubst::expr_lift(e, shift, cut)`** on `TmOExact` is `liftLooseBVars shift cut`, for
any cutoff the field holds (`cut` below the field's characteristic): at shift `0` the circuit
returns its argument, and at any other shift an observed call has its cutoff below `2^32`
(`expr_lift_cut_lt`), where `expr_lift_tmOExact` reads it. -/
theorem expr_lift_tmOExact_of_lt {E : KExpr} {pe r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {shift cut : Nat}
    (hshift : shift < 4611686018427387904) (hcut : cut < 18446744069414584321)
    (hbnd : IxVM.Consistency.Bounded cs) (hE : TmOExact κ h E pe)
    (ev : ObsFn Obs.W "KernelSubst::expr_lift" [pe, .field (shift : F), .field (cut : F)] h r h'
      cs) :
    TmOExact κ h' (E.liftLooseBVars shift cut) r := by
  by_cases hs : ((shift : Nat) : F) = 0
  · have hval : ZMod.val ((shift : Nat) : F) = shift :=
      ZMod.val_natCast_of_lt (Nat.lt_trans hshift (by decide))
    have h0 : shift = 0 := by rw [← hval, hs]; rfl
    subst h0
    rw [IxVM.Refinement.Decl.liftLooseBVars_zero]
    match Obs.«KernelSubst::expr_lift».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. => rw [hr, hh]; exact hE
    | .other_n0 (hne19 := hne) .. => exact absurd (by simp) hne
    | .other_n1 (hne19 := hne) .. => exact absurd (by simp) hne
  · have hc := expr_lift_cut_lt hs ev
    rw [ZMod.val_natCast_of_lt hcut] at hc
    exact expr_lift_tmOExact hshift hc hbnd hE ev

/-- **`KernelCheck::list_lift_indices(doms, shift, i)`** lifts the `j`-th term by `shift` at the
cutoff `i + j`; from `i = 0` it is `liftIndices`. The cutoffs are bounded by the field's
characteristic alone (`FamilyRecon.list_lift_indices_spec` takes them below `2^32`). -/
theorem list_lift_indices_of_le {shift : Nat} (hs : shift < 4611686018427387904) :
    ∀ (Ds : List KExpr) (i : Nat), i + Ds.length ≤ 18446744069414584321 →
      ∀ {xds r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      ObsFn Obs.W "KernelCheck::list_lift_indices" [xds, .field (shift : F), .field (i : F)] h r h'
        cs → IxVM.Consistency.Bounded cs → RepList kexprListEnum (TmOExact κ) h Ds xds →
      RepList kexprListEnum (TmOExact κ) h'
        ((Ds.zipIdx i).map fun p => p.1.liftLooseBVars shift p.2) r := by
  intro Ds
  induction Ds with
  | nil =>
    intro i hi xds r h h' cs ev hbnd hD
    rcases Obs.«KernelCheck::list_lift_indices».obs ev with
      ⟨ld12, rfl, rfl, -⟩ | ⟨x_d, x_rest, v54, v55, m57, cs65, m93, cs101, v106, ld12, -⟩
    · exact Lib.rep_store_nil h
    · obtain ⟨z, zs, hzs, -, -⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld12
      cases hzs
  | cons D Ds ih =>
    intro i hi xds r h h' cs ev hbnd hD
    rcases Obs.«KernelCheck::list_lift_indices».obs ev with
      ⟨ld12, -, -, -⟩ |
      ⟨x_d, x_rest, v54, v55, m57, cs65, m93, cs101, v106, ld12, rfl, rfl, ev67, op134, ev103,
        hc136⟩
    · cases IxVM.Refinement.Core.RepList.nil_of_load hD ld12
    · obtain ⟨z, zs, hzs, hz, hzs'⟩ := IxVM.Refinement.Core.RepList.cons_of_load hD ld12
      injection hzs with hz1 hz2
      subst hz1 hz2
      obtain rfl := binop_add_one_nat op134
      simp only [List.length_cons] at hi
      have b1 : IxVM.Consistency.Bounded cs65 :=
        RomBound.bounded_mono hbnd (fun c hc => by rw [hc136]; simp [hc])
      have b2 : IxVM.Consistency.Bounded cs101 :=
        RomBound.bounded_mono hbnd (fun c hc => by rw [hc136]; simp [hc])
      have hd := expr_lift_tmOExact_of_lt hs (by omega) b1 hz ev67
      have ext1 : Heap.Extends h m57 := ObsFn.heap_extends ev67
      have hrest := ih (i + 1) (by omega) ev103 b2 (tmOExactList_mono ext1 hzs')
      have ext2 : Heap.Extends m57 m93 := ObsFn.heap_extends ev103
      have := Lib.rep_store_cons tmOExact_heapMono₂ (TmOExact.mono ext2 hd) hrest
      simpa [List.zipIdx_cons] using this

end Lift



/-! ## Counters the circuit increments once per call (`occ_scan`'s binder depth) -/

section Calls

/-- **At most `n` distinct calls**: every call of `calls` is one of `n`. -/
def CallsAtMost (calls : List (Call F)) (n : Nat) : Prop :=
  ∃ L : List (Call F), L.length ≤ n ∧ ∀ c ∈ calls, c ∈ L

theorem CallsAtMost.mono {calls₁ calls₂ : List (Call F)} {n : Nat} (h : CallsAtMost calls₂ n)
    (sub : ∀ c ∈ calls₁, c ∈ calls₂) : CallsAtMost calls₁ n := by
  obtain ⟨L, hL, hmem⟩ := h
  exact ⟨L, hL, fun c hc => hmem c (sub c hc)⟩

theorem CallsAtMost.of_length (calls : List (Call F)) : CallsAtMost calls calls.length :=
  ⟨calls, le_rfl, fun _ h => h⟩

/-- **At most `n` binder depths among the scans of `root`**: the depth of every
`KernelModeled::occ_scan` among `root` is one of `n` field elements. Two scans at different
depths are different calls on different arguments (the depth is a field argument, whatever the
heap), so a count of the distinct calls of the trace, or of the rows that serve the scans, is
such a bound; `IxVM.Consistency.Bounded` counts the memory's addresses and gives none. -/
def ScanDepthsAtMost (root : List (Call F)) (n : Nat) : Prop :=
  ∃ L : List F, L.length ≤ n ∧
    ∀ {xb xe xacc : SourceValue F} {d : F} {h : Heap F},
      (⟨"KernelModeled::occ_scan", [xb, xe, .field d, xacc], h⟩ : Call F) ∈ root → d ∈ L

theorem ScanDepthsAtMost.mono {root₁ root₂ : List (Call F)} {n : Nat}
    (h : ScanDepthsAtMost root₂ n) (sub : ∀ c ∈ root₁, c ∈ root₂) : ScanDepthsAtMost root₁ n := by
  obtain ⟨L, hL, hmem⟩ := h
  exact ⟨L, hL, fun hc => hmem (sub _ hc)⟩

/-- The depth argument of a scan (`0` for a call of another shape). -/
private def depthOf (c : Call F) : F :=
  match c.args with
  | [_, _, .field d, _] => d
  | _ => 0

theorem CallsAtMost.scanDepths {root : List (Call F)} {n : Nat} (h : CallsAtMost root n) :
    ScanDepthsAtMost root n := by
  obtain ⟨L, hL, hmem⟩ := h
  refine ⟨L.map depthOf, by simpa using hL, ?_⟩
  intro xb xe xacc d h hc
  exact List.mem_map.mpr ⟨_, hmem _ hc, rfl⟩

/-- **A chain of pairwise different elements of a list of at most `n` is shorter than `n`**:
`key 0, …, key d`, all in `L`. -/
theorem chain_lt {α : Type} {L : List α} {n d : Nat} (hL : L.length ≤ n)
    (key : Nat → α) (hinj : ∀ i j, i ≤ d → j ≤ d → key i = key j → i = j)
    (hmem : ∀ j, j ≤ d → key j ∈ L) : d < n := by
  have hnd : ((List.range (d + 1)).map key).Nodup := by
    refine (List.nodup_map_iff_inj_on List.nodup_range).mpr ?_
    intro i hi j hj hij
    exact hinj i j (by have := List.mem_range.mp hi; omega) (by have := List.mem_range.mp hj; omega)
      hij
  have hss : (List.range (d + 1)).map key ⊆ L := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact hmem j (by have := List.mem_range.mp hj; omega)
  have := (hnd.subperm hss).length_le
  simp only [List.length_map, List.length_range] at this
  omega

/-- **A scan at every binder depth up to `d`**: `KernelModeled::occ_scan` is called, among
`root`, at each depth `0, …, d`. A scan entered at depth `0` has it (`ScanChain.zero`), and a
scan that has it and calls a scan one binder deeper gives it at `d + 1` (`ScanChain.succ`). -/
def ScanChain (root : List (Call F)) (d : Nat) : Prop :=
  ∀ j, j ≤ d → ∃ (xb xe xacc : SourceValue F) (h : Heap F),
    (⟨"KernelModeled::occ_scan", [xb, xe, .field ((j : Nat) : F), xacc], h⟩ : Call F) ∈ root

theorem ScanChain.zero {root : List (Call F)} {xb xe xacc : SourceValue F} {h : Heap F}
    (hc : (⟨"KernelModeled::occ_scan", [xb, xe, .field 0, xacc], h⟩ : Call F) ∈ root) :
    ScanChain root 0 := by
  intro j hj
  obtain rfl : j = 0 := by omega
  exact ⟨xb, xe, xacc, h, by simpa using hc⟩

theorem ScanChain.succ {root : List (Call F)} {d : Nat} (hd : ScanChain root d)
    {xb xe xacc : SourceValue F} {h : Heap F}
    (hc : (⟨"KernelModeled::occ_scan", [xb, xe, .field ((d + 1 : Nat) : F), xacc], h⟩ : Call F) ∈
      root) : ScanChain root (d + 1) := by
  intro j hj
  rcases Nat.lt_or_ge j (d + 1) with hlt | hge
  · exact hd j (by omega)
  · obtain rfl : j = d + 1 := by omega
    exact ⟨xb, xe, xacc, h, hc⟩

theorem ScanChain.mono {root₁ root₂ : List (Call F)} {d : Nat} (hd : ScanChain root₁ d)
    (sub : ∀ c ∈ root₁, c ∈ root₂) : ScanChain root₂ d := by
  intro j hj
  obtain ⟨xb, xe, xacc, h, hc⟩ := hd j hj
  exact ⟨xb, xe, xacc, h, sub _ hc⟩

/-- **A scan's binder depth is below the number of the scans' depths**: scans at every depth up
to `d` are at `d + 1` different depths while the depths are different field elements (`n` below
the field's characteristic). -/
theorem ScanChain.lt {root : List (Call F)} {n d : Nat} (hd : ScanChain root d)
    (hN : ScanDepthsAtMost root n) (hn : n < 18446744069414584321) : d < n := by
  by_contra hge
  have hnd : n ≤ d := by omega
  obtain ⟨L, hL, hmem⟩ := hN
  have := chain_lt hL (fun j => ((j : Nat) : F))
    (fun i j hi hj hij => by
      have hvi : ZMod.val ((i : Nat) : F) = i := ZMod.val_natCast_of_lt (Nat.lt_of_le_of_lt hi hn)
      have hvj : ZMod.val ((j : Nat) : F) = j := ZMod.val_natCast_of_lt (Nat.lt_of_le_of_lt hj hn)
      rw [← hvi, ← hvj, hij])
    (fun j hj => by
      obtain ⟨xb, xe, xacc, h, hc⟩ := hd j (by omega)
      exact hmem hc)
  omega

/-- **The depth a scan one binder deeper is called at**, as the circuit holds it: where scans
are called at every depth up to `d`, the next among them, and the scans of `root` are at no more
than `n ≤ 2^62` depths, `d + 1` is below `2^62` and is the value of the field element. -/
theorem ScanChain.succ_val {root : List (Call F)} {n d : Nat} (hd : ScanChain root d)
    {xb xe xacc : SourceValue F} {h : Heap F}
    (hc : (⟨"KernelModeled::occ_scan", [xb, xe, .field ((d + 1 : Nat) : F), xacc], h⟩ : Call F) ∈
      root)
    (hN : ScanDepthsAtMost root n) (hn : n ≤ 4611686018427387904) :
    ZMod.val ((d + 1 : Nat) : F) < 4611686018427387904 ∧ d + 1 < 4611686018427387904 := by
  have hlt : d + 1 < n :=
    (hd.succ hc).lt hN (Nat.lt_of_le_of_lt hn (by decide))
  have h1 : d + 1 < 4611686018427387904 := by omega
  refine ⟨?_, h1⟩
  rw [ZMod.val_natCast_of_lt (Nat.lt_trans h1 (by decide))]
  exact h1

/-- **`ScanDepthIn` from the scans' call structure and a count of their depths.** Where every
scan among `root` under a binder has a scan one binder up among `root` (a scan is entered at
depth `0`, and a scan calls scans at its own depth or one deeper), and the scans of `root` are at
no more than `n ≤ 2^62` depths, every scan among `root` is under fewer than `2^62` binders. -/
theorem scanDepthIn_of_pred {root : List (Call F)} {n : Nat}
    (hpred : ∀ {xb xe xacc : SourceValue F} {d : F} {h : Heap F},
      (⟨"KernelModeled::occ_scan", [xb, xe, .field d, xacc], h⟩ : Call F) ∈ root → d ≠ 0 →
      ∃ (xb' xe' xacc' : SourceValue F) (h' : Heap F),
        (⟨"KernelModeled::occ_scan", [xb', xe', .field (d - 1), xacc'], h'⟩ : Call F) ∈ root)
    (hN : ScanDepthsAtMost root n) (hn : n ≤ 4611686018427387904) : ScanDepthIn root := by
  intro xb xe xacc d h hc
  have hlt : ZMod.val d < 18446744069414584321 := ZMod.val_lt d
  have hdown : ∀ k, k ≤ ZMod.val d → ∃ (xb' xe' xacc' : SourceValue F) (h' : Heap F),
      (⟨"KernelModeled::occ_scan", [xb', xe', .field ((ZMod.val d - k : Nat) : F), xacc'], h'⟩ :
        Call F) ∈ root := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨xb, xe, xacc, h, by rw [Nat.sub_zero, ZMod.natCast_zmod_val]; exact hc⟩
    | succ k ih =>
      intro hk
      obtain ⟨xb', xe', xacc', h', hc'⟩ := ih (by omega)
      have hne : ((ZMod.val d - k : Nat) : F) ≠ 0 := by
        intro h0
        have hv : ZMod.val ((ZMod.val d - k : Nat) : F) = ZMod.val d - k :=
          ZMod.val_natCast_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hlt)
        rw [h0, ZMod.val_zero] at hv
        omega
      obtain ⟨xb'', xe'', xacc'', h'', hc''⟩ := hpred hc' hne
      refine ⟨xb'', xe'', xacc'', h'', ?_⟩
      rw [show ZMod.val d - (k + 1) = ZMod.val d - k - 1 by omega,
        Nat.cast_pred (by omega : 0 < ZMod.val d - k)]
      exact hc''
  have hchain : ScanChain root (ZMod.val d) := by
    intro j hj
    obtain ⟨xb', xe', xacc', h', hc'⟩ := hdown (ZMod.val d - j) (by omega)
    exact ⟨xb', xe', xacc', h', by
      rwa [show ZMod.val d - (ZMod.val d - j) = j by omega] at hc'⟩
  have := hchain.lt hN (Nat.lt_of_le_of_lt hn (by decide))
  omega

end Calls


/-! ## Terms at pairwise different addresses (binder depths and telescope lengths) -/

section Terms

variable {κ : _root_.Address → KKey}

/-- The cell an exact reading is read from. -/
theorem tmExact_cell {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat} {E : KExpr}
    {p : SourceValue F} (r : IxVM.Refinement.Decl.TmExact κ d Γ h k E p) :
    ∃ (addr : Nat) (c : String) (vs : List (SourceValue F)),
      p = .ptr (.enum kexprEnum) addr ∧ h[addr]? = some (.construct kexprEnum c vs) := by
  cases r with
  | bvarLocal cell _ _ => exact ⟨_, _, _, rfl, cell⟩
  | bvarFree cell _ _ _ => exact ⟨_, _, _, rfl, cell⟩
  | sort cell _ => exact ⟨_, _, _, rfl, cell⟩
  | const cell _ _ => exact ⟨_, _, _, rfl, cell⟩
  | app cell _ _ => exact ⟨_, _, _, rfl, cell⟩
  | lam cell _ _ _ => exact ⟨_, _, _, rfl, cell⟩
  | forallE cell _ _ _ => exact ⟨_, _, _, rfl, cell⟩
  | letE cell _ _ _ => exact ⟨_, _, _, rfl, cell⟩
  | litNat cell _ _ => exact ⟨_, _, _, rfl, cell⟩
  | litStr cell _ _ => exact ⟨_, _, _, rfl, cell⟩
  | proj cell _ _ => exact ⟨_, _, _, rfl, cell⟩

/-- **In a valid ROM, a value is the exact reading of terms of one key**: two pointers, each in
its heap, that one ROM value represents read terms `key` does not tell apart. At `key = id` the
value reads one term (for levels this is `Levels.rep_rom_det`); a key that forgets the leaves (a
term's shape, its size) asks less of the cells. -/
def TermRomDet {α : Type} (κ : _root_.Address → KKey) (key : KExpr → α) : Prop :=
  ∀ {rom : Aiur.ROM F}, rom.Valid → ∀ {h₁ h₂ : Heap F} {p₁ p₂ : SourceValue F}
    {w : Aiur.Value F} {E₁ E₂ : KExpr},
    Aiur.Represents rom h₁ p₁ w → Aiur.Represents rom h₂ p₂ w →
    TmOExact κ h₁ E₁ p₁ → TmOExact κ h₂ E₂ p₂ → key E₁ = key E₂

/-- **Terms of pairwise different keys among the arguments of a bounded derivation's calls are at
most `2^39`**: each is read at a cell of the trace's memory, and (`TermRomDet`) terms of
different keys are at different addresses. The terms a scan meets on its way under `d` binders are such terms (each a
proper subterm of the one before, a `Let` cell and its instance reading one term), and so are
the bodies a count of a telescope's binders passes. -/
theorem distinct_terms_le {root : List (Call F)} (hbd : IxVM.Consistency.Bounded root)
    {α : Type} {key : KExpr → α} (hdet : TermRomDet κ key) (Es : List KExpr)
    (hnd : (Es.map key).Nodup)
    (hmem : ∀ E ∈ Es, ∃ c ∈ root, ∃ p ∈ c.args, TmOExact κ c.heap E p) :
    Es.length ≤ 2 ^ 39 := by
  obtain ⟨rom, valid, bound, carried⟩ := hbd
  have hw : ∀ E ∈ Es, ∃ a : F, (∃ v, (a, v) ∈ rom.entries) ∧
      ∃ (h : Heap F) (p : SourceValue F),
        Aiur.Represents rom h p (.ptr (.enum kexprEnum) a) ∧ TmOExact κ h E p := by
    intro E hE
    obtain ⟨c, hc, p, hp, hrep⟩ := hmem E hE
    obtain ⟨w, hw⟩ := carried c hc p hp
    obtain ⟨k, hk⟩ := hrep
    obtain ⟨addr, cn, vs, rfl, cell⟩ := tmExact_cell hk
    obtain ⟨a, ws, mem, -, rfl⟩ := IxVM.Refinement.Levels.cell_represented cell hw
    exact ⟨a, ⟨_, mem⟩, c.heap, _, hw, ⟨k, hk⟩⟩
  classical
  let A : List F := Es.attach.map fun x => (hw x.1 x.2).choose
  have hA : A.Nodup := by
    refine (List.nodup_map_iff_inj_on (List.nodup_attach.mpr hnd.of_map)).mpr ?_
    intro x _ y _ hxy
    obtain ⟨-, h₁, p₁, r₁, t₁⟩ := (hw x.1 x.2).choose_spec
    obtain ⟨-, h₂, p₂, r₂, t₂⟩ := (hw y.1 y.2).choose_spec
    have hxy' : (hw x.1 x.2).choose = (hw y.1 y.2).choose := hxy
    rw [hxy'] at r₁
    exact Subtype.ext (List.inj_on_of_nodup_map hnd x.2 y.2 (hdet valid r₁ r₂ t₁ t₂))
  have hpres : ∀ a ∈ A, ∃ v, (a, v) ∈ rom.entries := by
    intro a ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
    exact (hw x.1 x.2).choose_spec.1
  have := IxVM.Refinement.RomBound.length_le_of_nodup bound hA hpres
  simpa [A] using this

/-- **A constructor's telescope past its instantiated parameters has fewer than `2^39` binders**,
where the circuit holds its field domains as a list it hands a call of a bounded derivation:
`fieldsClassify` returns one domain for each binder, and the list is in the trace's memory. -/
theorem fields_lt_of_call {root : List (Call F)} (hbd : IxVM.Consistency.Bounded root)
    {V : ReconView} {f : Nat} {es : List FlatEntry} {liftBy fidx : Nat} {E : KExpr}
    {ds ns : List KExpr} {ri rm : List Nat} {ret : KExpr}
    (hfc : fieldsClassify V f es liftBy fidx E = some (ds, ri, rm, ret, ns))
    {c : Call F} (hc : c ∈ root) {xds : SourceValue F} (hx : xds ∈ c.args)
    (hds : RepList kexprListEnum (TmOExact κ) c.heap ds xds) :
    (peelAll E).1.length < 2 ^ 39 := by
  rw [← (fieldsClassify_shape E fidx hfc).1]
  exact IxVM.Refinement.RomBound.bounded_length_lt hbd hc hx hds

end Terms

end IxVM.Refinement.Binding.FamilyReconBounds
