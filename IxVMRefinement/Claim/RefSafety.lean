import IxVMRefinement.Claim.TopBase
import IxVMRefinement.Claim.RecordSafety
import IxVMRefinement.Claim.SafetyAt
import IxVMRefinement.StatementRel.LoadedReadsWalked
import IxVMRefinement.Assembly.Closure

/-! # Reference-guard observations over the run's store

All repeated loads are tied through the run store's hashed-byte uniqueness. The record
coverage used for an owner is the claim phase's existing HashedRecordsStored property.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Claim
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

section Store
variable {calls : List (Call F)} {E₀ : Ixon.Env}

/-- A canonical record hashed during the run is read from its run-store slot. -/
theorem recordOf_hashed (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {bytes : ByteArray} {c : Ixon.Constant}
    (hh : Hashed calls bytes) (hsz : bytes.size < 4294967296)
    (hd : Ixon.deConstant bytes = .ok c) (he : Ixon.deConstantExact bytes = .ok c) :
    recordOf E₀ (Address.blake3Pure bytes) = some c := by
  obtain ⟨lc, hget, _, hcache⟩ := hH bytes c hh hsz hd he
  apply hS.recordOf_of_recordAt
  unfold Ix.Cert.recordAt
  rw [hget]
  exact hcache

/-- Safety of the stored source forces an observed safety query to take its zero branch. -/
theorem record_unsafe_eq_zero_in_store (hS : LoadedReads.RunStore calls E₀)
    {a : _root_.Address} {c : Ixon.Constant} {ap r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hc : recordOf E₀ a = some c) (hl : InLogic c)
    (ha : BaseSeams.addr h ap a)
    (ev : ObsFn Obs.W "KernelClaim::record_unsafe" [ap] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) : r = .field 0 := by
  obtain ⟨_, bytes, c', _, hh, hb, _, he, hs⟩ := record_unsafe_safe_spec ha ev
  have hr : Ix.Cert.recordAt E₀ a = some c := (hS.recordOf_eq_recordAt a).symm.trans hc
  have hcc : c' = c := hS.record_eq hr (hashed_mono hsub hh) hb he
  subst c'
  exact hs hl

/-- A zero result certifies the stored record's safety. Prefix and exact decoding are
identified through the same hashed bytes, rather than an assumed decoder congruence. -/
theorem record_unsafe_zero_in_store (hS : LoadedReads.RunStore calls E₀)
    {a : _root_.Address} {c : Ixon.Constant} {ap : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (hc : recordOf E₀ a = some c) (ha : BaseSeams.addr h ap a)
    (ev : ObsFn Obs.W "KernelClaim::record_unsafe" [ap] h (.field 0) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) : InLogic c := by
  obtain ⟨_, bytes, c', _, hh, hb, hd, he, _⟩ := record_unsafe_safe_spec ha ev
  have hr : Ix.Cert.recordAt E₀ a = some c := (hS.recordOf_eq_recordAt a).symm.trans hc
  have hcc : c' = c := hS.record_eq hr (hashed_mono hsub hh) hb he
  subst c'
  obtain ⟨_, bytes₀, c₀, hh₀, hb₀, hd₀, hl₀⟩ := record_unsafe_zero_spec ha ev
  have hbytes : bytes₀ = bytes :=
    hS.hashed_inj (hashed_mono hsub hh₀) (hashed_mono hsub hh) (hb₀.trans hb.symm)
  rw [hbytes, hd] at hd₀
  have hc₀ : c = c₀ := Except.ok.inj hd₀
  simpa only [hc₀] using hl₀

end Store

private theorem addr_set_member_nil {ap r : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelClaim::addr_set_member"
      [ap, .construct addrMapEnum "Nil" []] h r h' calls) : r = .field 0 ∧ h' = h := by
  obtain ⟨_, ev6, _⟩ := Obs.«KernelClaim::addr_set_member».obs ev
  rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev6
  match Obs.«RBTreeMap::rbtree_map_lookup_or_default».obs ev6 with
  | .Nil (he18 := hr) (he19 := hh) .. => exact ⟨hr, hh⟩
  | .Node_n0 (hv_yxogouup := hv) .. => simp [addrMapEnum] at hv
  | .Node_n1 (hv_yxogouup := hv) .. => simp [addrMapEnum] at hv
  | .Node_other (hv_yxogouup := hv) .. => simp [addrMapEnum] at hv

private theorem refs_small_of_decoded {bytes : ByteArray} {c : Ixon.Constant}
    (hsz : bytes.size < 4294967296) (he : Ixon.deConstantExact bytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c he
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

private theorem safe_used_refs_seg_spec
    {calls cs : List (Call F)} {E₀ : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {bAddr a : _root_.Address} {lim : Option Nat} {i : Nat} {idxs : List Nat}
    {hit nextUsed ap rest rc refs used r : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀) (hrc : RCLimRep t bAddr lim h rc)
    (ha : BaseSeams.addr h ap a) (hiff : hit = .field 1 ↔ i ∈ idxs)
    (ev : Obs.«KernelClaim::assert_safe_used_refs».Seg_fokxpuhl hit nextUsed ap rest rc refs used
      (.field (i : F)) (.construct addrMapEnum "Nil" []) h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧
      (i ∈ idxs → RefAllowedIn calls t bAddr lim a ∧ (¬ CoveredAt t lim a → SourceSafe E₀ a)) := by
  match ev with
  | .n1_n1 (ev_utgbirrs := ev91) .. =>
    have hz := (addr_set_member_nil ev91).1
    exact (one_ne_zero (Value.field.inj hz)).elim
  | .other (hne_yeueqpng := hn) (he_eemargwo := hh) .. =>
    exact ⟨hh ▸ Heap.Extends.refl _, fun hm => (hn (hiff.mpr hm)).elim⟩
  | .n1_other_other (cs_yrgjjoqc := csAllow) (ev_utgbirrs := ev91) (ev_qtjiirzs := ev134)
      (ev_phyxterm := ev165) (hne_ifyzjima := hn) (he_felbweqg := hh) (hc_ykqaogma := hcs) .. =>
    obtain ⟨_, rfl⟩ := addr_set_member_nil ev91
    have ext := ev134.heap_extends
    obtain ⟨he, hc⟩ := walk_covered_lim_spec (hrc.mono ext) (BaseSeams.addr_mono ext ha) ev165
    refine ⟨?_, fun _ => ⟨⟨_, _, rc, ap, _, csAllow, hrc, ha, ev134,
      fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])⟩, fun hnc => ?_⟩⟩
    · rw [hh, he]; exact ext
    · rcases hc with hz | hcov
      · exact (hn hz).elim
      · exact (hnc hcov).elim
  | .n1_other_n0 (cs_yrgjjoqc := csAllow) (cs_qjpwomix := csLoad) (cs_kgdddfzu := csUnsafe)
      (cs_kaixaukp := csOwner) (ev_utgbirrs := ev91) (ev_qtjiirzs := ev134)
      (ev_phyxterm := ev165) (ev_sbnkpoyd := ev199) (ev_qxxjnwmz := ev221)
      (ev_unasbjkv := ev262) (heq_jfdvmnjk := hz) (ev_ytdmykjs := ev302)
      (heq_ppgaohtc := hzo) (he_xjkoaywn := hh) (hc_uzyocwyw := hcs) .. =>
    have extPre := ev91.heap_extends
    have extAll := extPre.trans (ev134.heap_extends.trans
      (ev165.heap_extends.trans (ev199.heap_extends.trans (ev221.heap_extends.trans
        (ev262.heap_extends.trans ev302.heap_extends)))))
    refine ⟨by rw [hh]; exact extAll, fun _ =>
      ⟨⟨_, _, rc, ap, _, csAllow, hrc.mono extPre, BaseSeams.addr_mono extPre ha, ev134,
        fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])⟩, fun _ c hc => ?_⟩⟩
    have extLoad := extPre.trans (ev134.heap_extends.trans ev165.heap_extends)
    have haLoad := BaseSeams.addr_mono extLoad ha
    obtain ⟨extLoaded, bytes, c', _, hhash, haddr, _, he, hrep, _⟩ :=
      load_verified_constant_de haLoad ev199
    have hloadSub : ∀ cl ∈ csLoad, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hrecAt : Ix.Cert.recordAt E₀ a = some c := (hS.recordOf_eq_recordAt a).symm.trans hc
    have hcc : c' = c := hS.record_eq hrecAt (hashed_mono hloadSub hhash) haddr he
    subst c'
    have haOwner := BaseSeams.addr_mono extLoaded haLoad
    obtain ⟨_, ho⟩ := record_owner_spec haOwner hrep ev221
    rw [hz] at ev262
    rw [hzo] at ev302
    have huSub : ∀ cl ∈ csUnsafe, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hoSub : ∀ cl ∈ csOwner, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    refine ⟨record_unsafe_zero_in_store hS hc
      (BaseSeams.addr_mono ev221.heap_extends haOwner) ev262 huSub, fun cb hb => ?_⟩
    exact record_unsafe_zero_in_store hS hb
      (BaseSeams.addr_mono (ev221.heap_extends.trans ev262.heap_extends) ho) ev302 hoSub

/-- The empty-exclusion guard proves `assert_ref_allowed` at every used reference index and
safety at every used, uncovered reference index. -/
theorem assert_safe_used_refs_full_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rc rp used r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, i + refs.length < 8589934592 →
      RCLimRep t bAddr lim h rc →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs rp →
      RepSortedIdxFrom h idxs i used →
      ObsFn Obs.W "KernelClaim::assert_safe_used_refs"
        [rc, rp, used, .field (i : F), .construct addrMapEnum "Nil" []] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs →
        RefAllowedIn calls t bAddr lim refs[j] ∧
          (¬ CoveredAt t lim refs[j] → SourceSafe E₀ refs[j]) := by
  induction refs with
  | nil => intro i idxs rc rp used r h h' cs hb hrc hr hi ev hsub j hj; cases hj
  | cons a rest ih =>
    intro i idxs rc rp used r h h' cs hb hrc hr hi ev hsub
    match Obs.«KernelClaim::assert_safe_used_refs».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hr ld
    | .Cons (cs_bixmeype := csHead) (cs353 := csTail) (ld12 := ld) (ev_ahqcgauk := evPop)
        (sg_opqpxwys := seg) (op395 := op) (ev355 := ev355) (hc404 := hcs) .. =>
      obtain ⟨_, _, he, ha, hrest⟩ := Lib.rep_cons_of_load hr ld
      injection he with he1 he2
      subst he1 he2
      obtain ⟨rfl, hiff, hiNext⟩ := sorted_pop_spec idxs (by simp at hb; omega) hi evPop
      have hsegSub : ∀ cl ∈ csHead, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨ext, hsafe⟩ := safe_used_refs_seg_spec hS hrc ha hiff seg hsegSub
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      have hinc : (i : F) + 1 = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hinc] at ev355
      have htailSub : ∀ cl ∈ csTail, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have ht := ih (i + 1) (by simp at hb ⊢; omega) (hrc.mono ext)
        (repList_heapMono₂ _ repAddrElem_heapMono₂ ext hrest)
        (hiNext.mono ext) ev355 htailSub
      intro j hj hm
      cases j with
      | zero => exact hsafe (by simpa only [Nat.add_zero] using hm)
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        exact ht j hj' (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)

/-- The empty-exclusion guard proves safety at every used, uncovered reference index. -/
theorem assert_safe_used_refs_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rc rp used r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, i + refs.length < 8589934592 →
      RCLimRep t bAddr lim h rc →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs rp →
      RepSortedIdxFrom h idxs i used →
      ObsFn Obs.W "KernelClaim::assert_safe_used_refs"
        [rc, rp, used, .field (i : F), .construct addrMapEnum "Nil" []] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs →
        ¬ CoveredAt t lim refs[j] → SourceSafe E₀ refs[j] :=
  by
    intro i idxs rc rp used r h h' cs hb hrc hr hi ev hsub j hj hm hn
    exact (assert_safe_used_refs_full_spec hS refs i hb hrc hr hi ev hsub j hj hm).2 hn

/-- A concrete record guard supplies the conditional edge-safety clause. The source and
owner safety premises determine the guard branch; neither branch choice nor the conclusion
is assumed. -/
theorem RecordRefsIn.safe {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address} {lim : Option Nat} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hc : recordOf E₀ a = some c) (hsafe : SourceSafe E₀ a)
    (hg : RecordRefsIn calls t bAddr lim a c) :
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      ¬ CoveredAt t lim x → SourceSafe E₀ x := by
  obtain ⟨h, h', rc, ap, cp, r, cs, hrc, ha, hcp, ev, hsub⟩ := hg
  obtain ⟨csUnder, evUnder, hcalls⟩ := Obs.«KernelClaim::assert_safe_record_refs».obs ev
  have hsubUnder : ∀ cl ∈ csUnder, cl ∈ calls :=
    fun cl hcl => hsub cl (by rw [hcalls]; simp [hcl])
  match Obs.«KernelClaim::assert_safe_record_refs_under».obs evUnder with
  | .other (cs13 := csSrc) (ev15 := ev15) (hne190 := hn) (hc198 := hcs) .. =>
    have hs : ∀ cl ∈ csSrc, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    exact (hn (record_unsafe_eq_zero_in_store hS hc (hsafe c hc).1 ha ev15 hs)).elim
  | .n0_other (cs40 := csOwner) (ev15 := ev15) (ev55 := ev55) (ev42 := ev42)
      (hne181 := hn) (hc189 := hcs) .. =>
    have ext := ev15.heap_extends
    obtain ⟨_, haOwner⟩ := record_owner_spec (BaseSeams.addr_mono ext ha) (hcp.mono ext) ev55
    obtain ⟨_, bytes, cb, hsz, hh, hb, hd, he, himp⟩ :=
      record_unsafe_safe_spec (BaseSeams.addr_mono ev55.heap_extends haOwner) ev42
    have hs : ∀ cl ∈ csOwner, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    have howner := recordOf_hashed hS hH (hashed_mono hs hh) hsz hd he
    rw [hb] at howner
    exact (hn (himp ((hsafe c hc).2 cb howner))).elim
  | .n0_n0 (m147 := idxHeap) (cs13 := csSrc) (cs124 := csLoop) (x_refs := refsPtr) (ev15 := ev15)
      (ev55 := ev55) (ev42 := ev42) (hv90 := hv90) (ev157 := ev157) (ev126 := ev126)
      (hc179 := hcs) .. =>
    have hsSrc : ∀ cl ∈ csSrc, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    obtain ⟨_, bytes, c', hsz, hh, hb, _, he, _⟩ := record_unsafe_safe_spec ha ev15
    have hrecAt : Ix.Cert.recordAt E₀ a = some c := (hS.recordOf_eq_recordAt a).symm.trans hc
    have hcc : c' = c := hS.record_eq hrecAt (hashed_mono hsSrc hh) hb he
    subst c'
    have hrefsSmall := refs_small_of_decoded hsz he
    have extBefore := ev15.heap_extends.trans (ev55.heap_extends.trans ev42.heap_extends)
    obtain ⟨extIdx, hidx⟩ := const_idxs_of_spec (hcp.mono extBefore) ev157
    have hRefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem idxHeap c.refs.toList refsPtr := by
      obtain ⟨_, _, rp, _, _, heq, _, _, hrf, _, _⟩ := hcp
      have heq' := heq.symm.trans hv90
      simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at heq'
      rcases heq' with ⟨_, _, heqRefs, _, _⟩
      rw [heqRefs] at hrf
      exact repList_heapMono₂ _ repAddrElem_heapMono₂ (extBefore.trans extIdx) hrf
    have hloopSub : ∀ cl ∈ csLoop, cl ∈ calls :=
      fun cl hcl => hsubUnder cl (by rw [hcs]; simp [hcl])
    have hloop := assert_safe_used_refs_spec hS c.refs.toList 0
      (by simpa only [Nat.zero_add, Array.length_toList] using hrefsSmall)
      (hrc.mono (extBefore.trans extIdx)) hRefs hidx ev126 hloopSub
    intro i hi x hx hn
    obtain ⟨hiLt, hget⟩ := List.getElem?_eq_some_iff.mp hx
    have hi' : i ∈ BaseSeams.usedRefIdxs c := by
      rw [Assembly.usedRefIdxs_eq]
      exact hi
    have hs := hloop i hiLt (by simpa only [Nat.zero_add] using hi')
    rw [hget] at hs
    exact hs hn

end IxVM.Refinement.Claim
