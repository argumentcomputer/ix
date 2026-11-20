import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.Claim.RBTree

/-! # The reference safety guard with addresses excluded

`KernelClaim::assert_safe_used_refs` over an exclusion set the run built, and
`KernelClaim::assert_safe_refs_except`, which builds the one-address set of an operation and runs
it on a certificate's references: every used reference other than the operation, not covered at
the context's limit, is in Lean's logic with its block, whatever the certificate's own flags.

* `addr_set_member_set_spec`: the membership test of a represented address set answers `1` only
  at an address of the set.
* `assert_safe_used_refs_set_spec`: the guard over a represented exclusion set.
* `assert_safe_refs_except_spec`: the guard of a certificate's references.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Claim
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- **The membership test of a represented address set** answers `1` only at an address of the
set, and leaves the heap. -/
theorem addr_set_member_set_spec {S : List _root_.Address} {b : Bytes.Address}
    {x_b tree r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h b x_b) (hs : RepAddrSet h S tree)
    (ev : ObsFn Obs.W "KernelClaim::addr_set_member" [x_b, tree] h r h' calls) :
    (r = .field 1 → ixAddr b ∈ S) ∧ h' = h := by
  obtain ⟨es, hbst, -, hmem⟩ := hs
  obtain ⟨_, ev6, _⟩ := Obs.«KernelClaim::addr_set_member».obs ev
  rw [← Obs.Names.«RBTreeMap::rbtree_map_lookup_or_default<Field>».symbol] at ev6
  obtain ⟨hr, hh⟩ := rbtree_map_lookup_or_default_spec hb hbst ev6
  refine ⟨fun h1 => ?_, hh⟩
  rw [h1] at hr
  unfold lookupEntries at hr
  cases hf : es.find? (fun p => decide (p.1 = b)) with
  | none =>
    simp only [hf] at hr
    exact absurd (Value.field.inj hr) one_ne_zero
  | some p =>
    have hp1 : p.1 = b := by simpa using List.find?_some hf
    have hpm : p ∈ es := List.mem_of_find?_eq_some hf
    exact (hmem b).mp ⟨p.2, by rw [← hp1]; exact hpm⟩

/-- One step of the guard over a represented exclusion set: at a used index, a reference outside
the set and not covered is safe with its block. -/
private theorem safe_used_refs_set_seg_spec
    {calls cs : List (Call F)} {E₀ : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {bAddr a : _root_.Address} {lim : Option Nat} {i : Nat} {idxs : List Nat}
    {S : List _root_.Address}
    {hit nextUsed ap rest rc refs used ex r : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀) (hrc : RCLimRep t bAddr lim h rc)
    (ha : S0.addr h ap a) (hiff : hit = .field 1 ↔ i ∈ idxs)
    (hex : RepAddrSet h S ex)
    (ev : Obs.«KernelClaim::assert_safe_used_refs».Seg_fokxpuhl hit nextUsed ap rest rc refs used
      (.field (i : F)) ex h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧ (i ∈ idxs → a ∉ S → ¬ CoveredAt t lim a → SourceSafe E₀ a) := by
  obtain ⟨ab, hab, hab'⟩ := id ha
  match ev with
  | .n1_n1 (ev_utgbirrs := ev91) (he_xpwauxiq := hh) .. =>
    obtain ⟨hm, rfl⟩ := addr_set_member_set_spec hab hex ev91
    refine ⟨by rw [hh], fun _ hnS _ => ?_⟩
    exact (hnS (hab' ▸ hm rfl)).elim
  | .other (hne_yeueqpng := hn) (he_eemargwo := hh) .. =>
    exact ⟨hh ▸ Heap.Extends.refl _, fun hm _ _ => (hn (hiff.mpr hm)).elim⟩
  | .n1_other_other (ev_utgbirrs := ev91) (ev_qtjiirzs := ev134) (ev_phyxterm := ev165)
      (hne_ifyzjima := hn) (he_felbweqg := hh) .. =>
    obtain ⟨_, rfl⟩ := addr_set_member_set_spec hab hex ev91
    have ext := ev134.heap_extends
    obtain ⟨he, hc⟩ := walk_covered_lim_spec (hrc.mono ext) (S0.addr_mono ext ha) ev165
    refine ⟨?_, fun _ _ hnc => ?_⟩
    · rw [hh, he]; exact ext
    · rcases hc with hz | hcov
      · exact (hn hz).elim
      · exact (hnc hcov).elim
  | .n1_other_n0 (cs_qjpwomix := csLoad) (cs_kgdddfzu := csUnsafe) (cs_kaixaukp := csOwner)
      (ev_utgbirrs := ev91) (ev_qtjiirzs := ev134) (ev_phyxterm := ev165)
      (ev_sbnkpoyd := ev199) (ev_qxxjnwmz := ev221) (ev_unasbjkv := ev262) (heq_jfdvmnjk := hz)
      (ev_ytdmykjs := ev302) (heq_ppgaohtc := hzo) (he_xjkoaywn := hh) (hc_uzyocwyw := hcs) .. =>
    have extAll := ev91.heap_extends.trans (ev134.heap_extends.trans
      (ev165.heap_extends.trans (ev199.heap_extends.trans (ev221.heap_extends.trans
        (ev262.heap_extends.trans ev302.heap_extends)))))
    refine ⟨by rw [hh]; exact extAll, fun _ _ _ c hc => ?_⟩
    have extLoad := ev91.heap_extends.trans (ev134.heap_extends.trans ev165.heap_extends)
    have haLoad := S0.addr_mono extLoad ha
    obtain ⟨extLoaded, bytes, c', _, hhash, haddr, _, he, hrep, _⟩ :=
      load_verified_constant_de haLoad ev199
    have hloadSub : ∀ cl ∈ csLoad, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hrecAt : Ix.Cert.recordAt E₀ a = some c := (hS.recordOf_eq_recordAt a).symm.trans hc
    have hcc : c' = c := hS.record_eq hrecAt (hashed_mono hloadSub hhash) haddr he
    subst c'
    have haOwner := S0.addr_mono extLoaded haLoad
    obtain ⟨_, ho⟩ := record_owner_spec haOwner hrep ev221
    rw [hz] at ev262
    rw [hzo] at ev302
    have huSub : ∀ cl ∈ csUnsafe, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hoSub : ∀ cl ∈ csOwner, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    refine ⟨record_unsafe_zero_in_store hS hc
      (S0.addr_mono ev221.heap_extends haOwner) ev262 huSub, fun cb hb => ?_⟩
    exact record_unsafe_zero_in_store hS hb
      (S0.addr_mono (ev221.heap_extends.trans ev262.heap_extends) ho) ev302 hoSub

/-- **The guard over a represented exclusion set** proves safety at every used reference index
whose reference is outside the set and not covered. -/
theorem assert_safe_used_refs_set_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {S : List _root_.Address}
    (hS : LoadedReads.RunStore calls E₀) (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rc rp used ex r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, i + refs.length < 8589934592 →
      RCLimRep t bAddr lim h rc →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs rp →
      RepSortedIdxFrom h idxs i used →
      RepAddrSet h S ex →
      ObsFn Obs.W "KernelClaim::assert_safe_used_refs" [rc, rp, used, .field (i : F), ex] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs → refs[j] ∉ S →
        ¬ CoveredAt t lim refs[j] → SourceSafe E₀ refs[j] := by
  induction refs with
  | nil => intro i idxs rc rp used ex r h h' cs hb hrc hr hi hex ev hsub j hj; cases hj
  | cons a rest ih =>
    intro i idxs rc rp used ex r h h' cs hb hrc hr hi hex ev hsub
    match Obs.«KernelClaim::assert_safe_used_refs».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hr ld
    | .Cons (cs_bixmeype := csHead) (cs353 := csTail) (ld12 := ld) (ev_ahqcgauk := evPop)
        (sg_opqpxwys := seg) (op395 := op) (ev355 := ev355) (hc404 := hcs) .. =>
      obtain ⟨_, _, he, ha, hrest⟩ := Lib.rep_cons_of_load hr ld
      injection he with he1 he2
      subst he1 he2
      obtain ⟨rfl, hiff, hiNext⟩ := sorted_pop_spec idxs (by simp at hb; omega) hi evPop
      have hsegSub : ∀ cl ∈ csHead, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨ext, hsafe⟩ :=
        safe_used_refs_set_seg_spec hS hrc ha hiff hex seg hsegSub
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      have hinc : (i : F) + 1 = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hinc] at ev355
      have htailSub : ∀ cl ∈ csTail, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have ht := ih (i + 1) (by simp at hb ⊢; omega) (hrc.mono ext)
        (repList_heapMono₂ _ repAddrElem_heapMono₂ ext hrest)
        (hiNext.mono ext) (hex.mono ext) ev355 htailSub
      intro j hj hm hnS hn
      cases j with
      | zero => exact hsafe (by simpa only [Nat.add_zero] using hm) hnS hn
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        exact ht j hj'
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm) hnS hn

/-- **The guard on an operation certificate's references** (`KernelClaim::assert_safe_refs_except`
with the operation's address `a`): every used reference other than `a`, not covered at the
context's limit, is in Lean's logic with its block. -/
theorem assert_safe_refs_except_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) {refs : List _root_.Address} {idxs : List Nat}
    {a : _root_.Address} {rc rp used ap r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : refs.length < 8589934592) (hrc : RCLimRep t bAddr lim h rc)
    (hr : RepList Obs.Names.«Lists::Node<&[Field; 32]>» RepAddrElem h refs rp)
    (hi : RepSortedIdx h idxs used)
    (ha : S0.addr h ap a)
    (ev : ObsFn Obs.W "KernelClaim::assert_safe_refs_except" [rc, rp, used, ap] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ j, (hj : j < refs.length) → j ∈ idxs → refs[j] ≠ a → ¬ CoveredAt t lim refs[j] →
      SourceSafe E₀ refs[j] := by
  obtain ⟨ab, hab, hab'⟩ := id ha
  match Obs.«KernelClaim::assert_safe_refs_except».obs ev with
  | .run _ _ cs12 cs43 ev14 ev45 hc85 =>
    rw [← Obs.Names.«RBTreeMap::rbtree_map_insert<Field>».symbol] at ev14
    obtain ⟨ext, hset⟩ := rbtree_set_insert_spec hab (RepAddrSet.nil h) ev14
    have hsub' : ∀ cl ∈ cs43, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc85]; simp [hcl])
    have hguard := assert_safe_used_refs_set_spec hS refs 0 (by omega) (hrc.mono ext)
      (repList_heapMono₂ _ repAddrElem_heapMono₂ ext hr)
      (hi.mono ext) hset
      (by simpa using ev45) hsub'
    intro j hj hm hne hnc
    refine hguard j hj (by rw [Nat.zero_add]; exact hm) (fun hmS => hne ?_) hnc
    rw [← hab']
    exact List.mem_singleton.mp hmS

end IxVM.Refinement.Claim
