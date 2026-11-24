import IxVMRefinement.FamilyGraph.ProducersGraph
import IxVMRefinement.FamilyGraph.ProducersCallTree
import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.Claim.TopRefs
import IxVMRefinement.Obs.Convert1
import IxVMRefinement.Obs.Ingress0
import IxVMRefinement.Obs.KernelClaim0
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelModeled2

/-! # Reference safety of inner records checked inside a family check

Proves the reference-safety and non-inertness facts for every record checked inside a family check
that is not a twin (`Inner`), discharging both remaining obligations of `InnerOwed`:

* `coveredAt_iff_covered_top`: at the top-level limits (`some 77` or `none`), `Claim.CoveredAt`
  agrees with `Typing.Covered`;
* `assert_not_block_ref_stored`, `assert_used_not_block_spec`: `KernelClaim::assert_not_block_ref`
  and `KernelModeled::assert_used_not_block` certify that every used reference holds a non-block
  record in the run's store;
* `assert_inner_refs_safe_spec`: `KernelModeled::assert_inner_refs_safe` combines
  `KernelClaim::assert_safe_used_refs` (`Claim.assert_safe_used_refs_full_spec` and
  `Claim.refAllowed_not_inert_top`) with `KernelModeled::assert_used_not_block`, giving
  `¬ InertAt t x` and `Covered t x ∨ NeedOk E₀ x` at every used reference;
* `get_ci_loads_rec_is_recr_or_rPrj`: a record whose `Ingress::get_ci` load reads as
  `KConstantInfo::Rec` is a standalone recursor or a recursor projection;
* `check_advice_record_inner_refs_safe`: every used reference of a listed advice record is
  checked by `assert_inner_refs_safe` inside `KernelModeled::check_advice_record`;
* `container_recs_refs_standalone_safe`: every used reference of a standalone container recursor
  witnessed in a scope check is checked by `assert_inner_refs_safe` inside
  `KernelModeled::container_recs_refs` and `KernelModeled::container_refs_check`, reached via
  `obsFn_check_witness_enclosing_family`;
* `FamRunCtx.inner_ref_safe`: combines the advice, container, and nested-twin cases to establish
  `¬ InertAt K.t x ∧ (Covered K.t x ∨ NeedOk K.E₀ x)` for every non-twin inner record `a` and
  used reference `x`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Obs
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false

/-! ## Top-level coverage equivalence -/

/-- Every address covered at a limit (`Claim.CoveredAt`) is `Typing.Covered`. -/
theorem covered_of_coveredAt_top {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {x : _root_.Address} (h : Claim.CoveredAt t lim x) : Covered t x :=
  Claim.covered_of_coveredAt h

/-! ## Non-block and safety guards for inner records -/

private theorem refs_size_lt_of_exact {bytes : ByteArray} {c : Ixon.Constant}
    (hsz : bytes.size < 4294967296) (he : Ixon.deConstantExact bytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c he
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

/-- **`KernelClaim::assert_not_block_ref` certifies a stored non-block record** in the run's store:
its `Muts` branch asserts `0 = 1`, so only the non-`Muts` branch succeeds after loading and hashing
the record. -/
theorem assert_not_block_ref_stored {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {a : _root_.Address} {ap r : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (ha : BaseSeams.addr h ap a)
    (ev : ObsFn Obs.W "KernelClaim::assert_not_block_ref" [ap] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧ ∃ c, recordOf E₀ a = some c ∧ ¬ IsBlock c := by
  match Obs.«KernelClaim::assert_not_block_ref».obs ev with
  | .Muts (heq115 := heq) .. =>
    exact absurd (Value.field.inj heq) zero_ne_one
  | .other (cs12 := cs12) (x_info := x_info) (ev14 := ev14) (hne121 := hne)
      (he128 := hh) (hc129 := hcs) .. =>
    obtain ⟨ext, rawBytes, c, hsz, hhash, haddr, hd, he, hcRep, -⟩ :=
      Claim.load_verified_constant_de ha ev14
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hrec : recordOf E₀ a = some c := by
      rw [← haddr]
      exact Claim.recordOf_hashed hS hH (Claim.hashed_mono hsub12 hhash) hsz hd he
    refine ⟨by rw [hh]; exact ext, c, hrec, ?_⟩
    rintro ⟨ms, hms⟩
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := hcRep
    have hinfo_eq : x_info = infoVal := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [← hinfo_eq, hms] at hinfo
    obtain ⟨mv, hmv, -⟩ := hinfo
    exact hne [mv] rfl hmv

/-- **`KernelModeled::assert_used_not_block` certifies that every used reference holds a stored
non-block record.** -/
theorem assert_used_not_block_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rp used r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, i + refs.length < 8589934592 →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs rp →
      Claim.RepSortedIdxFrom h idxs i used →
      ObsFn Obs.W "KernelModeled::assert_used_not_block" [rp, used, .field (i : F)] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs →
        ∃ c, recordOf E₀ refs[j] = some c ∧ ¬ IsBlock c := by
  induction refs with
  | nil => intro i idxs rp used r h h' cs hb hr hi ev hsub j hj; cases hj
  | cons a rest ih =>
    intro i idxs rp used r h h' cs hb hr hi ev hsub
    match Obs.«KernelModeled::assert_used_not_block».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases Lib.rep_nil_of_load hr ld
    | .Cons (m_sszfdvej := mSeg) (cs_bixmeype := csHead) (cs_uirsovbz := csTail)
        (ld_bolbylmd := ld) (ev_ahqcgauk := evPop) (sg_opqpxwys := seg) (op_urfjlksd := op)
        (ev_tuyouizb := evRest) (hc_gtnunfxa := hcs) .. =>
      obtain ⟨_, _, he, ha, hrest⟩ := Lib.rep_cons_of_load hr ld
      injection he with he1 he2
      subst he1 he2
      obtain ⟨rfl, hiff, hiNext⟩ := Claim.sorted_pop_spec idxs (by simp at hb; omega) hi evPop
      have hsegSub : ∀ cl ∈ csHead, cl ∈ calls :=
        fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hseg : Heap.Extends h mSeg ∧
          (i ∈ idxs → ∃ c, recordOf E₀ a = some c ∧ ¬ IsBlock c) := by
        match seg with
        | .n1 (cs_hcikeilv := csNb) (ev_wlgujvgf := evnb) (hc_yfpefzhg := hcseg) .. =>
          have hnbSub : ∀ cl ∈ csNb, cl ∈ calls :=
            fun cl hcl => hsegSub cl (by rw [hcseg]; simp [hcl])
          obtain ⟨extNb, hnb⟩ := assert_not_block_ref_stored hS hH ha evnb hnbSub
          exact ⟨extNb, fun _ => hnb⟩
        | .other (hne_yeueqpng := hn) (he_eemargwo := hh) .. =>
          exact ⟨hh ▸ Heap.Extends.refl _, fun hm => (hn (hiff.mpr hm)).elim⟩
      obtain ⟨ext, hhead⟩ := hseg
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      have hinc : (i : F) + 1 = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hinc] at evRest
      have htailSub : ∀ cl ∈ csTail, cl ∈ calls :=
        fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have htail := ih (i + 1) (by simp at hb ⊢; omega)
        (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext hrest)
        (hiNext.mono ext) evRest htailSub
      intro j hj hm
      cases j with
      | zero => exact hhead (by simpa only [Nat.add_zero] using hm)
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        exact htail j hj' (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)

/-- **`KernelModeled::assert_inner_refs_safe` certifies non-inertness and `Covered ∨ NeedOk`**
for every used reference at a top-level limit (`some 77` or `none`). -/
theorem assert_inner_refs_safe_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hlim : lim = some 77 ∨ lim = none)
    {refs : List _root_.Address} {idxs : List Nat} {rc rp used r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hsz : refs.length < 8589934592)
    (hrc : Claim.RCLimRep t bAddr lim h rc)
    (hrp : RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs rp)
    (hidx : Claim.RepSortedIdx h idxs used)
    (ev : ObsFn Obs.W "KernelModeled::assert_inner_refs_safe" [rc, rp, used] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ j, (hj : j < refs.length) → j ∈ idxs →
      ¬ InertAt t refs[j] ∧ (Covered t refs[j] ∨ NeedOk E₀ refs[j]) := by
  match Obs.«KernelModeled::assert_inner_refs_safe».obs ev with
  | .run (cs_svbeyhut := csSafe) (cs_xuynpgdd := csNb)
      (ev_mxwoukvn := evSafe) (ev_hemnmxwe := evNb) (hc_sgljalbe := hcs) .. =>
    have hsafeSub : ∀ cl ∈ csSafe, cl ∈ calls :=
      fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hnbSub : ∀ cl ∈ csNb, cl ∈ calls :=
      fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hfull := Claim.assert_safe_used_refs_full_spec hS refs 0
      (by simpa only [Nat.zero_add] using hsz) hrc hrp hidx evSafe hsafeSub
    have hnb := assert_used_not_block_spec hS hH refs 0
      (by simpa only [Nat.zero_add] using hsz)
      (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ evSafe.heap_extends hrp)
      (hidx.mono evSafe.heap_extends)
      evNb hnbSub
    intro j hj hm
    have hm0 : 0 + j ∈ idxs := by simpa only [Nat.zero_add] using hm
    obtain ⟨hAllow, hSafe⟩ := hfull j hj hm0
    refine ⟨Claim.refAllowed_not_inert_top hAllow hlim, ?_⟩
    by_cases hcov : Covered t refs[j]
    · exact Or.inl hcov
    · have hss := hSafe (fun hc => hcov (covered_of_coveredAt_top hc))
      obtain ⟨cx, hcx, hnotb⟩ := hnb j hj hm0
      obtain ⟨hlog, hown⟩ := hss cx hcx
      exact Or.inr ⟨cx, hcx, hnotb, hlog, hown⟩

/-! ## Extracting `refs` representation from `Claim.RepConstant` -/

private theorem repConstant_refs_eq {h : Heap F} {c : Ixon.Constant}
    {x_info w1 x_refs w2 w3 : SourceValue F}
    (hcRep : Claim.RepConstant h c (.construct "Ixon::Constant" "Mk" [x_info, w1, x_refs, w2, w3])) :
    RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h c.refs.toList x_refs := by
  obtain ⟨_, _, rp, _, _, heq, -, -, hrf, -, -⟩ := hcRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at heq
  rcases heq with ⟨_, _, hrp, _, _⟩
  subst hrp
  exact hrf

private theorem assert_inner_refs_of_const {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr a x : _root_.Address} {lim : Option Nat}
    {c : Ixon.Constant} {rc x_info w1 x_refs w2 w3 v_idx r : SourceValue F}
    {h h_idx h' : Heap F} {cs_idx cs_safe : List (Call F)}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hlim : lim = some 77 ∨ lim = none)
    (hrc : Claim.RCLimRep t bAddr lim h rc)
    (hc : recordOf E₀ a = some c)
    (hsz : c.refs.size < 8589934592)
    (hcRep : Claim.RepConstant h c (.construct "Ixon::Constant" "Mk" [x_info, w1, x_refs, w2, w3]))
    (ev_idx : ObsFn Obs.W "KernelClaim::const_idxs_of"
      [.construct "Ixon::Constant" "Mk" [x_info, w1, x_refs, w2, w3]] h v_idx h_idx cs_idx)
    (ev_safe : ObsFn Obs.W "KernelModeled::assert_inner_refs_safe"
      [rc, x_refs, v_idx] h_idx r h' cs_safe)
    (hsub_safe : ∀ cl ∈ cs_safe, cl ∈ calls)
    (hu : UsedRef E₀ a x) :
    ¬ InertAt t x ∧ (Covered t x ∨ NeedOk E₀ x) := by
  obtain ⟨extIdx, hidx⟩ := Claim.const_idxs_of_spec hcRep ev_idx
  have hrp := repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ extIdx (repConstant_refs_eq hcRep)
  have hspec := assert_inner_refs_safe_spec hS hH hlim
    (by simpa only [Array.length_toList] using hsz)
    (hrc.mono extIdx) hrp hidx ev_safe hsub_safe
  obtain ⟨c', i, hc', hi, hget⟩ := hu
  have heq : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  have hi' : i ∈ BaseSeams.usedRefIdxs c := by
    rw [Assembly.usedRefIdxs_eq]
    exact hi
  have hgetL : c.refs.toList[i]? = some x := by simpa only [Array.getElem?_toList] using hget
  obtain ⟨hiLt, hval⟩ := List.getElem?_eq_some_iff.mp hgetL
  have hres := hspec i hiLt hi'
  rw [hval] at hres
  exact hres

/-! ## Advice record reference safety -/

private theorem check_advice_record_seg1_extends
    {e0 e1 e2 e3 e4 e5 e6 r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (sg : Obs.«KernelModeled::check_advice_record».Seg1 e0 e1 e2 e3 e4 e5 e6 h r h' cs) :
    Heap.Extends h h' := by
  match sg with
  | .Defn_Definition_Safe (ev210 := ev) ..
  | .Defn_Definition_other (ev264 := ev) ..
  | .Defn_Theorem (ev321 := ev) ..
  | .Defn_Opaque (ev378 := ev) .. => exact ev.heap_extends
  | .Recr (ev553 := e1) (ev540 := e2) (ev574 := e3) .. =>
    exact e1.heap_extends.trans (e2.heap_extends.trans e3.heap_extends)
  | .Muts (ev629 := e1) (ev649 := e2) (ev683 := e3) (ev723 := e4) (ev744 := e5) .. =>
    exact e1.heap_extends.trans (e2.heap_extends.trans
      (e3.heap_extends.trans (e4.heap_extends.trans e5.heap_extends)))
  | .IPrj (ev836 := e1) (ev822 := e2) (ev_gjbqzffr := e3) (he862 := hh) .. =>
    rw [hh]
    exact e1.heap_extends.trans (e2.heap_extends.trans e3.heap_extends)
  | .CPrj (ev915 := e1) (ev901 := e2) (ev_wwojrrlm := e3) (he941 := hh) .. =>
    rw [hh]
    exact e1.heap_extends.trans (e2.heap_extends.trans e3.heap_extends)

/-- **Every used reference of a listed advice record is non-inert and `Covered ∨ NeedOk`**:
`KernelModeled::check_advice_record` unconditionally runs `const_idxs_of` and
`assert_inner_refs_safe` on the loaded record. -/
theorem check_advice_record_inner_refs_safe {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr a x : _root_.Address} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hlim : lim = some 77 ∨ lim = none)
    (hadv : AdviceCheckIn cs bAddr t lim a)
    (hcs : ∀ cl ∈ cs, cl ∈ calls)
    (hu : UsedRef E₀ a x) :
    ¬ InertAt t x ∧ (Covered t x ∨ NeedOk E₀ x) := by
  obtain ⟨h, h', rc, x_a, aset, wset, r, cs₁, hrc, ha, ev, hsub₁⟩ := hadv
  have hsub : ∀ cl ∈ cs₁, cl ∈ calls := fun cl hcl => hcs cl (hsub₁ cl hcl)
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (cs12 := cs12) (cs_zlhtmzlz := csSafe) (ev_yqjbwijz := ev_ord) (ev14 := ev14)
      (sg952 := sg952) (ev_lawbyzgo := ev_idx1) (ev_bilbznow := ev_adv)
      (ev_ozxzdina := ev_idx2) (ev_tnqzszcy := ev_safe) (hc1011 := hcalls) .. =>
    have ⟨c, i, hc, _, _⟩ := hu
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls :=
      fun cl hcl => hsub cl (by rw [hcalls]; simp [hcl])
    have hsubSafe : ∀ cl ∈ csSafe, cl ∈ calls :=
      fun cl hcl => hsub cl (by rw [hcalls]; simp [hcl])
    obtain ⟨ext14, rawBytes, c', hsz, hh, haddr, -, he, hcRep, -⟩ :=
      Claim.load_verified_constant_de (BaseSeams.addr_mono ev_ord.heap_extends ha) ev14
    have hcc : c' = c :=
      hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub12 hh) haddr he
    subst c'
    have extAfter14 : Heap.Extends _ _ :=
      (check_advice_record_seg1_extends sg952).trans
        (ev_idx1.heap_extends.trans ev_adv.heap_extends)
    exact assert_inner_refs_of_const hS hH hlim
      (hrc.mono (ev_ord.heap_extends.trans (ext14.trans extAfter14)))
      hc (refs_size_lt_of_exact hsz he) (hcRep.mono extAfter14) ev_idx2 ev_safe hsubSafe hu

/-! ## Standalone container recursor reference safety -/

private theorem convert_definition_not_rec_inner
    {x_d x_sh x_rf x_ra x_un x_ht x_tb x_bs : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {args : List (SourceValue F)}
    (ev : ObsFn Obs.W "Convert::convert_definition"
      [x_d, x_sh, x_rf, x_ra, x_un, x_ht, x_tb, x_bs] h
      (.construct "KernelTypes::KConstantInfo" "Rec" args) h' cs) : False := by
  match Obs.«Convert::convert_definition».obs ev with
  | .Definition (he242 := he) .. => exact absurd (Value.construct.inj he).2.1 (by decide)
  | .Opaque (he329 := he) .. => exact absurd (Value.construct.inj he).2.1 (by decide)
  | .Theorem (he373 := he) .. => exact absurd (Value.construct.inj he).2.1 (by decide)

/-- **A record whose `Ingress::get_ci` load reads as `KConstantInfo::Rec` is a standalone recursor
or a recursor projection.** -/
theorem get_ci_loads_rec_is_recr_or_rPrj {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {ab : Bytes.Address} {ap ptr : SourceValue F} {h h' : Heap F}
    {args : List (SourceValue F)} {c : Ixon.Constant}
    (hS : LoadedReads.RunStore calls E₀)
    (hab : Bytes.RepAddressRef Core.addrTy h ab ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok (.construct "KernelTypes::KConstantInfo" "Rec" args))
    (hc : recordOf E₀ (Core.ixAddr ab) = some c) :
    (∃ rcr, c.info = .recr rcr) ∨ ∃ p, c.info = .rPrj p := by
  obtain ⟨raw, c', -, hh, hba, hde, -, hhead⟩ := Claim.get_ci_head hab ev
  have hcc : c' = c :=
    hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub hh) hba hde
  subst c'
  cases hinfo : c.info with
  | recr rcr => exact Or.inl ⟨rcr, rfl⟩
  | rPrj p => exact Or.inr ⟨p, rfl⟩
  | muts ms => exact (hhead.notMuts ms hinfo).elim
  | axio ax =>
    obtain ⟨_, _, hl⟩ := hhead.axio ax hinfo
    rw [hld] at hl
    exact absurd (Value.construct.inj (Except.ok.inj hl)).2.1 (by decide)
  | quot q =>
    obtain ⟨_, _, hl⟩ := hhead.quot q hinfo
    rw [hld] at hl
    exact absurd (Value.construct.inj (Except.ok.inj hl)).2.1 (by decide)
  | iPrj p =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hl, _, _⟩ := hhead.iPrj p.idx p.block hinfo
    rw [hld] at hl
    exact absurd (Value.construct.inj (Except.ok.inj hl)).2.1 (by decide)
  | cPrj p =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hl, _, _⟩ :=
      hhead.cPrj p.idx p.cidx p.block hinfo
    rw [hld] at hl
    exact absurd (Value.construct.inj (Except.ok.inj hl)).2.1 (by decide)
  | defn d =>
    exfalso
    match Obs.«Ingress::get_ci».obs ev with
    | .Defn_n0 (v215 := v215) (m216 := m216) (he219 := he) (hm218 := hm) (ev225 := evc) .. =>
      rw [he, hm, Claim.loadValue_snoc_self m216 v215] at hld
      have hv : v215 = .construct "KernelTypes::KConstantInfo" "Rec" args := Except.ok.inj hld
      subst hv
      exact convert_definition_not_rec_inner evc
    | .Defn_other (v336 := v336) (m337 := m337) (he340 := he) (hm339 := hm) (ev346 := evc) .. =>
      rw [he, hm, Claim.loadValue_snoc_self m337 v336] at hld
      have hv : v336 = .construct "KernelTypes::KConstantInfo" "Rec" args := Except.ok.inj hld
      subst hv
      exact convert_definition_not_rec_inner evc
    | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hcs) ..
    | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hcs) ..
    | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hcs) ..
    | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hcs) ..
    | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hcs) ..
    | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hcs) ..
    | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hcs) .. =>
      obtain ⟨-, raw1, c1, -, hh1, hba1, -, hde1, cRep1, -⟩ :=
        Claim.load_verified_constant_de ⟨ab, hab, rfl⟩ ev14
      have hsub1 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hc1 : c1 = c :=
        hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub1 hh1)
          hba1 hde1
      subst c1
      obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := cRep1
      have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
      rw [hinfo] at hinfoRep
      obtain ⟨dv, hdv, -⟩ := hinfoRep
      exact absurd (Value.construct.inj (hinfo_eq.trans hdv)).2.1 (by decide)
  | dPrj p =>
    exfalso
    match Obs.«Ingress::get_ci».obs ev with
    | .DPrj (ev650 := evdp) .. =>
      match Obs.«Ingress::get_ci_dprj».obs evdp with
      | .run (v226 := v226) (m227 := m227) (he230 := he) (hm229 := hm) (ev236 := evc) .. =>
        rw [he, hm, Claim.loadValue_snoc_self m227 v226] at hld
        have hv : v226 = .construct "KernelTypes::KConstantInfo" "Rec" args := Except.ok.inj hld
        subst hv
        exact convert_definition_not_rec_inner evc
    | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hcs) ..
    | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hcs) ..
    | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hcs) ..
    | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hcs) ..
    | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hcs) ..
    | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hcs) ..
    | .RPrj (cs12 := cs12) (ev14 := ev14) (hc926 := hcs) ..
    | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hcs) .. =>
      obtain ⟨-, raw1, c1, -, hh1, hba1, -, hde1, cRep1, -⟩ :=
        Claim.load_verified_constant_de ⟨ab, hab, rfl⟩ ev14
      have hsub1 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hc1 : c1 = c :=
        hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub1 hh1)
          hba1 hde1
      subst c1
      obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := cRep1
      have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
      rw [hinfo] at hinfoRep
      obtain ⟨pv, hpv, -⟩ := hinfoRep
      exact absurd (Value.construct.inj (hinfo_eq.trans hpv)).2.1 (by decide)

/-- **Every used reference of a standalone recursor in `container_recs_refs`'s witness list is
non-inert and `Covered ∨ NeedOk`.** -/
theorem container_recs_refs_standalone_safe {calls : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr a x : _root_.Address} {lim : Option Nat}
    {c : Ixon.Constant} {rcr : Ixon.Recursor}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hlim : lim = some 77 ∨ lim = none)
    (hc : recordOf E₀ a = some c) (hinfo : c.info = .recr rcr) (hu : UsedRef E₀ a x) :
    ∀ (elems : List (SourceValue F)) {rc x_xs wset xx r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» (fun _ u v => u = v) h elems x_xs →
      xx ∈ elems →
      Claim.RCLimRep t bAddr lim h rc →
      BaseSeams.addr h xx a →
      ObsFn Obs.W "KernelModeled::container_recs_refs" [rc, x_xs, wset] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ¬ InertAt t x ∧ (Covered t x ∨ NeedOk E₀ x) := by
  intro elems
  induction elems with
  | nil => intro _ _ _ _ _ _ _ _ _ hmem; cases hmem
  | cons y ys ih =>
    intro rc x_xs wset xx r h h' cs hrep hmem hrc ha ev hsub
    match Obs.«KernelModeled::container_recs_refs».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrep ld
    | .Cons_Recr (x_x := x_x) (x_rest := x_rest) (cs53 := cs53) (cs142 := cs142)
        (cs172 := cs172) (ld12 := ld) (ev55 := ev55) (ev144 := ev144) (ev174 := ev174)
        (hc191 := hcs) .. =>
      obtain ⟨_, _, hcons, rfl, hrestRep⟩ := Lib.rep_cons_of_load hrep ld
      injection hcons with hy hys
      subst hy hys
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · have hsub53 : ∀ cl ∈ cs53, cl ∈ calls :=
          fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
        have hsub142 : ∀ cl ∈ cs142, cl ∈ calls :=
          fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
        obtain ⟨ext55, rawBytes, c', hsz, hh, haddr, -, he, hcRep, -⟩ :=
          Claim.load_verified_constant_de ha ev55
        have hcc : c' = c :=
          hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub53 hh)
            haddr he
        subst c'
        match Obs.«KernelModeled::container_refs_check».obs ev144 with
        | .run (cs_zlhtmzlz := csSafe) (hv59 := hv59) (ev14 := ev14) (ev36 := ev36)
            (ev_iroawuwo := ev_i1) (ev_yqrkylod := ev_i2) (ev_wymffvuv := ev_ok)
            (ev_ozxzdina := ev_idx) (ev_tnqzszcy := ev_safe) (hc222 := hccrk) .. =>
          have hsubSafe : ∀ cl ∈ csSafe, cl ∈ calls :=
            fun cl hcl => hsub142 cl (by rw [hccrk]; simp [hcl])
          have extPre : Heap.Extends _ _ :=
            ev14.heap_extends.trans (ev36.heap_extends.trans
              (ev_i1.heap_extends.trans (ev_i2.heap_extends.trans ev_ok.heap_extends)))
          rw [hv59] at hcRep ev_idx
          exact assert_inner_refs_of_const hS hH hlim
            (hrc.mono (ext55.trans extPre)) hc (refs_size_lt_of_exact hsz he)
            (hcRep.mono extPre) ev_idx ev_safe hsubSafe hu
      · have extStep : Heap.Extends h _ := ev55.heap_extends.trans ev144.heap_extends
        exact ih (repList_heapMono₂ _ (fun _ _ _ _ _ e => e) extStep hrestRep) hmemRest
          (hrc.mono extStep) (BaseSeams.addr_mono extStep ha) ev174
          (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
    | .Cons_RPrj (x_x := x_x) (x_rest := x_rest) (cs53 := cs53) (cs264 := cs264)
        (ld12 := ld) (ev55 := ev55) (ev_fvuqobfi := evpb) (ev_vyniyqbz := evlb)
        (ev210 := ev210) (ev266 := ev266) (hc283 := hcs) .. =>
      obtain ⟨_, _, hcons, rfl, hrestRep⟩ := Lib.rep_cons_of_load hrep ld
      injection hcons with hy hys
      subst hy hys
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · exfalso
        have hsub53 : ∀ cl ∈ cs53, cl ∈ calls :=
          fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
        obtain ⟨-, rawBytes, c', -, hh, haddr, -, he, hcRep, -⟩ :=
          Claim.load_verified_constant_de ha ev55
        have hcc : c' = c :=
          hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub53 hh)
            haddr he
        subst c'
        obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := hcRep
        have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
        rw [hinfo] at hinfoRep
        obtain ⟨rv, hrv, -⟩ := hinfoRep
        exact absurd (Value.construct.inj (hinfo_eq.trans hrv)).2.1 (by decide)
      · have extStep : Heap.Extends h _ :=
          ev55.heap_extends.trans (evpb.heap_extends.trans
            (evlb.heap_extends.trans ev210.heap_extends))
        exact ih (repList_heapMono₂ _ (fun _ _ _ _ _ e => e) extStep hrestRep) hmemRest
          (hrc.mono extStep) (BaseSeams.addr_mono extStep ha) ev266
          (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
    | .Cons_other (x_x := x_x) (x_rest := x_rest) (cs53 := cs53) (cs293 := cs293)
        (x_info := x_info) (ld12 := ld) (ev55 := ev55) (hne192 := hneRecr)
        (ev295 := ev295) (hc312 := hcs) .. =>
      obtain ⟨_, _, hcons, rfl, hrestRep⟩ := Lib.rep_cons_of_load hrep ld
      injection hcons with hy hys
      subst hy hys
      rcases List.mem_cons.mp hmem with rfl | hmemRest
      · exfalso
        have hsub53 : ∀ cl ∈ cs53, cl ∈ calls :=
          fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
        obtain ⟨-, rawBytes, c', -, hh, haddr, -, he, hcRep, -⟩ :=
          Claim.load_verified_constant_de ha ev55
        have hcc : c' = c :=
          hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Claim.hashed_mono hsub53 hh)
            haddr he
        subst c'
        obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := hcRep
        have hinfo_eq : x_info = infoVal := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
        rw [← hinfo_eq, hinfo] at hinfoRep
        obtain ⟨rv, hrv, -⟩ := hinfoRep
        exact hneRecr [rv] rfl hrv
      · exact ih (repList_heapMono₂ _ (fun _ _ _ _ _ e => e) ev55.heap_extends hrestRep) hmemRest
          (hrc.mono ev55.heap_extends) (BaseSeams.addr_mono ev55.heap_extends ha) ev295
          (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))

/-! ## Combined safety for every non-twin inner record -/

/-- **Every used reference of a non-twin inner record is non-inert and `Covered ∨ NeedOk`.** -/
theorem FamRunCtx.inner_ref_safe {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {a x : _root_.Address} (hIa : K.Inner a) (htw : K.twin a = none) (hu : UsedRef K.E₀ a x) :
    ¬ InertAt K.t x ∧ (Covered K.t x ∨ NeedOk K.E₀ x) := by
  obtain ⟨-, -, hcase⟩ := hIa
  rcases hcase with ⟨B, rb, cs, hS, ⟨advAs, hown, hadv⟩ |
      ⟨hwit, -, -, ca, hca, hsa⟩⟩ | ⟨B', hN⟩
  · have hcs : ∀ cl ∈ cs, cl ∈ K.calls := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsub⟩ := hS.1
      exact hsub
    exact check_advice_record_inner_refs_safe hW.runStore hW.hashedStored hW.topLim
      (FamRunCtx.adviceCheck_of_listed hown hadv) hcs hu
  · obtain ⟨h₀, h₀', rc₀, xb₀, xrb₀, r₀, -, -, -, ev_fam, -, hsub_fam⟩ := hS.1
    obtain ⟨h_w, rc_w, xb_w, xx_w, s_w, hrc_w, -, hxx_w, hcl_w⟩ := hwit
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ev_asb, _, _, cs_cr, ev_cr,
      _, _, cs_w, ev_w, -, -, ext_w_ws', sub_ws, _, sub_cr, sub_w, elems, outsideRep,
      memOutside⟩ := obsFn_check_witness_enclosing_family ev_fam hcl_w
    have hrecr : ∃ rcr, ca.info = .recr rcr := by
      match Obs.«KernelModeled::check_witness».obs ev_w with
      | .n0 (hv14 := hv) .. => exact absurd (Value.field.inj hv) (by decide)
      | .n1 (hv171 := hv) .. => exact absurd (Value.field.inj hv) (by decide)
      | .n3 (hv447 := hv) .. => exact absurd (Value.field.inj hv) (by decide)
      | .n2 (cs412 := cs412) (ev328 := ev328) (ev_dpuowbtw := ev_walk)
          (ev_kjcbizia := ev_strip) (ev414 := ev_ccr) (hc442 := hcw) .. =>
        match Obs.«KernelModeled::check_container_rec».obs ev_ccr with
        | .run (cs_ymrayeri := cs_ci) (ev39 := ev39) (ev25 := ev25)
            (ev_nqhglzzq := ev_ci) (ld_hhcwtoqm := hld) (hc96 := hccr) .. =>
          have ext_ci : Heap.Extends h_w _ :=
            ev328.heap_extends.trans (ev_walk.heap_extends.trans
              (ev_strip.heap_extends.trans (ev39.heap_extends.trans ev25.heap_extends)))
          obtain ⟨ab, hab, rfl⟩ := BaseSeams.addr_mono ext_ci hxx_w
          have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ K.calls := fun cl hcl =>
            hsub_fam cl (sub_ws cl (sub_w cl (by rw [hcw]; simp [hccr, hcl])))
          rcases get_ci_loads_rec_is_recr_or_rPrj hW.runStore hab ev_ci hsub_ci hld hca with
            hrecr | ⟨p, hp⟩
          · exact hrecr
          · exact (standalone_not_proj hsa (Or.inr (Or.inr (Or.inr ⟨p, hp⟩)))).elim
    obtain ⟨rcr, hrcr⟩ := hrecr
    have ext_asb : Heap.Extends h_w _ :=
      ev_w.heap_extends.trans (ext_w_ws'.trans ev_asb.heap_extends)
    exact container_recs_refs_standalone_safe hW.runStore hW.hashedStored hW.topLim hca hrcr hu
      elems (repList_heapMono₂ _ (fun _ _ _ _ _ e => e) ev_asb.heap_extends outsideRep)
      memOutside (hrc_w.mono ext_asb) (BaseSeams.addr_mono ext_asb hxx_w) ev_cr
      (fun cl hcl => hsub_fam cl (sub_cr cl hcl))
  · obtain ⟨B'', h''⟩ := FamRunCtx.nestedTwin_of hN
    rw [htw] at h''
    cases h''

end IxVM.Refinement.Typing
