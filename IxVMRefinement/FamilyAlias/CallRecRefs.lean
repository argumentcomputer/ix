import IxVMRefinement.FamilyAlias.CheckFamilyReads
import IxVMRefinement.FamilyAlias.FamilyCall
import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.Claim.TopSeed

/-! # Family-record reference safety and unroled recursors

Reads two checks out of an observed `KernelModeled::check_family` run:

* `assert_used_not_block_spec` and `family_recRefs`: `KernelModeled::family_refs_ok` runs
  `assert_inner_refs_safe` (`KernelClaim::assert_safe_used_refs` with empty exclusion map and
  `KernelModeled::assert_used_not_block`) over the family record's used references, establishing
  that every reference the family record uses is covered at the limit or satisfies `NeedOk`;
* `assert_no_role_spec`: `KernelModeled::assert_no_role` asserts `role_index_of(rc, r) = 0` for
  each address in a list, establishing that no listed address keys to any role under `t`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

set_option linter.unusedVariables false

/-! ## `assert_not_block_ref` and `assert_used_not_block` -/

private theorem assert_not_block_ref_store {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {a : _root_.Address} {x_a r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : S0.addr h x_a a)
    (ev : ObsFn Obs.W "KernelClaim::assert_not_block_ref" [x_a] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧ ∃ c, recordOf E₀ a = some c ∧ ¬ IsBlock c := by
  have ext := ev.heap_extends
  match Obs.«KernelClaim::assert_not_block_ref».obs ev with
  | .Muts (heq115 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
  | .other (ev14 := ev14) (hne121 := hne) (hc129 := hc) .. =>
    obtain ⟨-, rawBytes, c, hsz, hh, hb, hde, hex, hrep, -⟩ :=
      Claim.load_verified_constant_de ha ev14
    have hrec : recordOf E₀ a = some c := by
      rw [← hb]
      exact Claim.recordOf_hashed hS hH
        (Core.hashed_mono (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) hh) hsz hde hex
    obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, -⟩ := hrep
    injection hv_c with _ _ hargs_c
    simp only [List.cons.injEq] at hargs_c
    rw [← hargs_c.1] at hinfo
    refine ⟨ext, c, hrec, fun hblk => ?_⟩
    obtain ⟨ms, hms⟩ := hblk
    rw [hms] at hinfo
    obtain ⟨_, hv', _⟩ := hinfo
    exact absurd hv' (hne [_] rfl)

private theorem assert_used_not_block_seg_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {a : _root_.Address} {i : Nat} {idxs : List Nat}
    {ap rest refs used r : SourceValue F} {h h' : Heap F}
    (ha : S0.addr h ap a)
    (hidx : RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs used)
    (hi : i < 72057594037927936)
    (ev : Obs.«KernelModeled::assert_used_not_block».Seg_czedwbeq ap rest refs used (.field (i : F))
      h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    Heap.Extends h h' ∧ (i ∈ idxs → ∃ c, recordOf E₀ a = some c ∧ ¬ IsBlock c) := by
  match ev with
  | .n1 (ev_zomhduxa := evHas) (ev_rewyseeq := evNb) (hc_hifgrvaq := hcs) .. =>
    obtain ⟨rfl, _⟩ := Claim.g_list_has_spec idxs hi hidx evHas
    have hnbSub : ∀ cl ∈ _, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨ext, hstore⟩ := assert_not_block_ref_store hS hH ha evNb hnbSub
    exact ⟨ext, fun _ => hstore⟩
  | .other (ev_zomhduxa := evHas) (hne_arfngzyc := hne) (he_xtnzeqqi := hh) .. =>
    refine ⟨by rw [hh]; exact evHas.heap_extends, fun hm => ?_⟩
    exact absurd ((Claim.g_list_has_spec idxs hi hidx evHas).2.mpr hm) hne

/-- **`KernelModeled::assert_used_not_block`**: every used reference index in the list holds a
non-block record in the run's store. -/
theorem assert_used_not_block_spec {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rp used r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      i + refs.length < 8589934592 →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs rp →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs used →
      ObsFn Obs.W "KernelModeled::assert_used_not_block" [rp, used, .field (i : F)] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs →
        ∃ c, recordOf E₀ refs[j] = some c ∧ ¬ IsBlock c := by
  induction refs with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ _ j hj; cases hj
  | cons a rest ih =>
    intro i idxs rp used r h h' cs hb hr hi ev hsub
    match Obs.«KernelModeled::assert_used_not_block».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases Lib.rep_nil_of_load hr ld
    | .Cons (ld_bolbylmd := ld) (sg_dugcmplc := seg) (op_urfjlksd := op)
        (ev_tuyouizb := evRest) (hc_gtnunfxa := hcs) .. =>
      obtain ⟨_, _, he, ha, hrest⟩ := Lib.rep_cons_of_load hr ld
      injection he with he1 he2
      subst he1 he2
      have hsegSub : ∀ cl ∈ _, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      obtain ⟨ext, hhead⟩ := assert_used_not_block_seg_spec hS hH ha hi (by simp at hb; omega)
        seg hsegSub
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      have hinc : (i : F) + 1 = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hinc] at evRest
      have htailSub : ∀ cl ∈ _, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have ht := ih (i + 1) (by simp at hb ⊢; omega)
        (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext hrest)
        (repList_heapMono₂ _ Claim.repBoundedIdx_heapMono₂ ext hi) evRest htailSub
      intro j hj hm
      cases j with
      | zero => exact hhead (by simpa only [Nat.add_zero] using hm)
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        exact ht j hj' (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)

/-! ## `family_refs_ok` → `FamilyCallFacts.recRefs` -/

private theorem refs_small_of_exact {bytes : ByteArray} {c : Ixon.Constant}
    (hsz : bytes.size < 4294967296) (he : Ixon.deConstantExact bytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound bytes c he
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]
    omega
  omega

/-- **`KernelModeled::family_refs_ok`**: every reference the family record uses is covered at the
check's limit, or satisfies `NeedOk`. -/
theorem family_recRefs {calls : List (Call F)} {E₀ : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {bAddr rb : _root_.Address} {lim : Option Nat} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hR : FamRecRecord E₀ rb crb rs)
    {rc xrb xb wset r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h rc) (hrb : S0.addr h xrb rb)
    (ev : ObsFn Obs.W "KernelModeled::family_refs_ok" [rc, xrb, xb, wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x := by
  obtain ⟨C⟩ := familyRefsOk_chain ev
  obtain ⟨extLd, bytes, c', hsz, hh, hb, _, hex, hcp, -⟩ :=
    Claim.load_verified_constant_de hrb C.evLoadRb.obs
  have hrecAt : Ix.Cert.recordAt E₀ rb = some crb :=
    (hS.recordOf_eq_recordAt rb).symm.trans hR.record
  have hcc : c' = crb := hS.record_eq hrecAt
    (Core.hashed_mono (fun cl hcl => hsub cl (C.evLoadRb.sub cl hcl)) hh) hb hex
  subst c'
  have hrefsSmall := refs_small_of_exact hsz hex
  have extToIdx : Heap.Extends h C.mGo := extLd.trans C.extToIdxs
  obtain ⟨extIdx, hidx⟩ := Claim.const_idxs_of_spec (hcp.mono C.extToIdxs) C.evIdxs.obs
  have hRefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem C.mIdxs
      crb.refs.toList C.refs := by
    obtain ⟨_, _, rp, _, _, heq, _, _, hrf, _, _⟩ := hcp
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at heq
    rcases heq with ⟨_, _, heqRefs, _, _⟩
    rw [heqRefs] at hrf
    exact repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ (C.extToIdxs.trans extIdx) hrf
  obtain ⟨I⟩ := assertInnerRefsSafe_chain C.evInner.obs
  have hsafe := Claim.assert_safe_used_refs_spec hS crb.refs.toList 0
    (by simpa only [Nat.zero_add, Array.length_toList] using hrefsSmall)
    (hrc.mono (extToIdx.trans extIdx)) hRefs hidx I.evSafe.obs
    (fun cl hcl => hsub cl (C.evInner.sub cl (I.evSafe.sub cl hcl)))
  have hnb := assert_used_not_block_spec hS hH crb.refs.toList 0
    (by simpa only [Nat.zero_add, Array.length_toList] using hrefsSmall)
    (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ I.evSafe.extends hRefs)
    (repList_heapMono₂ _ Claim.repBoundedIdx_heapMono₂ I.evSafe.extends hidx)
    I.evNotBlk.obs
    (fun cl hcl => hsub cl (C.evInner.sub cl (I.evNotBlk.sub cl hcl)))
  intro x hx
  obtain ⟨c₁, i, hc₁, hi, hget⟩ := hx
  have ec : c₁ = crb := Option.some.inj (hc₁.symm.trans hR.record)
  subst ec
  have hgetL : crb.refs.toList[i]? = some x := by
    rw [Array.getElem?_toList]
    exact hget
  obtain ⟨hiLt, hgetElem⟩ := List.getElem?_eq_some_iff.mp hgetL
  have hi' : i ∈ S0.usedRefIdxs crb := by
    rw [Assembly.usedRefIdxs_eq]
    exact hi
  by_cases hcov : Claim.CoveredAt t lim x
  · exact Or.inl hcov
  · right
    have hss := hsafe i hiLt (by simpa only [Nat.zero_add] using hi') (by simpa [hgetElem] using hcov)
    have hst := hnb i hiLt (by simpa only [Nat.zero_add] using hi')
    rw [hgetElem] at hss hst
    obtain ⟨cx, hrecx, hnotblk⟩ := hst
    obtain ⟨hlog, hown⟩ := hss cx hrecx
    exact ⟨cx, hrecx, hnotblk, hlog, hown⟩

/-! ## `assert_no_role` -/

private theorem keyOf_ne_role_of_no_address {t : Ix.Kernel.RoleTable} (hchk : t.check = .ok ())
    {a : _root_.Address} (hno : ∀ ro : Ix.Kernel.Role, t.addressOf? ro ≠ some a) :
    ∀ ro : Ix.Kernel.Role, Core.keyOf t a ≠ .role ro := by
  intro ro heq
  unfold Core.keyOf at heq
  cases hf : t.bound.find? (·.2 == a) with
  | none =>
    rw [hf] at heq
    cases heq
  | some p =>
    rcases p with ⟨r', a'⟩
    have hfL : t.bound.toList.find? (·.2 == a) = some (r', a') := by
      rwa [Array.find?_toList]
    have hmem : (r', a') ∈ t.bound.toList := List.mem_of_find?_eq_some hfL
    have ha' : a' = a := beq_iff_eq.mp (by simpa using List.find?_some hfL)
    subst ha'
    exact hno r' (Claim.addressOf_eq_some_of_mem_bound hchk hmem)

/-- **`KernelModeled::assert_no_role`**: no address in the list keys to any role under `t`. -/
theorem assert_no_role_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    {rc : SourceValue F} :
    ∀ (as : List Bytes.Address) {xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Claim.RCLimRep t bAddr lim h rc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h as xs →
      ObsFn Obs.W "KernelModeled::assert_no_role" [rc, xs] h r h' cs →
      ∀ a ∈ as, ∀ ro : Ix.Kernel.Role, Core.keyOf t (ixAddr a) ≠ .role ro
  | [], xs, r, h, h', cs, hrc, has, ev => fun _ hm => nomatch hm
  | a :: rest, xs, r, h, h', cs, hrc, has, ev => by
    match Obs.«KernelModeled::assert_no_role».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases Lib.rep_nil_of_load has ld
    | .Cons (ld_bolbylmd := ld) (ev_bpdlygwe := evIdx) (heq_qeodfzug := heq0)
        (ev_ilgjjknx := evRest) .. =>
      obtain ⟨a', rest', heq, ha, hrest⟩ := Lib.rep_cons_of_load has ld
      injection heq with h1 h2
      subst h1 h2
      obtain ⟨rfl, hres⟩ := Claim.role_index_of_lim_spec hrc ⟨a, ha, rfl⟩ evIdx
      have hno : ∀ ro, t.addressOf? ro ≠ some (ixAddr a) := by
        rcases hres with ⟨_, hn⟩ | ⟨ro, hro, _⟩
        · exact hn
        · exact absurd (Value.field.inj (heq0.symm.trans hro)) (RolesAux.roleNum_add_one_ne_zero ro)
      have hchk : t.check = .ok () := by
        obtain ⟨_, ⟨hwf, -⟩, -⟩ := hrc.cases
        exact RoleClosure.check_ok_of_wf hwf
      have hhead := keyOf_ne_role_of_no_address hchk hno
      have htail := assert_no_role_spec rest hrc hrest evRest
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hhead
      · exact htail x hx'

end IxVM.Refinement.Typing.FamilyAlias
