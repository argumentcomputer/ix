import IxVMRefinement.Binding.RunStepStores
import IxVMRefinement.Binding.StoreOpOrder
import IxVMRefinement.Binding.PayloadDirectLoads
import IxVMRefinement.Assembly.BlockRouteFunctional
import IxVMRefinement.FamilyGraph.ProducersGraph
import IxVMRefinement.FamilyAlias.CallLists
import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.Claim.TopRec
import IxVMRefinement.Claim.TopSeed
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck3
import IxVMRefinement.Obs.KernelCheck4
import IxVMRefinement.Obs.KernelCheck12
import IxVMRefinement.Obs.KernelCheck13
import IxVMRefinement.Obs.KernelModeled0
import IxVMRefinement.Obs.KernelModeled1
import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled5
import IxVMRefinement.Obs.KernelRoles1
import IxVMRefinement.Obs.KernelRoles2

/-! # Core circuit specifications for the payload of a binding run

Reusable specifications of the circuit helpers that govern a modeled family check's payload,
recursor checks, and operation-order / safety guards:

* **Route determinism** (`modeledRouteAt_of_obs_ne_zero`, `not_modeledRouteAt_of_nativeObs`):
  one non-zero observation of `KernelModeled::block_is_modeled` under `RunStepStores` puts the
  block on the run's modeled route; one zero observation (`Claim.NativeObsAt`) refutes it.
* **Order and inner-reference safety guards** (`assert_in_order_spec`,
  `assert_used_not_block_spec`, `assert_used_in_order_spec`, `assert_inner_refs_safe_spec`):
  `KernelRoles::assert_in_order` gives `Claim.OpOrderedAt`; `KernelModeled::assert_inner_refs_safe`
  gives `RefAllowedIn`, uncovered `SourceSafe`, `NotBlockIn`, and `OpOrderedAt` for every used
  reference of a record.
* **Non-empty family records under group validation** (`rc_validates_group_spec`,
  `familyCall_isTwinShape`): at a group limit `n < 77`, `KernelRoles::rc_validates_group`
  answers `1`, forcing `check_family` to reject an empty family record (`0 < rs.size`).
* **Native refusal for recursor blocks and projections** (`check_const_rec_block_modeled_family`,
  `rprj_checked_modeled_family`, `recBlock_memberChecked_modeled_family`): `check_const` on a
  recursor member of a `Muts` block cannot take the native arm (`check_recursor_member` refuses
  distinct `Muts` blocks for recursor and parent inductive), so it takes the modeled arm and
  produces `ModeledRouteAt`, `FamilyCallAtLim`, and the observed `rec_family_block` call.
* **First-motive carrier head over `RawConvExpr`** (`rec_family_block_det`,
  `rec_family_block_usedRef`, `familyCall_block_unique`, `familyCall_uses_block`): peeling
  `rc.params` binders, taking `last_binder_dom` and `collect_spine` on a recursor's converted
  type yields a unique used reference of the recursor's owner record, fixing the family block of
  `rec_family_block` and of any complete `FamilyCallAtLim`.
* **Projection and basis-role helpers** (`projection_block_spec`, `projection_member_spec`,
  `basis_role_allowed_spec`). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)

/-! ## Route determinism -/

private theorem empty_agreesCommitted : AgreesCommitted ({} : Ixon.Env) := by
  intro p _ lc hget
  simp at hget

private theorem empty_zeroFree :
    ({} : Ixon.Env).consts.get? Ix.HostAdmission.Merkle.padding = none ∧
    ({} : Ixon.Env).blobs.get? Ix.HostAdmission.Merkle.padding = none := by
  simp

/-- **One non-zero observation of `KernelModeled::block_is_modeled` puts the block on the run's
modeled route**, under `RunStepStores`. -/
theorem modeledRouteAt_of_obs_ne_zero {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀) (hstep : RunStepStores calls t E₀)
    {bp r : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {b : Bytes.Address}
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [bp] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) (hb : Bytes.RepAddressRef Core.addrTy h b bp)
    (hr : r ≠ .field 0) : ModeledRouteAt calls (Core.ixAddr b) := by
  obtain ⟨Ec, -, hst⟩ := hstep ({} : Ixon.Env) (by intro _ _ h; simp at h)
    (by intro _ _ h; simp at h) empty_agreesCommitted empty_zeroFree
  have hg : Core.Good ⟨Ec, Ix.Kernel.Env.empty, t, none⟩ calls := hst.good Ix.Kernel.Env.empty none
  have hcov : L1.CanonicalHashCoverage Ec calls :=
    stepStore_canonicalHashCoverage hC.runStore hC.hashedStored hst
  intro bp₂ r₂ h₂ h₂' cs₂ b₂ ev₂ hsub₂ hb₂ hix₂ heq0
  have g₁ := hg.sub hsub
  have g₂ := hg.sub hsub₂
  have hcov₁ : L1.CanonicalHashCoverage Ec cs := fun bytes val hh hsz hx =>
    hcov bytes val (Core.hashed_mono hsub hh) hsz hx
  have hreq : r = r₂ := Typing.blockRouteFunctional Ec bp bp₂ h h' h₂ h₂' cs cs₂ b b₂ r r₂
    ev ev₂ g₁.1 g₁.2 hcov₁ g₂.1 g₂.2 hb hb₂ hix₂.symm
  exact hr (hreq.trans heq0)

/-- **One zero observation of `KernelModeled::block_is_modeled` refutes `ModeledRouteAt`.** -/
theorem not_modeledRouteAt_of_nativeObs {calls : List (Call F)} {B : _root_.Address}
    (hnat : Claim.NativeObsAt calls B) : ¬ ModeledRouteAt calls B := by
  intro hmod
  obtain ⟨bp, h, h', cs, b, ev, hsub, hb, hix⟩ := hnat
  exact hmod bp (.field 0) h h' cs b ev hsub hb hix rfl

/-! ## Operation-order and inner-reference safety guards -/

private theorem sub_one_roleNum_pcs {ro : Ix.Kernel.Role} {v : SourceValue F}
    (op : evalBinOp .sub (.field (Core.roleNum ro + 1)) (.field 1) = .ok v) :
    v = .field (Core.roleNum ro) := by
  simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op
  exact op.symm

/-- **`KernelRoles::assert_in_order(rc, a)` enforces `Claim.OpOrderedAt` at the limit of `rc`.** -/
theorem assert_in_order_spec {t : Ix.Kernel.RoleTable} {bAddr a : _root_.Address}
    {lim : Option Nat} {x_rc x_a r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc) (ha : Core.S0.addr h x_a a)
    (ev : ObsFn Obs.W "KernelRoles::assert_in_order" [x_rc, x_a] h r h' cs) :
    Claim.OpOrderedAt t lim a := by
  intro ro hro h2 n hn h33
  obtain ⟨tbl, htbl, ⟨n', rfl, hn', hl⟩ | ⟨rfl, hl⟩⟩ := hrc.cases
  · have e : n' = n := Option.some.inj hn
    subst e
    have hwf : t.wf = true := htbl.1
    have hinj : ∀ ro', t.addressOf? ro' = some a → ro' = ro :=
      fun ro' h' => addressOf_role_inj hwf h' hro
    match Obs.«KernelRoles::assert_in_order».obs ev with
    | .Mk_n0 (ld_bolbylmd := ld12) (ev_mrvohxmv := ev71) (ev_evsidpuf := ev49) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨-, -, hlk⟩ := Claim.addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨-, hnone⟩ | ⟨ro', hv', -⟩
      · exact absurd hro (hnone ro)
      · exact absurd (Value.field.inj hv')
          (fun e => Core.RolesAux.roleNum_add_one_ne_zero ro' e.symm)
    | .Mk_other (ld_bolbylmd := ld12) (ev_mrvohxmv := ev71) (ev_evsidpuf := ev49)
        (hne_svmgbuyu := hne) (op_hulpzetj := op1) (op_sjbdwqxx := op2)
        (ev_syddzypv := evg) (ev_dirxqlec := evo) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨rfl, rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, hlk⟩ := Claim.addr_index_lookup htbl ha ev71 ev49
      rcases hlk with ⟨rfl, -⟩ | ⟨ro', rfl, hof⟩
      · exact absurd rfl hne
      · obtain rfl := hinj ro' hof
        rw [sub_one_roleNum_pcs op2] at evg
        rw [sub_one_roleNum_pcs op1] at evo
        obtain ⟨rfl, rfl⟩ := Core.RolesAux.role_group_spec evg
        exact Claim.assert_op_reached_in_order_spec hn' evo h2 h33
    | .Assumed (ld_bolbylmd := ld12) .. => rw [hl] at ld12; simp at ld12
  · cases hn

/-- **`KernelModeled::assert_used_not_block`** checks `Claim.NotBlockIn` on every used
reference. -/
theorem assert_used_not_block_spec {calls : List (Call F)} (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rp used r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, i + refs.length < 8589934592 →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs rp →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs used →
      ObsFn Obs.W "KernelModeled::assert_used_not_block" [rp, used, .field (i : F)] h r h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs → Claim.NotBlockIn calls refs[j] := by
  induction refs with
  | nil => intro i idxs rp used r h h' cs _ _ _ _ _ j hj; cases hj
  | cons a rest ih =>
    intro i idxs rp used r h h' cs hb hr hi ev hsub
    match Obs.«KernelModeled::assert_used_not_block».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases Lib.rep_nil_of_load hr ld
    | .Cons (m_yvuflqli := mHead) (cs_juuuvegi := csHead) (cs_uirsovbz := csTail) (ld_bolbylmd := ld)
        (sg_dugcmplc := seg) (op_urfjlksd := op) (ev_tuyouizb := evTail) (hc_gtnunfxa := hcs) .. =>
      obtain ⟨_, _, he, ha, hrest⟩ := Lib.rep_cons_of_load hr ld
      injection he with he1 he2
      subst he1 he2
      have hsegSub : ∀ cl ∈ csHead, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have hseg : Heap.Extends h mHead ∧ (i ∈ idxs → Claim.NotBlockIn calls a) := by
        have hiSmall : i < 72057594037927936 := by simp at hb; omega
        match seg with
        | .n1 (cs_rexuxvwa := csNb) (ev_zomhduxa := evHas) (ev_rewyseeq := evNb)
            (hc_hifgrvaq := hcs1) .. =>
          have ext1 := evHas.heap_extends
          obtain ⟨ext2, hnb⟩ := Claim.assert_not_block_ref_notBlock (Core.S0.addr_mono ext1 ha) evNb
          refine ⟨ext1.trans ext2, fun _ => ?_⟩
          exact Claim.NotBlockIn.mono (fun cl hcl => hsegSub cl (by rw [hcs1]; simp [hcl])) hnb
        | .other (ev_zomhduxa := evHas) (hne_arfngzyc := hne) (he_xtnzeqqi := hh) .. =>
          refine ⟨by rw [hh]; exact evHas.heap_extends, fun hm => ?_⟩
          exact (hne ((Claim.g_list_has_spec idxs hiSmall hi evHas).2.mpr hm)).elim
      obtain ⟨ext, hhead⟩ := hseg
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      have hinc : (i : F) + 1 = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hinc] at evTail
      have htailSub : ∀ cl ∈ csTail, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
      have ht := ih (i + 1) (by simp at hb ⊢; omega)
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext hrest)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext hi) evTail htailSub
      intro j hj hm
      cases j with
      | zero => exact hhead (by simpa only [Nat.add_zero] using hm)
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        exact ht j hj' (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)

/-- **`KernelModeled::assert_used_in_order`** checks `Claim.OpOrderedAt` on every used
reference. -/
theorem assert_used_in_order_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} (refs : List _root_.Address) :
    ∀ (i : Nat) {idxs : List Nat} {rc rp used r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)}, i + refs.length < 8589934592 →
      Claim.RCLimRep t bAddr lim h rc →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs rp →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h idxs used →
      ObsFn Obs.W "KernelModeled::assert_used_in_order" [rc, rp, used, .field (i : F)] h r h' cs →
      ∀ j, (hj : j < refs.length) → i + j ∈ idxs → Claim.OpOrderedAt t lim refs[j] := by
  induction refs with
  | nil => intro i idxs rc rp used r h h' cs _ _ _ _ _ j hj; cases hj
  | cons a rest ih =>
    intro i idxs rc rp used r h h' cs hb hrc hr hi ev
    match Obs.«KernelModeled::assert_used_in_order».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases Lib.rep_nil_of_load hr ld
    | .Cons (m_yvuflqli := mHead) (ld_bolbylmd := ld) (sg_dugcmplc := seg) (op_gskedpnl := op)
        (ev_ohnkrrnf := evTail) .. =>
      obtain ⟨_, _, he, ha, hrest⟩ := Lib.rep_cons_of_load hr ld
      injection he with he1 he2
      subst he1 he2
      have hseg : Heap.Extends h mHead ∧ (i ∈ idxs → Claim.OpOrderedAt t lim a) := by
        have hiSmall : i < 72057594037927936 := by simp at hb; omega
        match seg with
        | .n1 (ev_zomhduxa := evHas) (ev_rsdpehjw := evOrd) .. =>
          have ext1 := evHas.heap_extends
          exact ⟨ext1.trans evOrd.heap_extends, fun _ =>
            assert_in_order_spec (hrc.mono ext1) (Core.S0.addr_mono ext1 ha) evOrd⟩
        | .other (ev_zomhduxa := evHas) (hne_arfngzyc := hne) (he_xtnzeqqi := hh) .. =>
          refine ⟨by rw [hh]; exact evHas.heap_extends, fun hm => ?_⟩
          exact (hne ((Claim.g_list_has_spec idxs hiSmall hi evHas).2.mpr hm)).elim
      obtain ⟨ext, hhead⟩ := hseg
      simp only [evalBinOp, Except.ok.injEq] at op
      subst op
      have hinc : (i : F) + 1 = ((i + 1 : Nat) : F) := by push_cast; rfl
      rw [hinc] at evTail
      have ht := ih (i + 1) (by simp at hb ⊢; omega) (hrc.mono ext)
        (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext hrest)
        (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext hi) evTail
      intro j hj hm
      cases j with
      | zero => exact hhead (by simpa only [Nat.add_zero] using hm)
      | succ j =>
        have hj' : j < rest.length := by simpa using hj
        exact ht j hj' (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hm)

/-- **`KernelModeled::assert_inner_refs_safe` full specification**: every used reference of the
record satisfies `RefAllowedIn`, uncovered `SourceSafe`, `NotBlockIn`, and `OpOrderedAt`. -/
theorem assert_inner_refs_safe_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat}
    (hS : LoadedReads.RunStore calls E₀) {c : Ixon.Constant} (hrefsSmall : c.refs.size < 8589934592)
    {rc rp used r : SourceValue F} {h h' : Heap F}
    (hrc : Claim.RCLimRep t bAddr lim h rc)
    (hRefs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h c.refs.toList rp)
    (hIdx : RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h (Core.S0.usedRefIdxs c) used)
    (ev : ObsFn Obs.W "KernelModeled::assert_inner_refs_safe" [rc, rp, used] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs[i]? = some x →
      Claim.RefAllowedIn calls t bAddr lim x ∧
      (¬ Claim.CoveredAt t lim x → Claim.SourceSafe E₀ x) ∧
      Claim.NotBlockIn calls x ∧
      Claim.OpOrderedAt t lim x := by
  match Obs.«KernelModeled::assert_inner_refs_safe».obs ev with
  | .run (cs_svbeyhut := csSafe) (cs_xuynpgdd := csNb) (cs_ipozlptq := csOrd)
      (ev_mxwoukvn := evSafe) (ev_hemnmxwe := evNb) (ev_xsejfvgw := evOrd)
      (hc_sgljalbe := hcs) .. =>
    have hb : 0 + c.refs.toList.length < 8589934592 := by
      simpa only [Nat.zero_add, Array.length_toList] using hrefsSmall
    have hsubSafe : ∀ cl ∈ csSafe, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubNb : ∀ cl ∈ csNb, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have ext1 := evSafe.heap_extends
    have ext12 := ext1.trans evNb.heap_extends
    have h1 := Claim.assert_safe_used_refs_full_spec hS c.refs.toList 0 hb hrc hRefs hIdx
      evSafe hsubSafe
    have h2 := assert_used_not_block_spec c.refs.toList 0 hb
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext1 hRefs)
      (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext1 hIdx) evNb hsubNb
    have h3 := assert_used_in_order_spec c.refs.toList 0 hb (hrc.mono ext12)
      (RepLinkedList.mono Claim.repAddrElem_heapMono₂ ext12 hRefs)
      (RepLinkedList.mono Claim.repBoundedIdx_heapMono₂ ext12 hIdx) evOrd
    intro i hi x hx
    obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp hx
    have hlt' : i < c.refs.toList.length := by simpa using hlt
    have hi' : 0 + i ∈ Core.S0.usedRefIdxs c := by
      rw [Nat.zero_add, Assembly.usedRefIdxs_eq]
      exact hi
    have hxe : c.refs.toList[i]'hlt' = x := by simpa using hget
    obtain ⟨hra, hss⟩ := h1 i hlt' hi'
    have hnb := h2 i hlt' hi'
    have hord := h3 i hlt' hi'
    rw [hxe] at hra hss hnb hord
    exact ⟨hra, hss, hnb, hord⟩

/-! ## Group validation refuses an empty family record -/

/-- **`KernelRoles::rc_validates_group`** returns `1` under any group-validation limit
`n < 77`. -/
theorem rc_validates_group_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {n : Nat}
    (hn : n < 77) {x_rc r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr (some n) h x_rc)
    (ev : ObsFn Obs.W "KernelRoles::rc_validates_group" [x_rc] h r h' cs) :
    r = .field 1 ∧ h' = h := by
  obtain ⟨tbl, -, ⟨n', heq, -, hl⟩ | ⟨hnone, -⟩⟩ := hrc.cases
  · obtain rfl := Option.some.inj heq
    match Obs.«KernelRoles::rc_validates_group».obs ev with
    | .Mk (ld_bolbylmd := ld12) (ev_vaxwfknm := evGc) (ev_pcvgohly := evLt) .. =>
      rw [hl] at ld12
      injection ld12 with hv
      injection hv with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨-, rfl, -⟩ := hargs
      obtain ⟨rfl, rfl, -⟩ := Obs.«KernelRoleSpec::group_count».obs evGc
      obtain ⟨-, -, hiff, -, hh⟩ := Lib.less_than_fields_field evLt
      have hnv : ZMod.val (n : F) = n :=
        Core.RolesAux.val_natCast (Nat.lt_trans hn (by decide))
      have h77v : ZMod.val (77 : F) = 77 := Core.RolesAux.val_natCast (by decide)
      exact ⟨hiff.mpr (by rw [hnv, h77v]; exact hn), hh⟩
    | .Assumed (ld_bolbylmd := ld12) .. => rw [hl] at ld12; simp at ld12
  · cases hnone

private abbrev flatEntryTy : Generic.Ty :=
  .tuple [.ptr (.array .field 32), .field,
    .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KExprNode" [])]),
    .ptr (.named "Lists::Node" [.ptr (.named "KernelTypes::KLevelNode" [])])]

private abbrev flatListEnum : String :=
  Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>»

private theorem flatListEnum_eq :
    (Instance.mk "Lists::Node" [flatEntryTy]).symbol = flatListEnum :=
  Obs.Names.«Lists::Node<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol

private theorem flat_originals_walk_len {x_all x_blk x_uo : SourceValue F} :
    ∀ (ms : List Ixon.MutConst) {x_cur x_pos r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList L1.mutConstListEnum L1.RepMutConst h ms x_cur →
      ObsFn Obs.W "KernelCheck::flat_originals_walk" [x_all, x_cur, x_blk, x_uo, x_pos] h r h' cs →
      ∃ xs : List Unit, xs.length = (ms.filter Core.Specs.Callees.isIndc).length ∧
        RepList flatListEnum (fun _ _ _ => True) h' xs r := by
  intro ms
  induction ms with
  | nil =>
    intro x_cur x_pos r h h' cs hrep ev
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (he24 := hr) (hm23 := hh) .. =>
      rw [hr, hh]
      exact ⟨[], rfl, Lib.rep_store_nil h⟩
    | .Cons_Indc (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hrep ld
      cases he
  | cons m rest ih =>
    intro x_cur x_pos r h h' cs hrep ev
    match Obs.«KernelCheck::flat_originals_walk».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrep ld
    | .Cons_Indc (m107 := m107) (m214 := m214) (ld12 := ld) (ev81 := e1) (ev122 := e2)
        (sg221 := sg) (ev235 := e3)
        (he263 := hr) (hm262 := hh) (hm303 := hm3) (ev325 := evRec) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hrep ld
      injection he with h1 h2
      subst h1 h2
      cases m with
      | indc ind =>
        have ext_sg : Heap.Extends m107 m214 := by
          match sg with
          | .Induct (he209 := hsg) .. => rw [hsg]; exact Heap.Extends.refl _
          | .other (he219 := hsg) .. => rw [hsg]; exact Heap.Extends.refl _
        have ext_rec : Heap.Extends h _ :=
          e1.heap_extends.trans (e2.heap_extends.trans (ext_sg.trans (e3.heap_extends.trans
            (by rw [hm3]; exact Heap.Extends.snoc _ _))))
        obtain ⟨xs, hlen, hxs⟩ := ih
          (RepLinkedList.mono L1.repMutConst_heapMono₂ ext_rec hrest) evRec
        rw [hr, hh]
        refine ⟨() :: xs, ?_,
          Lib.rep_store_cons (fun _ _ _ _ _ _ => trivial) trivial hxs⟩
        simp [Core.Specs.Callees.isIndc, Core.isIndc, hlen]
      | defn d => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
      | recr rc => obtain ⟨_, hmv, -⟩ := hm; simp at hmv
    | .Cons_other (ld12 := ld) (hne375 := hne) (ev384 := evRec) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hrep ld
      injection he with h1 h2
      subst h1 h2
      cases m with
      | indc ind =>
        obtain ⟨iv, hiv, -⟩ := hm
        exact absurd hiv (hne [iv] rfl)
      | defn d =>
        obtain ⟨xs, hlen, hxs⟩ := ih hrest evRec
        exact ⟨xs, by simp [Core.Specs.Callees.isIndc, Core.isIndc, hlen], hxs⟩
      | recr rc =>
        obtain ⟨xs, hlen, hxs⟩ := ih hrest evRec
        exact ⟨xs, by simp [Core.Specs.Callees.isIndc, Core.isIndc, hlen], hxs⟩

/-- **The block of an observed family check is a non-empty block of inductive types in `E₀`.** -/
theorem familyCall_block_indc_nonempty {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ cb msB, recordOf E₀ B = some cb ∧ cb.info = .muts msB ∧ 0 < msB.size ∧
      (msB.toList.filter Core.Specs.Callees.isIndc).length = msB.size := by
  obtain ⟨h, h', rc, xb, xrb, r, -, ⟨bB, hbB, rfl⟩, -, ev, -, hsub⟩ := hfc
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (m105 := m105) (m501 := m501) (m589 := m589) (m624 := m624)
      (cs511 := cs511) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := evo) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309) (ev344 := ev344)
      (ev403 := ev403) (ev435 := ev435) (ev465 := ev465) (ev513 := ev513) (ev601 := ev601)
      (ev634 := ev634) (heq650 := heq650) (ev664 := ev664) (hc1474 := hc) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. => rw [he33]; exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have e453 : Heap.Extends h _ :=
      e0.trans <| ev126.heap_extends.trans <| ev148.heap_extends.trans <|
        ev194.heap_extends.trans <| evo.heap_extends.trans <| ev231.heap_extends.trans <|
        ev266.heap_extends.trans <| ev309.heap_extends.trans <| ev344.heap_extends.trans <|
        ev403.heap_extends.trans <| ev435.heap_extends.trans ev465.heap_extends
    have hsub511 : ∀ cl ∈ cs511, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨cb, msB, hbl, hrep⟩ :=
      Claim.load_block_head (Bytes.repAddressRef_heapMono₂ Core.addrTy e453 hbB) ev513
    obtain ⟨hcb, hmsB⟩ := (hbl.mono hsub511).stored hH
    have hszLt : msB.size < 8589934592 := by
      have := Claim.muts_size_le hmsB
      omega
    have hrep1 := RepLinkedList.mono L1.repMutConst_heapMono₂ ev601.heap_extends hrep
    have hlenV : _ = Value.field (msB.toList.length : F) := by
      have evLen' : ObsFn Obs.W
          (Instance.mk "Lists::length" [.named "Ixon::MutConst" []]).symbol [_] _ _ _ _ := by
        rw [Obs.Names.«Lists::length<Ixon::MutConst>».symbol]
        exact ev601
      exact (Lib.Lists.length_spec evLen' hrep).1
    obtain ⟨hindV, -⟩ := Core.muts_indc_count_spec (Route.membersRep_of_repMutConstList hrep1) ev634
    have hfilt : (msB.toList.filter Core.Specs.Callees.isIndc).length = msB.size := by
      have he : ((msB.toList.filter Core.Specs.Callees.isIndc).length : F) =
          (msB.toList.length : F) :=
        Value.field.inj (hindV.symm.trans (heq650.trans hlenV))
      have hle : (msB.toList.filter Core.Specs.Callees.isIndc).length ≤ msB.toList.length :=
        List.length_filter_le _ _
      have hlt : msB.toList.length < 8589934592 := by simpa using hszLt
      have hnat := Core.ModeledAux.natCast_inj_lt
        (Nat.lt_of_le_of_lt hle (Nat.lt_trans hlt (by decide)))
        (Nat.lt_trans hlt (by decide)) he
      simpa using hnat
    refine ⟨cb, msB, hcb, hmsB, ?_, hfilt⟩
    match Obs.«KernelModeled::block_nparams».obs ev664 with
    | .run (ld12 := ld12) .. =>
      have e624 : Heap.Extends m501 m624 := ev601.heap_extends.trans ev634.heap_extends
      obtain ⟨z, zs, hz, -, -⟩ :=
        Lib.rep_cons_of_load (RepLinkedList.mono L1.repMutConst_heapMono₂ e624 hrep) ld12
      have hlen : msB.toList.length = zs.length + 1 := by rw [hz]; rfl
      rw [← Array.length_toList, hlen]
      exact Nat.succ_pos _

/-- **Under a group validation limit `n < 77`, the family record of any observed `check_family` is
a non-empty block of recursors** (`0 < rs.size`), in Lean's logic, with all member projections
stored. -/
theorem familyCall_isTwinShape {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {n : Nat}
    {cs : List (Call F)} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hn : n < 77)
    (hfc : FamilyCallAtLim calls bAddr t B rb (some n) cs) :
    ∃ c rs, recordOf E₀ rb = some c ∧ InLogic c ∧ c.info = .muts rs ∧ 0 < rs.size ∧
      (∀ m ∈ rs.toList, ∃ r, m = .recr r) ∧
      ∀ i m, rs[i]? = some m →
        recordOf E₀ (memberAddr rb i m) = some (memberProjection rb i m) := by
  obtain ⟨c, rs, hc, hlog, hrs, hall, hmem⟩ := familyCall_record_block hS hH hfc
  refine ⟨c, rs, hc, hlog, hrs, ?_, hall, hmem⟩
  by_contra hnpos
  have hrs0 : rs.size = 0 := by omega
  have hrsNil : rs.toList = [] := by
    have := Array.length_toList (xs := rs)
    exact List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨cb, msB, hcb, hmsB, hposB, hfilt⟩ := familyCall_block_indc_nonempty hS hH hfc
  obtain ⟨h, h', rc, xb, xrb, r, hrc, ⟨bB, hbB, rfl⟩, ⟨bR, hbR, rfl⟩, ev, -, hsub⟩ := hfc
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (m105 := m105) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := ev_ord) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309)
      (ev344 := ev344) (ev403 := ev403) (ev435 := ev435) (ev465 := ev465) (ev513 := ev513)
      (ev601 := ev601) (ev634 := ev634) (ev664 := ev664) (ev686 := ev686) (ev716 := ev716)
      (ev759 := ev759) (ev817 := ev817) (ev796 := ev796) (ev852 := ev852)
      (ev_ursqbimm := ev_norole) (ev874 := ev874) (ev896 := ev896) (ev960 := ev960)
      (ev939 := ev939) (ev1011 := ev1011) (ev990 := ev990) (ev_edyzsqzv := ev_mv1)
      (ev_gkddqxhv := ev_cat) (ev_ittpynob := ev_mv2) (ev_biaifgpd := ev_mv3)
      (ev1203 := ev1203) (ev_cwwgzxtj := ev_flat) (ev1246 := ev1246)
      (ev_mitevvsv := ev_flen) (op_jmfoqaec := op_sub) (ev_rqpeovbn := ev_z1)
      (ev_xrhmaojz := ev_z2) (ev_whimdwjd := ev_vg) (op_qfbltjlu := op_1mvg)
      (op_cnutjuwu := op_eok) (op_ymhwloon := op_add) (op_mvhbzaru := op_mul)
      (op_zaucahqq := op_or) (heq_sujkqzii := heq_or)
      (cs_pblrtsmj := cs_flat) (cs850 := cs850) (hc1474 := hc1474) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. => rw [he33]; exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have ext_453 : Heap.Extends h _ :=
      e0.trans <| ev126.heap_extends.trans <| ev148.heap_extends.trans <|
        ev194.heap_extends.trans <| ev_ord.heap_extends.trans <| ev231.heap_extends.trans <|
        ev266.heap_extends.trans <| ev309.heap_extends.trans <| ev344.heap_extends.trans <|
        ev403.heap_extends.trans <| ev435.heap_extends.trans ev465.heap_extends
    have ext_784 : Heap.Extends h _ :=
      ext_453.trans <| ev513.heap_extends.trans <| ev601.heap_extends.trans <|
        ev634.heap_extends.trans <| ev664.heap_extends.trans <| ev686.heap_extends.trans <|
        ev716.heap_extends.trans <| ev759.heap_extends.trans <| ev817.heap_extends.trans
        ev796.heap_extends
    have ext_1191 : Heap.Extends h _ :=
      ext_784.trans <| ev852.heap_extends.trans <| ev_norole.heap_extends.trans <|
        ev874.heap_extends.trans <| ev896.heap_extends.trans <| ev960.heap_extends.trans <|
        ev939.heap_extends.trans <| ev1011.heap_extends.trans <| ev990.heap_extends.trans <|
        ev_mv1.heap_extends.trans <| ev_cat.heap_extends.trans <| ev_mv2.heap_extends.trans <|
        ev_mv3.heap_extends.trans ev1203.heap_extends
    have ext_vg : Heap.Extends h _ :=
      ext_1191.trans <| ev_flat.heap_extends.trans <| ev1246.heap_extends.trans <|
        ev_flen.heap_extends.trans <| ev_z1.heap_extends.trans ev_z2.heap_extends
    -- `family_recs` on empty `rs` returns `Nil`, so `v861 = .field 0`
    have hsub850 : ∀ cl ∈ cs850, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1474]; simp [hcl])
    obtain ⟨asR, hasR, hmapR⟩ := FamilyAlias.family_recs_list hH
      (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_784 hbR) ev852 hsub850
      ⟨hc, hrs, hall, hlog, hmem⟩
    have hasNil : asR = [] := by
      have hlen : (asR.map Core.ixAddr).length = 0 := by rw [hmapR, hrsNil]; simp
      simp at hlen
      exact hlen
    subst hasNil
    obtain ⟨hv861, -⟩ := Decl.addrList_length_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy)
        ev_norole.heap_extends hasR) ev874
    simp only [List.length_nil, Nat.cast_zero] at hv861
    subst hv861
    -- `rc_validates_group` answers `1`, so `v_tabgyphp = 1`, hence `y_xxqgtlpp = .field 0`
    obtain ⟨hvg1, -⟩ := rc_validates_group_spec hn (hrc.mono ext_vg) ev_vg
    rw [hvg1] at op_1mvg
    simp only [evalBinOp, sub_self, Except.ok.injEq] at op_1mvg
    subst op_1mvg
    obtain ⟨hz2, -⟩ := Lib.is_zero_field ev_z2
    simp only [↓reduceIte] at hz2
    subst hz2
    simp only [evalBinOp, mul_zero, Except.ok.injEq] at op_eok
    subst op_eok
    -- `v_arypxepi = .field (0 - y)` and `ev_z1` returns `v_tabgyphp = 1`
    obtain ⟨hz1, -⟩ := Lib.is_zero_spec ev_z1
    subst hz1
    simp only [evalBinOp, add_zero, mul_zero, sub_zero, Except.ok.injEq] at op_add op_mul op_or
    subst op_add op_mul op_or
    have hsub0 : _ = (.field 0 : SourceValue F) := by
      by_contra hne
      rw [ite_eq_right hne] at heq_or
      exact zero_ne_one (Value.field.inj heq_or)
    -- `build_flat_block` on empty `rs` returns `build_flat_originals` on `B`, of length `msB.size`
    have hsubF : ∀ cl ∈ cs_flat, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1474]; simp [hcl])
    have hbR_f := Bytes.repAddressRef_heapMono₂ Core.addrTy ext_1191 hbR
    have hbB_f := Bytes.repAddressRef_heapMono₂ Core.addrTy ext_1191 hbB
    have hflatLen : ∃ xs : List Unit, xs.length = msB.size ∧ msB.size < 8589934592 ∧
        RepList flatListEnum (fun _ _ _ => True) _ xs _ := by
      have hloadEmpty : ∀ {x_m w1 w2 w3 w4 : SourceValue F} {m0 m1 : Heap F} {csL : List (Call F)},
          Heap.Extends _ m0 →
          ObsFn Obs.W "Ingress::load_verified_constant" [xrb] m0
            (.construct "Ixon::Constant" "Mk"
              [.construct "Ixon::ConstantInfo" "Muts" [x_m], w1, w2, w3, w4]) m1 csL →
          (∀ cl ∈ csL, cl ∈ calls) →
          RepList L1.mutConstListEnum L1.RepMutConst m1 [] x_m := by
        intro x_m w1 w2 w3 w4 m0 m1 csL extL evL hsubL
        obtain ⟨c', rs', hbl, hrep⟩ :=
          Claim.load_block_head (Bytes.repAddressRef_heapMono₂ Core.addrTy extL hbR_f) evL
        have ec := ((hbl.mono hsubL).record hS hc).1
        subst ec
        have ers := Ixon.ConstantInfo.muts.inj (hbl.info.symm.trans hrs)
        subst ers
        rwa [hrsNil] at hrep
      have hflatOrig : ∀ {m0 m1 : Heap F} {vO : SourceValue F} {csO : List (Call F)},
          Heap.Extends _ m0 →
          ObsFn Obs.W "KernelCheck::build_flat_originals" [xb, _] m0 vO m1 csO →
          (∀ cl ∈ csO, cl ∈ calls) →
          ∃ xs : List Unit, xs.length = msB.size ∧ msB.size < 8589934592 ∧
            RepList flatListEnum (fun _ _ _ => True) m1 xs vO := by
        intro m0 m1 vO csO extO evO hsubO
        have hbBO := Bytes.repAddressRef_heapMono₂ Core.addrTy extO hbB_f
        match Obs.«KernelCheck::build_flat_originals».obs evO with
        | .Muts (cs12 := csL) (ev14 := evL) (ev94 := evW) (hc134 := hcsO) .. =>
          have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsubO cl (by rw [hcsO]; simp [hcl])
          obtain ⟨msPtr, hxm, hlist, hltB⟩ := Decl.load_block_info hS hbBO evL hsubL hcb hmsB
          have hxe := (List.cons.inj (Value.construct.inj hxm).2.2).1
          subst hxe
          obtain ⟨xs, hlen, hxs⟩ := flat_originals_walk_len msB.toList hlist evW
          exact ⟨xs, hlen.trans hfilt, hltB, hxs⟩
        | .other_Induct (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc332 := hcsO) ..
        | .other_other (cs12 := csL) (ev14 := evL) (hne135 := hne) (hc345 := hcsO) .. =>
          have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsubO cl (by rw [hcsO]; simp [hcl])
          obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hbBO evL hsubL hcb hmsB
          exact absurd hxm (hne [msPtr] rfl)
      have hprim : ∀ {m0 m1 : Heap F} {vP : SourceValue F} {csP : List (Call F)},
          Heap.Extends _ m0 →
          ObsFn Obs.W "KernelCheck::primary_parent_block_of" [xrb, xb] m0 vP m1 csP →
          (∀ cl ∈ csP, cl ∈ calls) → vP = xb := by
        intro m0 m1 vP csP extP evP hsubP
        match Obs.«KernelCheck::primary_parent_block_of».obs evP with
        | .Muts (cs12 := csL) (ev14 := evL) (ev94 := evFirst) (hc134 := hcsP) .. =>
          have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsubP cl (by rw [hcsP]; simp [hcl])
          have hnil := hloadEmpty extP evL hsubL
          match Obs.«KernelCheck::first_recr_parent_block».obs evFirst with
          | .Nil (he21 := hr) .. => exact hr
          | .Cons_Recr_Rec_Induct (ld12 := ld) .. | .Cons_Recr_Rec_other (ld12 := ld) ..
          | .Cons_Recr_other (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
            obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hnil ld
            cases he
        | .other (he140 := hr) .. => exact hr
      match Obs.«KernelCheck::build_flat_block».obs ev_flat with
      | .n0 (cs12 := csP) (cs42 := csO) (ev14 := evP) (ev44 := evO) (ev75 := evM)
          (he89 := hr) (he90 := hh) (hc91 := hcsF) .. =>
        have hsubP : ∀ cl ∈ csP, cl ∈ calls := fun cl hcl => hsubF cl (by rw [hcsF]; simp [hcl])
        have hsubO : ∀ cl ∈ csO, cl ∈ calls := fun cl hcl => hsubF cl (by rw [hcsF]; simp [hcl])
        have hp := hprim (Heap.Extends.refl _) evP hsubP
        subst hp
        obtain ⟨xs, hlen, hltB, hxs⟩ := hflatOrig evP.heap_extends evO hsubO
        rw [hr, hh]
        exact ⟨xs, hlen, hltB,
          RepLinkedList.mono (fun _ _ _ _ _ _ => trivial) evM.heap_extends hxs⟩
      | .other (cs12 := csP) (cs42 := csO) (cs99 := csD) (ev14 := evP) (ev44 := evO)
          (ev75 := evM) (ev101 := evD) (hc134 := hcsF) .. =>
        have hsubP : ∀ cl ∈ csP, cl ∈ calls := fun cl hcl => hsubF cl (by rw [hcsF]; simp [hcl])
        have hsubO : ∀ cl ∈ csO, cl ∈ calls := fun cl hcl => hsubF cl (by rw [hcsF]; simp [hcl])
        have hsubD : ∀ cl ∈ csD, cl ∈ calls := fun cl hcl => hsubF cl (by rw [hcsF]; simp [hcl])
        have hp := hprim (Heap.Extends.refl _) evP hsubP
        subst hp
        obtain ⟨xs, hlen, hltB, hxs⟩ := hflatOrig evP.heap_extends evO hsubO
        have ext_D : Heap.Extends _ _ := evP.heap_extends.trans (evO.heap_extends.trans evM.heap_extends)
        match Obs.«KernelCheck::detect_aux_from_recrs_ex».obs evD with
        | .Muts (cs12 := csL) (ev14 := evL) (ev94 := evAux) (hc150 := hcsD) .. =>
          have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsubD cl (by rw [hcsD]; simp [hcl])
          have hnil := hloadEmpty ext_D evL hsubL
          match Obs.«KernelCheck::aux_from_recrs_walk_ex».obs evAux with
          | .Nil (he21 := hr) (he22 := hh) .. =>
            rw [hr, hh]
            exact ⟨xs, hlen, hltB, RepLinkedList.mono (fun _ _ _ _ _ _ => trivial)
              (evM.heap_extends.trans evL.heap_extends) hxs⟩
          | .Cons_Recr_n0_other_other_other_other (ld12 := ld) ..
          | .Cons_Recr_other_bind_other_bind_bind_n1 (ld12 := ld) ..
          | .Cons_Recr_other_bind_other_bind_bind_other (ld12 := ld) ..
          | .Cons_other (ld12 := ld) .. =>
            obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hnil ld
            cases he
        | .other (ev14 := evL) (he156 := hr) (he157 := hh) .. =>
          rw [hr, hh]
          exact ⟨xs, hlen, hltB, RepLinkedList.mono (fun _ _ _ _ _ _ => trivial)
            (evM.heap_extends.trans evL.heap_extends) hxs⟩
    obtain ⟨xs, hlen, hltB, hxs⟩ := hflatLen
    have hxs' : RepList (Instance.mk "Lists::Node" [flatEntryTy]).symbol
        (fun _ _ _ => True) _ xs _ := by
      rw [flatListEnum_eq]
      exact RepLinkedList.mono (fun _ _ _ _ _ _ => trivial) ev1246.heap_extends hxs
    have evLen' : ObsFn Obs.W (Instance.mk "Lists::length" [flatEntryTy]).symbol
        [_] _ _ _ _ := by
      rw [Obs.Names.«Lists::length<(&[Field; 32], Field, &Lists::Node<&KernelTypes::KExprNode>, &Lists::Node<&KernelTypes::KLevelNode>)>».symbol]
      exact ev_flen
    obtain ⟨hflen, -⟩ := Lib.Lists.length_spec evLen' hxs'
    rw [hflen, hlen] at op_sub
    simp only [evalBinOp, zero_sub, Except.ok.injEq] at op_sub
    have hneg0 : (-(msB.size : F)) = 0 := Value.field.inj (op_sub.trans hsub0)
    have hsz0 : ((msB.size : Nat) : F) = ((0 : Nat) : F) := by
      rw [Nat.cast_zero]
      exact neg_eq_zero.mp hneg0
    have hzero := Core.ModeledAux.natCast_inj_lt
      (Nat.lt_trans hltB (by decide)) (by decide) hsz0
    omega

/-! ## Native refusal for recursor blocks and projections -/

/-- **`KernelCheck::muts_has_kind`** on a represented member list tests for `Indc` (`0`),
`Defn` (`1`), or `Recr` (`2`). -/
theorem muts_has_kind_spec :
    ∀ (ms : List Ixon.MutConst) {k : Nat} {x_members r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      RepList L1.mutConstListEnum L1.RepMutConst h ms x_members →
      ObsFn Obs.W "KernelCheck::muts_has_kind" [x_members, .field (k : F)] h r h' cs →
      h' = h ∧
      (k = 0 → (r = .field 1 ↔ ∃ ind, .indc ind ∈ ms) ∧ (r = .field 0 ↔ ∀ ind, .indc ind ∉ ms)) ∧
      (k = 2 → (r = .field 1 ↔ ∃ rc, .recr rc ∈ ms) ∧ (r = .field 0 ↔ ∀ rc, .recr rc ∉ ms)) := by
  intro ms
  induction ms with
  | nil =>
    intro k x_members r h h' cs hrep ev
    match Obs.«KernelCheck::muts_has_kind».obs ev with
    | .Nil (he20 := hr) (he21 := hh) .. =>
      subst hr hh
      refine ⟨rfl, fun _ => ⟨by simp [zero_ne_one], by simp⟩,
        fun _ => ⟨by simp [zero_ne_one], by simp⟩⟩
    | .Cons_n1 (ld12 := ld) .. | .Cons_other (ld12 := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load hrep ld
      cases he
  | cons m rest ih =>
    intro k x_members r h h' cs hrep ev
    match Obs.«KernelCheck::muts_has_kind».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrep ld
    | .Cons_n1 (ld12 := ld) (sg169 := sg) (he184 := hr) (he185 := hh) .. =>
      obtain ⟨m', rest', he, hm, -⟩ := Lib.rep_cons_of_load hrep ld
      injection he with h1 h2
      subst h1 h2 hr
      match sg with
      | .Indc_n0 (hv54 := hmv) (hv75 := hk0) (he77 := hsg) .. =>
        rw [hh, hsg]
        cases m with
        | indc ind =>
          refine ⟨rfl, fun _ => ⟨⟨fun _ => ⟨ind, List.mem_cons_self⟩, fun _ => rfl⟩,
              ⟨fun h => absurd (Value.field.inj h) one_ne_zero,
               fun h => absurd List.mem_cons_self (h ind)⟩⟩,
            fun hk2 => ?_⟩
          rw [hk2] at hk0
          exact absurd (Value.field.inj hk0) (by decide)
        | defn d => obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
        | recr rc => obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
      | .Defn_n1 (hv112 := hk1) (he114 := hsg) .. =>
        refine ⟨hh.trans hsg, fun hk0 => ?_, fun hk2 => ?_⟩
        · rw [hk0] at hk1; exact absurd (Value.field.inj hk1) (by decide)
        · rw [hk2] at hk1; exact absurd (Value.field.inj hk1) (by decide)
      | .Recr_n2 (hv128 := hmv) (hv149 := hk2) (he151 := hsg) .. =>
        rw [hh, hsg]
        cases m with
        | recr rc =>
          refine ⟨rfl, fun hk0 => ?_,
            fun _ => ⟨⟨fun _ => ⟨rc, List.mem_cons_self⟩, fun _ => rfl⟩,
              ⟨fun h => absurd (Value.field.inj h) one_ne_zero,
               fun h => absurd List.mem_cons_self (h rc)⟩⟩⟩
          rw [hk0] at hk2
          exact absurd (Value.field.inj hk2) (by decide)
        | defn d => obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
        | indc ind => obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
      | .Indc_other (he83 := h01) .. | .Defn_other (he120 := h01) ..
      | .Recr_other (he157 := h01) .. =>
        exact absurd (Value.field.inj h01) one_ne_zero
    | .Cons_other (ld12 := ld) (sg169 := sg) (hne187 := hne) (ev196 := evRec) .. =>
      obtain ⟨m', rest', he, hm, hrest⟩ := Lib.rep_cons_of_load hrep ld
      injection he with h1 h2
      subst h1 h2
      have hseg : _ = h ∧ (k = 0 → ∀ ind, m ≠ .indc ind) ∧ (k = 2 → ∀ rc, m ≠ .recr rc) := by
        match sg with
        | .Indc_n0 (he76 := h1) .. | .Defn_n1 (he113 := h1) .. | .Recr_n2 (he150 := h1) .. =>
          exact absurd h1 hne
        | .Indc_other (hv54 := hmv) (hne79 := hne0) (he84 := hsg) .. =>
          refine ⟨hsg, fun hk0 => ?_, fun _ rc hrc => ?_⟩
          · rw [hk0] at hne0; exact absurd rfl hne0
          · rw [hrc] at hm; obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
        | .Defn_other (hv91 := hmv) (he121 := hsg) .. =>
          refine ⟨hsg, fun _ ind hind => ?_, fun _ rc hrc => ?_⟩
          · rw [hind] at hm; obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
          · rw [hrc] at hm; obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
        | .Recr_other (hv128 := hmv) (hne153 := hne2) (he158 := hsg) .. =>
          refine ⟨hsg, fun _ ind hind => ?_, fun hk2 => ?_⟩
          · rw [hind] at hm; obtain ⟨_, h', -⟩ := hm; rw [hmv] at h'; simp at h'
          · rw [hk2] at hne2; exact absurd rfl hne2
      obtain ⟨hsg, hni, hnr⟩ := hseg
      rw [hsg] at evRec
      obtain ⟨hh, h0, h2⟩ := ih hrest evRec
      refine ⟨hh, fun hk0 => ?_, fun hk2 => ?_⟩
      · obtain ⟨ha, hb⟩ := h0 hk0
        refine ⟨ha.trans ⟨fun ⟨ind, hi⟩ => ⟨ind, List.mem_cons_of_mem _ hi⟩,
            fun ⟨ind, hi⟩ => by
              rcases List.mem_cons.mp hi with rfl | hi'
              · exact absurd rfl (hni hk0 ind)
              · exact ⟨ind, hi'⟩⟩,
          hb.trans ⟨fun h ind hi => by
              rcases List.mem_cons.mp hi with rfl | hi'
              · exact hni hk0 ind rfl
              · exact h ind hi',
            fun h ind hi => h ind (List.mem_cons_of_mem _ hi)⟩⟩
      · obtain ⟨ha, hb⟩ := h2 hk2
        refine ⟨ha.trans ⟨fun ⟨rc, hr⟩ => ⟨rc, List.mem_cons_of_mem _ hr⟩,
            fun ⟨rc, hr⟩ => by
              rcases List.mem_cons.mp hr with rfl | hr'
              · exact absurd rfl (hnr hk2 rc)
              · exact ⟨rc, hr'⟩⟩,
          hb.trans ⟨fun h rc hr => by
              rcases List.mem_cons.mp hr with rfl | hr'
              · exact hnr hk2 rc rfl
              · exact h rc hr',
            fun h rc hr => h rc (List.mem_cons_of_mem _ hr)⟩⟩

/-- **`KernelCheck::check_block_member_kinds` on a `Muts` block containing a recursor**: the
block contains no inductive member. -/
theorem check_block_member_kinds_recr_no_indc {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {A : _root_.Address} {cA : Ixon.Constant}
    {ms : Array Ixon.MutConst} {x_blk r : SourceValue F} {h h' : Heap F}
    (ha : Core.S0.addr h x_blk A) (hcA : recordOf E₀ A = some cA) (hms : cA.info = .muts ms)
    (hhasRec : ∃ rc, .recr rc ∈ ms.toList)
    (ev : ObsFn Obs.W "KernelCheck::check_block_member_kinds" [x_blk] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) : ∀ ind, .indc ind ∉ ms.toList := by
  obtain ⟨ab, hab, rfl⟩ := ha
  match Obs.«KernelCheck::check_block_member_kinds».obs ev with
  | .Muts (cs12 := csL) (ev14 := evL) (ev102 := e1) (ev151 := e2) (ev187 := e3)
      (ev301 := e4) (ev356 := evInd) (ev377 := evRec) (op350 := op) (heq399 := heq0)
      (hc404 := hcs) .. =>
    have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨c', ms', hbl, hrep⟩ := Claim.load_block_head hab evL
    have ec := ((hbl.mono hsubL).record hS hcA).1
    subst ec
    have ems : ms' = ms := Ixon.ConstantInfo.muts.inj (hbl.info.symm.trans hms)
    subst ems
    have ext : Heap.Extends _ _ :=
      e1.heap_extends.trans (e2.heap_extends.trans (e3.heap_extends.trans e4.heap_extends))
    have hrep1 := RepLinkedList.mono L1.repMutConst_heapMono₂ ext hrep
    have evInd' : ObsFn Obs.W "KernelCheck::muts_has_kind" [_, .field ((0 : Nat) : F)] _ _ _ _ :=
      evInd
    obtain ⟨hmI, h0, -⟩ := muts_has_kind_spec ms'.toList hrep1 evInd'
    rw [hmI] at evRec
    have evRec' : ObsFn Obs.W "KernelCheck::muts_has_kind" [_, .field ((2 : Nat) : F)] _ _ _ _ :=
      evRec
    obtain ⟨-, -, h2⟩ := muts_has_kind_spec ms'.toList hrep1 evRec'
    have hy1 := (h2 rfl).1.mpr hhasRec
    intro ind hind
    have hx1 := (h0 rfl).1.mpr ⟨ind, hind⟩
    rw [hx1, hy1] at op
    simp only [evalBinOp, mul_one, Except.ok.injEq] at op
    exact one_ne_zero (Value.field.inj (op.trans heq0))
  | .other (cs12 := csL) (ev14 := evL) (hne405 := hne) (hc413 := hcs) .. =>
    have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS hab evL hsubL hcA hms
    exact absurd hxm (hne [msPtr] rfl)

/-- **`KernelCheck::is_muts_block` answers `1` on a `Muts` block of `E₀`.** -/
theorem is_muts_block_of_muts {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {ab : Bytes.Address} {x_addr r : SourceValue F}
    {h h' : Heap F} (ha : Bytes.RepAddressRef Core.addrTy h ab x_addr)
    {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : recordOf E₀ (Core.ixAddr ab) = some c) (hms : c.info = .muts ms)
    (ev : ObsFn Obs.W "KernelCheck::is_muts_block" [x_addr] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) : r = .field 1 := by
  match Obs.«KernelCheck::is_muts_block».obs ev with
  | .Muts (he90 := hr) .. => exact hr
  | .other (cs12 := csL) (ev14 := evL) (hne93 := hne) (hc99 := hcs) .. =>
    have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨msPtr, hxm, -, -⟩ := Decl.load_block_info hS ha evL hsubL hc hms
    exact absurd hxm (hne [msPtr] rfl)

/-- **`KernelCheck::check_const` on a recursor belonging to a `Muts` block takes the modeled arm**:
`check_block_member_kinds` excludes inductive members from `A`, so `check_recursor_member`
cannot match `A` against the parent inductive's `Muts` block and fails on the native arm. -/
theorem check_const_rec_block_modeled_family {calls cs : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀) (hstep : RunStepStores calls t E₀)
    {x_rc x_addr x_rec_block nl ty np ni nm nmin rls kf uns ridx r : SourceValue F}
    {h h' : Heap F} {x A : _root_.Address} {cA : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hrc : Claim.RCLimRep t bAddr lim h x_rc) (ha : Core.S0.addr h x_addr x)
    (hblk : Core.S0.addr h x_rec_block A) (hcA : recordOf E₀ A = some cA)
    (hms : cA.info = .muts ms) (hhasRec : ∃ rc, .recr rc ∈ ms.toList)
    (ev : ObsFn Obs.W "KernelCheck::check_const"
      [x_rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [nl, ty, np, ni, nm, nmin, rls, kf, uns, x_rec_block, ridx], x_addr] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (family : _root_.Address) (cs' : List (Call F)) (h_rf m_rf : Heap F)
      (ap_rf fb_rf : SourceValue F) (cs_rf : List (Call F)),
      ModeledRouteAt calls family ∧
      FamilyCallAtLim calls bAddr t family A lim cs' ∧ (∀ cl ∈ cs', cl ∈ cs) ∧
      Core.S0.addr h_rf ap_rf x ∧ Core.S0.addr m_rf fb_rf family ∧
      ObsFn Obs.W "KernelModeled::rec_family_block" [ap_rf] h_rf fb_rf m_rf cs_rf ∧
      (∀ cl ∈ cs_rf, cl ∈ cs) := by
  match Obs.«KernelCheck::check_const».obs ev with
  | .Axiom_n1 (hv37 := shape) .. | .Axiom_other_n0 (hv37 := shape) ..
  | .Axiom_other_other (hv37 := shape) .. | .Defn (hv269 := shape) ..
  | .Thm (hv526 := shape) .. | .Opaque (hv825 := shape) .. | .Quot (hv1076 := shape) ..
  | .Induct_n0 (hv1240 := shape) .. | .Induct_other_n0 (hv1240 := shape) ..
  | .Induct_other_other (hv1240 := shape) .. | .Ctor_n0_n0 (hv1989 := shape) ..
  | .Ctor_n0_other (hv1989 := shape) .. | .Ctor_other_n0 (hv1989 := shape) ..
  | .Ctor_other_other (hv1989 := shape) .. =>
    injection shape with _ tag _
    exact absurd tag (by decide)
  | .Rec_n0 (m2789 := m2789) (m2857 := m2857) (cs2940 := csKinds) (cs3066 := csMem)
      (ev14 := e1) (hv2727 := shape) (ev2801 := e2) (hm2865 := hmnil) (ev2838 := e3)
      (ev2882 := e4) (ev2912 := e5) (ev2942 := evKinds) (ev2964 := evRf) (ev2986 := evMod)
      (ev3068 := evMem) (hc3093 := hcs) .. =>
    exfalso
    injection shape with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl, -⟩ := fields
    have ext_nil : Heap.Extends m2789 m2857 := by rw [hmnil]; exact Heap.Extends.snoc _ _
    have ext_k : Heap.Extends h _ :=
      e1.heap_extends.trans (e2.heap_extends.trans (ext_nil.trans (e3.heap_extends.trans
        (e4.heap_extends.trans e5.heap_extends))))
    have hnoInd : ∀ ind, .indc ind ∉ ms.toList :=
      check_block_member_kinds_recr_no_indc hC.runStore (Core.S0.addr_mono ext_k hblk)
        hcA hms hhasRec evKinds (fun cl hcl => hsub cl (by rw [hcs]; simp [hcl]))
    have ext_m : Heap.Extends h _ :=
      ext_k.trans (evKinds.heap_extends.trans (evRf.heap_extends.trans evMod.heap_extends))
    have hsubMem : ∀ cl ∈ csMem, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    match Obs.«KernelCheck::check_recursor_member».obs evMem with
    | .run (cs140 := csCi) (cs276 := csM1) (cs290 := csM2) (hv15 := hv15) (ev85 := evP)
        (ev142 := evCi) (ld136 := ldInd) (ev233 := evBM) (ev278 := evM1) (ev292 := evM2)
        (op272 := opMul1) (ev314 := evEq) (op308 := opSub) (op264 := opMul2)
        (heq357 := heq0) (hc898 := hcsMem) .. =>
      injection hv15 with _ _ f2
      simp only [List.cons.injEq, and_true] at f2
      obtain ⟨-, -, -, -, -, -, -, -, -, rfl, -⟩ := f2
      have hsubCi : ∀ cl ∈ csCi, cl ∈ calls := fun cl hcl => hsubMem cl (by rw [hcsMem]; simp [hcl])
      have hsubM1 : ∀ cl ∈ csM1, cl ∈ calls := fun cl hcl => hsubMem cl (by rw [hcsMem]; simp [hcl])
      have hsubM2 : ∀ cl ∈ csM2, cl ∈ calls := fun cl hcl => hsubMem cl (by rw [hcsMem]; simp [hcl])
      obtain ⟨bP, rawP, cP, ipP, cbP, msP, indP, hbP, -, -, -, -, -, hblP, hmemP⟩ :=
        Claim.get_ci_induct_head evCi ldInd
      obtain ⟨hrecP, hmsP⟩ := (hblP.mono hsubCi).stored hC.hashedStored
      have hneAP : A ≠ Core.ixAddr bP := by
        intro e
        rw [← e] at hrecP
        have ec := Option.some.inj (hrecP.symm.trans hcA)
        subst ec
        have ems := Ixon.ConstantInfo.muts.inj (hmsP.symm.trans hms)
        subst ems
        exact hnoInd indP (List.mem_of_getElem? hmemP)
      obtain ⟨bA, hbA, hixA⟩ := hblk
      have ext_m1 : Heap.Extends h _ :=
        ext_m.trans (evP.heap_extends.trans (evCi.heap_extends.trans evBM.heap_extends))
      have hbA1 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext_m1 hbA
      have hm1 := is_muts_block_of_muts hC.runStore hbA1 (by rw [hixA]; exact hcA) hms evM1 hsubM1
      have hbP2 := Bytes.repAddressRef_heapMono₂ Core.addrTy
        (evBM.heap_extends.trans evM1.heap_extends) hbP
      have hm2 := is_muts_block_of_muts hC.runStore hbP2 hrecP hmsP evM2 hsubM2
      have hbA3 := Bytes.repAddressRef_heapMono₂ Core.addrTy
        (evM1.heap_extends.trans evM2.heap_extends) hbA1
      have hbP3 := Bytes.repAddressRef_heapMono₂ Core.addrTy evM2.heap_extends hbP2
      obtain ⟨heq_v, -⟩ := Lib.address_eq_spec evEq hbA3 hbP3
      have hneB : bA ≠ bP := fun e => hneAP (by rw [← hixA, e])
      simp [hneB] at heq_v
      rw [hm1, hm2] at opMul1
      simp only [evalBinOp, mul_one, Except.ok.injEq] at opMul1
      subst opMul1
      rw [heq_v] at opSub
      simp only [evalBinOp, sub_zero, Except.ok.injEq] at opSub
      subst opSub
      simp only [evalBinOp, mul_one, Except.ok.injEq] at opMul2
      exact one_ne_zero (Value.field.inj (opMul2.trans heq0))
  | .Rec_other (m2789 := m2789) (m2857 := m2857) (v2951 := fb) (cs2962 := csRf)
      (cs2984 := csMod) (cs3155 := csFam) (ev14 := e1) (hv2727 := shape) (ev2801 := e2)
      (hm2865 := hmnil) (ev2838 := e3) (ev2882 := e4) (ev2912 := e5) (ev2942 := evKinds)
      (ev2964 := evRf) (ev2986 := evMod) (hne3094 := hne0) (ev3157 := evFam)
      (hc3182 := hcs) .. =>
    injection shape with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨-, -, -, -, -, -, -, -, -, rfl, -⟩ := fields
    have ext_nil : Heap.Extends m2789 m2857 := by rw [hmnil]; exact Heap.Extends.snoc _ _
    have ext_rf : Heap.Extends h _ :=
      e1.heap_extends.trans (e2.heap_extends.trans (ext_nil.trans (e3.heap_extends.trans
        (e4.heap_extends.trans (e5.heap_extends.trans evKinds.heap_extends)))))
    have ext_mod : Heap.Extends h _ := ext_rf.trans evRf.heap_extends
    have ext_fam : Heap.Extends h _ := ext_mod.trans evMod.heap_extends
    have hsubRf : ∀ cl ∈ csRf, cl ∈ cs := fun cl hcl => by rw [hcs]; simp [hcl]
    have hsubMod : ∀ cl ∈ csMod, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubFam : ∀ cl ∈ csFam, cl ∈ cs := fun cl hcl => by rw [hcs]; simp [hcl]
    match Obs.«KernelModeled::rec_family_block».obs evRf with
    | .run (ev268 := evInd) (ld262 := ldInd) (he331 := hfb) (he332 := hhe) .. =>
      obtain ⟨bF, -, -, -, -, -, -, hbF, -⟩ := Claim.get_ci_induct_head evInd ldInd
      rw [← hfb, ← hhe] at hbF
      have hmod := modeledRouteAt_of_obs_ne_zero hC hstep evMod hsubMod hbF hne0
      have hfc : FamilyCallAtLim calls bAddr t (Core.ixAddr bF) A lim csFam :=
        ⟨_, _, x_rc, fb, x_rec_block, r, hrc.mono ext_fam,
          ⟨bF, Bytes.repAddressRef_heapMono₂ Core.addrTy evMod.heap_extends hbF, rfl⟩,
          Core.S0.addr_mono ext_fam hblk, evFam,
          hsub _ (by rw [hcs]; simp), fun cl hcl => hsub cl (hsubFam cl hcl)⟩
      exact ⟨Core.ixAddr bF, csFam, _, _, x_addr, fb, csRf, hmod, hfc, hsubFam,
        Core.S0.addr_mono ext_rf ha, ⟨bF, hbF, rfl⟩, evRf, hsubRf⟩

/-- **A checked recursor projection (`RPrj`) triggers a modeled family check of its recursor
block** at the same limit, with its family block on the modeled route. -/
theorem rprj_checked_modeled_family {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀) (hstep : RunStepStores calls t E₀)
    {x : _root_.Address} {cx : Ixon.Constant} {rp : Ixon.RecursorProj}
    (hchk : Claim.CheckedLimAt calls bAddr t x lim) (hc : recordOf E₀ x = some cx)
    (hrp : cx.info = .rPrj rp) :
    ∃ (family : _root_.Address) (cs' : List (Call F)) (h_rf m_rf : Heap F)
      (ap_rf fb_rf : SourceValue F) (cs_rf : List (Call F)),
      ModeledRouteAt calls family ∧
      FamilyCallAtLim calls bAddr t family rp.block lim cs' ∧
      Core.S0.addr h_rf ap_rf x ∧ Core.S0.addr m_rf fb_rf family ∧
      ObsFn Obs.W "KernelModeled::rec_family_block" [ap_rf] h_rf fb_rf m_rf cs_rf ∧
      (∀ cl ∈ cs_rf, cl ∈ calls) := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    -, hrc_m, ⟨ab, hab, rfl⟩, ha_m, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨raw, c', -, hh, hba, hx, -, hhead⟩ := Claim.get_ci_head hab ev_ld
  have ec : c' = cx := hC.runStore.record_eq ((hC.runStore.recordOf_eq_recordAt _).symm.trans hc)
    (Core.hashed_mono hsub_ld hh) hba hx
  subst ec
  obtain ⟨cb, ms, rcr, hbl, hmem, nl, ty, np, ni, nm, nmin, rules, k, x_blk, b, hldR, hb_rep,
    hb_eq⟩ := hhead.rPrj rp.idx rp.block hrp
  rw [hld] at hldR
  injection hldR with hv
  subst hv
  obtain ⟨hrecB, hmsB⟩ := (hbl.mono hsub_ld).stored hC.hashedStored
  obtain ⟨family, cs', h_rf, m_rf, ap_rf, fb_rf, cs_rf, hmod, hfc, -, ha_rf, hfb_rf, ev_rf,
    hsub_rf⟩ :=
    check_const_rec_block_modeled_family hC hstep hrc_m ha_m ⟨b, hb_rep, hb_eq⟩ hrecB hmsB
      ⟨rcr, List.mem_of_getElem? hmem⟩ ev_chk hsub_chk
  exact ⟨family, cs', h_rf, m_rf, ap_rf, fb_rf, cs_rf, hmod, hfc, ha_rf, hfb_rf, ev_rf,
    fun cl hcl => hsub_chk cl (hsub_rf cl hcl)⟩

/-- **A checked recursor member of a `Muts` block triggers a modeled family check of that block**
at the same limit, with its family block on the modeled route. -/
theorem recBlock_memberChecked_modeled_family {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat}
    (hC : CollisionFreeRun calls E₀) (hstep : RunStepStores calls t E₀)
    {A : _root_.Address} {cA : Ixon.Constant} {ms : Array Ixon.MutConst} {k : Nat}
    {rcr : Ixon.Recursor} (hcA : recordOf E₀ A = some cA) (hms : cA.info = .muts ms)
    (hk : ms.toList[((k : F)).val]? = some (.recr rcr))
    (hchk : Claim.MemberCheckedLimAt calls bAddr t A ms k lim) :
    ∃ (family : _root_.Address) (cs' : List (Call F)),
      ModeledRouteAt calls family ∧
      FamilyCallAtLim calls bAddr t family A lim cs' := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, ⟨b', hb', rfl⟩, ev_pa, -, hsub_pa,
    -, hrc_m, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨-, -, -, mc, a', hget', ha', hproj, hhashed⟩ :=
    L1.projection_addr_hashed_spec hmem hb' ev_pa
  obtain ⟨iv, hiv⟩ : ∃ iv, ((k : F)).val = iv := ⟨_, rfl⟩
  rw [hiv] at hget' hproj hhashed hk
  have emc : mc = .recr rcr := Option.some.inj (hget'.symm.trans hk)
  subst emc
  obtain ⟨raw, cp, hsz, hh, hba, hx, -, hhead⟩ := Claim.get_ci_head ha' ev_ld
  have hX : Address.blake3Pure (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.recr rcr), #[], #[], #[], #[]⟩) =
      Core.ixAddr a' := hproj.symm
  have hraw : raw = Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.recr rcr), #[], #[], #[], #[]⟩ :=
    hC.runStore.hashed_inj (Core.hashed_mono hsub_ld hh) (Core.hashed_mono hsub_pa hhashed)
      (hba.trans hX.symm)
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.recr rcr),
      #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF :=
    L1.projConstant_wireWF_rPrj iv.toUInt64 b'
  rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hx
  injection hx with hcp
  subst hcp
  obtain ⟨cb', ms', rc', hbl, hmem', nl, ty, np, ni, nm, nmin, rules, kf, x_blk, b, hldR, hb_rep,
    hb_eq⟩ := hhead.rPrj _ _ rfl
  rw [hld] at hldR
  injection hldR with hv
  subst hv
  have hcb := ((hbl.mono hsub_ld).record hC.runStore hcA).1
  subst hcb
  have hms' := Ixon.ConstantInfo.muts.inj (hbl.info.symm.trans hms)
  subst hms'
  have ha_m : Core.S0.addr m_chk ap (Core.ixAddr a') :=
    ⟨a', Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ld.heap_extends ha', rfl⟩
  obtain ⟨family, cs', -, -, -, -, -, hmod, hfc, -⟩ :=
    check_const_rec_block_modeled_family hC hstep hrc_m ha_m ⟨b, hb_rep, hb_eq⟩ hcA hms
      ⟨rc', List.mem_of_getElem? hmem'⟩ ev_chk hsub_chk
  exact ⟨family, cs', hmod, hfc⟩

/-! ## Pure carrier-head reading over `RawConvExpr` -/

/-- Unroll leading `.share` nodes in an `Ixon.Expr` up to `bound`. -/
def ixonUnshare (sharing : List Ixon.Expr) : Nat → Ixon.Expr → Option (Nat × Ixon.Expr)
  | bound, .share idx =>
    if _h : idx.toNat < bound then
      match sharing[idx.toNat]? with
      | some s => ixonUnshare sharing idx.toNat s
      | none => none
    else none
  | bound, e => some (bound, e)

/-- Peel `m` leading `.all` binders from an `Ixon.Expr` (unrolling `.share`). -/
def ixonPeelForalls (sharing : List Ixon.Expr) : Nat → Nat → Ixon.Expr → Option (Nat × Ixon.Expr)
  | 0, bound, e => some (bound, e)
  | m + 1, bound, e =>
    match ixonUnshare sharing bound e with
    | some (b', .all _ body) => ixonPeelForalls sharing m b' body
    | _ => none

/-- Take the domain of the last leading `.all` binder (mirroring `last_binder_dom`). -/
def ixonLastBinderDom (sharing : List Ixon.Expr) : Nat → Nat → Ixon.Expr → Option (Nat × Ixon.Expr)
  | 0, _, _ => none
  | fuel + 1, bound, e =>
    match ixonUnshare sharing bound e with
    | some (b', .all dom body) =>
      match ixonUnshare sharing b' body with
      | some (b'', .all d2 bo2) => ixonLastBinderDom sharing fuel b'' (.all d2 bo2)
      | some _ => some (b', dom)
      | none => none
    | _ => none

/-- Walk left down `.app` spine to a `.ref rIdx _` head index. -/
def ixonAppHeadRef (sharing : List Ixon.Expr) : Nat → Nat → Ixon.Expr → Option Nat
  | 0, _, _ => none
  | fuel + 1, bound, e =>
    match ixonUnshare sharing bound e with
    | some (b', .app f _) => ixonAppHeadRef sharing fuel b' f
    | some (_, .ref rIdx _) => some rIdx.toNat
    | _ => none

private theorem ixonUnshare_rawConv {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F} :
    ∀ {bound : Nat} {e : Ixon.Expr} {p : SourceValue F},
      L1.RawConvExpr refs [] univs sharing blobs h bound e p →
      ∃ b' e', ixonUnshare sharing bound e = some (b', e') ∧
        (∀ idx, e' ≠ .share idx) ∧
        (∀ i ∈ exprRefIdxs e', i ∈ exprRefIdxs e ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s) ∧
        L1.RawConvExpr refs [] univs sharing blobs h b' e' p := by
  intro bound e p hraw
  induction hraw with
  | share hidx hsh _ ih =>
    obtain ⟨b', e', hu, hns, href, hr'⟩ := ih
    refine ⟨b', e', ?_, hns, ?_, hr'⟩
    · simp only [ixonUnshare, hidx, ↓reduceDIte, hsh]
      exact hu
    · intro i hi
      rcases href i hi with h1 | h2
      · exact Or.inr ⟨_, List.mem_of_getElem? hsh, h1⟩
      · exact Or.inr h2
  | var hidx cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi, L1.RawConvExpr.var hidx cell⟩
  | sort huIdx hu rl cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi,
      L1.RawConvExpr.sort huIdx hu rl cell⟩
  | ref hrIdx href hd ra hls rls cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi,
      L1.RawConvExpr.ref hrIdx href hd ra hls rls cell⟩
  | recur _ hrec _ _ _ _ _ => simp at hrec
  | prj htIdx hfIdx href hd ra rin cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi,
      L1.RawConvExpr.prj htIdx hfIdx href hd ra rin cell⟩
  | str hbIdx href hmem rbs hs cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi,
      L1.RawConvExpr.str hbIdx href hmem rbs hs cell⟩
  | nat hbIdx href hmem hcanon rlimbs hlast hval cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi,
      L1.RawConvExpr.nat hbIdx href hmem hcanon rlimbs hlast hval cell⟩
  | app rf ra cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi, L1.RawConvExpr.app rf ra cell⟩
  | lam rl rt rb cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi, L1.RawConvExpr.lam rl rt rb cell⟩
  | all rl rt rb cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi, L1.RawConvExpr.all rl rt rb cell⟩
  | letE rt rv rb cell =>
    exact ⟨_, _, rfl, fun _ h => nomatch h, fun _ hi => Or.inl hi,
      L1.RawConvExpr.letE rt rv rb cell⟩

private theorem rawConv_forall_of_load {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p d b m : SourceValue F}
    (hraw : L1.RawConvExpr refs [] univs sharing blobs h bound e p)
    (hns : ∀ idx, e ≠ .share idx)
    (hld : loadValue h p = .ok (.construct Core.kexprEnum "Forall" [d, b, m])) :
    ∃ ty body, e = .all ty body ∧
      L1.RawConvExpr refs [] univs sharing blobs h bound ty d ∧
      L1.RawConvExpr refs [] univs sharing blobs h bound body b := by
  cases hraw with
  | all _ rt rb cell =>
    rw [Core.loadValue_enum_cell cell] at hld
    injection hld with hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hd, hb, -⟩ := hargs
    subst hd hb
    exact ⟨_, _, rfl, rt, rb⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | recur _ hrec _ _ _ _ _ => simp at hrec
  | var _ cell | sort _ _ _ cell | ref _ _ _ _ _ _ cell | prj _ _ _ _ _ _ cell
  | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell | app _ _ cell | lam _ _ _ cell
  | letE _ _ _ cell =>
    exact (Core.load_cell_ne cell hld (by decide)).elim

private theorem rawConv_app_of_load {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p f a : SourceValue F}
    (hraw : L1.RawConvExpr refs [] univs sharing blobs h bound e p)
    (hns : ∀ idx, e ≠ .share idx)
    (hld : loadValue h p = .ok (.construct Core.kexprEnum "App" [f, a])) :
    ∃ ef ea, e = .app ef ea ∧
      L1.RawConvExpr refs [] univs sharing blobs h bound ef f ∧
      L1.RawConvExpr refs [] univs sharing blobs h bound ea a := by
  cases hraw with
  | app rf ra cell =>
    rw [Core.loadValue_enum_cell cell] at hld
    injection hld with hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hf, ha⟩ := hargs
    subst hf ha
    exact ⟨_, _, rfl, rf, ra⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | recur _ hrec _ _ _ _ _ => simp at hrec
  | var _ cell | sort _ _ _ cell | ref _ _ _ _ _ _ cell | prj _ _ _ _ _ _ cell
  | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell | all _ _ _ cell | lam _ _ _ cell
  | letE _ _ _ cell =>
    exact (Core.load_cell_ne cell hld (by decide)).elim

private theorem rawConv_const_of_load {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p ap lsp : SourceValue F}
    (hraw : L1.RawConvExpr refs [] univs sharing blobs h bound e p)
    (hns : ∀ idx, e ≠ .share idx)
    (hld : loadValue h p = .ok (.construct Core.kexprEnum "Const" [ap, lsp])) :
    ∃ (rIdx : UInt64) (uIdxs : Array UInt64) (a : _root_.Address) (d : Bytes.Address),
      e = .ref rIdx uIdxs ∧ refs[rIdx.toNat]? = some a ∧ Core.ixAddr d = a ∧
      Bytes.RepAddressRef Core.addrTy h d ap := by
  cases hraw with
  | ref _ href hd ra _ _ cell =>
    rw [Core.loadValue_enum_cell cell] at hld
    injection hld with hv
    injection hv with _ _ hargs
    simp only [List.cons.injEq] at hargs
    obtain ⟨hap, -⟩ := hargs
    subst hap
    exact ⟨_, _, _, _, rfl, href, hd, ra⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | recur _ hrec _ _ _ _ _ => simp at hrec
  | var _ cell | sort _ _ _ cell | prj _ _ _ _ _ _ cell
  | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell | app _ _ cell | all _ _ _ cell
  | lam _ _ _ cell | letE _ _ _ cell =>
    exact (Core.load_cell_ne cell hld (by decide)).elim

private theorem rawConv_not_forall_of_ne {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p v : SourceValue F}
    (hraw : L1.RawConvExpr refs [] univs sharing blobs h bound e p)
    (hns : ∀ idx, e ≠ .share idx)
    (hld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct Core.kexprEnum "Forall" vs) :
    ∀ d b, e ≠ .all d b := by
  intro d b he
  subst he
  cases hraw with
  | all _ _ _ cell =>
    rw [Core.loadValue_enum_cell cell] at hld
    exact hne [_, _, _] rfl (Except.ok.inj hld).symm

private theorem rawConv_not_app_of_ne {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} {h : Heap F}
    {bound : Nat} {e : Ixon.Expr} {p v : SourceValue F}
    (hraw : L1.RawConvExpr refs [] univs sharing blobs h bound e p)
    (hns : ∀ idx, e ≠ .share idx)
    (hld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 2 → v ≠ .construct Core.kexprEnum "App" vs) :
    ∀ f a, e ≠ .app f a := by
  intro f a he
  subst he
  cases hraw with
  | app _ _ cell =>
    rw [Core.loadValue_enum_cell cell] at hld
    exact hne [_, _] rfl (Except.ok.inj hld).symm

private theorem peel_n_foralls_rawConv {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} :
    ∀ (m : Nat) {n : F} {bound : Nat} {e : Ixon.Expr} {x_e r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n = m →
      L1.RawConvExpr refs [] univs sharing blobs h bound e x_e →
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [x_e, .field n] h r h' cs →
      h' = h ∧ ∃ b' e', ixonPeelForalls sharing m bound e = some (b', e') ∧
        (∀ i ∈ exprRefIdxs e', i ∈ exprRefIdxs e ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s) ∧
        L1.RawConvExpr refs [] univs sharing blobs h b' e' r := by
  intro m
  induction m with
  | zero =>
    intro n bound e x_e r h h' cs hval hraw ev
    have hn0 : n = 0 := (ZMod.val_eq_zero n).mp hval
    subst hn0
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 _ hr hh _ =>
      subst hr hh
      exact ⟨rfl, bound, e, rfl, fun _ hi => Or.inl hi, hraw⟩
    | other _ _ _ _ _ hne19 _ _ _ _ => exact (hne19 rfl).elim
  | succ m ih =>
    intro n bound e x_e r h h' cs hval hraw ev
    have hn0 : n ≠ 0 := by intro h0; subst h0; simp at hval
    cases Obs.«KernelCheck::peel_n_foralls».obs ev with
    | n0 hv14 _ _ _ => exact (hn0 (Value.field.inj hv14)).elim
    | other w42 x_body w43 cs62 v66 _ ld34 op87 ev64 _ =>
      obtain ⟨b1, e1, hu1, hns1, href1, hr1⟩ := ixonUnshare_rawConv hraw
      obtain ⟨ty1, body1, rfl, -, hrBody⟩ := rawConv_forall_of_load hr1 hns1 ld34
      have hv66 : v66 = .field (n - 1) := by
        simp only [evalBinOp, Except.ok.injEq] at op87
        exact op87.symm
      subst hv66
      have hval' : ZMod.val (n - 1) = m := by
        have hs := Lib.val_sub_one hn0
        omega
      obtain ⟨rfl, b', e', hpeel, href2, hr'⟩ := ih hval' hrBody ev64
      refine ⟨rfl, b', e', ?_, ?_, hr'⟩
      · simp only [ixonPeelForalls, hu1]
        exact hpeel
      · intro i hi
        rcases href2 i hi with h1 | h2
        · exact href1 i (by simp [exprRefIdxs, h1])
        · exact Or.inr h2

private theorem last_binder_dom_rawConv {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} :
    ∀ (fuel : Nat) {bound : Nat} {e : Ixon.Expr} {x_e r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cs.length < fuel →
      L1.RawConvExpr refs [] univs sharing blobs h bound e x_e →
      ObsFn Obs.W "KernelModeled::last_binder_dom" [x_e] h r h' cs →
      h' = h ∧ ∃ b' d',
        (∀ f, cs.length < f → ixonLastBinderDom sharing f bound e = some (b', d')) ∧
        (∀ i ∈ exprRefIdxs d', i ∈ exprRefIdxs e ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s) ∧
        L1.RawConvExpr refs [] univs sharing blobs h b' d' r := by
  intro fuel
  induction fuel with
  | zero => intro bound e x_e r h h' cs hlt; omega
  | succ fuel ih =>
    intro bound e x_e r h h' cs hlt hraw ev
    obtain ⟨b1, e1, hu1, hns1, href1, hr1⟩ := ixonUnshare_rawConv hraw
    match Obs.«KernelModeled::last_binder_dom».obs ev with
    | .Forall (cs76 := cs76) (ld12 := ld12) (ld47 := ld47) (ev78 := evRec) (hc87 := hcs) .. =>
      obtain ⟨dom1, body1, rfl, -, hrBody⟩ := rawConv_forall_of_load hr1 hns1 ld12
      obtain ⟨b2, e2, hu2, hns2, href2, hr2⟩ := ixonUnshare_rawConv hrBody
      obtain ⟨d2, bo2, rfl, -, -⟩ := rawConv_forall_of_load hr2 hns2 ld47
      have hlt' : cs76.length < fuel := by rw [hcs] at hlt; simp at hlt; omega
      obtain ⟨rfl, b', d', hfun, href3, hr'⟩ := ih hlt' hr2 evRec
      refine ⟨rfl, b', d', ?_, ?_, hr'⟩
      · intro f hf
        cases f with
        | zero => omega
        | succ f' =>
          simp only [ixonLastBinderDom, hu1, hu2]
          exact hfun f' (by rw [hcs] at hf; simp at hf; omega)
      · intro i hi
        rcases href3 i hi with h3 | h3
        · rcases href2 i h3 with h2' | h2'
          · exact href1 i (by simp [exprRefIdxs, h2'])
          · exact Or.inr h2'
        · exact Or.inr h3
    | .other (ld12 := ld12) (ld47 := ld47) (hne88 := hne) (he93 := hr) (he94 := hh) .. =>
      subst hr hh
      obtain ⟨dom1, body1, rfl, hrDom, hrBody⟩ := rawConv_forall_of_load hr1 hns1 ld12
      obtain ⟨b2, e2, hu2, hns2, -, hr2⟩ := ixonUnshare_rawConv hrBody
      have hna := rawConv_not_forall_of_ne hr2 hns2 ld47 hne
      refine ⟨rfl, b1, dom1, ?_, ?_, hrDom⟩
      · intro f hf
        cases f with
        | zero => omega
        | succ f' =>
          simp only [ixonLastBinderDom, hu1, hu2]
          cases e2 with
          | all d2 bo2 => exact (hna d2 bo2 rfl).elim
          | _ => rfl
      · intro i hi
        exact href1 i (by simp [exprRefIdxs, hi])

private theorem collect_spine_rawConv {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)} :
    ∀ (fuel : Nat) {bound : Nat} {e : Ixon.Expr} {x_e hd sp : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      cs.length < fuel →
      L1.RawConvExpr refs [] univs sharing blobs h bound e x_e →
      ObsFn Obs.W "KernelTypes::collect_spine" [x_e] h (.tuple [hd, sp]) h' cs →
      Heap.Extends h h' ∧ ∃ b' eh,
        (∀ f, cs.length < f →
          ∀ rIdx uIdxs, eh = .ref rIdx uIdxs → ixonAppHeadRef sharing f bound e = some rIdx.toNat) ∧
        (∀ idx, eh ≠ .share idx) ∧
        (∀ i ∈ exprRefIdxs eh, i ∈ exprRefIdxs e ∨ ∃ s ∈ sharing, i ∈ exprRefIdxs s) ∧
        L1.RawConvExpr refs [] univs sharing blobs h' b' eh hd := by
  intro fuel
  induction fuel with
  | zero => intro bound e x_e hd sp h h' cs hlt; omega
  | succ fuel ih =>
    intro bound e x_e hd sp h h' cs hlt hraw ev
    obtain ⟨b1, e1, hu1, hns1, href1, hr1⟩ := ixonUnshare_rawConv hraw
    match Obs.«KernelTypes::collect_spine».obs ev with
    | .App (cs41 := cs41) (ld12 := ld12) (ev43 := evRec) (he69 := hr) (ev88 := evSnoc)
        (he105 := hh) (hc106 := hcs) .. =>
      obtain ⟨ef, ea, rfl, hrf, -⟩ := rawConv_app_of_load hr1 hns1 ld12
      injection hr with htl
      injection htl with hhd _
      subst hhd
      have hlt' : cs41.length < fuel := by rw [hcs] at hlt; simp at hlt; omega
      obtain ⟨ext1, b', eh, hfun, hns', href', hr'⟩ := ih hlt' hrf evRec
      have ext_snoc : Heap.Extends _ h' := by rw [hh]; exact evSnoc.heap_extends
      refine ⟨ext1.trans ext_snoc, b', eh, ?_, hns', ?_, hr'.mono ext_snoc (fun _ hm => hm)⟩
      · intro f hf rIdx uIdxs heh
        cases f with
        | zero => omega
        | succ f' =>
          simp only [ixonAppHeadRef, hu1]
          exact hfun f' (by rw [hcs] at hf; simp at hf; omega) rIdx uIdxs heh
      · intro i hi
        rcases href' i hi with h1 | h2
        · exact href1 i (by simp [exprRefIdxs, h1])
        · exact Or.inr h2
    | .other (ld12 := ld12) (hne107 := hne) (he115 := hr) (hm132 := hm) (he136 := hh) .. =>
      injection hr with htl
      injection htl with hhd _
      subst hhd
      have hna := rawConv_not_app_of_ne hr1 hns1 ld12 hne
      have ext_snoc : Heap.Extends h h' := by rw [hh, hm]; exact Heap.Extends.snoc _ _
      refine ⟨ext_snoc, b1, e1, ?_, hns1, href1, hr1.mono ext_snoc (fun _ hm => hm)⟩
      · intro f hf rIdx uIdxs heh
        cases f with
        | zero => omega
        | succ f' =>
          subst heh
          simp only [ixonAppHeadRef, hu1]

/-- Pure first-motive carrier reference index extracted from a recursor's converted type. -/
private theorem motive0_carrier_rawConv {refs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {h h1 h2 h3 : Heap F} {rc : Ixon.Recursor}
    {tyPtr vPeel vDom hd sp x_t0 w_lvls : SourceValue F} {cs1 cs2 cs3 : List (Call F)}
    (hp : rc.params.toNat < 72057594037927936)
    (hty : L1.RawConvExpr refs [] univs sharing blobs h 4294967295 rc.typ tyPtr)
    (evPeel : ObsFn Obs.W "KernelCheck::peel_n_foralls" [tyPtr, .field (rc.params.toNat : F)]
      h vPeel h1 cs1)
    (ldM : loadValue h1 vPeel = .ok (.construct Core.kexprEnum "Forall" [x_mdom, x_body, w_m]))
    (evDom : ObsFn Obs.W "KernelModeled::last_binder_dom" [x_mdom] h1 vDom h2 cs2)
    (evSp : ObsFn Obs.W "KernelTypes::collect_spine" [vDom] h2 (.tuple [hd, sp]) h3 cs3)
    (ldHd : loadValue h3 hd = .ok (.construct Core.kexprEnum "Const" [x_t0, w_lvls])) :
    ∃ (rIdx : Nat) (a : _root_.Address) (d : Bytes.Address),
      (∀ f1 f2, cs2.length < f1 → cs3.length < f2 →
        (ixonPeelForalls sharing rc.params.toNat 4294967295 rc.typ).bind (fun (b1, e1) =>
          (ixonUnshare sharing b1 e1).bind (fun (b2, e2) =>
            match e2 with
            | .all dom _ =>
              (ixonLastBinderDom sharing f1 b2 dom).bind (fun (b3, d3) =>
                ixonAppHeadRef sharing f2 b3 d3)
            | _ => none)) = some rIdx) ∧
      refs[rIdx]? = some a ∧ Core.ixAddr d = a ∧ Bytes.RepAddressRef Core.addrTy h3 d x_t0 ∧
      (rIdx ∈ exprRefIdxs rc.typ ∨ ∃ s ∈ sharing, rIdx ∈ exprRefIdxs s) := by
  have hval : ZMod.val (rc.params.toNat : F) = rc.params.toNat := L1.val_cast_u56_ing hp
  obtain ⟨rfl, b1, e1, hpeel, href1, hr1⟩ := peel_n_foralls_rawConv rc.params.toNat hval hty evPeel
  obtain ⟨b2, e2, hu2, hns2, href2, hr2⟩ := ixonUnshare_rawConv hr1
  obtain ⟨dom2, body2, rfl, hrDom, -⟩ := rawConv_forall_of_load hr2 hns2 ldM
  obtain ⟨rfl, b3, d3, hlast, href3, hr3⟩ :=
    last_binder_dom_rawConv (cs2.length + 1) (Nat.lt_succ_self _) hrDom evDom
  obtain ⟨-, b4, eh, happ, hns4, href4, hr4⟩ :=
    collect_spine_rawConv (cs3.length + 1) (Nat.lt_succ_self _) hr3 evSp
  obtain ⟨rIdx, uIdxs, a, d, rfl, href, hd_eq, ra⟩ := rawConv_const_of_load hr4 hns4 ldHd
  refine ⟨rIdx.toNat, a, d, ?_, href, hd_eq, ra, ?_⟩
  · intro f1 f2 hf1 hf2
    simp only [hpeel, Option.bind_some, hu2, hlast f1 hf1]
    exact happ f2 hf2 rIdx uIdxs rfl
  · have hm : rIdx.toNat ∈ exprRefIdxs (.ref rIdx uIdxs) := by simp [exprRefIdxs]
    rcases href4 _ hm with h4 | h4
    · rcases href3 _ h4 with h3 | h3
      · rcases href2 rIdx.toNat (by simp [exprRefIdxs]; exact Or.inl h3) with h2 | h2
        · exact href1 _ h2
        · exact Or.inr h2
      · exact Or.inr h3
    · exact Or.inr h4

private theorem bounded_sub {cs calls : List (Call F)}
    (hbd : IxVM.Consistency.Bounded calls) (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    IxVM.Consistency.Bounded cs := by
  obtain ⟨rom, hv, ha, hmem⟩ := hbd
  exact ⟨rom, hv, ha, fun cl hcl => hmem cl (hsub cl hcl)⟩

/-- **`KernelModeled::rec_family_block`** extracts the pure motive-0 carrier head reference `t0`
from the recursor's owner record (a `UsedRef` of that owner) and its inductive block `family`. -/
theorem rec_family_block_head_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    {x : _root_.Address} {x_rec r : SourceValue F} {h h' : Heap F}
    (hx : Core.S0.addr h x_rec x)
    (ev : ObsFn Obs.W "KernelModeled::rec_family_block" [x_rec] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (cx cOwn : Ixon.Constant) (rc : Ixon.Recursor) (t0 family : _root_.Address)
      (bF : Bytes.Address) (f1 f2 : Nat),
      recordOf E₀ x = some cx ∧
      recordOf E₀ (Ix.Cert.ownerOf x cx) = some cOwn ∧
      UsedRef E₀ (Ix.Cert.ownerOf x cx) t0 ∧
      (∃ c0 ip, recordOf E₀ t0 = some c0 ∧ c0.info = .iPrj ip ∧ ip.block = family) ∧
      Core.ixAddr bF = family ∧ Bytes.RepAddressRef Core.addrTy h' bF r ∧
      ((cx.info = .recr rc ∧ cOwn = cx) ∨
        (∃ rp ms, cx.info = .rPrj rp ∧ cOwn.info = .muts ms ∧
          ms.toList[rp.idx.toNat]? = some (.recr rc))) ∧
      ∃ rIdx, cOwn.refs[rIdx]? = some t0 ∧
        ∀ g1 g2, f1 ≤ g1 → f2 ≤ g2 →
          (ixonPeelForalls cOwn.sharing.toList rc.params.toNat 4294967295 rc.typ).bind
            (fun (b1, e1) => (ixonUnshare cOwn.sharing.toList b1 e1).bind (fun (b2, e2) =>
              match e2 with
              | .all dom _ =>
                (ixonLastBinderDom cOwn.sharing.toList g1 b2 dom).bind (fun (b3, d3) =>
                  ixonAppHeadRef cOwn.sharing.toList g2 b3 d3)
              | _ => none)) = some rIdx := by
  obtain ⟨ab, hab, rfl⟩ := hx
  match Obs.«KernelModeled::rec_family_block».obs ev with
  | .run (cs16 := csCi) (cs108 := cs1) (cs174 := cs2) (cs196 := cs3) (cs266 := csInd)
      (ev18 := evCi) (ld12 := ldRec) (ev110 := evPeel) (ld138 := ldM) (ev176 := evDom)
      (ev198 := evSp) (ld232 := ldHd) (ev268 := evInd) (ld262 := ldInd)
      (he331 := hr) (he332 := hh) (hc333 := hcs) .. =>
    have hsubCi : ∀ cl ∈ csCi, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsubInd : ∀ cl ∈ csInd, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hbdCi : IxVM.Consistency.Bounded csCi := bounded_sub hbd hsubCi
    have hbdInd : IxVM.Consistency.Bounded csInd := bounded_sub hbd hsubInd
    obtain ⟨-, raw, cx, blobs, hhx, hba, hdeE, hde, -, -, hres⟩ :=
      L1.get_ci_spec hbdCi hab evCi
    have hrecX : recordOf E₀ (Core.ixAddr ab) = some cx := by
      rw [← hba]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubCi hhx)
        (by
          obtain ⟨raw', -, hsz, hh', hba', -, -, -⟩ := Claim.get_ci_head hab evCi
          have er := hC.runStore.hashed_inj (Core.hashed_mono hsubCi hhx)
            (Core.hashed_mono hsubCi hh') (hba.trans hba'.symm)
          rwa [er])
        hde hdeE
    have hfinish : ∀ (cOwn : Ixon.Constant) (rc : Ixon.Recursor)
        (hown : recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) cx) = some cOwn)
        (hrcIn : ∀ i ∈ exprRefIdxs rc.typ, i ∈ usedRefIdxs cOwn)
        (hrcWit : (cx.info = .recr rc ∧ cOwn = cx) ∨
          (∃ rp ms, cx.info = .rPrj rp ∧ cOwn.info = .muts ms ∧
            ms.toList[rp.idx.toNat]? = some (.recr rc)))
        (hrr : L1.RawRecrValRep cOwn.refs.toList _ cOwn.univs.toList cOwn.sharing.toList
          blobs _ rc _ _ _),
        ∃ (cx' cOwn' : Ixon.Constant) (rc' : Ixon.Recursor) (t0 family : _root_.Address)
          (bF' : Bytes.Address) (f1 f2 : Nat),
          recordOf E₀ (Core.ixAddr ab) = some cx' ∧
          recordOf E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) cx') = some cOwn' ∧
          UsedRef E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) cx') t0 ∧
          (∃ c0 ip, recordOf E₀ t0 = some c0 ∧ c0.info = .iPrj ip ∧ ip.block = family) ∧
          Core.ixAddr bF' = family ∧ Bytes.RepAddressRef Core.addrTy h' bF' r ∧
          ((cx'.info = .recr rc' ∧ cOwn' = cx') ∨
            (∃ rp ms, cx'.info = .rPrj rp ∧ cOwn'.info = .muts ms ∧
              ms.toList[rp.idx.toNat]? = some (.recr rc'))) ∧
          ∃ rIdx, cOwn'.refs[rIdx]? = some t0 ∧
            ∀ g1 g2, f1 ≤ g1 → f2 ≤ g2 →
              (ixonPeelForalls cOwn'.sharing.toList rc'.params.toNat 4294967295 rc'.typ).bind
                (fun (b1, e1) => (ixonUnshare cOwn'.sharing.toList b1 e1).bind (fun (b2, e2) =>
                  match e2 with
                  | .all dom _ =>
                    (ixonLastBinderDom cOwn'.sharing.toList g1 b2 dom).bind (fun (b3, d3) =>
                      ixonAppHeadRef cOwn'.sharing.toList g2 b3 d3)
                  | _ => none)) = some rIdx := by
      intro cOwn rc hown hrcIn hrcWit hrr
      obtain ⟨-, hp, -, -, -, -, tyPtr, rulesPtr, blkPtr, b, -, -, hv_eq, hty, -⟩ := hrr
      have hv_ok := hv_eq.symm.trans (Except.ok.inj ldRec)
      injection hv_ok with _ _ hargs
      simp only [List.cons.injEq] at hargs
      obtain ⟨-, rfl, rfl, -⟩ := hargs
      obtain ⟨rIdx, a0, d0, hfun, href, hd0, ra0, hmemIdx⟩ :=
        motive0_carrier_rawConv hp hty evPeel ldM evDom evSp ldHd
      have husedIdx : rIdx ∈ usedRefIdxs cOwn := by
        rcases hmemIdx with h1 | ⟨s, hs, h2⟩
        · exact hrcIn rIdx h1
        · unfold usedRefIdxs
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, h2⟩)
      have hrefArr : cOwn.refs[rIdx]? = some a0 := by rwa [← Array.getElem?_toList]
      have hused : UsedRef E₀ (Ix.Cert.ownerOf (Core.ixAddr ab) cx) a0 :=
        ⟨cOwn, rIdx, hown, husedIdx, hrefArr⟩
      obtain ⟨-, rawI, c0, blobsI, hhI, hbaI, hdeEI, hdeI, -, -, hresI⟩ :=
        L1.get_ci_spec hbdInd ra0 evInd
      have hrec0 : recordOf E₀ a0 = some c0 := by
        rw [← hd0, ← hbaI]
        exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsubInd hhI)
          (by
            obtain ⟨rawI', -, hszI, hhI', hbaI', -, -, -⟩ := Claim.get_ci_head ra0 evInd
            have er := hC.runStore.hashed_inj (Core.hashed_mono hsubInd hhI)
              (Core.hashed_mono hsubInd hhI') (hbaI.trans hbaI'.symm)
            rwa [er])
          hdeI hdeEI
      cases hinfo0 : c0.info <;> simp only [L1.GetCIRawResult, hinfo0] at hresI
      · obtain ⟨v, hld, hrrI⟩ := hresI
        rw [hld] at ldInd; injection ldInd with hv; subst hv
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hv_eq0, -⟩ := hrrI; simp at hv_eq0
      · obtain ⟨v, hld, hrrI⟩ := hresI
        rw [hld] at ldInd; injection ldInd with hv; subst hv
        obtain ⟨_, _, _, _, hv_eq0, -⟩ := hrrI; simp at hv_eq0
      · obtain ⟨v, hld, hrrI⟩ := hresI
        rw [hld] at ldInd; injection ldInd with hv; subst hv
        obtain ⟨_, _, _, _, hv_eq0, -⟩ := hrrI; simp at hv_eq0
      · obtain ⟨v, hld, hrrI⟩ := hresI
        rw [hld] at ldInd; injection ldInd with hv; subst hv
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hv_eq0, -⟩ := hrrI; simp at hv_eq0
      · obtain ⟨-, -, -, -, -, -, v, -, -, -, -, -, -, hld, hrrI⟩ := hresI
        rw [hld] at ldInd; injection ldInd with hv; subst hv
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hv_eq0, -⟩ := hrrI; simp at hv_eq0
      · -- `c0.info = .iPrj ip`
        rename_i ip
        obtain ⟨-, -, -, -, -, v, -, -, -, -, -, -, hld, hrrI⟩ := hresI
        rw [hld] at ldInd
        injection ldInd with hv
        subst hv
        obtain ⟨-, -, -, -, -, tyPtrI, blkPtrI, bF, hbF_eq, hbF_rep, hv_eq0, -⟩ := hrrI
        injection hv_eq0 with _ _ hargs0
        simp only [List.cons.injEq] at hargs0
        obtain ⟨-, -, -, -, -, -, rfl, -⟩ := hargs0
        rw [hr, hh]
        exact ⟨cx, cOwn, rc, a0, ip.block, bF, cs2.length + 1, cs3.length + 1,
          hrecX, hown, hused, ⟨c0, ip, hrec0, hinfo0, rfl⟩, hbF_eq, hbF_rep, hrcWit,
          rIdx, hrefArr, hfun⟩
      · obtain ⟨-, -, -, -, -, -, -, v, -, -, -, -, -, -, -, hld, hrrI⟩ := hresI
        rw [hld] at ldInd; injection ldInd with hv; subst hv
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hv_eq0, -⟩ := hrrI; simp at hv_eq0
      · obtain ⟨-, -, -, -, -, v, -, -, -, -, -, -, hld, hrrI⟩ := hresI
        rw [hld] at ldInd; injection ldInd with hv; subst hv
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hv_eq0, -⟩ := hrrI; simp at hv_eq0
      · cases hresI
    cases hinfo : cx.info <;> simp only [L1.GetCIRawResult, hinfo] at hres
    · obtain ⟨v, hld, hrr⟩ := hres
      rw [hld] at ldRec; injection ldRec with hv; subst hv
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hv_eq, -⟩ := hrr
      simp at hv_eq
    · obtain ⟨v, hld, hrr⟩ := hres
      rw [hld] at ldRec; injection ldRec with hv; subst hv
      obtain ⟨_, _, _, _, hv_eq, -⟩ := hrr
      simp at hv_eq
    · obtain ⟨v, hld, hrr⟩ := hres
      rw [hld] at ldRec; injection ldRec with hv; subst hv
      obtain ⟨_, _, _, _, hv_eq, -⟩ := hrr
      simp at hv_eq
    · -- `cx.info = .recr rc`
      rename_i rc
      obtain ⟨v, hld, hrr⟩ := hres
      rw [hld] at ldRec
      injection ldRec with hv
      subst hv
      exact hfinish cx rc (by simp [Ix.Cert.ownerOf, hinfo, hrecX])
        (fun i hi => by simp [usedRefIdxs, hinfo, hi])
        (Or.inl ⟨hinfo, rfl⟩)
        hrr
    · obtain ⟨-, -, -, -, -, v, -, -, -, -, -, -, hld, hrr⟩ := hres
      rw [hld] at ldRec; injection ldRec with hv; subst hv
      obtain ⟨_, _, _, _, _, _, _, _, _, _, hv_eq, -⟩ := hrr
      simp at hv_eq
    · obtain ⟨-, -, -, -, -, v, -, -, -, -, -, -, hld, hrr⟩ := hres
      rw [hld] at ldRec; injection ldRec with hv; subst hv
      obtain ⟨_, _, _, _, _, _, _, _, _, hv_eq, -⟩ := hrr
      simp at hv_eq
    · obtain ⟨-, -, -, -, -, -, v, -, -, -, -, -, -, -, hld, hrr⟩ := hres
      rw [hld] at ldRec; injection ldRec with hv; subst hv
      obtain ⟨_, _, _, _, _, _, _, _, _, hv_eq, -⟩ := hrr
      simp at hv_eq
    · -- `cx.info = .rPrj rp`
      rename_i rp
      obtain ⟨-, blkBytes, cb, ms, rc, v, hhb, hblk, hdeEb, hdeb, hcbm, hmem, hld, hrr⟩ := hres
      rw [hld] at ldRec
      injection ldRec with hv
      subst hv
      have hrecB : recordOf E₀ rp.block = some cb := by
        obtain ⟨rawX, cx', -, hhX, hbaX, hdeX, -, hheadX⟩ := Claim.get_ci_head hab evCi
        have ecX := hC.runStore.record_eq ((hC.runStore.recordOf_eq_recordAt _).symm.trans hrecX)
          (Core.hashed_mono hsubCi hhX) hbaX hdeX
        subst ecX
        obtain ⟨cb', ms', rc', hbl', -, -⟩ := hheadX.rPrj rp.idx rp.block hinfo
        obtain ⟨hrecB', -⟩ := (hbl'.mono hsubCi).stored hC.hashedStored
        have ecb := hC.runStore.record_eq ((hC.runStore.recordOf_eq_recordAt _).symm.trans hrecB')
          (Core.hashed_mono hsubCi hhb) hblk hdeEb
        rwa [ecb]
      exact hfinish cb rc (by simp [Ix.Cert.ownerOf, hinfo, hrecB])
        (fun i hi => by
          unfold usedRefIdxs
          rw [hcbm]
          exact List.mem_append_right _ (List.mem_flatMap.mpr
            ⟨.recr rc, List.mem_of_getElem? hmem, by simp [mutRefIdxs, hi]⟩))
        (Or.inr ⟨rp, ms, hinfo, hcbm, hmem⟩)
        hrr
    · cases hres

/-- **`KernelModeled::rec_family_block` is deterministic on `E₀`**: two observed calls on the same
recursor address return the same inductive family block address. -/
theorem rec_family_block_det {calls cs₁ cs₂ : List (Call F)} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    {x fam₁ fam₂ : _root_.Address} {xr₁ xr₂ r₁ r₂ : SourceValue F} {h₁ h₁' h₂ h₂' : Heap F}
    (hx₁ : Core.S0.addr h₁ xr₁ x) (hx₂ : Core.S0.addr h₂ xr₂ x)
    (ev₁ : ObsFn Obs.W "KernelModeled::rec_family_block" [xr₁] h₁ r₁ h₁' cs₁)
    (ev₂ : ObsFn Obs.W "KernelModeled::rec_family_block" [xr₂] h₂ r₂ h₂' cs₂)
    (hsub₁ : ∀ cl ∈ cs₁, cl ∈ calls) (hsub₂ : ∀ cl ∈ cs₂, cl ∈ calls)
    (hr₁ : Core.S0.addr h₁' r₁ fam₁) (hr₂ : Core.S0.addr h₂' r₂ fam₂) :
    fam₁ = fam₂ := by
  obtain ⟨cx₁, cOwn₁, rc₁, t0₁, f₁, bF₁, f1₁, f2₁, hrecX₁, hown₁, -, ⟨c0₁, ip₁, hrec0₁, hi0₁, hf₁⟩,
    hbF₁, hrep₁, hwit₁, rIdx₁, href₁, hfun₁⟩ :=
    rec_family_block_head_spec hC hbd hx₁ ev₁ hsub₁
  obtain ⟨cx₂, cOwn₂, rc₂, t0₂, f₂, bF₂, f1₂, f2₂, hrecX₂, hown₂, -, ⟨c0₂, ip₂, hrec0₂, hi0₂, hf₂⟩,
    hbF₂, hrep₂, hwit₂, rIdx₂, href₂, hfun₂⟩ :=
    rec_family_block_head_spec hC hbd hx₂ ev₂ hsub₂
  have efam₁ : fam₁ = f₁ := by
    obtain ⟨b, hb, rfl⟩ := hr₁
    rw [← hbF₁, Bytes.repAddressRef_inj U32.Goldilocks.compatible hb hrep₁]
  have efam₂ : fam₂ = f₂ := by
    obtain ⟨b, hb, rfl⟩ := hr₂
    rw [← hbF₂, Bytes.repAddressRef_inj U32.Goldilocks.compatible hb hrep₂]
  have ecx : cx₁ = cx₂ := Option.some.inj (hrecX₁.symm.trans hrecX₂)
  subst ecx
  have eown : cOwn₁ = cOwn₂ := Option.some.inj (hown₁.symm.trans hown₂)
  subst eown
  have erc : rc₁ = rc₂ := by
    rcases hwit₁ with ⟨h1, -⟩ | ⟨rp₁, ms₁, h1, hm₁, hg₁⟩ <;>
      rcases hwit₂ with ⟨h2, -⟩ | ⟨rp₂, ms₂, h2, hm₂, hg₂⟩
    · exact Ixon.ConstantInfo.recr.inj (h1.symm.trans h2)
    · rw [h1] at h2; cases h2
    · rw [h1] at h2; cases h2
    · have erp := Ixon.ConstantInfo.rPrj.inj (h1.symm.trans h2)
      subst erp
      have ems := Ixon.ConstantInfo.muts.inj (hm₁.symm.trans hm₂)
      subst ems
      exact Ixon.MutConst.recr.inj (Option.some.inj (hg₁.symm.trans hg₂))
  subst erc
  have eidx : rIdx₁ = rIdx₂ := Option.some.inj
    ((hfun₁ (max f1₁ f1₂) (max f2₁ f2₂) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (hfun₂ (max f1₁ f1₂) (max f2₁ f2₂) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  subst eidx
  have et0 : t0₁ = t0₂ := Option.some.inj (href₁.symm.trans href₂)
  subst et0
  have ec0 : c0₁ = c0₂ := Option.some.inj (hrec0₁.symm.trans hrec0₂)
  subst ec0
  have eip : ip₁ = ip₂ := Ixon.ConstantInfo.iPrj.inj (hi0₁.symm.trans hi0₂)
  subst eip
  rw [efam₁, efam₂, ← hf₁, ← hf₂]

/-- **`KernelModeled::rec_family_block` exhibits a used reference of the recursor's owner** that is
an inductive projection of the returned family block. -/
theorem rec_family_block_usedRef {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    {x : _root_.Address} {x_rec r : SourceValue F} {h h' : Heap F}
    (hx : Core.S0.addr h x_rec x)
    (ev : ObsFn Obs.W "KernelModeled::rec_family_block" [x_rec] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (cx cOwn c0 : Ixon.Constant) (ip : Ixon.InductiveProj) (t0 family : _root_.Address),
      recordOf E₀ x = some cx ∧
      recordOf E₀ (Ix.Cert.ownerOf x cx) = some cOwn ∧
      UsedRef E₀ (Ix.Cert.ownerOf x cx) t0 ∧
      recordOf E₀ t0 = some c0 ∧ c0.info = .iPrj ip ∧ ip.block = family ∧
      Core.S0.addr h' r family := by
  obtain ⟨cx, cOwn, -, t0, family, bF, -, -, hrecX, hown, hused, ⟨c0, ip, hrec0, hi0, hfam⟩,
    hbF, hrep, -⟩ := rec_family_block_head_spec hC hbd hx ev hsub
  exact ⟨cx, cOwn, c0, ip, t0, family, hrecX, hown, hused, hrec0, hi0, hfam, bF, hrep, hbF⟩

/-- Helper: member projection `0` of a block is hashed by `Ingress::build_recur_addrs`. -/
private theorem build_recur_addrs_head_hashed {m0 : Ixon.MutConst} {rest : List Ixon.MutConst}
    {b : Bytes.Address} {x_members x_block r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h (m0 :: rest) x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block)
    (ev : ObsFn Obs.W "Ingress::build_recur_addrs" [x_members, x_block] h r h' cs) :
    Hashed cs (Ixon.serConstant (memberProjection (Core.ixAddr b) 0 m0)) := by
  obtain ⟨cs4, ev6, hc38⟩ := Obs.«Ingress::build_recur_addrs».obs ev
  have ev6' : ObsFn Obs.W "Ingress::build_recur_addrs_walk"
      [x_members, x_block, x_members, .field ((0 : Nat) : F)] h r h' cs4 := by
    simpa using ev6
  rcases Obs.«Ingress::build_recur_addrs_walk».obs ev6' with
    ⟨ld12, _, _, _⟩ |
    ⟨w36, x_rest, v55, v56, m58, cs66, m94, cs102, v108,
      ld12, he51, hm50, ev68, op143, ev104, hc145⟩
  · cases Lib.rep_nil_of_load hms ld12
  · obtain ⟨-, -, -, mc, -, hget, -, -, hhash⟩ := L1.projection_addr_hashed_spec hms hb ev68
    have h0 : ((0 : Nat) : F).val = 0 := by simp
    rw [h0] at hget hhash
    have emc : mc = m0 := (by simpa using hget : m0 = mc).symm
    subst emc
    have hmemb : memberProjection (Core.ixAddr b) 0 mc =
        ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) 0 mc, #[], #[], #[], #[]⟩ := by
      cases mc <;> rfl
    rw [hmemb]
    exact Core.hashed_mono (fun cl hcl => by rw [hc38, hc145]; simp [hcl]) hhash

/-- **A complete family check at a group limit pins the pure motive-0 carrier head of its first
recursor to `memberAddr B 0 ms[0]`**, a used reference of `rb` whose serialization is hashed. -/
theorem familyCall_motive0_spec {calls cs : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {n : Nat}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    (hn : n < 77) (hfc : FamilyCallAtLim calls bAddr t B rb (some n) cs) :
    ∃ (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst) (rc0 : Ixon.Recursor)
      (hBpos : 0 < ms.size) (rIdx f1 f2 : Nat),
      recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧
      recordOf E₀ rb = some crb ∧ crb.info = .muts rs ∧ 0 < rs.size ∧
      rs[0]? = some (.recr rc0) ∧
      Hashed calls (Ixon.serConstant (memberProjection B 0 (ms[0]'hBpos))) ∧
      (memberProjection B 0 (ms[0]'hBpos)).wireWF ∧
      UsedRef E₀ rb (memberAddr B 0 (ms[0]'hBpos)) ∧
      crb.refs[rIdx]? = some (memberAddr B 0 (ms[0]'hBpos)) ∧
      ∀ g1 g2, f1 ≤ g1 → f2 ≤ g2 →
        (ixonPeelForalls crb.sharing.toList rc0.params.toNat 4294967295 rc0.typ).bind
          (fun (b1, e1) => (ixonUnshare crb.sharing.toList b1 e1).bind (fun (b2, e2) =>
            match e2 with
            | .all dom _ =>
              (ixonLastBinderDom crb.sharing.toList g1 b2 dom).bind (fun (b3, d3) =>
                ixonAppHeadRef crb.sharing.toList g2 b3 d3)
            | _ => none)) = some rIdx := by
  obtain ⟨cb, ms, hcb, hms, hBpos, -⟩ :=
    familyCall_block_indc_nonempty hC.runStore hC.hashedStored hfc
  obtain ⟨crb, rs, hcrb, hlog2, hrs, hRpos, hrecrs, hmem2⟩ :=
    familyCall_isTwinShape hC.runStore hC.hashedStored hn hfc
  have hfamRec : TwinFamily.FamRecRecord E₀ rb crb rs :=
    ⟨hcrb, hrs, hrecrs, hlog2, hmem2⟩
  have hms0 : ms.toList ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  cases hml : ms.toList with
  | nil => exact absurd hml hms0
  | cons m0 mrest =>
    have hm0_eq : ms[0]'hBpos = m0 := by
      have : ms.toList[0]? = some m0 := by rw [hml]; rfl
      rw [Array.getElem?_toList, Array.getElem?_eq_getElem hBpos] at this
      exact Option.some.inj this
    have hrs0 : rs.toList ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    cases hrl : rs.toList with
    | nil => exact absurd hrl hrs0
    | cons r0 rrest =>
      obtain ⟨rc0, rfl⟩ := hrecrs r0 (by rw [hrl]; exact List.mem_cons_self)
      have hrc0_get : rs[0]? = some (.recr rc0) := by
        rw [← Array.getElem?_toList, hrl]; rfl
      obtain ⟨h, h', rc, xb, xrb, r, -, ⟨bb, hbb, rfl⟩, ⟨brb, hbrb, rfl⟩, ev, -, hsub⟩ := hfc
      match Obs.«KernelModeled::check_family».obs ev with
      | .run (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
          (ev_yqjbwijz := evo) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309)
          (ev344 := ev344) (ev403 := ev403) (ev435 := ev435) (ev465 := ev465)
          (cs511 := cs511) (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
          (cs684 := cs684) (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817)
          (ev796 := ev796) (cs850 := cs850) (ev852 := ev852) (ev_ursqbimm := evr)
          (ev874 := ev874) (ev896 := ev896) (ev960 := ev960) (ev939 := ev939) (ev1011 := ev1011)
          (ev990 := ev990) (ev_edyzsqzv := evm1) (ev_gkddqxhv := evcc) (ev_ittpynob := evm2)
          (ev_biaifgpd := evm3) (ev1203 := ev1203) (ev_cwwgzxtj := evfl) (ev1246 := ev1246)
          (ev_mitevvsv := evln) (ev_rqpeovbn := evz1) (ev_xrhmaojz := evz2) (ev_whimdwjd := evvg)
          (ev1305 := ev1305) (cs1341 := cs1341) (ev1343 := ev1343) (hc1474 := hc) .. =>
        have e0 : Heap.Extends h _ := by
          match sg112 with
          | .Nil (ev15 := ev15) (he33 := he33) .. => rw [he33]; exact ev15.heap_extends
          | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
        have e453 : Heap.Extends h _ :=
          e0.trans <| ev126.heap_extends.trans <| ev148.heap_extends.trans <|
            ev194.heap_extends.trans <| evo.heap_extends.trans <| ev231.heap_extends.trans <|
            ev266.heap_extends.trans <| ev309.heap_extends.trans <| ev344.heap_extends.trans <|
            ev403.heap_extends.trans <| ev435.heap_extends.trans ev465.heap_extends
        have hsub511 : ∀ cl ∈ cs511, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have hsub684 : ∀ cl ∈ cs684, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have hsub850 : ∀ cl ∈ cs850, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have hsub1341 : ∀ cl ∈ cs1341, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        -- `ev513` + `ev686` give `v673` = type projection addresses and hash of member 0
        have hbb453 := Bytes.repAddressRef_heapMono₂ Core.addrTy e453 hbb
        obtain ⟨cb', ms', hbl, hrepM⟩ := Claim.load_block_head hbb453 ev513
        have ecb' := ((hbl.mono hsub511).record hC.runStore hcb).1
        subst ecb'
        have ems' := Ixon.ConstantInfo.muts.inj (hbl.info.symm.trans hms)
        subst ems'
        have e501_652 : Heap.Extends _ _ :=
          ev601.heap_extends.trans (ev634.heap_extends.trans ev664.heap_extends)
        have hmemRep : Core.Specs.Callees.MembersRep _ (m0 :: mrest) _ := by
          rw [← hml]
          exact Route.membersRep_of_repMutConstList
            (RepLinkedList.mono L1.repMutConst_heapMono₂ e501_652 hrepM)
        have hbb652 := Bytes.repAddressRef_heapMono₂ Core.addrTy
          (ev513.heap_extends.trans e501_652) hbb453
        obtain ⟨-, typeAs, htypeAs, htypeMap⟩ := L1.build_recur_addrs_spec hmemRep hbb652 ev686
        have hhashM0 : Hashed calls (Ixon.serConstant (memberProjection (Core.ixAddr bb) 0 m0)) :=
          Core.hashed_mono hsub684 (build_recur_addrs_head_hashed hmemRep hbb652 ev686)
        have hwfM0 : (memberProjection (Core.ixAddr bb) 0 m0).wireWF := by
          cases m0 with
          | defn _ => exact L1.projConstant_wireWF_dPrj 0 bb
          | indc _ => exact L1.projConstant_wireWF_iPrj 0 bb
          | recr _ => exact L1.projConstant_wireWF_rPrj 0 bb
        cases typeAs with
        | nil => simp at htypeMap
        | cons tA0 tArest =>
          have htA0_eq : Core.ixAddr tA0 = memberAddr (Core.ixAddr bb) 0 m0 := by
            have h0 := (List.cons.inj htypeMap).1
            rw [LoadedReads.memberAddr_eq_projAddr]
            exact h0
          -- `ev852` gives `v839` = recursor projection addresses
          have e453_784 : Heap.Extends _ _ :=
            ev513.heap_extends.trans <| e501_652.trans <| ev686.heap_extends.trans <|
              ev716.heap_extends.trans <| ev759.heap_extends.trans <|
              ev817.heap_extends.trans ev796.heap_extends
          have hbrb784 := Bytes.repAddressRef_heapMono₂ Core.addrTy (e453.trans e453_784) hbrb
          obtain ⟨recAs, hrecAs, hrecMap⟩ :=
            FamilyAlias.family_recs_list hC.hashedStored hbrb784 ev852 hsub850 hfamRec
          rw [hrl] at hrecMap
          cases recAs with
          | nil => simp at hrecMap
          | cons rA0 rArest =>
            have hrA0_eq : Core.ixAddr rA0 = memberAddr (Core.ixAddr brb) 0 (.recr rc0) := by
              have h0 := (List.cons.inj hrecMap).1
              rw [LoadedReads.memberAddr_eq_projAddr]
              exact h0
            have e840_1293 : Heap.Extends _ _ :=
              evr.heap_extends.trans <| ev874.heap_extends.trans <| ev896.heap_extends.trans <|
                ev960.heap_extends.trans <| ev939.heap_extends.trans <| ev1011.heap_extends.trans <|
                ev990.heap_extends.trans <| evm1.heap_extends.trans <| evcc.heap_extends.trans <|
                evm2.heap_extends.trans <| evm3.heap_extends.trans <| ev1203.heap_extends.trans <|
                evfl.heap_extends.trans <| ev1246.heap_extends.trans <| evln.heap_extends.trans <|
                evz1.heap_extends.trans <| evz2.heap_extends.trans <| evvg.heap_extends.trans <|
                ev1305.heap_extends
            have e674_1293 : Heap.Extends _ _ :=
              ev716.heap_extends.trans <| ev759.heap_extends.trans <| ev817.heap_extends.trans <|
                ev796.heap_extends.trans <| ev852.heap_extends.trans e840_1293
            have htypeAs1293 :=
              RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) e674_1293 htypeAs
            have hrecAs1293 :=
              RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy) e840_1293 hrecAs
            -- Step into `check_recs` on head `rA0`
            match Obs.«KernelModeled::check_recs».obs ev1343 with
            | .Nil (ld12 := ld) .. =>
              exact absurd (Lib.rep_nil_of_load hrecAs1293 ld) (by simp)
            | .Cons (ld12 := ldR) (cs80 := cs80) (ev82 := evCi) (ld76 := ldRec)
                (ev298 := e298) (ev359 := e359) (ev345 := e345) (ev403 := e403)
                (cs483 := cs483) (ev485 := evCar) (hc1137 := hcRecs) .. =>
              obtain ⟨a', rest', he, hrA0, -⟩ := Lib.rep_cons_of_load hrecAs1293 ldR
              injection he with ha' _
              subst ha'
              have hsub80 : ∀ cl ∈ cs80, cl ∈ calls := fun cl hcl =>
                hsub1341 cl (by rw [hcRecs]; simp [hcl])
              have hbd80 : IxVM.Consistency.Bounded cs80 := bounded_sub hbd hsub80
              obtain ⟨-, rawR, cR0, blobsR, hhR, hbaR, hdeER, hdeR, -, -, hresR⟩ :=
                L1.get_ci_spec hbd80 hrA0 evCi
              have hrecR0 : recordOf E₀ (Core.ixAddr rA0) = some cR0 := by
                rw [← hbaR]
                exact Claim.recordOf_hashed hC.runStore hC.hashedStored
                  (Core.hashed_mono hsub80 hhR)
                  (by
                    obtain ⟨rawR', -, hszR, hhR', hbaR', -, -, -⟩ := Claim.get_ci_head hrA0 evCi
                    have er := hC.runStore.hashed_inj (Core.hashed_mono hsub80 hhR)
                      (Core.hashed_mono hsub80 hhR') (hbaR.trans hbaR'.symm)
                    rwa [er])
                  hdeR hdeER
              have hmemR0 := hmem2 0 (.recr rc0) hrc0_get
              rw [← hrA0_eq] at hmemR0
              have ecR0 : cR0 = memberProjection (Core.ixAddr brb) 0 (.recr rc0) :=
                Option.some.inj (hrecR0.symm.trans hmemR0)
              have hinfoR0 : cR0.info = .rPrj ⟨0, Core.ixAddr brb⟩ := by
                rw [ecR0]; rfl
              simp only [L1.GetCIRawResult, hinfoR0] at hresR
              obtain ⟨-, blkBytesR, crb', rs', rc0', vR, hhbR, hblkR, hdeEbR, -, hcrb'm, hmemR',
                hldR, hrrR⟩ := hresR
              have ecrb' : crb' = crb := hC.runStore.record_eq
                ((hC.runStore.recordOf_eq_recordAt _).symm.trans hcrb)
                (Core.hashed_mono hsub80 hhbR) hblkR hdeEbR
              subst ecrb'
              have ers' : rs' = rs := Ixon.ConstantInfo.muts.inj (hcrb'm.symm.trans hrs)
              subst ers'
              have erc0' : rc0' = rc0 := by
                rw [Array.getElem?_toList, hrc0_get] at hmemR'
                exact Ixon.MutConst.recr.inj (Option.some.inj hmemR')
              subst erc0'
              rw [hldR] at ldRec
              injection ldRec with hvR
              subst hvR
              obtain ⟨-, hp, -, -, -, -, tyPtr, -, -, -, -, -, hv_eq, hty, -⟩ := hrrR
              injection hv_eq with _ _ hargsR
              simp only [List.cons.injEq] at hargsR
              obtain ⟨-, rfl, rfl, -⟩ := hargsR
              -- Step into `check_carriers` and `check_carriers_go` on head `tA0`
              have e67_391 : Heap.Extends _ _ :=
                e298.heap_extends.trans <| e359.heap_extends.trans <|
                  e345.heap_extends.trans e403.heap_extends
              have hty391 := hty.mono e67_391 (fun _ hx => hx)
              match Obs.«KernelModeled::check_carriers».obs evCar with
              | .run (ev20 := evPeel) (ev6 := evGo) .. =>
                have htypeAsGo :=
                  RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ Core.addrTy)
                    (evCi.heap_extends.trans (e67_391.trans evPeel.heap_extends)) htypeAs1293
                match Obs.«KernelModeled::check_carriers_go».obs evGo with
                | .Nil (ld12 := ldT) .. =>
                  exact absurd (Lib.rep_nil_of_load htypeAsGo ldT) (by simp)
                | .Cons (ld12 := ldT) (ld53 := ldM) (cs101 := csD) (ev103 := evDom)
                    (cs88 := csS) (ev90 := evSp) (ld137 := ldHd) (ev180 := evEq)
                    (heq203 := heq1) .. =>
                  obtain ⟨ta', _, htaEq, htaRep, -⟩ := Lib.rep_cons_of_load htypeAsGo ldT
                  injection htaEq with hta' _
                  subst hta'
                  obtain ⟨rIdx, a0, d0, hfun, href, hd0, ra0, hmemIdx⟩ :=
                    motive0_carrier_rawConv hp hty391 evPeel ldM evDom evSp ldHd
                  have hta78 := Bytes.repAddressRef_heapMono₂ Core.addrTy
                    (evDom.heap_extends.trans evSp.heap_extends) htaRep
                  have hteq := Bytes.address_eq_spec ra0 hta78 evEq
                  have ed0 : d0 = tA0 := by
                    by_cases hdeq : d0 = tA0
                    · exact hdeq
                    · simp [hdeq] at hteq
                      exact absurd (hteq.1.symm.trans heq1) zero_ne_one
                  subst ed0
                  have ha0 : a0 = memberAddr (Core.ixAddr bb) 0 (ms[0]'hBpos) := by
                    rw [← hd0, htA0_eq, hm0_eq]
                  subst ha0
                  have husedIdx : rIdx ∈ usedRefIdxs crb := by
                    rcases hmemIdx with h1 | ⟨s, hs, h2⟩
                    · unfold usedRefIdxs
                      rw [hrs]
                      exact List.mem_append_right _ (List.mem_flatMap.mpr
                        ⟨.recr rc0, by rw [hrl]; exact List.mem_cons_self,
                          by simp [mutRefIdxs, h1]⟩)
                    · unfold usedRefIdxs
                      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, h2⟩)
                  have hrefArr : crb.refs[rIdx]? = some (memberAddr (Core.ixAddr bb) 0 (ms[0]'hBpos)) := by
                    rwa [← Array.getElem?_toList]
                  exact ⟨cb, crb, ms, rs, rc0, hBpos, rIdx, csD.length + 1, csS.length + 1,
                    hcb, hms, hcrb, hrs, hRpos, hrc0_get,
                    by rwa [hm0_eq], by rwa [hm0_eq],
                    ⟨crb, rIdx, hcrb, husedIdx, hrefArr⟩, hrefArr, hfun⟩

/-- **A family record at a group limit belongs to a unique inductive block (`blockOf`)**:
`check_carriers` pins the pure motive-0 carrier head of `rb`'s first recursor to
`memberAddr B 0 ms[0]`, and hashing injectivity + `deConstantExact_serConstant` recover `B`. -/
theorem familyCall_block_unique {calls cs₁ cs₂ : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B₁ B₂ rb : _root_.Address} {n₁ n₂ : Nat}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    (hn₁ : n₁ < 77) (hn₂ : n₂ < 77)
    (hfc₁ : FamilyCallAtLim calls bAddr t B₁ rb (some n₁) cs₁)
    (hfc₂ : FamilyCallAtLim calls bAddr t B₂ rb (some n₂) cs₂) :
    B₁ = B₂ := by
  obtain ⟨cb₁, crb₁, ms₁, rs₁, rc0₁, hB1, rIdx₁, f1₁, f2₁, -, -, hcrb₁, hrs₁, -, hrc₁,
    hhash₁, hwf₁, -, href₁, hfun₁⟩ := familyCall_motive0_spec hC hbd hn₁ hfc₁
  obtain ⟨cb₂, crb₂, ms₂, rs₂, rc0₂, hB2, rIdx₂, f1₂, f2₂, -, -, hcrb₂, hrs₂, -, hrc₂,
    hhash₂, hwf₂, -, href₂, hfun₂⟩ := familyCall_motive0_spec hC hbd hn₂ hfc₂
  have ecrb : crb₁ = crb₂ := Option.some.inj (hcrb₁.symm.trans hcrb₂)
  subst ecrb
  have ers : rs₁ = rs₂ := Ixon.ConstantInfo.muts.inj (hrs₁.symm.trans hrs₂)
  subst ers
  have erc : rc0₁ = rc0₂ := Ixon.MutConst.recr.inj (Option.some.inj (hrc₁.symm.trans hrc₂))
  subst erc
  have eidx : rIdx₁ = rIdx₂ := Option.some.inj
    ((hfun₁ (max f1₁ f1₂) (max f2₁ f2₂) (Nat.le_max_left _ _) (Nat.le_max_left _ _)).symm.trans
      (hfun₂ (max f1₁ f1₂) (max f2₁ f2₂) (Nat.le_max_right _ _) (Nat.le_max_right _ _)))
  subst eidx
  have emem : memberAddr B₁ 0 (ms₁[0]'hB1) = memberAddr B₂ 0 (ms₂[0]'hB2) :=
    Option.some.inj (href₁.symm.trans href₂)
  have hser : Ixon.serConstant (memberProjection B₁ 0 (ms₁[0]'hB1)) =
      Ixon.serConstant (memberProjection B₂ 0 (ms₂[0]'hB2)) :=
    hC.runStore.hashed_inj hhash₁ hhash₂ emem
  have hde := congrArg Ixon.deConstantExact hser
  rw [Ixon.Verify.deConstantExact_serConstant _ hwf₁,
    Ixon.Verify.deConstantExact_serConstant _ hwf₂] at hde
  have hproj := Except.ok.inj hde
  cases hm1 : ms₁[0]'hB1 <;> cases hm2 : ms₂[0]'hB2 <;>
    simp [memberProjection, hm1, hm2] at hproj
  all_goals exact hproj

/-- **A complete family record at a group limit uses `memberAddr B 0 ms[0]` (`recUsesBlock`)**. -/
theorem familyCall_uses_block {calls cs : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {n : Nat}
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    (hn : n < 77) (hfc : FamilyCallAtLim calls bAddr t B rb (some n) cs) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (hpos : 0 < ms.size),
      recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧
      ConstAddrOf B cb (memberAddr B 0 (ms[0]'hpos)) ∧
      UsedRef E₀ rb (memberAddr B 0 (ms[0]'hpos)) := by
  obtain ⟨cb, -, ms, -, -, hpos, -, -, -, hcb, hms, -, -, -, -, -, -, hused, -, -⟩ :=
    familyCall_motive0_spec hC hbd hn hfc
  exact ⟨cb, ms, hpos, hcb, hms,
    Or.inr ⟨ms, 0, ms[0]'hpos, hms, Array.getElem?_eq_getElem hpos, Or.inl rfl⟩, hused⟩

/-! ## Projection and basis-role helpers -/

/-- **`KernelModeled::projection_block`** on a represented `Ixon.Constant` leaves the heap
unchanged, implies `IsProj c`, and returns `ownerOf a c`. -/
theorem projection_block_spec {c : Ixon.Constant} {a : _root_.Address}
    {x_c r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrep : L1.RepConstant h c x_c)
    (ev : ObsFn Obs.W "KernelModeled::projection_block" [x_c] h r h' cs) :
    h' = h ∧ IsProj c ∧ Core.S0.addr h r (Ix.Cert.ownerOf a c) := by
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := hrep
  match Obs.«KernelModeled::projection_block».obs ev with
  | .IPrj (hv15 := hv) (he95 := hr) (he96 := hh) .. =>
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    rw [e] at hinfoRep
    obtain ⟨ip, hci, -, hblk⟩ := L1.repConstantInfo_iPrj_inv hinfoRep
    obtain ⟨b, hb_eq, hb⟩ := L1.repIxonAddressRef_to_core_ing hblk
    rw [hh, hr]
    exact ⟨rfl, Or.inr (Or.inl ⟨ip, hci⟩), b, hb, by simp [Ix.Cert.ownerOf, hci, hb_eq]⟩
  | .CPrj (hv15 := hv) (he145 := hr) (he146 := hh) .. =>
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    rw [e] at hinfoRep
    obtain ⟨cp, hci, -, -, hblk⟩ := L1.repConstantInfo_cPrj_inv hinfoRep
    obtain ⟨b, hb_eq, hb⟩ := L1.repIxonAddressRef_to_core_ing hblk
    rw [hh, hr]
    exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨cp, hci⟩)), b, hb, by simp [Ix.Cert.ownerOf, hci, hb_eq]⟩
  | .RPrj (hv15 := hv) (he189 := hr) (he190 := hh) .. =>
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    rw [e] at hinfoRep
    obtain ⟨rp, hci, -, hblk⟩ := L1.repConstantInfo_rPrj_inv hinfoRep
    obtain ⟨b, hb_eq, hb⟩ := L1.repIxonAddressRef_to_core_ing hblk
    rw [hh, hr]
    exact ⟨rfl, Or.inr (Or.inr (Or.inr ⟨rp, hci⟩)), b, hb, by simp [Ix.Cert.ownerOf, hci, hb_eq]⟩
  | .DPrj (hv15 := hv) (he233 := hr) (he234 := hh) .. =>
    have e := (List.cons.inj (Value.construct.inj (hc_eq.symm.trans hv)).2.2).1
    rw [e] at hinfoRep
    obtain ⟨dp, hci, -, hblk⟩ := L1.repConstantInfo_dPrj_inv hinfoRep
    obtain ⟨b, hb_eq, hb⟩ := L1.repIxonAddressRef_to_core_ing hblk
    rw [hh, hr]
    exact ⟨rfl, Or.inl ⟨dp, hci⟩, b, hb, by simp [Ix.Cert.ownerOf, hci, hb_eq]⟩

/-- **A projection record loaded by `Ingress::get_ci` has empty `usedRefIdxs`.** -/
theorem proj_usedRefIdxs_nil {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {ab : Bytes.Address} {ap ptr : SourceValue F}
    {h h' : Heap F} (hab : Bytes.RepAddressRef Core.addrTy h ab ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs) (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : recordOf E₀ (Core.ixAddr ab) = some c) (hpr : IsProj c) :
    usedRefIdxs c = [] := by
  obtain ⟨raw, c', -, hh, hba, hx, htv, -⟩ := Claim.get_ci_head hab ev
  have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
    (Core.hashed_mono hsub hh) hba hx
  subst hcc
  have hpi : Assembly.IsProjInfo c.info := by
    rcases hpr with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> exact True.intro
  obtain ⟨hcanon, -⟩ := Claim.proj_canon hba hx htv hpi
  rw [hcanon]
  rcases hpr with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [usedRefIdxs, h]

/-- **`KernelModeled::projection_member`**: if `x` is a projection record in `E₀`, its parent block
is in `E₀`, `x` is a `ConstAddrOf` that parent block, and `usedRefIdxs c = []`. -/
theorem projection_member_spec {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {x : _root_.Address} {x_x r : SourceValue F} {h h' : Heap F}
    (hx : Core.S0.addr h x_x x)
    (ev : ObsFn Obs.W "KernelModeled::projection_member" [x_x] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ c, recordOf E₀ x = some c → IsProj c →
      usedRefIdxs c = [] ∧
      ∃ cb, recordOf E₀ (Ix.Cert.ownerOf x c) = some cb ∧
        ConstAddrOf (Ix.Cert.ownerOf x c) cb x := by
  intro c hc hpr
  obtain ⟨ab, hab, rfl⟩ := hx
  match Obs.«KernelModeled::projection_member».obs ev with
  | .IPrj (ev_crkizsgj := evL) (cs_skilefqi := csG) (ev_pvplyepc := evG) (hc_xqszncas := hcs) .. =>
    have hab' := Bytes.repAddressRef_heapMono₂ Core.addrTy evL.heap_extends hab
    have hsubG : ∀ cl ∈ csG, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    exact ⟨proj_usedRefIdxs_nil hS hab' evG hsubG hc hpr,
      proj_member_of_load hS hH hab' evG hsubG hc hpr⟩
  | .CPrj (ev_crkizsgj := evL) (cs_tafpebbo := csG) (ev_rnaxgwez := evG) (hc_efncukkh := hcs) .. =>
    have hab' := Bytes.repAddressRef_heapMono₂ Core.addrTy evL.heap_extends hab
    have hsubG : ∀ cl ∈ csG, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    exact ⟨proj_usedRefIdxs_nil hS hab' evG hsubG hc hpr,
      proj_member_of_load hS hH hab' evG hsubG hc hpr⟩
  | .RPrj (ev_crkizsgj := evL) (cs_nwqbwyif := csG) (ev_jqzwxbpt := evG) (hc_vptjzawx := hcs) .. =>
    have hab' := Bytes.repAddressRef_heapMono₂ Core.addrTy evL.heap_extends hab
    have hsubG : ∀ cl ∈ csG, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    exact ⟨proj_usedRefIdxs_nil hS hab' evG hsubG hc hpr,
      proj_member_of_load hS hH hab' evG hsubG hc hpr⟩
  | .DPrj (ev_crkizsgj := evL) (cs_hvhyumie := csG) (ev_tdzysuam := evG) (hc_nxcjkmpf := hcs) .. =>
    have hab' := Bytes.repAddressRef_heapMono₂ Core.addrTy evL.heap_extends hab
    have hsubG : ∀ cl ∈ csG, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    exact ⟨proj_usedRefIdxs_nil hS hab' evG hsubG hc hpr,
      proj_member_of_load hS hH hab' evG hsubG hc hpr⟩
  | .other (cs_oxwpunas := csL) (ev_crkizsgj := evL) (hne_xmppnoqc := hni)
      (hne_ovfsyazc := hnc) (hne_jztycgco := hnr) (hne_gmqblbbq := hnd) (hc_kjrxaxhl := hcs) .. =>
    exfalso
    have hsubL : ∀ cl ∈ csL, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨-, bytes, c', hsz, hh, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab evL
    have hrec' : recordOf E₀ (Core.ixAddr ab) = some c' := by
      have haddr' : _root_.Address.blake3Pure ⟨bytes.toArray⟩ = Core.ixAddr ab := haddr
      rw [← haddr']
      exact Claim.recordOf_of_hashed hH (Core.hashed_mono hsubL hh)
        (by simpa only [ByteArray.size, List.size_toArray] using hsz) hexact
    have ec : c' = c := Option.some.inj (hrec'.symm.trans hc)
    subst ec
    obtain ⟨infoVal, -, -, -, -, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have e := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [← e] at hinfoRep
    rcases hpr with ⟨dp, hci⟩ | ⟨ip, hci⟩ | ⟨cp, hci⟩ | ⟨rp, hci⟩
    · rw [hci] at hinfoRep; obtain ⟨_, hv, -⟩ := hinfoRep; exact hnd _ rfl hv
    · rw [hci] at hinfoRep; obtain ⟨_, hv, -⟩ := hinfoRep; exact hni _ rfl hv
    · rw [hci] at hinfoRep; obtain ⟨_, hv, -⟩ := hinfoRep; exact hnc _ rfl hv
    · rw [hci] at hinfoRep; obtain ⟨_, hv, -⟩ := hinfoRep; exact hnr _ rfl hv

private theorem roleNum_eq_nat_imp (ro : Ix.Kernel.Role) (k : Nat)
    (hk : k ∈ [0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 32, 33, 34, 35, 36])
    (heq : (Claim.roleNum ro : F) = (k : F)) :
    Ix.SpecDigest.groupOf ro < 6 ∧
    (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true) := by
  have hlt : Claim.roleNum ro < 100 := by cases ro <;> decide
  have hklt : k < 100 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> omega
  have hnat : Claim.roleNum ro = k :=
    Core.ModeledAux.natCast_inj_lt (Nat.lt_trans hlt (by decide)) (Nat.lt_trans hklt (by decide)) heq
  rw [← hnat] at hk
  cases ro <;> revert hk <;> decide

/-- **`KernelModeled::basis_role_allowed`** returning `1` on `roleNum ro` means `ro` is one of the
15 basis roles in groups `< 6` (`Nat`, `Eq`, `PUnit`, `Quot`), every one of which is either
`roleWalksBound` or `isQuotRole`. -/
theorem basis_role_allowed_spec {ro : Ix.Kernel.Role} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::basis_role_allowed" [.field (Claim.roleNum ro : F)] h r h' cs)
    (hr : r = .field 1) :
    h' = h ∧ Ix.SpecDigest.groupOf ro < 6 ∧
    (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true) := by
  match Obs.«KernelModeled::basis_role_allowed».obs ev with
  | .n0 (hv14 := hv) (he16 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 0 (by decide) (Value.field.inj hv)⟩
  | .n1 (hv22 := hv) (he24 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 1 (by decide) (Value.field.inj hv)⟩
  | .n2 (hv30 := hv) (he32 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 2 (by decide) (Value.field.inj hv)⟩
  | .n3 (hv38 := hv) (he40 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 3 (by decide) (Value.field.inj hv)⟩
  | .n8 (hv46 := hv) (he48 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 8 (by decide) (Value.field.inj hv)⟩
  | .n9 (hv54 := hv) (he56 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 9 (by decide) (Value.field.inj hv)⟩
  | .n10 (hv62 := hv) (he64 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 10 (by decide) (Value.field.inj hv)⟩
  | .n11 (hv70 := hv) (he72 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 11 (by decide) (Value.field.inj hv)⟩
  | .n12 (hv78 := hv) (he80 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 12 (by decide) (Value.field.inj hv)⟩
  | .n13 (hv86 := hv) (he88 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 13 (by decide) (Value.field.inj hv)⟩
  | .n32 (hv94 := hv) (he96 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 32 (by decide) (Value.field.inj hv)⟩
  | .n33 (hv102 := hv) (he104 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 33 (by decide) (Value.field.inj hv)⟩
  | .n34 (hv110 := hv) (he112 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 34 (by decide) (Value.field.inj hv)⟩
  | .n35 (hv118 := hv) (he120 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 35 (by decide) (Value.field.inj hv)⟩
  | .n36 (hv126 := hv) (he128 := hh) .. =>
    exact ⟨hh, roleNum_eq_nat_imp ro 36 (by decide) (Value.field.inj hv)⟩
  | .other (he150 := h0) .. =>
    exact absurd (Value.field.inj (h0.symm.trans hr)) zero_ne_one

/-- Every basis role accepted by `basis_role_allowed` is already stored (`AlreadyStoredRole`) at
every group `6 ≤ g`. -/
theorem basisRole_alreadyStoredRole {t : Ix.Kernel.RoleTable} {g : Nat} {x : _root_.Address}
    {ro : Ix.Kernel.Role} (hg : 6 ≤ g) (had : t.addressOf? ro = some x)
    (hlt : Ix.SpecDigest.groupOf ro < 6)
    (hk : RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true) :
    AlreadyStoredRole t g x := by
  have hvl : 6 ≤ valLimit g := by
    unfold valLimit
    split_ifs <;> omega
  rcases hk with hwb | hq
  · refine Or.inl ⟨ro, had, by rw [Claim.walkedRole_eq_roleWalksBound]; exact hwb, fun n hn => ?_⟩
    cases hn
    omega
  · exact Or.inr (Or.inl ⟨ro, had, by omega, Or.inr (Or.inr hq)⟩)

end IxVM.Refinement.Binding
