import IxVMRefinement.Binding.StoreOpOrder
import IxVMRefinement.Binding.RunFamilies
import IxVMRefinement.Binding.TableAdmitsValidate
import IxVM.Obs.KernelRoles

/-! # Operation-order scan for the well-founded block (groups 33 to 40)

In groups 33 to 40 (validated at limit 33), `KernelRoles::walk_ctx` skips its per-reference
operation-order assertion and `KernelRoles::op_order_scan` stands in for it:
* `KernelRoles::validate_op` calls `KernelRoles::op_order_scan_refs` on each well-founded
  operation's bound record;
* `KernelRoles::validate_op_equations` calls `KernelRoles::op_order_scan_except` on the used
  references (other than the operation's own address) of every certificate proof.

Every non-stop step of `op_order_scan` is at an address bound to no operation (`NotOp`), and
every `Muts` block entered by `op_order_scan_refs` is asserted non-modeled
(`KernelModeled::block_is_modeled = 0`, contradicting `ModeledRouteAt`). Since every stop of the
scan that is not an inert axiom is an `AlreadyStoredRole` of group `g`, an induction on
`GroupReach t E₀ g x` shows that every walk-reached address in groups 33 to 40 is entered by the
scan (`groupReach_in_scan_wf`), discharging both:
* `blockSteps_of_run`: `WalkStepsOrdered t E₀ g` for all `33 ≤ g ≤ 40`;
* `payReach_empty_wf`: `¬ PayReach t E₀ (runPayload calls bAddr t) g x` for all `33 ≤ g ≤ 40`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Core
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)

/-! ## Decided facts about roles in groups 33 to 40 -/

private theorem role_idx_lt_bound (ro : Ix.Kernel.Role) : ro.idx < 72057594037927936 := by
  cases ro <;> decide

private theorem wf_group_role_op (ro : Ix.Kernel.Role) :
    33 ≤ Ix.SpecDigest.groupOf ro → Ix.SpecDigest.groupOf ro ≤ 40 →
    RoleVal.roleSpecKindNat ro = 2 ∧
    RolesAux.evalLitTable (RolesAux.matchArms IxVM.KernelRoleSpec.op_evidence_is_proof.body)
      (roleNum ro) = some 1 := by
  cases ro <;> decide +kernel

private theorem specKind_four_inert (ro : Ix.Kernel.Role) :
    RoleVal.roleSpecKindNat ro = 4 → ro.inert = true := by
  cases ro <;> decide

private theorem roleSpecKind_cast_inj {ro : Ix.Kernel.Role} {k : Nat} (hk : k < 10)
    (h : ((RoleVal.roleSpecKindNat ro : Nat) : F) = (k : F)) :
    RoleVal.roleSpecKindNat ro = k := by
  have hlt : RoleVal.roleSpecKindNat ro < 10 := by cases ro <;> decide
  have hv := congrArg ZMod.val h
  rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hv
  exact hv

private theorem anchorWalkedF_cases (ro : Ix.Kernel.Role) :
    RoleVal.anchorWalkedF ro = 0 ∨ RoleVal.anchorWalkedF ro = 1 := by
  cases ro <;> decide

/-! ## `op_order_scan` step (`OpOrderScanStep` and non-operation tracking) -/

/-- **An address bound to no operation role.** -/
def NotOp (t : Ix.Kernel.RoleTable) (x : _root_.Address) : Prop :=
  ∀ ro : Ix.Kernel.Role, t.addressOf? ro = some x → RoleVal.roleSpecKindNat ro ≠ 2

/-- **Extended seam for `KernelRoles::op_order_scan`**: either the scan stops with `Ok a`, or
`NotOp t a` holds and it calls `op_order_scan_refs` on `a` strictly inside the call. -/
def ScanSeamExt (x_tbl x_lim x_needs : SourceValue F) (h₀ : Heap F)
    (t : Ix.Kernel.RoleTable) (Ok : _root_.Address → Prop) : Prop :=
  ∀ (a : _root_.Address) (x_a r : SourceValue F) (h h' : Heap F) (calls : List (Call F)),
    Heap.Extends h₀ h → BaseSeams.addr h x_a a →
    ObsFn Obs.W "KernelRoles::op_order_scan" [x_tbl, x_lim, x_needs, x_a] h r h' calls →
    Ok a ∨ (NotOp t a ∧ ∃ (r' : SourceValue F) (h₁ h₂ : Heap F) (cs : List (Call F)),
      Heap.Extends h h₁ ∧
      ObsFn Obs.W "KernelRoles::op_order_scan_refs" [x_tbl, x_lim, x_needs, x_a] h₁ r' h₂ cs ∧
      (∀ cl ∈ cs, cl ∈ calls) ∧ cs.length < calls.length)

private theorem sub_one_roleNum_scan {ro : Ix.Kernel.Role} {v : SourceValue F}
    (op : evalBinOp .sub (.field (roleNum ro + 1)) (.field 1) = .ok v) :
    v = .field (roleNum ro) := by
  simp only [evalBinOp, add_sub_cancel_right, Except.ok.injEq] at op
  exact op.symm

private theorem mul_one_of_bool_fields {a b : F}
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hmul : evalBinOp .mul (.field a : SourceValue F) (.field b : SourceValue F) =
      .ok (.field 1 : SourceValue F)) :
    a = 1 ∧ b = 1 := by
  simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at hmul
  rcases ha with rfl | rfl
  · simp at hmul
  · rcases hb with rfl | rfl
    · simp at hmul
    · exact ⟨rfl, rfl⟩

/-- **The step of `KernelRoles::op_order_scan`**, tracking both `ScanStopsAt` and `NotOp` on
every recursive entry into `op_order_scan_refs`. -/
theorem op_order_scan_step_ext (t : Ix.Kernel.RoleTable) (bAddr : _root_.Address)
    (n : Nat) (needs : List Ix.Kernel.Role) (x_tbl x_needs : SourceValue F) (h₀ : Heap F)
    (hn : n < 4294967296) (htbl : Claim.TableFullRep t bAddr h₀ x_tbl)
    (hneeds : RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h₀
      (needs.map (·.idx)) x_needs) :
    ScanSeamExt x_tbl (.field (n : F)) x_needs h₀ t (RoleVal.ScanStopsAt t n needs) := by
  intro a x_a r h h' calls hext ha ev
  have htbl_h := htbl.mono hext
  have hwf : t.wf = true := htbl_h.1
  have hnv : ZMod.val (n : F) = n := RolesAux.val_natCast (Nat.lt_trans hn (by decide))
  match Obs.«KernelRoles::op_order_scan».obs ev with
  | .n0 (m2 := m2) (cs68 := cs68) (ev36 := ev36) (ev14 := ev14) (ev70 := ev70) (hc103 := hc) .. =>
    obtain ⟨rfl, rfl, hlk⟩ := Claim.addr_index_lookup htbl_h ha ev36 ev14
    rcases hlk with ⟨-, hnone⟩ | ⟨ro, hbad, -⟩
    · refine Or.inr ⟨fun ro had => (hnone ro had).elim, r, _, h', cs68, Heap.Extends.refl _,
        ev70, fun cl hm => by rw [hc]; simp [hm], ?_⟩
      rw [hc]; simp only [List.length_cons, List.length_append]; omega
    · exact (RolesAux.roleNum_add_one_ne_zero ro (Value.field.inj hbad).symm).elim
  | .other_n2 (ev36 := ev36) (ev14 := ev14) (hne104 := hne) (op123 := op123)
      (ev152 := ev152) (ev138 := ev138) (ev182 := ev182) (sg247 := sg) (heq274 := heq1) .. =>
    obtain ⟨rfl, rfl, hlk⟩ := Claim.addr_index_lookup htbl_h ha ev36 ev14
    rcases hlk with ⟨rfl, -⟩ | ⟨ro, rfl, hof⟩
    · exact (hne rfl).elim
    · rw [sub_one_roleNum_scan op123] at ev152 ev182 sg
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev152
      obtain ⟨-, -, hlt_iff, -, rfl⟩ := Lib.less_than_fields_field ev138
      obtain ⟨hsk, rfl⟩ := RoleVal.role_spec_kind_spec ev182
      have hk2 : RoleVal.roleSpecKindNat ro = 2 := roleSpecKind_cast_inj (by decide)
        (Value.field.inj hsk.symm)
      left
      refine ⟨ro, hof, Or.inl ⟨hk2, ?_⟩⟩
      cases sg with
      | n1 hv1 _ _ _ =>
        left
        have h1 := hlt_iff.mp hv1
        rwa [RolesAux.val_groupOf, hnv] at h1
      | other cs219 _ ev221 _ =>
        right
        have hneeds_h := repList_heapMono₂ _ Claim.repBoundedIdx_heapMono₂ hext hneeds
        have ev221' : ObsFn Obs.W "KernelClaim::g_list_has"
            [x_needs, .field ((ro.idx : Nat) : F)] _ _ _ cs219 := ev221
        obtain ⟨-, hhas⟩ := Claim.g_list_has_spec (needs.map (·.idx)) (role_idx_lt_bound ro)
          hneeds_h ev221'
        obtain ⟨ro', hmem', hidx⟩ := List.mem_map.mp (hhas.mp heq1)
        rwa [← Ix.Kernel.Role.idx_inj hidx]
  | .other_n1_n1 (ev36 := ev36) (ev14 := ev14) (hne104 := hne) (op123 := op123)
      (ev152 := ev152) (ev138 := ev138) (ev182 := ev182) (ev_trfxbwiw := evAw)
      (op_uwfjvvdv := opMul) .. =>
    obtain ⟨rfl, rfl, hlk⟩ := Claim.addr_index_lookup htbl_h ha ev36 ev14
    rcases hlk with ⟨rfl, -⟩ | ⟨ro, rfl, hof⟩
    · exact (hne rfl).elim
    · rw [sub_one_roleNum_scan op123] at ev152 ev182 evAw
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev152
      obtain ⟨-, -, hlt_iff, h01, rfl⟩ := Lib.less_than_fields_field ev138
      obtain ⟨hsk, rfl⟩ := RoleVal.role_spec_kind_spec ev182
      obtain ⟨rfl, rfl⟩ := RoleVal.anchor_walked_full evAw
      have hk1 : RoleVal.roleSpecKindNat ro = 1 := roleSpecKind_cast_inj (by decide)
        (Value.field.inj hsk.symm)
      rcases h01 with rfl | rfl
      · obtain ⟨hbad, -⟩ := mul_one_of_bool_fields (Or.inl rfl) (anchorWalkedF_cases ro) opMul
        exact (zero_ne_one hbad).elim
      · obtain ⟨-, haw1⟩ := mul_one_of_bool_fields (Or.inr rfl) (anchorWalkedF_cases ro) opMul
        have hlt : Ix.SpecDigest.groupOf ro < n := by
          have h1 := hlt_iff.mp rfl
          rwa [RolesAux.val_groupOf, hnv] at h1
        have haw : RoleVal.anchorWalked ro = true := by
          unfold RoleVal.anchorWalked
          rw [haw1]; decide
        left
        refine ⟨ro, hof, Or.inr ⟨by omega, hlt, fun ⟨_, hf⟩ => by rw [haw] at hf; cases hf⟩⟩
  | .other_n1_other (cs_inseifvo := cs_rec) (ev36 := ev36) (ev14 := ev14) (hne104 := hne)
      (op123 := op123) (ev152 := ev152) (ev138 := ev138) (ev182 := ev182)
      (ev_trfxbwiw := evAw) (ev_oksdtpbz := evr) (hc_cpeakbbh := hc) .. =>
    obtain ⟨rfl, rfl, hlk⟩ := Claim.addr_index_lookup htbl_h ha ev36 ev14
    rcases hlk with ⟨rfl, -⟩ | ⟨ro, rfl, hof⟩
    · exact (hne rfl).elim
    · rw [sub_one_roleNum_scan op123] at ev152 ev182 evAw
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev152
      obtain ⟨-, -, -, -, rfl⟩ := Lib.less_than_fields_field ev138
      obtain ⟨hsk, rfl⟩ := RoleVal.role_spec_kind_spec ev182
      obtain ⟨-, rfl⟩ := RoleVal.anchor_walked_full evAw
      have hk1 : RoleVal.roleSpecKindNat ro = 1 := roleSpecKind_cast_inj (by decide)
        (Value.field.inj hsk.symm)
      refine Or.inr ⟨fun ro' had' h2 => ?_, r, _, h', cs_rec, Heap.Extends.refl _, evr,
        fun cl hm => by rw [hc]; simp [hm], ?_⟩
      · have e : ro' = ro := addressOf_role_inj hwf had' hof
        rw [e, hk1] at h2; cases h2
      · rw [hc]; simp only [List.length_cons, List.length_append]; omega
  | .other_other_n1 (ev36 := ev36) (ev14 := ev14) (hne104 := hne) (op123 := op123)
      (ev152 := ev152) (ev138 := ev138) (ev182 := ev182) (hne280 := hne2)
      (hne_arcdkpuy := hne1) .. =>
    obtain ⟨rfl, rfl, hlk⟩ := Claim.addr_index_lookup htbl_h ha ev36 ev14
    rcases hlk with ⟨rfl, -⟩ | ⟨ro, rfl, hof⟩
    · exact (hne rfl).elim
    · rw [sub_one_roleNum_scan op123] at ev152 ev182
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev152
      obtain ⟨-, -, hlt_iff, -, rfl⟩ := Lib.less_than_fields_field ev138
      obtain ⟨hsk, rfl⟩ := RoleVal.role_spec_kind_spec ev182
      have hlt : Ix.SpecDigest.groupOf ro < n := by
        have h1 := hlt_iff.mp rfl
        rwa [RolesAux.val_groupOf, hnv] at h1
      have hnk2 : RoleVal.roleSpecKindNat ro ≠ 2 := fun h2 =>
        hne2 (by rw [hsk, h2]; rfl)
      have hnk1 : RoleVal.roleSpecKindNat ro ≠ 1 := fun h1 =>
        hne1 (by rw [hsk, h1]; rfl)
      left
      exact ⟨ro, hof, Or.inr ⟨hnk2, hlt, fun ⟨h1, _⟩ => hnk1 h1⟩⟩
  | .other_other_other (cs310 := cs_rec) (ev36 := ev36) (ev14 := ev14) (hne104 := hne)
      (op123 := op123) (ev152 := ev152) (ev138 := ev138) (ev182 := ev182) (hne280 := hne2)
      (ev312 := evr) (hc345 := hc) .. =>
    obtain ⟨rfl, rfl, hlk⟩ := Claim.addr_index_lookup htbl_h ha ev36 ev14
    rcases hlk with ⟨rfl, -⟩ | ⟨ro, rfl, hof⟩
    · exact (hne rfl).elim
    · rw [sub_one_roleNum_scan op123] at ev152 ev182
      obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev152
      obtain ⟨-, -, -, -, rfl⟩ := Lib.less_than_fields_field ev138
      obtain ⟨hsk, rfl⟩ := RoleVal.role_spec_kind_spec ev182
      have hnk2 : RoleVal.roleSpecKindNat ro ≠ 2 := fun h2 =>
        hne2 (by rw [hsk, h2]; rfl)
      refine Or.inr ⟨fun ro' had' h2 => ?_, r, _, h', cs_rec, Heap.Extends.refl _, evr,
        fun cl hm => by rw [hc]; simp [hm], ?_⟩
      · have e : ro' = ro := addressOf_role_inj hwf had' hof
        exact hnk2 (e ▸ h2)
      · rw [hc]; simp only [List.length_cons, List.length_append]; omega

/-- **The step specification `RoleVal.OpOrderScanStep` holds unconditionally.** -/
theorem op_order_scan_step : RoleVal.OpOrderScanStep := by
  intro t bAddr n needs x_tbl x_needs h₀ hn htbl hneeds a x_a r h h' calls hext ha ev
  rcases op_order_scan_step_ext t bAddr n needs x_tbl x_needs h₀ hn htbl hneeds
      a x_a r h h' calls hext ha ev with h | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

/-! ## Extended scan closure: non-modeled blocks and non-operation children -/

private theorem notModeledRouteAt_mono {cs₁ cs₂ : List (Call F)} {x : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : ¬ ModeledRouteAt cs₁ x) : ¬ ModeledRouteAt cs₂ x :=
  fun h2 => h fun bp r h0 h1 cs b ev hcs hb hix =>
    h2 bp r h0 h1 cs b ev (fun cl hcl => hsub cl (hcs cl hcl)) hb hix

/-- **A record entered by `op_order_scan_refs`**, carrying both the non-modeled assertion on
`Muts` blocks and `NotOp` on every non-stop child entered via `op_order_scan`. -/
def ScanEntryExt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (Ok : _root_.Address → Prop)
    (within : List _root_.Address) (x : _root_.Address) : Prop :=
  ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
    rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = x ∧
    Ixon.deConstant rawBytes = .ok c ∧ Ixon.deConstantExact rawBytes = .ok c ∧
    (∀ ms, c.info = .muts ms → ¬ ModeledRouteAt calls x) ∧
    (Ok (Ix.Cert.ownerOf x c) ∨ (Ix.Cert.ownerOf x c ∈ within ∧ NotOp t (Ix.Cert.ownerOf x c)) ∨
      (¬ IsProj c ∧ Ix.Cert.ownerOf x c = x)) ∧
    ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ BaseSeams.usedRefIdxs c →
      Ok c.refs.toList[j] ∨ (c.refs.toList[j] ∈ within ∧ NotOp t c.refs.toList[j])

/-- **The extended entered records are closed.** -/
def ScanClosedExt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (Ok : _root_.Address → Prop)
    (entered : List _root_.Address) : Prop :=
  ∀ x ∈ entered, ScanEntryExt calls t Ok entered x

theorem ScanEntryExt.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    {Ok : _root_.Address → Prop} {w₁ w₂ : List _root_.Address} {x : _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (hw : ∀ y ∈ w₁, y ∈ w₂) (h : ScanEntryExt cs₁ t Ok w₁ x) :
    ScanEntryExt cs₂ t Ok w₂ x := by
  obtain ⟨rawBytes, c, hsz, hh, hb, hde, hdeExact, hnm, hown, hrefs⟩ := h
  refine ⟨rawBytes, c, hsz, Claim.hashed_mono hsub hh, hb, hde, hdeExact,
    fun ms hms => notModeledRouteAt_mono hsub (hnm ms hms), ?_, ?_⟩
  · rcases hown with h | ⟨hm, hno⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨hw _ hm, hno⟩)
    · exact Or.inr (Or.inr h)
  · intro j hj hu
    rcases hrefs j hj hu with h | ⟨hm, hno⟩
    · exact Or.inl h
    · exact Or.inr ⟨hw _ hm, hno⟩

theorem ScanClosedExt.mono {cs₁ cs₂ : List (Call F)} {t : Ix.Kernel.RoleTable}
    {Ok : _root_.Address → Prop} {entered : List _root_.Address}
    (hsub : ∀ cl ∈ cs₁, cl ∈ cs₂) (h : ScanClosedExt cs₁ t Ok entered) :
    ScanClosedExt cs₂ t Ok entered :=
  fun x hx => (h x hx).mono hsub (fun _ hy => hy)

theorem scanClosedExt_nil (calls : List (Call F)) (t : Ix.Kernel.RoleTable)
    (Ok : _root_.Address → Prop) : ScanClosedExt calls t Ok [] :=
  fun _ hx => (nomatch hx)

theorem ScanClosedExt.append {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {Ok : _root_.Address → Prop} {e₁ e₂ : List _root_.Address}
    (h₁ : ScanClosedExt calls t Ok e₁) (h₂ : ScanClosedExt calls t Ok e₂) :
    ScanClosedExt calls t Ok (e₁ ++ e₂) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact (h₁ x h).mono (fun _ hc => hc) (fun _ hy => List.mem_append_left _ hy)
  · exact (h₂ x h).mono (fun _ hc => hc) (fun _ hy => List.mem_append_right _ hy)

private theorem refs_size_lt_bound_ext {rawBytes : ByteArray} {c : Ixon.Constant}
    (hsz : rawBytes.size < 4294967296)
    (hdeExact : Ixon.deConstantExact rawBytes = .ok c) :
    c.refs.size < 8589934592 := by
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound rawBytes c hdeExact
  have hrefs : c.refs.size ≤ c.resourceSize := by
    dsimp [Ixon.Constant.resourceSize]; omega
  omega

private theorem scan_ext_fuel_aux {x_tbl x_lim x_needs : SourceValue F} {h₀ : Heap F}
    {t : Ix.Kernel.RoleTable} {Ok : _root_.Address → Prop}
    (seam : ScanSeamExt x_tbl x_lim x_needs h₀ t Ok) :
    ∀ (fuel : Nat),
      (∀ {a : _root_.Address} {x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel → Heap.Extends h₀ h → BaseSeams.addr h x_a a →
         ObsFn Obs.W "KernelRoles::op_order_scan_refs" [x_tbl, x_lim, x_needs, x_a] h r h' calls →
         ∃ entered : List _root_.Address, a ∈ entered ∧ ScanClosedExt calls t Ok entered) ∧
      (∀ {i : Nat} {refs : List _root_.Address} {idxs : List Nat}
         {x_refs x_used r : SourceValue F} {h h' : Heap F} {calls : List (Call F)},
         calls.length ≤ fuel → Heap.Extends h₀ h →
         i + refs.length < 8589934592 →
         RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs x_refs →
         Claim.RepSortedIdxFrom h idxs i x_used →
         ObsFn Obs.W "KernelRoles::op_order_scan_list"
           [x_tbl, x_lim, x_needs, x_refs, x_used, .field (i : F)] h r h' calls →
         ∃ entered : List _root_.Address, ScanClosedExt calls t Ok entered ∧
           ∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs →
             Ok refs[j] ∨ (refs[j] ∈ entered ∧ NotOp t refs[j])) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel ih =>
    have scanAt : ∀ {b : _root_.Address} {x_b r : SourceValue F} {h h' : Heap F}
        {cs : List (Call F)}, cs.length < fuel → Heap.Extends h₀ h → BaseSeams.addr h x_b b →
        ObsFn Obs.W "KernelRoles::op_order_scan" [x_tbl, x_lim, x_needs, x_b] h r h' cs →
        ∃ entered : List _root_.Address, ScanClosedExt cs t Ok entered ∧
          (Ok b ∨ (b ∈ entered ∧ NotOp t b)) := by
      intro b x_b r h h' cs hlt hbase hb evs
      rcases seam b x_b r h h' cs hbase hb evs with
        hok | ⟨hno, r', h₁, h₂, cs', hext, evr, hsub, hlen⟩
      · exact ⟨[], scanClosedExt_nil cs t Ok, Or.inl hok⟩
      · obtain ⟨entered, hmem, hcl⟩ :=
          (ih cs'.length (by omega)).1 (Nat.le_refl _) (hbase.trans hext)
            (BaseSeams.addr_mono hext hb) evr
        exact ⟨entered, hcl.mono hsub, Or.inr ⟨hmem, hno⟩⟩
    refine ⟨?_, ?_⟩
    · intro a x_a r h h' calls hfuel hbase ha ev
      obtain ⟨m2, cs12, x_info, w39, x_refs, w40, w41, v407, m408, cs410, cs419, v426, m457,
        cs465, ev14, sg415, ev467, ev421, hc482⟩ :=
        Obs.«KernelRoles::op_order_scan_refs».obs ev
      obtain ⟨ext1, rawBytes, c, hsz, hh_load, hblk, hde, hdeExact, hrep, _⟩ :=
        Claim.load_verified_constant_de ha ev14
      have hlen410 : cs410.length < calls.length := by
        rw [hc482]; simp only [List.length_cons, List.length_append]; omega
      have hseg : Heap.Extends m2 m408 ∧
          (∀ ms, c.info = .muts ms → ¬ ModeledRouteAt cs410 a) ∧
          ∃ entered₁ : List _root_.Address,
            ScanClosedExt cs410 t Ok entered₁ ∧
            (Ok (Ix.Cert.ownerOf a c) ∨
              (Ix.Cert.ownerOf a c ∈ entered₁ ∧ NotOp t (Ix.Cert.ownerOf a c)) ∨
              (¬ IsProj c ∧ Ix.Cert.ownerOf a c = a)) := by
        obtain ⟨infoVal, _, _, _, _, hv_c, hinfo, _, _, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.1] at hinfo
        rcases sg415 with
          ⟨w104, x_b, cs118, hv81, ev120, hc153⟩ |
          ⟨w183, w184, x_b, cs203, hne155, hv160, ev205, hc238⟩ |
          ⟨w268, x_b, cs282, hne155, hne240, hv245, ev284, hc317⟩ |
          ⟨w347, x_b, cs361, hne155, hne240, hne319, hv324, ev363, hc396⟩ |
          ⟨wM, vM, mM, csM, hne155, hne240, hne319, hne398, hvM, evM, heqM, hrM, hhM, hcM⟩ |
          ⟨hne155, hne240, hne319, hne398, hneM, he404, he405, hc406⟩
        · rw [hv81] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case iPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs118.length < fuel := by
              have : cs118.length < cs410.length := by rw [hc153]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev120
            refine ⟨ev120.heap_extends, (fun _ hms => by cases hms),
              entered₁, hcl.mono (fun cl hcl' => by rw [hc153]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv160] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case cPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs203.length < fuel := by
              have : cs203.length < cs410.length := by rw [hc238]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev205
            refine ⟨ev205.heap_extends, (fun _ hms => by cases hms),
              entered₁, hcl.mono (fun cl hcl' => by rw [hc238]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv245] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case rPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs282.length < fuel := by
              have : cs282.length < cs410.length := by rw [hc317]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev284
            refine ⟨ev284.heap_extends, (fun _ hms => by cases hms),
              entered₁, hcl.mono (fun cl hcl' => by rw [hc317]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · rw [hv324] at hinfo
          cases hc_i : c.info <;> rw [hc_i] at hinfo
          case dPrj p =>
            obtain ⟨pv, hpv_eq, blkPtr, hpv, hblk_addr⟩ := hinfo
            rw [hpv] at hpv_eq
            injection hpv_eq with _ _ h1
            simp only [List.cons.injEq, and_true] at h1
            injection h1 with _ _ hpargs
            simp only [List.cons.injEq, and_true] at hpargs
            rw [← hpargs.2] at hblk_addr
            have hown : Ix.Cert.ownerOf a c = p.block := by simp [Ix.Cert.ownerOf, hc_i]
            have hlt : cs361.length < fuel := by
              have : cs361.length < cs410.length := by rw [hc396]; simp
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt (hbase.trans ext1) hblk_addr ev363
            refine ⟨ev363.heap_extends, (fun _ hms => by cases hms),
              entered₁, hcl.mono (fun cl hcl' => by rw [hc396]; simp [hcl']), ?_⟩
            rw [hown]
            rcases hmem with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
          all_goals (obtain ⟨_, hv', _⟩ := hinfo; simp at hv')
        · have hnp : ¬ IsProj c := by
            intro hp
            rcases hp with ⟨_, hi⟩ | ⟨_, hi⟩ | ⟨_, hi⟩ | ⟨_, hi⟩ <;>
              (rw [hi] at hinfo; obtain ⟨pv, hv', _⟩ := hinfo;
                first | exact hne155 [_] rfl hv' | exact hne240 [_] rfl hv'
                      | exact hne319 [_] rfl hv' | exact hne398 [_] rfl hv')
          have hown : Ix.Cert.ownerOf a c = a := by
            unfold Ix.Cert.ownerOf
            cases hc_i : c.info <;> try rfl
            all_goals
              exfalso; apply hnp
              first | exact Or.inl ⟨_, hc_i⟩ | exact Or.inr (Or.inl ⟨_, hc_i⟩)
                    | exact Or.inr (Or.inr (Or.inl ⟨_, hc_i⟩))
                    | exact Or.inr (Or.inr (Or.inr ⟨_, hc_i⟩))
          have hnm : ∀ ms, c.info = .muts ms → ¬ ModeledRouteAt cs410 a := by
            intro ms _ hmod
            obtain ⟨ab, hab, hix⟩ := BaseSeams.addr_mono ext1 ha
            exact hmod x_a vM m2 mM csM ab evM (fun cl hm => by rw [hcM]; simp [hm]) hab hix heqM
          refine ⟨by subst hhM; exact evM.heap_extends, hnm, [], scanClosedExt_nil cs410 t Ok,
            Or.inr (Or.inr ⟨hnp, hown⟩)⟩
        · have hnp : ¬ IsProj c := by
            intro hp
            rcases hp with ⟨_, hi⟩ | ⟨_, hi⟩ | ⟨_, hi⟩ | ⟨_, hi⟩ <;>
              (rw [hi] at hinfo; obtain ⟨pv, hv', _⟩ := hinfo;
                first | exact hne155 [_] rfl hv' | exact hne240 [_] rfl hv'
                      | exact hne319 [_] rfl hv' | exact hne398 [_] rfl hv')
          have hown : Ix.Cert.ownerOf a c = a := by
            unfold Ix.Cert.ownerOf
            cases hc_i : c.info <;> try rfl
            all_goals
              exfalso; apply hnp
              first | exact Or.inl ⟨_, hc_i⟩ | exact Or.inr (Or.inl ⟨_, hc_i⟩)
                    | exact Or.inr (Or.inr (Or.inl ⟨_, hc_i⟩))
                    | exact Or.inr (Or.inr (Or.inr ⟨_, hc_i⟩))
          have hnm : ∀ ms, c.info = .muts ms → ¬ ModeledRouteAt cs410 a := by
            intro ms hms
            rw [hms] at hinfo
            obtain ⟨pv, hv', _⟩ := hinfo
            exact (hneM [pv] rfl hv').elim
          refine ⟨by subst he405; exact Heap.Extends.refl _, hnm, [],
            scanClosedExt_nil cs410 t Ok, Or.inr (Or.inr ⟨hnp, hown⟩)⟩
      obtain ⟨ext_seg, hnm_seg, entered₁, hcl₁, hown⟩ := hseg
      obtain ⟨ext_idx, hidxs⟩ := Claim.const_idxs_of_spec (hrep.mono ext_seg) ev467
      have hrefs_rep :
          RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem m457 c.refs.toList
            x_refs := by
        obtain ⟨_, _, refsPtr, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
        injection hv_c with _ _ hargs_c
        simp only [List.cons.injEq] at hargs_c
        rw [← hargs_c.2.2.1] at hr_list
        exact repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ (ext_seg.trans ext_idx) hr_list
      have hrefs_bound : 0 + c.refs.toList.length < 8589934592 := by
        rw [Nat.zero_add, Array.length_toList]
        exact refs_size_lt_bound_ext hsz hdeExact
      have ev421' : ObsFn Obs.W "KernelRoles::op_order_scan_list"
          [x_tbl, x_lim, x_needs, x_refs, v426, .field ((0 : Nat) : F)] m457 r h' cs419 := by
        rw [Nat.cast_zero]; exact ev421
      have hlen419 : cs419.length < calls.length := by
        rw [hc482]; simp only [List.length_cons, List.length_append]; omega
      obtain ⟨entered₂, hcl₂, hlist⟩ :=
        (ih cs419.length (by omega)).2 (i := 0) (Nat.le_refl _)
          (hbase.trans (ext1.trans (ext_seg.trans ext_idx))) hrefs_bound hrefs_rep hidxs ev421'
      have hsub1 : ∀ cl ∈ cs410, cl ∈ calls := fun cl hcl => by rw [hc482]; simp [hcl]
      have hsub2 : ∀ cl ∈ cs419, cl ∈ calls := fun cl hcl => by rw [hc482]; simp [hcl]
      have hsub0 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => by rw [hc482]; simp [hcl]
      refine ⟨a :: (entered₁ ++ entered₂), List.mem_cons_self .., ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · refine ⟨rawBytes, c, hsz, Claim.hashed_mono hsub0 hh_load, hblk, hde, hdeExact,
          fun ms hms => notModeledRouteAt_mono hsub1 (hnm_seg ms hms), ?_, ?_⟩
        · rcases hown with h | ⟨hm, hno⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hm), hno⟩)
          · exact Or.inr (Or.inr h)
        · intro j hj hu
          rcases hlist j hj (by rw [Nat.zero_add]; exact hu) with h | ⟨hm, hno⟩
          · exact Or.inl h
          · exact Or.inr ⟨List.mem_cons_of_mem _ (List.mem_append_right _ hm), hno⟩
      · rcases List.mem_append.mp hx' with h | h
        · exact (hcl₁ x h).mono hsub1
            (fun _ hy => List.mem_cons_of_mem _ (List.mem_append_left _ hy))
        · exact (hcl₂ x h).mono hsub2
            (fun _ hy => List.mem_cons_of_mem _ (List.mem_append_right _ hy))
    · intro i refs idxs x_refs x_used r h h' calls hfuel hbase hbound hrefs hidxs ev
      cases Obs.«KernelRoles::op_order_scan_list».obs ev with
      | Nil ld12 he22 he23 hc24 =>
        obtain rfl := Lib.rep_nil_of_load hrefs ld12
        exact ⟨[], scanClosedExt_nil calls t Ok, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      | Cons x_b x_rest m_pop cs_pop x_hit x_next_used v125 m126 cs128 cs137 v145
          ld12 ev_pop sg133 op194 ev139 hc196 =>
        obtain ⟨b, rest, rfl, hb_rep, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
        have hi : i < 72057594037927936 := by simp at hbound; omega
        obtain ⟨rfl, hiff, hidxs_next⟩ := Claim.sorted_pop_spec idxs hi hidxs ev_pop
        have hlen128 : cs128.length ≤ calls.length := by
          rw [hc196]; simp only [List.length_cons, List.length_append]; omega
        have hseg : Heap.Extends h m126 ∧ ∃ entered₁ : List _root_.Address,
            ScanClosedExt cs128 t Ok entered₁ ∧
              (i ∈ idxs → Ok b ∨ (b ∈ entered₁ ∧ NotOp t b)) := by
          cases sg133 with
          | n1 cs80 _ ev82 hc115 =>
            have hlt : cs80.length < fuel := by
              have : cs80.length < cs128.length := by
                rw [hc115]; simp only [List.length_cons]; omega
              omega
            obtain ⟨entered₁, hcl, hmem⟩ := scanAt hlt hbase hb_rep ev82
            exact ⟨ev82.heap_extends, entered₁,
              hcl.mono (fun cl hcl' => by rw [hc115]; simp [hcl']), fun _ => hmem⟩
          | other hne116 he122 he123 hc124 =>
            refine ⟨?_, [], scanClosedExt_nil cs128 t Ok, fun hin => absurd (hiff.mpr hin) hne116⟩
            subst he123; exact Heap.Extends.refl _
        obtain ⟨ext1, entered₁, hcl₁, hhead⟩ := hseg
        obtain rfl := Decl.evalBinOp_add_one i op194
        have hbound' : (i + 1) + rest.length < 8589934592 := by simp at hbound; omega
        have hlen137 : cs137.length < calls.length := by
          rw [hc196]; simp only [List.length_cons, List.length_append]; omega
        obtain ⟨entered₂, hcl₂, htail⟩ :=
          (ih cs137.length (by omega)).2 (Nat.le_refl _) (hbase.trans ext1) hbound'
            (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext1 hrest_rep)
            (hidxs_next.mono ext1) ev139
        have hsub1 : ∀ cl ∈ cs128, cl ∈ calls := fun cl hcl => by rw [hc196]; simp [hcl]
        have hsub2 : ∀ cl ∈ cs137, cl ∈ calls := fun cl hcl => by rw [hc196]; simp [hcl]
        refine ⟨entered₁ ++ entered₂, (hcl₁.mono hsub1).append (hcl₂.mono hsub2),
          fun j hj hij => ?_⟩
        cases j with
        | zero =>
          rcases hhead (by simpa using hij) with h0 | ⟨hm, hno⟩
          · exact Or.inl (by simpa using h0)
          · exact Or.inr ⟨List.mem_append_left _ (by simpa using hm), by simpa using hno⟩
        | succ j' =>
          have hj' : j' < rest.length := by simpa using hj
          have hij' : i + 1 + j' ∈ idxs := by
            rw [show i + 1 + j' = i + (j' + 1) by omega]; exact hij
          rcases htail j' hj' hij' with h1 | ⟨hm, hno⟩
          · exact Or.inl (by simpa using h1)
          · exact Or.inr ⟨List.mem_append_right _ (by simpa using hm), by simpa using hno⟩

/-- **The extended scan from a record** (`KernelRoles::op_order_scan_refs`). -/
theorem op_order_scan_refs_ext_spec {x_tbl x_lim x_needs : SourceValue F} {h₀ : Heap F}
    {t : Ix.Kernel.RoleTable} {Ok : _root_.Address → Prop}
    (seam : ScanSeamExt x_tbl x_lim x_needs h₀ t Ok)
    {a : _root_.Address} {x_a r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbase : Heap.Extends h₀ h) (ha : BaseSeams.addr h x_a a)
    (ev : ObsFn Obs.W "KernelRoles::op_order_scan_refs" [x_tbl, x_lim, x_needs, x_a] h r h' calls) :
    ∃ entered : List _root_.Address, a ∈ entered ∧ ScanClosedExt calls t Ok entered :=
  (scan_ext_fuel_aux seam calls.length).1 (Nat.le_refl _) hbase ha ev

private theorem except_guard_scan {x y y' v : SourceValue F} {p : Prop} [Decidable p]
    (hy : y = .field (if p then 1 else 0))
    (op1 : evalBinOp .sub (.field 1) y = .ok y')
    (op2 : evalBinOp .mul x y' = .ok v)
    (hx : x = .field 1) (hp : ¬ p) : v = .field 1 := by
  subst hy hx
  simp only [hp, ↓reduceIte] at op1
  simp only [evalBinOp, Except.ok.injEq] at op1
  subst op1
  simp only [evalBinOp, Except.ok.injEq] at op2
  rw [← op2]; simp

/-- **The extended scan from a certificate's references** (`KernelRoles::op_order_scan_except`). -/
theorem op_order_scan_except_ext_spec {x_tbl x_lim x_needs : SourceValue F} {h₀ : Heap F}
    {t : Ix.Kernel.RoleTable} {Ok : _root_.Address → Prop}
    (seam : ScanSeamExt x_tbl x_lim x_needs h₀ t Ok) {a : _root_.Address} {idxs : List Nat} :
    ∀ (refs : List _root_.Address) {i : Nat} {x_refs x_used x_a r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      Heap.Extends h₀ h → i + refs.length < 8589934592 →
      RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem h refs x_refs →
      Claim.RepSortedIdxFrom h idxs i x_used →
      BaseSeams.addr h x_a a →
      ObsFn Obs.W "KernelRoles::op_order_scan_except"
        [x_tbl, x_lim, x_needs, x_refs, x_used, .field (i : F), x_a] h r h' calls →
      ∃ entered : List _root_.Address, ScanClosedExt calls t Ok entered ∧
        ∀ j : Nat, (hj : j < refs.length) → i + j ∈ idxs → refs[j] ≠ a →
          Ok refs[j] ∨ (refs[j] ∈ entered ∧ NotOp t refs[j])
  | [], _, _, _, _, _, _, _, _, _, _, hrefs, _, _, ev => by
    cases Obs.«KernelRoles::op_order_scan_except».obs ev with
    | Nil _ _ _ _ =>
      exact ⟨[], scanClosedExt_nil _ t Ok, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    | Cons _ _ _ _ _ _ _ _ _ _ _ ld12 _ _ _ _ _ =>
      obtain ⟨_, _, hbad, -⟩ := Lib.rep_cons_of_load hrefs ld12
      cases hbad
  | b :: rest, i, x_refs, x_used, x_a, r, h, h', calls, hbase, hbound, hrefs, hidxs, ha, ev => by
    cases Obs.«KernelRoles::op_order_scan_except».obs ev with
    | Nil ld12 _ _ _ => cases Lib.rep_nil_of_load hrefs ld12
    | Cons x_b x_rest m_pop cs_pop x_hit x_next_used v163 m164 cs166 cs175 v183
        ld12 ev_pop sg171 op233 ev177 hc242 =>
      obtain ⟨b', rest', heq, hb_rep, hrest_rep⟩ := Lib.rep_cons_of_load hrefs ld12
      injection heq with hb hrs
      subst hb hrs
      have hi : i < 72057594037927936 := by simp at hbound; omega
      obtain ⟨rfl, hiff, hidxs_next⟩ := Claim.sorted_pop_spec idxs hi hidxs ev_pop
      obtain ⟨b₀, hb₀, hbix⟩ := id hb_rep
      obtain ⟨a₀, ha₀, haix⟩ := id ha
      have hseg : Heap.Extends h m164 ∧ ∃ entered₁ : List _root_.Address,
          ScanClosedExt cs166 t Ok entered₁ ∧
            (i ∈ idxs → b ≠ a → Ok b ∨ (b ∈ entered₁ ∧ NotOp t b)) := by
        cases sg171 with
        | n1 m43 y52 y82 cs92 cs118 ev94 _ _ ev120 hc153 =>
          obtain ⟨_, hh43⟩ := Lib.address_eq_spec ev94 hb₀ ha₀
          have hh43' : h = m43 := hh43.symm; subst hh43'
          rcases seam b x_b v163 h m164 cs118 hbase hb_rep ev120 with
            hok | ⟨hno, r', h₁, h₂, cs', hext, evr, hsub, _⟩
          · exact ⟨ev120.heap_extends, [], scanClosedExt_nil cs166 t Ok, fun _ _ => Or.inl hok⟩
          · obtain ⟨entered₁, hmem, hcl⟩ :=
              op_order_scan_refs_ext_spec seam (hbase.trans hext) (BaseSeams.addr_mono hext hb_rep) evr
            have hsub' : ∀ cl ∈ cs', cl ∈ cs166 :=
              fun cl hm => by rw [hc153]; simp [hsub cl hm]
            exact ⟨ev120.heap_extends, entered₁, hcl.mono hsub',
              fun _ _ => Or.inr ⟨hmem, hno⟩⟩
        | other v42 m43 y52 y82 cs92 ev94 op88 op58 hne154 _ he161 _ =>
          obtain ⟨hy, hh43⟩ := Lib.address_eq_spec ev94 hb₀ ha₀
          have hh43' : h = m43 := hh43.symm; subst hh43'
          refine ⟨by rw [he161], [], scanClosedExt_nil cs166 t Ok, fun hin hne => ?_⟩
          exfalso
          have hba : ¬ b₀ = a₀ := fun e => hne (by rw [← hbix, ← haix, e])
          exact hne154 (except_guard_scan hy op88 op58 (hiff.mpr hin) hba)
      obtain ⟨ext1, entered₁, hcl₁, hhead⟩ := hseg
      obtain rfl := Decl.evalBinOp_add_one i op233
      have hbound' : (i + 1) + rest.length < 8589934592 := by simp at hbound; omega
      obtain ⟨entered₂, hcl₂, htail⟩ :=
        op_order_scan_except_ext_spec seam rest (hbase.trans ext1) hbound'
          (repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ ext1 hrest_rep)
          (hidxs_next.mono ext1)
          (BaseSeams.addr_mono ext1 ha) ev177
      have hsub1 : ∀ cl ∈ cs166, cl ∈ calls := fun cl hcl => by rw [hc242]; simp [hcl]
      have hsub2 : ∀ cl ∈ cs175, cl ∈ calls := fun cl hcl => by rw [hc242]; simp [hcl]
      refine ⟨entered₁ ++ entered₂, (hcl₁.mono hsub1).append (hcl₂.mono hsub2),
        fun j hj hij hne => ?_⟩
      cases j with
      | zero =>
        rcases hhead (by simpa using hij) (by simpa using hne) with h0 | ⟨hm, hno⟩
        · exact Or.inl (by simpa using h0)
        · exact Or.inr ⟨List.mem_append_left _ (by simpa using hm), by simpa using hno⟩
      | succ j' =>
        have hj' : j' < rest.length := by simpa using hj
        have hij' : i + 1 + j' ∈ idxs := by
          rw [show i + 1 + j' = i + (j' + 1) by omega]; exact hij
        rcases htail j' hj' hij' (by simpa using hne) with h1 | ⟨hm, hno⟩
        · exact Or.inl (by simpa using h1)
        · exact Or.inr ⟨List.mem_append_right _ (by simpa using hm), by simpa using hno⟩

/-! ## `KernelRoles::op_group_needs` as a bounded index list -/

private def repIdx (_ : Heap F) (n : Nat) (v : SourceValue F) : Prop :=
  v = .field (n : F)

private theorem repIdx_heapMono₂ : HeapMono₂ repIdx := fun _ _ _ _ _ h => h

private def isFldListCtor (ctorWant : String) :
    Generic.Expr F → Option (List (Generic.Expr F))
  | .construct name args ctor es =>
    if ctor == ctorWant && instanceName [] name args == Obs.Names.«Lists::Node<Field>» then
      some es
    else none
  | .constructAs _ t ctor es =>
    if ctor == ctorWant && constructorName [] t == Obs.Names.«Lists::Node<Field>» then
      some es
    else none
  | _ => none

private theorem isFldListCtor_sound {ctorWant : String} {inner : Generic.Expr F}
    {es : List (Generic.Expr F)} (hc : isFldListCtor ctorWant inner = some es)
    {locals : Environment F Nat} {h : Heap F} {v : SourceValue F} {h' : Heap F}
    {calls : List (Call F)}
    (d : ObsExpr Obs.W [] locals inner h v h' calls) :
    ∃ vs, ObsArgs Obs.W [] locals es h vs h' calls ∧
      v = .construct Obs.Names.«Lists::Node<Field>» ctorWant vs := by
  cases inner with
  | construct name args ctor es' =>
    simp only [isFldListCtor] at hc
    split at hc
    case isTrue hcond =>
      obtain ⟨rfl, hinst⟩ := by simpa [Bool.and_eq_true, beq_iff_eq] using hcond
      injection hc with hes; subst hes
      obtain ⟨vs, a, hres⟩ := d.construct_inv
      rw [hinst] at hres; exact ⟨vs, a, hres⟩
    case isFalse => cases hc
  | constructAs ps t ctor es' =>
    simp only [isFldListCtor] at hc
    split at hc
    case isTrue hcond =>
      obtain ⟨rfl, hctor⟩ := by simpa [Bool.and_eq_true, beq_iff_eq] using hcond
      injection hc with hes; subst hes
      obtain ⟨vs, a, hres⟩ := d.constructAs_inv
      rw [hctor] at hres; exact ⟨vs, a, hres⟩
    case isFalse => cases hc
  | _ => simp [isFldListCtor] at hc

private def decodeNatList : Nat → Generic.Expr F → Option (List Nat)
  | 0, _ => none
  | fuel + 1, .builtin (.ascribe _) [e] => decodeNatList fuel e
  | fuel + 1, .store inner =>
    match isFldListCtor "Nil" inner with
    | some [] => some []
    | _ =>
      match isFldListCtor "Cons" inner with
      | some [.literal x, tail] => (decodeNatList fuel tail).map (ZMod.val x :: ·)
      | _ => none
  | _, _ => none

private theorem natCast_val_eq_scan (x : F) : ((ZMod.val x : Nat) : F) = x := by
  apply ZMod.val_injective
  exact RolesAux.val_natCast (ZMod.val_lt x)

private theorem decodeNatList_sound :
    ∀ (fuel : Nat) {e : Generic.Expr F} {ns : List Nat}
      (hd : decodeNatList fuel e = some ns)
      {locals : Environment F Nat} {h : Heap F} {r : SourceValue F} {h' : Heap F}
      {calls : List (Call F)}
      (d : ObsExpr Obs.W [] locals e h r h' calls),
      Heap.Extends h h' ∧ RepList Obs.Names.«Lists::Node<Field>» repIdx h' ns r
  | 0, _, _, hd, _, _, _, _, _, _ => by simp [decodeNatList] at hd
  | fuel + 1, e, ns, hd, locals, h, r, h', calls, d => by
    cases e with
    | builtin op es =>
      cases op with
      | ascribe t =>
        cases es with
        | nil => simp [decodeNatList] at hd
        | cons e0 es1 =>
          cases es1 with
          | nil =>
            simp only [decodeNatList] at hd
            obtain ⟨vs, a, ap⟩ := d.builtin_inv
            obtain ⟨v0, vs1, m1, _, _, rfl, d0, a1, _⟩ := a.cons_inv
            obtain ⟨rfl, rfl, _⟩ := a1.nil_inv
            obtain rfl := Builtin.ascribe_inv ap
            exact decodeNatList_sound fuel hd d0
          | cons _ _ => simp [decodeNatList] at hd
      | _ => simp [decodeNatList] at hd
    | store inner =>
      simp only [decodeNatList] at hd
      obtain ⟨vin, min, din, rfl, rfl⟩ := d.store_inv
      cases hnil : isFldListCtor "Nil" inner with
      | some es_nil =>
        rw [hnil] at hd
        cases es_nil with
        | nil =>
          simp only [Option.some.injEq] at hd; subst hd
          obtain ⟨vs, a, hvin⟩ := isFldListCtor_sound hnil din
          obtain ⟨rfl, rfl, _⟩ := a.nil_inv; subst hvin
          rw [Value.type]
          exact ⟨Heap.Extends.snoc _ _,
            Lib.rep_store_nil (en := Obs.Names.«Lists::Node<Field>») (R := repIdx) min⟩
        | cons _ _ =>
          cases hcons : isFldListCtor "Cons" inner with
          | none => rw [hcons] at hd; cases hd
          | some es_cons =>
            obtain ⟨_, _, h1⟩ := isFldListCtor_sound hnil din
            obtain ⟨_, _, h2⟩ := isFldListCtor_sound hcons din
            exact (RolesAux.construct_ctor_ne (by decide) (h1.symm.trans h2)).elim
      | none =>
        rw [hnil] at hd
        cases hcons : isFldListCtor "Cons" inner with
        | none => rw [hcons] at hd; cases hd
        | some es_cons =>
          rw [hcons] at hd
          cases es_cons with
          | nil => simp at hd
          | cons e_head es_tail1 =>
            cases e_head with
            | literal x =>
              cases es_tail1 with
              | nil => simp at hd
              | cons tail es_tail2 =>
                cases es_tail2 with
                | nil =>
                  simp only [Option.map_eq_some_iff] at hd
                  obtain ⟨ns', htail, rfl⟩ := hd
                  obtain ⟨vs, a, hvin⟩ := isFldListCtor_sound hcons din
                  obtain ⟨vx, vs1, m1, _, _, rfl, dx, a1, _⟩ := a.cons_inv
                  obtain ⟨rfl, rfl, _⟩ := dx.literal_inv
                  obtain ⟨vt, vs2, m2, _, _, rfl, dt, a2, _⟩ := a1.cons_inv
                  obtain ⟨rfl, rfl, _⟩ := a2.nil_inv; subst hvin
                  rw [Value.type]
                  obtain ⟨ext_t, hrep_t⟩ := decodeNatList_sound fuel htail dt
                  have hhead : repIdx min (ZMod.val x) (.field x) :=
                    congrArg Value.field (natCast_val_eq_scan x).symm
                  exact ⟨ext_t.trans (Heap.Extends.snoc _ _),
                    Lib.rep_store_cons repIdx_heapMono₂ hhead hrep_t⟩
                | cons _ _ => simp at hd
            | _ =>
              cases es_tail1 with
              | nil => simp at hd
              | cons _ es_tail2 => cases es_tail2 <;> simp at hd
    | _ => simp [decodeNatList] at hd

private def evalNatListArms (k : Nat) :
    List (Generic.Pattern F × Generic.Expr F) → Option (List Nat)
  | (.literal c, body) :: rest =>
    if k == ZMod.val c then decodeNatList 32 body else evalNatListArms k rest
  | (.wildcard, body) :: _ => decodeNatList 32 body
  | _ => none

private theorem selectArm_natListArms {arms : List (Generic.Pattern F × Generic.Expr F)}
    {x : F} {ns : List Nat}
    (ht : evalNatListArms (ZMod.val x) arms = some ns)
    {h : Heap F} {bs : Environment F Nat} {body : Generic.Expr F}
    (hsel : selectArm Obs.W [] h (.field x) arms = Except.ok (some (bs, body))) :
    decodeNatList 32 body = some ns := by
  induction arms with
  | nil => simp [evalNatListArms] at ht
  | cons arm rest ih =>
    rcases arm with ⟨pat, armBody⟩
    cases pat with
    | literal c =>
      simp only [evalNatListArms] at ht
      by_cases hxc_b : (ZMod.val x == ZMod.val c) = true
      · rw [ite_eq_left hxc_b] at ht
        have hxc : x = c := ZMod.val_injective _ (beq_iff_eq.mp hxc_b)
        subst hxc
        rcases selectArm_cons_inv hsel with ⟨_, rfl⟩ | ⟨nm, _⟩
        · exact ht
        · exact absurd rfl (MatchesConst.none_inv (MatchesConst.literal x) nm)
      · rw [ite_eq_right hxc_b] at ht
        have hxc_ne : x ≠ c := fun e => hxc_b (beq_iff_eq.mpr (congrArg ZMod.val e))
        rcases selectArm_cons_inv hsel with ⟨mt, _⟩ | ⟨_, hsel'⟩
        · obtain ⟨hv, _⟩ := MatchesConst.some_inv (MatchesConst.literal c) mt
          exact absurd (Value.field.inj hv) hxc_ne
        · exact ih ht hsel'
    | wildcard =>
      simp only [evalNatListArms] at ht
      rcases selectArm_cons_inv hsel with ⟨_, rfl⟩ | ⟨nm, _⟩
      · exact ht
      · exact (matchPattern_wildcard_none nm).elim
    | _ => simp [evalNatListArms] at ht

private theorem group_needs_arms_fin :
    ∀ i : Fin 77,
      evalNatListArms i.val (RolesAux.matchArms IxVM.KernelRoleSpec.group_needs.body) =
        some ((RoleVal.groupNeededRoles i.val).map Ix.Kernel.Role.idx) := by
  decide +kernel

private theorem repList_idx_to_bounded :
    ∀ {ns : List Nat} {h : Heap F} {p : SourceValue F},
      (∀ n ∈ ns, n < 72057594037927936) →
      RepList Obs.Names.«Lists::Node<Field>» repIdx h ns p →
      RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h ns p
  | [], _, _, _, .nil cell => .nil cell
  | n :: rest, _, _, hlt, .cons cell rh rt =>
    .cons cell ⟨hlt n (List.mem_cons_self ..), rh⟩
      (repList_idx_to_bounded (fun m hm => hlt m (List.mem_cons_of_mem _ hm)) rt)

/-- **`KernelRoles::op_group_needs`** returns the group's needed role indices as a
`Claim.RepBoundedIdx` list. -/
theorem op_group_needs_bounded_spec {ro : Ix.Kernel.Role} {r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ev : ObsFn Obs.W "KernelRoles::op_group_needs" [.field (roleNum ro)] h r h' calls) :
    Heap.Extends h h' ∧
    RepList Obs.Names.«Lists::Node<Field>» Claim.RepBoundedIdx h'
      ((RoleVal.groupNeededRoles (Ix.SpecDigest.groupOf ro)).map (·.idx)) r := by
  match Obs.«KernelRoles::op_group_needs».obs ev with
  | .run (ev19 := ev19) (ev6 := ev6) .. =>
    obtain ⟨rfl, rfl⟩ := RolesAux.role_group_spec ev19
    have hg77 : Ix.SpecDigest.groupOf ro < 77 := RoleVal.groupOf_lt_77 ro
    have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.KernelRoleSpec.group_needs.lookup
      (by simp [IxVM.KernelRoleSpec.group_needs, ControlLower.hasControl]) ev6
    have hp : (IxVM.KernelRoleSpec.group_needs.params.map fun (n, t) =>
        (n, (t.subst []).toCore)).map Prod.fst = ["g"] := rfl
    have hb : IxVM.KernelRoleSpec.group_needs.body =
        .matchValue (.var "g") (RolesAux.matchArms IxVM.KernelRoleSpec.group_needs.body) := rfl
    rw [hp, hb] at d0
    obtain ⟨_, m2, bs3, body4, _, _, d7, sel8, d9, -⟩ := d0.matchValue_inv
    obtain ⟨l10, rfl, -⟩ := d7.var_inv
    simp at l10; subst l10
    have hval : ZMod.val ((Ix.SpecDigest.groupOf ro : Nat) : F) = Ix.SpecDigest.groupOf ro :=
      RolesAux.val_groupOf ro
    have ht : evalNatListArms (ZMod.val ((Ix.SpecDigest.groupOf ro : Nat) : F))
        (RolesAux.matchArms IxVM.KernelRoleSpec.group_needs.body) =
        some ((RoleVal.groupNeededRoles (Ix.SpecDigest.groupOf ro)).map Ix.Kernel.Role.idx) := by
      rw [hval]; exact group_needs_arms_fin ⟨_, hg77⟩
    have hdec := selectArm_natListArms ht sel8
    obtain ⟨ext, hrep⟩ := decodeNatList_sound 32 hdec d9
    refine ⟨ext, repList_idx_to_bounded (fun n hn => ?_) hrep⟩
    obtain ⟨ro', -, rfl⟩ := List.mem_map.mp hn
    exact role_idx_lt_bound ro'

/-! ## Scan observations extracted from well-founded operation validations -/

private theorem evList_length_scan {es : List (Ix.Kernel.Evidence _root_.Address)}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<KernelRoles::RoleEvidence>» [l] h r h' cs)
    (hl : RepList evListEnum EvRep h es l) :
    r = .field (es.length : F) ∧ h' = h := by
  have ev' : ObsFn Obs.W (Instance.mk "Lists::length" [.named "KernelRoles::RoleEvidence" []]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelRoles::RoleEvidence>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.named "KernelRoles::RoleEvidence" []]).symbol
      EvRep h es l := by
    rw [Obs.Names.«Lists::Node<KernelRoles::RoleEvidence>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

private theorem evRep_proof_inv_scan {h : Heap F} {thm : _root_.Address}
    {x_e x_thm : SourceValue F} (hev : EvRep h (.proof thm) x_e)
    (hx : x_e = .construct "KernelRoles::RoleEvidence" "Proof" [x_thm]) :
    BaseSeams.addr h x_thm thm := by
  rcases hev with ⟨hdef, _⟩ | ⟨a, p, hprf, hv, ha⟩
  · cases hdef
  · injection hprf with hix
    rw [hx] at hv
    injection hv with _ _ hargs
    injection hargs with hp _
    subst hp
    exact ⟨a, ha, hix.symm⟩

private theorem evRep_proof_not_defeq_scan {h : Heap F} {thm : _root_.Address}
    {x_e : SourceValue F} (hev : EvRep h (.proof thm) x_e)
    (hx : x_e = .construct "KernelRoles::RoleEvidence" "Defeq" []) : False := by
  rcases hev with ⟨hdef, _⟩ | ⟨_, p, _, hv, _⟩
  · cases hdef
  · rw [hx] at hv
    exact RolesAux.construct_ctor_ne (by decide) hv

private theorem nonempty_evidence_scan {ro : Ix.Kernel.Role} {t : Ix.Kernel.RoleTable}
    {es : List (Ix.Kernel.Evidence _root_.Address)} {k : Nat}
    (hk0 : 0 < k) (hk10 : k < 10)
    (hes : es = [] ∨ ∃ arr, (ro, arr) ∈ t.evidence.toList ∧ arr.toList = es)
    (heq : (Value.field (es.length : F) : SourceValue F) = .field (k : F)) :
    ∃ arr : Array (Ix.Kernel.Evidence _root_.Address),
      (ro, arr) ∈ t.evidence.toList ∧ arr.toList = es := by
  rcases hes with rfl | ⟨arr, hmem, harr⟩
  · exfalso
    have hz := congrArg ZMod.val (Value.field.inj heq)
    rw [List.length_nil, Nat.cast_zero, ZMod.val_zero,
      RolesAux.val_natCast (Nat.lt_trans hk10 (by decide))] at hz
    omega
  · exact ⟨arr, hmem, harr⟩

/-- **The certificate scan observed inside `KernelRoles::validate_op_equations`.** -/
private theorem validate_op_equations_scan {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {n : Nat} {ro : Ix.Kernel.Role} {a : _root_.Address}
    {es : List (Ix.Kernel.Evidence _root_.Address)} :
    ∀ {x_rc x_tbl x_a x_val x_ev x_k r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)},
      n < 4294967296 →
      Claim.RCFullRep t bAddr n h x_rc →
      Claim.TableFullRep t bAddr h x_tbl →
      BaseSeams.addr h x_a a →
      RepList evListEnum EvRep h es x_ev →
      ObsFn Obs.W "KernelRoles::validate_op_equations"
        [x_rc, x_tbl, .field (roleNum ro), x_a, x_val, x_ev, x_k] h r h' calls →
      Heap.Extends h h' ∧
      ∀ thm : _root_.Address, .proof thm ∈ es →
        ∃ (rawBytes : ByteArray) (c : Ixon.Constant) (entered : List _root_.Address),
          rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = thm ∧
          Ixon.deConstantExact rawBytes = .ok c ∧
          ScanClosedExt calls t
            (RoleVal.ScanStopsAt t n (RoleVal.groupNeededRoles (Ix.SpecDigest.groupOf ro)))
            entered ∧
          ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ BaseSeams.usedRefIdxs c →
            c.refs.toList[j] ≠ a →
            RoleVal.ScanStopsAt t n (RoleVal.groupNeededRoles (Ix.SpecDigest.groupOf ro))
              c.refs.toList[j] ∨
            (c.refs.toList[j] ∈ entered ∧ NotOp t c.refs.toList[j])
  | x_rc, x_tbl, x_a, x_val, x_ev, x_k, r, h, h', calls, hn, hrc, htbl, ha, hlist, ev => by
    cases Obs.«KernelRoles::validate_op_equations».obs ev with
    | Nil ld12 _ he23 _ =>
      rw [← evListEnum] at ld12
      obtain rfl := Lib.rep_nil_of_load hlist ld12
      subst he23
      exact ⟨Heap.Extends.refl _, fun _ hm => (nomatch hm)⟩
    | Cons x_e x_rest v1048 m1049 cs1051 cs1060 v1069 ld12 sg1056 _ ev1062 hc1127 =>
      rw [← evListEnum] at ld12
      obtain ⟨e, rest, rfl, he_rep, hrest_rep⟩ := Lib.rep_cons_of_load hlist ld12
      have tailMember : (⟨"KernelRoles::validate_op_equations",
          [x_rc, x_tbl, .field (roleNum ro), x_a, x_val, x_rest, v1069], m1049⟩ : Call F) ∈ calls := by
        rw [hc1127]; simp
      have ext_seg_all : Heap.Extends h m1049 := (ev.call_heap_bounds tailMember).1
      have hseg : Heap.Extends h m1049 ∧
          ∀ thm : _root_.Address, e = .proof thm →
            ∃ (rawBytes : ByteArray) (c : Ixon.Constant) (entered : List _root_.Address),
              rawBytes.size < 4294967296 ∧ Hashed cs1051 rawBytes ∧
              Address.blake3Pure rawBytes = thm ∧ Ixon.deConstantExact rawBytes = .ok c ∧
              ScanClosedExt cs1051 t
                (RoleVal.ScanStopsAt t n (RoleVal.groupNeededRoles (Ix.SpecDigest.groupOf ro)))
                entered ∧
              ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ BaseSeams.usedRefIdxs c →
                c.refs.toList[j] ≠ a →
                RoleVal.ScanStopsAt t n (RoleVal.groupNeededRoles (Ix.SpecDigest.groupOf ro))
                  c.refs.toList[j] ∨
                (c.refs.toList[j] ∈ entered ∧ NotOp t c.refs.toList[j]) := by
        match sg1056 with
        | .n0_Defeq (hv83 := hv83) .. =>
          refine ⟨ext_seg_all, fun thm he => ?_⟩
          exact (evRep_proof_not_defeq_scan (by rwa [← he]) hv83).elim
        | .n0_Proof (heq379 := heq) .. => exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Defeq (heq431 := heq) .. => exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Proof_Defn_other (heq1257 := heq) .. =>
          exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Proof_other (heq1904 := heq) .. =>
          exact (zero_ne_one (Value.field.inj heq)).elim
        | .other_Proof_Defn_Theorem
            (m43 := roleHeap) (x_thm := thmPtr) (m450 := rawHeap) (cs460 := rawCalls)
            (w496 := refsPtr) (m728 := scopeHeap) (m809 := idxHeap) (m831 := walkHeap)
            (m877 := mWalkOut) (cs932 := scanCalls) (v936 := limVal) (v937 := needsVal)
            (m950 := limHeap) (m970 := needsHeap)
            (ev56 := roleRun) (hv442 := proofShape) (ev462 := rawRun)
            (ev631 := ciRun) (ev702 := substRun) (ev740 := scopeRun)
            (ev821 := idxRun) (ev843 := guardRun) (ev889 := walkRun)
            (ev960 := limRun) (ev980 := needsRun) (ev934 := scanRun)
            (hc1225 := segCalls) .. =>
          cases e with
          | defeq => exact ⟨ext_seg_all, fun _ he => by cases he⟩
          | proof thm₀ =>
            have extRole := roleRun.heap_extends
            have extRaw := rawRun.heap_extends
            have extToScope := ciRun.heap_extends.trans (substRun.heap_extends.trans scopeRun.heap_extends)
            have ha_raw : BaseSeams.addr roleHeap thmPtr thm₀ :=
              BaseSeams.addr_mono extRole (evRep_proof_inv_scan he_rep proofShape)
            obtain ⟨_, rawBytes, c, hsz, hh_raw, hblk, _, hdeExact, hrep, _⟩ :=
              Claim.load_verified_constant_de ha_raw rawRun
            obtain ⟨extIdx, hidxs⟩ := Claim.const_idxs_of_spec (hrep.mono extToScope) idxRun
            have extWalkOut : Heap.Extends h mWalkOut :=
              extRole.trans (extRaw.trans (extToScope.trans (extIdx.trans
                (guardRun.heap_extends.trans walkRun.heap_extends))))
            obtain ⟨rfl, rfl⟩ := Claim.role_ctx_limit_spec (hrc.mono extWalkOut) limRun
            obtain ⟨extNeeds, hneeds⟩ := op_group_needs_bounded_spec needsRun
            have extToNeeds : Heap.Extends h needsHeap := extWalkOut.trans extNeeds
            have extRawToNeeds : Heap.Extends rawHeap needsHeap :=
              extToScope.trans (extIdx.trans (guardRun.heap_extends.trans
                (walkRun.heap_extends.trans extNeeds)))
            have hrefs_needs : RepList Obs.Names.«Lists::Node<&[Field; 32]>» Claim.RepAddrElem
                needsHeap c.refs.toList refsPtr := by
              obtain ⟨_, _, refsVal, _, _, hv_c, _, _, hr_list, _, _⟩ := hrep
              injection hv_c with _ _ hargs_c
              simp only [List.cons.injEq] at hargs_c
              rw [← hargs_c.2.2.1] at hr_list
              exact repList_heapMono₂ _ Claim.repAddrElem_heapMono₂ extRawToNeeds hr_list
            have hidxs_needs := hidxs.mono
              (guardRun.heap_extends.trans (walkRun.heap_extends.trans extNeeds))
            have hbound : 0 + c.refs.toList.length < 8589934592 := by
              rw [Nat.zero_add, Array.length_toList]
              exact refs_size_lt_bound_ext hsz hdeExact
            have seam := op_order_scan_step_ext t bAddr n
              (RoleVal.groupNeededRoles (Ix.SpecDigest.groupOf ro)) x_tbl needsVal needsHeap
              hn (htbl.mono extToNeeds) hneeds
            rw [← Nat.cast_zero (R := F)] at scanRun
            obtain ⟨entered, hcl, hscan⟩ :=
              op_order_scan_except_ext_spec seam c.refs.toList (Heap.Extends.refl _) hbound
                hrefs_needs hidxs_needs (BaseSeams.addr_mono extToNeeds ha) scanRun
            have hsub_raw : ∀ cl ∈ rawCalls, cl ∈ cs1051 := fun cl hm => by rw [segCalls]; simp [hm]
            have hsub_sc : ∀ cl ∈ scanCalls, cl ∈ cs1051 := fun cl hm => by rw [segCalls]; simp [hm]
            refine ⟨ext_seg_all, fun thm he => ?_⟩
            injection he with hthm; subst hthm
            exact ⟨rawBytes, c, entered, hsz, Claim.hashed_mono hsub_raw hh_raw, hblk, hdeExact,
              hcl.mono hsub_sc, fun j hj hu hne => hscan j hj (by rw [Nat.zero_add]; exact hu) hne⟩
      obtain ⟨ext1, hhead⟩ := hseg
      obtain ⟨ext2, htail⟩ :=
        validate_op_equations_scan hn (hrc.mono ext1) (htbl.mono ext1) (BaseSeams.addr_mono ext1 ha)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext1 hrest_rep) ev1062
      have hsub1 : ∀ cl ∈ cs1051, cl ∈ calls := fun cl hm => by rw [hc1127]; simp [hm]
      have hsub2 : ∀ cl ∈ cs1060, cl ∈ calls := fun cl hm => by rw [hc1127]; simp [hm]
      refine ⟨ext1.trans ext2, fun thm hmem => ?_⟩
      rcases List.mem_cons.mp hmem with rfl | hrest
      · obtain ⟨raw, c, ent, hsz, hh, hbl, hde, hcl, hsc⟩ := hhead thm rfl
        exact ⟨raw, c, ent, hsz, Claim.hashed_mono hsub1 hh, hbl, hde, hcl.mono hsub1, hsc⟩
      · obtain ⟨raw, c, ent, hsz, hh, hbl, hde, hcl, hsc⟩ := htail thm hrest
        exact ⟨raw, c, ent, hsz, Claim.hashed_mono hsub2 hh, hbl, hde, hcl.mono hsub2, hsc⟩

/-- **Both operation-order scans of a well-founded operation (`33 ≤ g ≤ 40`)**: `validate_op`
scans its bound record via `op_order_scan_refs`, and `validate_op_equations` scans every
certificate proof's used references (other than the operation's own address) via
`op_order_scan_except`, both at limit `33` and needs `groupNeededRoles g`. -/
theorem validate_role_wf_op_scans {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {g : Nat} {ro : Ix.Kernel.Role}
    (hg33 : 33 ≤ g) (hg40 : g ≤ 40) (hr : ro ∈ roleGroup g)
    (hv : RoleValidationIn calls bAddr t g ro) :
    (∃ (a : _root_.Address) (entered : List _root_.Address),
      t.addressOf? ro = some a ∧ a ∈ entered ∧
      ScanClosedExt calls t (RoleVal.ScanStopsAt t 33 (RoleVal.groupNeededRoles g)) entered) ∧
    (∀ (arr : Array (Ix.Kernel.Evidence _root_.Address)) (thm a : _root_.Address),
      t.addressOf? ro = some a → (ro, arr) ∈ t.evidence.toList →
      Ix.Kernel.Evidence.proof thm ∈ arr.toList →
      ∃ (rawBytes : ByteArray) (c : Ixon.Constant) (entered : List _root_.Address),
        rawBytes.size < 4294967296 ∧ Hashed calls rawBytes ∧ Address.blake3Pure rawBytes = thm ∧
        Ixon.deConstantExact rawBytes = .ok c ∧
        ScanClosedExt calls t (RoleVal.ScanStopsAt t 33 (RoleVal.groupNeededRoles g)) entered ∧
        ∀ j : Nat, (hj : j < c.refs.toList.length) → j ∈ BaseSeams.usedRefIdxs c →
          c.refs.toList[j] ≠ a →
          RoleVal.ScanStopsAt t 33 (RoleVal.groupNeededRoles g) c.refs.toList[j] ∨
          (c.refs.toList[j] ∈ entered ∧ NotOp t c.refs.toList[j])) := by
  have hgro : Ix.SpecDigest.groupOf ro = g := groupOf_of_mem_roleGroup hr
  obtain ⟨h2, hp1⟩ := wf_group_role_op ro (hgro ▸ hg33) (hgro ▸ hg40)
  have hlim33 : RoleVal.groupValLimit g = 33 := by
    unfold RoleVal.groupValLimit
    have h1 : ¬ g < 33 := by omega
    have h2' : g < 41 := by omega
    simp [h1, h2']
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsub⟩ := hv
  rw [hlim33] at hrc
  have hwf : t.wf = true := htbl.1
  let c₀ : Ctx := { E := default, env := default, t := t, lim := none }
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _
  | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, _⟩ := RoleVal.role_spec_kind_spec ev124
    rw [h2] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n2 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs236
      ev14 ev47 _ ev80 ev100 _ ev124 ev238 hc279 =>
    obtain ⟨ext_ba, a, ha_m2, had⟩ := RoleVal.role_bound_addr_uncond htbl.toTableRep ev14
    have ext_m111 : Heap.Extends m2 m111 :=
      ev47.heap_extends.trans (ev80.heap_extends.trans
        (ev100.heap_extends.trans ev124.heap_extends))
    match Obs.«KernelRoles::validate_op».obs ev238 with
    | .other (heq575 := hbad) .. => exact (zero_ne_one (Value.field.inj hbad)).elim
    | .Defn (m2 := rawHeap) (m200 := m102_op) (m209 := m111_op) (m260 := m162)
        (m391 := m_sg2) (cs393 := cs_sg2) (v399 := v191) (m400 := m192)
        (m463 := m255) (cs486 := cs278)
        (ev14 := rawLoad) (sg207 := sg109) (ev242 := ev144) (ev221 := ev123)
        (ev272 := ev174) (sg398 := sg2) (ev412 := ev204) (ev453 := ev245)
        (ev473 := ev265) (heq482 := heq274) (ev488 := ev280) (hc544 := hc320) .. =>
      have ext_safe : Heap.Extends rawHeap m102_op := by
        cases sg109 with
        | Safe _ _ he64 _ => rw [he64]
        | other _ heq95 _ _ _ => exact absurd (Value.field.inj heq95) zero_ne_one
      have ext_w : Heap.Extends m111 m111_op :=
        rawLoad.heap_extends.trans (ext_safe.trans (ev144.heap_extends.trans ev123.heap_extends))
      have ext_162 : Heap.Extends h m162 :=
        ext_ba.trans (ext_m111.trans (ext_w.trans ev174.heap_extends))
      have ha_162 : BaseSeams.addr m162 v1 a :=
        BaseSeams.addr_mono (ext_m111.trans (ext_w.trans ev174.heap_extends)) ha_m2
      have hrc_162 := hrc.mono ext_162
      have htbl_162 := htbl.mono ext_162
      have hscan_bound : Heap.Extends m162 m_sg2 ∧
          ∃ entered : List _root_.Address, a ∈ entered ∧
            ScanClosedExt calls t (RoleVal.ScanStopsAt t 33 (RoleVal.groupNeededRoles g)) entered := by
        cases sg2 with
        | other _ _ _ ev_p hne_p _ _ _ =>
          exact absurd (op_evidence_is_proof_val hp1 ev_p).1 hne_p
        | n1 m290 _ cs319 v323 v324 m334 _ m354 _ ev_p ev_lim ev_needs ev_scan hc_sg2 =>
          obtain ⟨-, hm290⟩ := op_evidence_is_proof_val hp1 ev_p
          subst hm290
          obtain ⟨rfl, rfl⟩ := Claim.role_ctx_limit_spec hrc_162 ev_lim
          obtain ⟨ext_gn, hneeds⟩ := op_group_needs_bounded_spec ev_needs
          rw [hgro] at hneeds
          have seam := op_order_scan_step_ext t bAddr 33 (RoleVal.groupNeededRoles g)
            x_tbl v324 m354 (by decide) (htbl_162.mono ext_gn) hneeds
          obtain ⟨entered, hmem, hcl⟩ :=
            op_order_scan_refs_ext_spec seam (Heap.Extends.refl _) (BaseSeams.addr_mono ext_gn ha_162)
              ev_scan
          have hsub_sc : ∀ cl ∈ cs319, cl ∈ calls := fun cl hm =>
            hsub cl (by rw [hc279]; simp [show cl ∈ cs236 by
              rw [hc320]; simp [show cl ∈ cs_sg2 by rw [hc_sg2]; simp [hm]]])
          exact ⟨ext_gn.trans ev_scan.heap_extends, entered, hmem, hcl.mono hsub_sc⟩
      obtain ⟨ext_sg2, entered₀, hmem₀, hcl₀⟩ := hscan_bound
      refine ⟨⟨a, entered₀, had, hmem₀, hcl₀⟩, ?_⟩
      have htbl_sg2 : TableRep c₀.t m_sg2 x_tbl := (htbl_162.mono ext_sg2).toTableRep
      obtain ⟨es, hlist_m192, hes⟩ :=
        Core.role_evidence_step (ScopedCtx.unrestricted c₀) ev204 x_tbl ro rfl htbl_sg2
      obtain ⟨rfl, rfl⟩ := evList_length_scan ev245 hlist_m192
      obtain ⟨rfl, k, hk0, hk10, rfl⟩ := RoleVal.op_equation_count_pos h2 ev265
      obtain ⟨arr₀, hmem_ev₀, harr_eq⟩ := nonempty_evidence_scan hk0 hk10 hes heq274
      have e_255 : Heap.Extends m162 m255 := ext_sg2.trans ev204.heap_extends
      obtain ⟨_, hprfs⟩ :=
        validate_op_equations_scan (by decide) (hrc_162.mono e_255) (htbl_162.mono e_255)
          (BaseSeams.addr_mono e_255 ha_162) hlist_m192 ev280
      have hsub_ev : ∀ cl ∈ cs278, cl ∈ calls := fun cl hm =>
        hsub cl (by rw [hc279]; simp [show cl ∈ cs236 by rw [hc320]; simp [hm]])
      intro arr thm a' had' hm hthm
      have ha_eq : a' = a := Option.some.inj (had'.symm.trans had)
      subst ha_eq
      have harr : arr = arr₀ := RoleVal.evidence_eq_of_wf hwf hm hmem_ev₀
      subst harr
      rw [harr_eq] at hthm
      obtain ⟨raw, c, ent, hsz, hh, hbl, hde, hcl, hsc⟩ := hprfs thm hthm
      rw [hgro] at hcl hsc
      exact ⟨raw, c, ent, hsz, Claim.hashed_mono hsub_ev hh, hbl, hde, hcl.mono hsub_ev, hsc⟩

/-! ## Every role-bound record is no `Muts` block -/

private theorem bound_notMuts_of_get_ci {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {ro : Ix.Kernel.Role} {x_tbl v1 p39 : SourceValue F} {h m2 m32 : Heap F}
    {cs12 cs45 : List (Call F)}
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev14 : ObsFn Obs.W "KernelRoles::role_bound_addr" [x_tbl, .field (roleNum ro)] h v1 m2 cs12)
    (ev47 : ObsFn Obs.W "Ingress::get_ci" [v1] m2 p39 m32 cs45)
    (hsub : ∀ cl ∈ cs45, cl ∈ calls)
    {a : _root_.Address} (had : t.addressOf? ro = some a)
    {c : Ixon.Constant} (hc : recordOf E₀ a = some c) : ¬ IsBlock c := by
  obtain ⟨-, a', ⟨ab, hab, rfl⟩, had'⟩ := RoleVal.role_bound_addr_uncond htbl.toTableRep ev14
  have ea : Core.ixAddr ab = a := Option.some.inj (had'.symm.trans had)
  rw [← ea] at hc
  obtain ⟨raw, c', -, hh, hba, hde, -, hhead⟩ := Claim.get_ci_head hab ev47
  have hcc : c' = c := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc)
    (Core.hashed_mono hsub hh) hba hde
  subst c'
  intro ⟨ms, hms⟩
  exact hhead.notMuts ms hms

/-- **No role-bound record is a `Muts` block**: every arm of `KernelRoles::validate_role` loads
the bound address with `Ingress::get_ci`, which refuses `Muts` (`Claim.GetCIHead.notMuts`). -/
theorem roleBound_notBlock {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀)
    {ro : Ix.Kernel.Role} (hv : RoleValidationIn calls bAddr t (Ix.SpecDigest.groupOf ro) ro)
    {a : _root_.Address} (had : t.addressOf? ro = some a)
    {c : Ixon.Constant} (hc : recordOf E₀ a = some c) : ¬ IsBlock c := by
  obtain ⟨h, h', x_rc, x_tbl, res, cs, -, htbl, ev, hsub⟩ := hv
  match Obs.«KernelRoles::validate_role».obs ev with
  | .n0 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc183 := hcs) ..
  | .n1 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc227 := hcs) ..
  | .n2 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc279 := hcs) ..
  | .n3 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc323 := hcs) ..
  | .n4 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc367 := hcs) ..
  | .n5 (cs45 := cs45) (ev14 := ev14) (ev47 := ev47) (hc419 := hcs) .. =>
    exact bound_notMuts_of_get_ci hS htbl ev14 ev47
      (fun cl hm => hsub cl (by rw [hcs]; simp [hm])) had hc

/-! ## `ScanStopsAt` vs `OpEarlier` and `AlreadyStoredRole` on groups 33 to 40 -/

private theorem notOp_opEarlier {t : Ix.Kernel.RoleTable} {g : Nat} {y : _root_.Address}
    (h : NotOp t y) : OpEarlier t g y :=
  fun ro had hop => (h ro had ((specKind_two_iff ro).mpr hop)).elim

private theorem scanStopsAt_opEarlier {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {g : Nat} (hg33 : 33 ≤ g) {y : _root_.Address}
    (h : RoleVal.ScanStopsAt t 33 (RoleVal.groupNeededRoles g) y) : OpEarlier t g y := by
  intro ro had hop
  rcases h.operation hwf had ((specKind_two_iff ro).mpr hop) (fun _ _ => addressOf_role_inj hwf) with hlt | hmem
  · omega
  · exact RoleVal.groupNeeds_groupOf_lt hmem

private theorem scanStopsAt_alreadyStored_or_inert {t : Ix.Kernel.RoleTable}
    {g : Nat} (hg33 : 33 ≤ g) (hg40 : g ≤ 40) {y : _root_.Address}
    (h : RoleVal.ScanStopsAt t 33 (RoleVal.groupNeededRoles g) y)
    (hns : ¬ AlreadyStoredRole t g y) :
    ∃ ro : Ix.Kernel.Role, t.addressOf? ro = some y ∧ ro.inert = true := by
  have hlim : valLimit g = 33 := by
    show RoleVal.groupValLimit g = 33
    unfold RoleVal.groupValLimit
    have h1 : ¬ g < 33 := by omega
    have h2 : g < 41 := by omega
    simp [h1, h2]
  obtain ⟨ro, had, hcase⟩ := h
  rcases hcase with ⟨hk2, hlt | hmem⟩ | ⟨hnk2, hlt, hnUnw⟩
  · exfalso
    exact hns (Or.inr (Or.inr ⟨ro, had, hk2, by omega⟩))
  · exfalso
    exact hns (Or.inr (Or.inr ⟨ro, had, hk2, RoleVal.groupNeeds_groupOf_lt hmem⟩))
  · rcases RoleVal.inForce_block_cases ro hlt with hwb | haw | hq | hk3 | hk4 | hunw
    · exfalso
      apply hns; left
      refine ⟨ro, had, Or.inl ⟨by rw [Claim.walkedRole_eq_roleWalksBound]; exact hwb, fun n hn => ?_⟩⟩
      cases Option.some.inj hn
      rwa [hlim]
    · exfalso
      exact hns (Or.inr (Or.inl ⟨ro, had, by rwa [hlim], Or.inl haw⟩))
    · exfalso
      exact hns (Or.inr (Or.inl ⟨ro, had, by rwa [hlim], Or.inr (Or.inr hq)⟩))
    · exfalso
      exact hns (Or.inr (Or.inl ⟨ro, had, by rwa [hlim],
        Or.inr (Or.inl ((RoleVal.specKind_three_iff ro).mp hk3))⟩))
    · exact ⟨ro, had, specKind_four_inert ro hk4⟩
    · exfalso
      obtain ⟨_, hk1, hawf⟩ := (RoleVal.unwalkedAnchorsInForce_iff ro).mp hunw
      exact hnUnw ⟨hk1, hawf⟩

private theorem groupReach_not_inert_wf {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀)
    {g : Nat} (hg33 : 33 ≤ g) (hg40 : g ≤ 40)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    {y : _root_.Address} (hy : GroupReach t E₀ g y)
    {ro : Ix.Kernel.Role} (had : t.addressOf? ro = some y) (hin : ro.inert = true) : False := by
  have hwf := (hvalAll (Ix.SpecDigest.groupOf ro) ro (role_mem_roleGroup ro)).wf
  rcases hy.root_or_allowed hC (hvalAll g) hw with ⟨_, _, r', hni, had'⟩ | ⟨cb, ms, hcb, hms⟩ |
      hal | ⟨h46, -⟩
  · have e : r' = ro := addressOf_role_inj hwf had' had
    subst e
    rw [hni] at hin
    cases hin
  · exact roleBound_notBlock hC.runStore
      (hvalAll (Ix.SpecDigest.groupOf ro) ro (role_mem_roleGroup ro)) had hcb ⟨ms, hms⟩
  · obtain ⟨n, hn, hle⟩ := Claim.refAllowed_inert hal hin had
    have hlim : valLimit g = 33 := by
      show RoleVal.groupValLimit g = 33
      unfold RoleVal.groupValLimit
      have h1 : ¬ g < 33 := by omega
      have h2 : g < 41 := by omega
      simp [h1, h2]
    have e : n = 33 := by rw [← hlim]; exact (Option.some.inj hn).symm
    subst e
    have hlt33 : Ix.SpecDigest.groupOf ro < 33 := by
      cases ro <;> first | exact absurd hin (by decide) | decide
    omega
  · omega

/-! ## Master induction: every `GroupReach g` node (`33 ≤ g ≤ 40`) is entered by the scan -/

/-- **Every address reached by a well-founded group's walk (`33 ≤ g ≤ 40`) is entered by its
operation-order scan.** -/
theorem groupReach_in_scan_wf {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀)
    {g : Nat} (hg33 : 33 ≤ g) (hg40 : g ≤ 40)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    {x : _root_.Address} (hx : GroupReach t E₀ g x) :
    ∃ entered : List _root_.Address, x ∈ entered ∧
      ScanClosedExt calls t (RoleVal.ScanStopsAt t 33 (RoleVal.groupNeededRoles g)) entered := by
  induction hx with
  | @root r a hr hwk had =>
    obtain ⟨⟨a', ent, had', hmem, hcl⟩, -⟩ :=
      validate_role_wf_op_scans hg33 hg40 hr (hvalAll g r hr)
    have ea : a' = a := Option.some.inj (had'.symm.trans had)
    subst ea
    exact ⟨ent, hmem, hcl⟩
  | @axiomRef r _ _ hr hs _ _ _ =>
    exfalso
    have hlt := stdAxiom_group_lt r hs
    rw [groupOf_of_mem_roleGroup hr] at hlt
    omega
  | @ref a y ha hu hns ih =>
    obtain ⟨ent, hmem, hcl⟩ := ih
    obtain ⟨raw, c, hsz, hh, hbl, hde, hdeE, -, -, hrefs⟩ := hcl a hmem
    have hrec : recordOf E₀ a = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    have ⟨c', i, hc', hi, hy⟩ := hu
    have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
    subst ec
    obtain ⟨hlt, hye⟩ := Array.getElem?_eq_some_iff.mp hy
    have hlt' : i < c'.refs.toList.length := by simpa using hlt
    have hyl : c'.refs.toList[i]'hlt' = y := by simpa using hye
    rcases hrefs i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi) with hstop | ⟨hyent, -⟩
    · rw [hyl] at hstop
      obtain ⟨ro, had, hin⟩ := scanStopsAt_alreadyStored_or_inert hg33 hg40 hstop hns
      exact (groupReach_not_inert_wf hC hg33 hg40 hvalAll hw (GroupReach.ref ha hu hns) had hin).elim
    · rw [hyl] at hyent
      exact ⟨ent, hyent, hcl⟩
  | @owner a c ha hc hp ih =>
    obtain ⟨ent, hmem, hcl⟩ := ih
    obtain ⟨raw, c', hsz, hh, hbl, hde, hdeE, -, hown, -⟩ := hcl a hmem
    have hrec : recordOf E₀ a = some c' := by
      rw [← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    have ec : c' = c := Option.some.inj (hrec.symm.trans hc)
    subst ec
    rcases hown with hstop | ⟨hent, -⟩ | ⟨hnp, -⟩
    · exfalso
      obtain ⟨ro, had, -⟩ := hstop
      obtain ⟨cb, hcb, hblk⟩ := ha.owner_block hC hw hc hp
      exact roleBound_notBlock hC.runStore
        (hvalAll (Ix.SpecDigest.groupOf ro) ro (role_mem_roleGroup ro)) had hcb hblk
    · exact ⟨ent, hent, hcl⟩
    · exact (hnp hp).elim
  | @evidenceRef r arr thm y hr hm hthm hu hne hns =>
    obtain ⟨-, hcert⟩ := validate_role_wf_op_scans hg33 hg40 hr (hvalAll g r hr)
    obtain ⟨a₀, had₀, -⟩ := (RoleValidationIn.walks (hvalAll g r hr)).1
    obtain ⟨raw, c, ent, hsz, hh, hbl, hdeE, hcl, hsc⟩ := hcert arr thm a₀ had₀ hm hthm
    have hrec : recordOf E₀ thm = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz
        (Ingress.deConstant_of_deConstantExact hdeE) hdeE
    have ⟨c', i, hc', hi, hy⟩ := hu
    have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
    subst ec
    obtain ⟨hlt, hye⟩ := Array.getElem?_eq_some_iff.mp hy
    have hlt' : i < c'.refs.toList.length := by simpa using hlt
    have hyl : c'.refs.toList[i]'hlt' = y := by simpa using hye
    have hne' : c'.refs.toList[i]'hlt' ≠ a₀ := by
      rw [hyl]; intro e; exact hne (by rw [e]; exact had₀)
    rcases hsc i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi) hne' with hstop | ⟨hyent, -⟩
    · rw [hyl] at hstop
      obtain ⟨ro, had, hin⟩ := scanStopsAt_alreadyStored_or_inert hg33 hg40 hstop hns
      exact (groupReach_not_inert_wf hC hg33 hg40 hvalAll hw
        (GroupReach.evidenceRef hr hm hthm hu hne hns) had hin).elim
    · rw [hyl] at hyent
      exact ⟨ent, hyent, hcl⟩
  | eqnsProof hr h5 _ _ =>
    have hgr := groupOf_of_mem_roleGroup hr
    have h46 := specKind5_group_ge_46 _ h5
    omega
  | eqnsAnchor hr h5 _ _ =>
    have hgr := groupOf_of_mem_roleGroup hr
    have h46 := specKind5_group_ge_46 _ h5
    omega

/-! ## Discharging `blockSteps` and well-founded `payloadOps` -/

/-- **Well-founded block operation order of every run**: in groups 33 to 40, every reference
the group's walk follows is bound to no operation of the group or a later one. -/
theorem blockSteps_of_run {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 33 ≤ g → g ≤ 40 → WalkStepsOrdered t E₀ g := by
  intro g hg33 hg40
  obtain ⟨recs, hw⟩ := hws g
  have hwf : t.wf = true := (hvalAll 0 .nat (by decide)).wf
  refine ⟨fun x y hx hu _ => ?_, fun r hr arr thm y hm hthm hu hne _ => ?_⟩
  · obtain ⟨ent, hmem, hcl⟩ := groupReach_in_scan_wf hC hg33 hg40 hvalAll hw hx
    obtain ⟨raw, c, hsz, hh, hbl, hde, hdeE, -, -, hrefs⟩ := hcl x hmem
    have hrec : recordOf E₀ x = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    obtain ⟨c', i, hc', hi, hy⟩ := hu
    have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
    subst ec
    obtain ⟨hlt, hye⟩ := Array.getElem?_eq_some_iff.mp hy
    have hlt' : i < c'.refs.toList.length := by simpa using hlt
    have hyl : c'.refs.toList[i]'hlt' = y := by simpa using hye
    rcases hrefs i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi) with hstop | ⟨-, hno⟩
    · rw [hyl] at hstop
      exact scanStopsAt_opEarlier hwf hg33 hstop
    · rw [hyl] at hno
      exact notOp_opEarlier hno
  · obtain ⟨-, hcert⟩ := validate_role_wf_op_scans hg33 hg40 hr (hvalAll g r hr)
    obtain ⟨a₀, had₀, -⟩ := (RoleValidationIn.walks (hvalAll g r hr)).1
    obtain ⟨raw, c, ent, hsz, hh, hbl, hdeE, -, hsc⟩ := hcert arr thm a₀ had₀ hm hthm
    have hrec : recordOf E₀ thm = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz
        (Ingress.deConstant_of_deConstantExact hdeE) hdeE
    obtain ⟨c', i, hc', hi, hy⟩ := hu
    have ec : c' = c := Option.some.inj (hc'.symm.trans hrec)
    subst ec
    obtain ⟨hlt, hye⟩ := Array.getElem?_eq_some_iff.mp hy
    have hlt' : i < c'.refs.toList.length := by simpa using hlt
    have hyl : c'.refs.toList[i]'hlt' = y := by simpa using hye
    have hne' : c'.refs.toList[i]'hlt' ≠ a₀ := by
      rw [hyl]; intro e; exact hne (by rw [e]; exact had₀)
    rcases hsc i hlt' (by rw [Assembly.usedRefIdxs_eq]; exact hi) hne' with hstop | ⟨-, hno⟩
    · rw [hyl] at hstop
      exact scanStopsAt_opEarlier hwf hg33 hstop
    · rw [hyl] at hno
      exact notOp_opEarlier hno

/-- **No address is reached through the payload in the well-founded block (`33 ≤ g ≤ 40`)**:
every walk-reached `Muts` block in those groups is entered by `op_order_scan_refs`, which
asserts `KernelModeled::block_is_modeled = 0`, contradicting `ModeledRouteAt` in `runPayload`. -/
theorem payReach_empty_wf {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg33 : 33 ≤ g) (hg40 : g ≤ 40) :
    ∀ x, ¬ PayReach t E₀ (runPayload calls bAddr t) g x := by
  obtain ⟨recs, hw⟩ := hws g
  intro x hx
  induction hx with
  | @payload B a hB hpay =>
    obtain ⟨-, hmod, rb, cs, advAs, hex, -⟩ := hpay
    have hfc := FamilyCallExact.toCall hex
    obtain ⟨cb, ms, hcb, hms, -⟩ := familyCall_block_nonempty hC.runStore hC.hashedStored hfc
    obtain ⟨ent, hmem, hcl⟩ := groupReach_in_scan_wf hC hg33 hg40 hvalAll hw hB
    obtain ⟨raw, c, hsz, hh, hbl, hde, hdeE, hnm, -, -⟩ := hcl B hmem
    have hrec : recordOf E₀ B = some c := by
      rw [← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    have ec : c = cb := Option.some.inj (hrec.symm.trans hcb)
    subst ec
    exact hnm ms hms hmod
  | payloadOf _ _ ih => exact ih
  | ref _ _ _ ih => exact ih
  | owner _ _ _ ih => exact ih

end IxVM.Refinement.Binding
