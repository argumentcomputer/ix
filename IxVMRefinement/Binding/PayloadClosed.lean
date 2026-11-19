import IxVMRefinement.Binding.RunFamilies
import IxVMRefinement.Binding.OpOrderBlock

/-! # Payload closure, operation order, and run-fact discharge

Proves by strong induction on the group index `g` (`6 ≤ g < 77`) that every address reached
through the run's family-check payload (`PayReach t E₀ (runPayload calls bAddr t) g`) belongs to
one of six closed classes (`PayClass`):
1. `stored`: already held in `groupStore ... g`;
2. `walked`: reached by `GroupReach t E₀ g`;
3. `famRec`: the family record of an exact family check anchored at a walked or stored modeled
   block;
4. `directAdv`: an advice record of such a family check;
5. `directCont`: a directly witnessed container recursor of such a family check;
6. `checkedProj`: a canonical projection record (`usedRefIdxs = []`) of a stored, walked, or
   direct-advice block.

The prefix-truncation device `truncPay Pay g` lets the inductive step invoke the existing
`groupStore_usedClosed_all` and `storedBelow_record` on all groups below `g`, giving `UsedClosed`
and `AlreadyStoredRole` completeness on `groupStore ... g` without duplicating store lemmas.

From the closed strong induction, this module discharges:
* `payloadFacts_of_run`: `PayloadFacts t E₀ (runPayload calls bAddr t)` (eliminating `payloadSteps`);
* `payloadOps_of_run`: `OpEarlier t g` on `PayReach` for `6 ≤ g < 41` (`6..32` from the induction,
  `33..40` vacuous by `payReach_empty_wf`);
* `claimed_of_run`: every new non-empty recursor block is claimed by a `FamilyCallAtLim`;
* `payloadChecked_of_run`: every new non-twin unit reached through the payload is `UnitCheckedAt`;
* `runFactsLeft_of_run`: all four fields of `RunFactsLeft` (`notInert`, `needOk`, `famNotInert`,
  `famNeedOk`). -/

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

/-! ## Decided facts about the basis rows and basis roles -/

set_option maxRecDepth 100000 in
/-- No basis row is a standalone definition (decided over the 24 rows). -/
theorem basisRows_no_defn :
    StoreInhabit.basisRows.all (fun e => match e.2.info with
      | .defn _ => false
      | _ => true) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- No basis role is inert (decided). -/
theorem basisRoles_not_inert : ∀ r ∈ TableInhabit.basisRoleOrder, r.inert = false := by
  decide +kernel

/-- Decidable check for `InLogicMut`. -/
private def inLogicMutBool : Ixon.MutConst → Bool
  | .defn d => (Ix.Kernel.Reader.safetyDecline d).isNone
  | .indc i => !i.isUnsafe && i.ctors.toList.all fun ct => !ct.isUnsafe
  | .recr r => !r.isUnsafe

private theorem inLogicMut_of_bool {m : Ixon.MutConst} (h : inLogicMutBool m = true) :
    InLogicMut m := by
  cases m with
  | defn d =>
    simp only [inLogicMutBool, Option.isNone_iff_eq_none] at h
    exact h
  | indc i =>
    simp only [inLogicMutBool, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact ⟨h.1, fun ct hct => h.2 ct hct⟩
  | recr r =>
    simp only [inLogicMutBool, Bool.not_eq_true'] at h
    exact h

/-- Decidable check for `InLogic`. -/
private def inLogicBool (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d => (Ix.Kernel.Reader.safetyDecline d).isNone
  | .recr r => !r.isUnsafe
  | .axio a => !a.isUnsafe
  | .muts ms => ms.toList.all inLogicMutBool
  | _ => true

private theorem inLogic_of_bool {c : Ixon.Constant} (h : inLogicBool c = true) : InLogic c := by
  unfold inLogicBool at h
  unfold InLogic
  cases hi : c.info with
  | defn d =>
    rw [hi] at h
    exact Option.isNone_iff_eq_none.mp h
  | recr r =>
    rw [hi] at h
    simp only [Bool.not_eq_true'] at h
    exact h
  | axio a =>
    rw [hi] at h
    simp only [Bool.not_eq_true'] at h
    exact h
  | muts ms =>
    rw [hi] at h
    intro m hm
    exact inLogicMut_of_bool (List.all_eq_true.mp h m hm)
  | quot _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ => trivial

set_option maxRecDepth 100000 in
/-- Every basis row is in Lean's logic (decided over the 24 rows). -/
theorem basisRows_inLogic :
    StoreInhabit.basisRows.all (fun e => inLogicBool e.2) = true := by
  decide +kernel

private theorem byteArray_eq_of_toList_eq {b₁ b₂ : ByteArray}
    (h : b₁.data.toList = b₂.data.toList) : b₁ = b₂ := by
  cases b₁ with
  | mk a₁ =>
    cases b₂ with
    | mk a₂ =>
      cases a₁
      cases a₂
      simp only at h
      subst h
      rfl

/-- Decidable structural match of a projection basis row against its parent block row, without
re-hashing. -/
private def basisProjMatch (c : Ixon.Constant) (B : _root_.Address) (cb : Ixon.Constant) : Bool :=
  match c.info, cb.info with
  | .dPrj p, .muts ms =>
    p.block == B && match ms[p.idx.toNat]? with
      | some (.defn d) =>
        (Ixon.serConstant c).data.toList ==
          (Ixon.serConstant (memberProjection B p.idx.toNat (.defn d))).data.toList
      | _ => false
  | .iPrj p, .muts ms =>
    p.block == B && match ms[p.idx.toNat]? with
      | some (.indc ind) =>
        (Ixon.serConstant c).data.toList ==
          (Ixon.serConstant (memberProjection B p.idx.toNat (.indc ind))).data.toList
      | _ => false
  | .rPrj p, .muts ms =>
    p.block == B && match ms[p.idx.toNat]? with
      | some (.recr r) =>
        (Ixon.serConstant c).data.toList ==
          (Ixon.serConstant (memberProjection B p.idx.toNat (.recr r))).data.toList
      | _ => false
  | .cPrj p, .muts ms =>
    p.block == B && match ms[p.idx.toNat]? with
      | some (.indc ind) =>
        decide (p.cidx.toNat < ind.ctors.size) &&
          ((Ixon.serConstant c).data.toList ==
            (Ixon.serConstant (constructorProjection B p.idx.toNat p.cidx.toNat)).data.toList)
      | _ => false
  | _, _ => false

set_option maxRecDepth 100000 in
/-- Every projection row in `basisRows` is the canonical projection of a member or constructor of
its parent block row in `basisRows` (decided over the 24 rows). -/
theorem basisRows_projMatch :
    StoreInhabit.basisRows.all (fun e => match e.2.info with
      | .dPrj _ | .iPrj _ | .rPrj _ | .cPrj _ =>
        StoreInhabit.basisRows.any fun b => basisProjMatch e.2 b.1 b.2
      | _ => true) = true := by
  decide +kernel

/-- Every record in `basisStore` is in Lean's logic. -/
theorem basisStore_inLogic {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf basisStore a = some c) : InLogic c :=
  inLogic_of_bool (List.all_eq_true.mp basisRows_inLogic (a, c) (StoreInhabit.store_record_inv h))

/-- Every projection record in `basisStore` is a `ConstAddrOf` its owner block in `basisStore`. -/
theorem basisStore_projMember {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf basisStore a = some c) (hp : IsProj c) :
    ∃ cb, recordOf basisStore (Ix.Cert.ownerOf a c) = some cb ∧
      ConstAddrOf (Ix.Cert.ownerOf a c) cb a := by
  have hmem : (a, c) ∈ StoreInhabit.basisRows := StoreInhabit.store_record_inv h
  have hhash : Address.blake3Pure (Ixon.serConstant c) = a :=
    ClosedFacts.committedRows_hashed (a, Ixon.serConstant c)
      (ClosedFacts.committedPrelude_rows (a, c) (StoreInhabit.basisRows_sub (a, c) hmem)).1
  have hall := List.all_eq_true.mp basisRows_projMatch (a, c) hmem
  rcases hp with ⟨p, hi⟩ | ⟨p, hi⟩ | ⟨p, hi⟩ | ⟨p, hi⟩
  · simp only [hi] at hall
    obtain ⟨⟨B, cb⟩, hbMem, hmat⟩ := List.any_eq_true.mp hall
    unfold basisProjMatch at hmat
    rw [hi] at hmat
    cases hcb : cb.info with
    | muts ms =>
      rw [hcb] at hmat
      obtain ⟨hB, hrest⟩ := Bool.and_eq_true _ _ |>.mp hmat
      have eB : p.block = B := beq_iff_eq.mp hB
      cases hget : ms[p.idx.toNat]? with
      | none => rw [hget] at hrest; cases hrest
      | some m =>
        rw [hget] at hrest
        cases m with
        | defn d =>
          have hser := byteArray_eq_of_toList_eq (beq_iff_eq.mp hrest)
          have ha : a = memberAddr B p.idx.toNat (.defn d) := by
            rw [← hhash, hser]; rfl
          refine ⟨cb, ?_, ?_⟩
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact StoreInhabit.store_record_of_mem hbMem
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact Or.inr ⟨ms, p.idx.toNat, .defn d, hcb, hget, Or.inl ha⟩
        | indc _ | recr _ => cases hrest
    | defn _ | recr _ | axio _ | quot _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
      rw [hcb] at hmat; cases hmat
  · simp only [hi] at hall
    obtain ⟨⟨B, cb⟩, hbMem, hmat⟩ := List.any_eq_true.mp hall
    unfold basisProjMatch at hmat
    rw [hi] at hmat
    cases hcb : cb.info with
    | muts ms =>
      rw [hcb] at hmat
      obtain ⟨hB, hrest⟩ := Bool.and_eq_true _ _ |>.mp hmat
      have eB : p.block = B := beq_iff_eq.mp hB
      cases hget : ms[p.idx.toNat]? with
      | none => rw [hget] at hrest; cases hrest
      | some m =>
        rw [hget] at hrest
        cases m with
        | indc ind =>
          have hser := byteArray_eq_of_toList_eq (beq_iff_eq.mp hrest)
          have ha : a = memberAddr B p.idx.toNat (.indc ind) := by
            rw [← hhash, hser]; rfl
          refine ⟨cb, ?_, ?_⟩
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact StoreInhabit.store_record_of_mem hbMem
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact Or.inr ⟨ms, p.idx.toNat, .indc ind, hcb, hget, Or.inl ha⟩
        | defn _ | recr _ => cases hrest
    | defn _ | recr _ | axio _ | quot _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
      rw [hcb] at hmat; cases hmat
  · simp only [hi] at hall
    obtain ⟨⟨B, cb⟩, hbMem, hmat⟩ := List.any_eq_true.mp hall
    unfold basisProjMatch at hmat
    rw [hi] at hmat
    cases hcb : cb.info with
    | muts ms =>
      rw [hcb] at hmat
      obtain ⟨hB, hrest⟩ := Bool.and_eq_true _ _ |>.mp hmat
      have eB : p.block = B := beq_iff_eq.mp hB
      cases hget : ms[p.idx.toNat]? with
      | none => rw [hget] at hrest; cases hrest
      | some m =>
        rw [hget] at hrest
        cases m with
        | indc ind =>
          obtain ⟨hlt, heq⟩ := Bool.and_eq_true _ _ |>.mp hrest
          have hj : p.cidx.toNat < ind.ctors.size := of_decide_eq_true hlt
          have hser := byteArray_eq_of_toList_eq (beq_iff_eq.mp heq)
          have ha : a = ctorAddr B p.idx.toNat p.cidx.toNat := by
            rw [← hhash, hser]; rfl
          refine ⟨cb, ?_, ?_⟩
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact StoreInhabit.store_record_of_mem hbMem
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact Or.inr ⟨ms, p.idx.toNat, .indc ind, hcb, hget,
              Or.inr ⟨ind, p.cidx.toNat, rfl, hj, ha⟩⟩
        | defn _ | recr _ => cases hrest
    | defn _ | recr _ | axio _ | quot _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
      rw [hcb] at hmat; cases hmat
  · simp only [hi] at hall
    obtain ⟨⟨B, cb⟩, hbMem, hmat⟩ := List.any_eq_true.mp hall
    unfold basisProjMatch at hmat
    rw [hi] at hmat
    cases hcb : cb.info with
    | muts ms =>
      rw [hcb] at hmat
      obtain ⟨hB, hrest⟩ := Bool.and_eq_true _ _ |>.mp hmat
      have eB : p.block = B := beq_iff_eq.mp hB
      cases hget : ms[p.idx.toNat]? with
      | none => rw [hget] at hrest; cases hrest
      | some m =>
        rw [hget] at hrest
        cases m with
        | recr r =>
          have hser := byteArray_eq_of_toList_eq (beq_iff_eq.mp hrest)
          have ha : a = memberAddr B p.idx.toNat (.recr r) := by
            rw [← hhash, hser]; rfl
          refine ⟨cb, ?_, ?_⟩
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact StoreInhabit.store_record_of_mem hbMem
          · simp only [Ix.Cert.ownerOf, hi, eB]
            exact Or.inr ⟨ms, p.idx.toNat, .recr r, hcb, hget, Or.inl ha⟩
        | defn _ | indc _ => cases hrest
    | defn _ | recr _ | axio _ | quot _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ =>
      rw [hcb] at hmat; cases hmat

/-! ## Prefix truncation of payloads and empty late groups -/

/-- The five fields of `PayloadFacts` localized to a single group `g`. -/
structure PayloadFactsAt (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (Pay : PayloadRel) (g : Nat) :
    Prop where
  record : ∀ a, PayReach t E₀ Pay g a → ∃ c, recordOf E₀ a = some c
  blockMembers : ∀ B c ms, PayReach t E₀ Pay g B → recordOf E₀ B = some c → c.info = .muts ms →
    ∀ i m, ms[i]? = some m →
      recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j)
  projMember : ∀ a c, PayReach t E₀ Pay g a → recordOf E₀ a = some c → IsProj c →
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf a c) cb a
  logic : ∀ a c, PayReach t E₀ Pay g a → recordOf E₀ a = some c → InLogic c
  notAxiomLike : ∀ a c, PayReach t E₀ Pay g a →
    New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a → recordOf E₀ a = some c →
    ¬ IsAxiomLike c

/-- Payload relation truncated strictly below group `n`. -/
def truncPay (Pay : PayloadRel) (n : Nat) : PayloadRel :=
  fun k B a => k < n ∧ Pay k B a

theorem truncPay_payReach_iff {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {n k : Nat} (hk : k < n) {a : _root_.Address} :
    PayReach t E₀ (truncPay Pay n) k a ↔ PayReach t E₀ Pay k a := by
  constructor
  · intro h
    induction h with
    | payload hB hp => exact PayReach.payload hB hp.2
    | payloadOf _ hp ih => exact PayReach.payloadOf ih hp.2
    | ref _ hu hns ih => exact PayReach.ref ih hu hns
    | owner _ hc hp ih => exact PayReach.owner ih hc hp
  · intro h
    induction h with
    | payload hB hp => exact PayReach.payload hB ⟨hk, hp⟩
    | payloadOf _ hp ih => exact PayReach.payloadOf ih ⟨hk, hp⟩
    | ref _ hu hns ih => exact PayReach.ref ih hu hns
    | owner _ hc hp ih => exact PayReach.owner ih hc hp

theorem truncPay_payReach_bounds {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {n k : Nat} {a : _root_.Address} (h : PayReach t E₀ (truncPay Pay n) k a) : k < n := by
  induction h with
  | payload _ hp => exact hp.1
  | payloadOf _ hp _ => exact hp.1
  | ref _ _ _ ih => exact ih
  | owner _ _ _ ih => exact ih

theorem truncPay_groupAdds_iff {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {n k : Nat} (hk : k < n) {a : _root_.Address} :
    GroupAdds t E₀ (truncPay Pay n) k a ↔ GroupAdds t E₀ Pay k a := by
  unfold GroupAdds PayAdds
  simp only [truncPay_payReach_iff hk]

theorem truncPay_storedBelow_iff {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {n k : Nat} (hk : k ≤ n) {a : _root_.Address} :
    StoredBelow t E₀ (truncPay Pay n) k a ↔ StoredBelow t E₀ Pay k a := by
  unfold StoredBelow
  constructor
  · rintro (h | ⟨j, hj6, hjk, hadd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj6, hjk, (truncPay_groupAdds_iff (by omega)).mp hadd⟩
  · rintro (h | ⟨j, hj6, hjk, hadd⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj6, hjk, (truncPay_groupAdds_iff (by omega)).mpr hadd⟩

theorem truncPay_groupStore_eq {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {n k : Nat} (hk : k ≤ n) :
    groupStore t E₀ (truncPay Pay n) k = groupStore t E₀ Pay k := by
  unfold groupStore
  split_ifs
  · rfl
  · congr 1
    funext x
    exact propext (truncPay_storedBelow_iff hk)

theorem payloadFacts_truncPay {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {n : Nat} (hge6 : ∀ k B a, Pay k B a → 6 ≤ k)
    (hih : ∀ k, 6 ≤ k → k < n → PayloadFactsAt t E₀ Pay k) :
    PayloadFacts t E₀ (truncPay Pay n) := by
  have hbounds : ∀ k a, PayReach t E₀ (truncPay Pay n) k a → 6 ≤ k ∧ k < n := by
    intro k a h
    induction h with
    | payload _ hp => exact ⟨hge6 _ _ _ hp.2, hp.1⟩
    | payloadOf _ hp _ => exact ⟨hge6 _ _ _ hp.2, hp.1⟩
    | ref _ _ _ ih => exact ih
    | owner _ _ _ ih => exact ih
  refine
    { record := fun k a h => by
        obtain ⟨h6, hlt⟩ := hbounds k a h
        exact (hih k h6 hlt).record a ((truncPay_payReach_iff hlt).mp h)
      blockMembers := fun k B c ms h => by
        obtain ⟨h6, hlt⟩ := hbounds k B h
        exact (hih k h6 hlt).blockMembers B c ms ((truncPay_payReach_iff hlt).mp h)
      projMember := fun k a c h => by
        obtain ⟨h6, hlt⟩ := hbounds k a h
        exact (hih k h6 hlt).projMember a c ((truncPay_payReach_iff hlt).mp h)
      logic := fun k a c h => by
        obtain ⟨h6, hlt⟩ := hbounds k a h
        exact (hih k h6 hlt).logic a c ((truncPay_payReach_iff hlt).mp h)
      notAxiomLike := fun k a c h hnew hc => by
        obtain ⟨h6, hlt⟩ := hbounds k a h
        rw [truncPay_groupStore_eq (Nat.le_of_lt hlt),
          truncPay_groupStore_eq (Nat.succ_le_of_lt hlt)] at hnew
        exact (hih k h6 hlt).notAxiomLike a c ((truncPay_payReach_iff hlt).mp h) hnew hc }

/-- No group at or above 77 has any walk-reached address. -/
theorem groupReach_empty_of_ge {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {g : Nat} (hg : 77 ≤ g)
    {a : _root_.Address} (h : GroupReach t E₀ g a) : False := by
  have hnil : roleGroup g = [] := roleGroup_eq_nil (by rw [groups_length]; omega)
  induction h with
  | root hr _ _ => rw [hnil] at hr; cases hr
  | axiomRef hr _ _ _ _ => rw [hnil] at hr; cases hr
  | ref _ _ _ ih => exact ih
  | owner _ _ _ ih => exact ih
  | evidenceRef hr _ _ _ _ _ => rw [hnil] at hr; cases hr

/-- No group at or above 77 has any payload-reached address. -/
theorem payReach_empty_of_ge {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {Pay : PayloadRel}
    {g : Nat} (hg : 77 ≤ g) {a : _root_.Address} (h : PayReach t E₀ Pay g a) : False := by
  induction h with
  | payload hB _ => exact groupReach_empty_of_ge hg hB
  | payloadOf _ _ ih => exact ih
  | ref _ _ _ ih => exact ih
  | owner _ _ _ ih => exact ih

/-! ## Container-recursor and standing helpers -/

section Helpers

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- Extracts the `KernelModeled::rec_family_block` call inside `KernelModeled::check_container_rec`
and identifies its return address with `ib`. -/
theorem check_container_rec_rec_family_block (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls)
    {x ib : _root_.Address} {rc xx xib r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hx : Core.S0.addr h xx x) (hib : Core.S0.addr h xib ib)
    (ev : ObsFn Obs.W "KernelModeled::check_container_rec" [rc, xx, xib] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∃ (v26 : SourceValue F) (m29 : Heap F) (cs37 : List (Call F)),
      ObsFn Obs.W "KernelModeled::rec_family_block" [xx] h v26 m29 cs37 ∧
      Core.S0.addr m29 v26 ib ∧
      (∀ cl ∈ cs37, cl ∈ calls) := by
  match Obs.«KernelModeled::check_container_rec».obs ev with
  | .run (v26 := v26) (m29 := m29) (cs37 := cs37) (ev39 := ev39) (ev25 := ev25)
      (heq61 := heq61) (hc96 := hc96) .. =>
    have hsub37 : ∀ cl ∈ cs37, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc96]; simp [hcl])
    obtain ⟨_, _, _, _, _, fam, _, _, _, _, _, _, bF, hrepF, _⟩ :=
      rec_family_block_usedRef hC hbd hx ev39 hsub37
    obtain ⟨b_ib, hbIb, rfl⟩ := hib
    have hbIb29 := Bytes.repAddressRef_heapMono₂ Core.addrTy ev39.heap_extends hbIb
    obtain ⟨heqV, -⟩ := Lib.address_eq_spec ev25 hrepF hbIb29
    have eb : bF = b_ib := by
      by_cases hne : bF = b_ib
      · exact hne
      · simp [hne] at heqV
        exact absurd (Value.field.inj (heqV.symm.trans heq61)) zero_ne_one
    subst eb
    exact ⟨v26, m29, cs37, ev39, ⟨bF, hrepF, rfl⟩, hsub37⟩

/-- A container recursor checked by `check_container_rec` has `info` either `.recr` or `.rPrj`. -/
theorem check_container_rec_shape (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls)
    {x ib : _root_.Address} {rc xx xib r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hx : Core.S0.addr h xx x) (hib : Core.S0.addr h xib ib)
    (ev : ObsFn Obs.W "KernelModeled::check_container_rec" [rc, xx, xib] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) {c : Ixon.Constant} (hc : recordOf E₀ x = some c) :
    (∃ rc, c.info = .recr rc) ∨ (∃ rp, c.info = .rPrj rp) := by
  obtain ⟨v26, m29, cs37, ev39, -, hsub37⟩ :=
    check_container_rec_rec_family_block hC hbd hx hib ev hsub
  obtain ⟨cx, _, rc', _, _, _, _, _, hrecX, _, _, _, _, _, hshape, _⟩ :=
    rec_family_block_head_spec hC hbd hx ev39 hsub37
  have ec : cx = c := Option.some.inj (hrecX.symm.trans hc)
  subst ec
  rcases hshape with ⟨hr, -⟩ | ⟨rp, -, hrp, -, -⟩
  · exact Or.inl ⟨rc', hr⟩
  · exact Or.inr ⟨rp, hrp⟩

/-- A walk-reached address not stored before group `g` cannot be an axiom or quotient record
(extracted from `groupStore_standing`, independent of `PayloadFacts`). -/
theorem groupReach_new_not_axiomLike (hC : CollisionFreeRun calls E₀) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) {Pay : PayloadRel} {g : Nat}
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hsafe : ∀ a, GroupReach t E₀ g a → Claim.SourceSafe E₀ a)
    {a : _root_.Address} {c : Ixon.Constant}
    (hra : GroupReach t E₀ g a) (hnot : ¬ StoredBelow t E₀ Pay g a)
    (hE : recordOf E₀ a = some c) (hk : IsAxiomLike c) : False := by
  have hnotBasis : ∀ ro ∈ TableInhabit.basisRoleOrder, t.addressOf? ro = some a → False :=
    fun ro hr had => hnot (Or.inl (basisRow_of_basisRole hpin hr had))
  have hnotStd : ∀ ro, ro ∈ standardAxioms → 6 ≤ Ix.SpecDigest.groupOf ro →
      Ix.SpecDigest.groupOf ro < g → t.addressOf? ro = some a → False :=
    fun ro hs h6 hlt had => hnot (Or.inr ⟨_, h6, hlt,
      GroupAdds.stdAxiom (role_mem_roleGroup ro) hs had⟩)
  obtain ⟨y, hy, hya⟩ := hra.listed hC.hashedStored hw
  have hyc : y.c = c := by
    have h1 := topRec_recordOf hC.hashedStored y
    rw [hya, hE] at h1
    exact (Option.some.inj h1).symm
  have hchk : Claim.CheckedLimAt calls bAddr t a (some (valLimit g)) := by
    rcases y.hchecked with ⟨ms, hms, -⟩ | hck
    · exfalso
      rw [hyc] at hms
      rcases hk with ⟨ax, h⟩ | ⟨q, h⟩ <;> (rw [h] at hms; cases hms)
    · rw [hya] at hck
      exact hck
  have hl : InLogic c := (hsafe a hra c hE).1
  obtain ⟨ro, hb', hcase⟩ := Claim.checkedLimAt_standing_role hC.runStore hE hl hk hchk
  rcases hcase with ⟨⟨ax, hax'⟩, hforce, hrole⟩ | ⟨⟨q, hq⟩, hm⟩
  · have hlt : Ix.SpecDigest.groupOf ro < valLimit g := hforce _ rfl
    rcases hrole with hm | hin
    · rcases standingRole_cases ro hm with ⟨hs, h6⟩ | hbas
      · exact hnotStd ro hs h6 (Nat.lt_of_lt_of_le hlt (valLimit_le g)) hb'
      · exact hnotBasis ro hbas hb'
    · rcases hra.root_or_allowed hC hval hw with ⟨r', hr', hwk, had'⟩ | ⟨cb, ms, hcb, hms⟩ | hal
      · have hwf := (hval r' hr').wf
        have hk' := (Core.keyOf_of_addressOf hwf had').symm.trans
          (Core.keyOf_of_addressOf hwf hb')
        injection hk' with e
        rw [← e, walked_not_inert r' hwk] at hin
        cases hin
      · rw [hE] at hcb
        have e : c = cb := Option.some.inj hcb
        rw [← e, hax'] at hms
        cases hms
      · obtain ⟨n, hn, hle⟩ := Claim.refAllowed_inert hal hin hb'
        have e : n = valLimit g := (Option.some.inj hn).symm
        rw [e] at hle
        exact absurd hlt (Nat.not_lt.mpr hle)
  · rcases standingRole_cases ro hm with ⟨hs, -⟩ | hbas
    · obtain ⟨c₂, ax, hc₂, hi, -⟩ := hax ro hs a hb'
      rw [hE] at hc₂
      have e : c = c₂ := Option.some.inj hc₂
      rw [← e, hq] at hi
      cases hi
    · exact hnotBasis ro hbas hb'

/-- Every record already stored in `groupStore ... g` (with `PayloadFacts` on `truncPay Pay g`)
satisfies `InLogic` and `projMember`. -/
theorem stored_logic_and_projMember (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hroots : RootsSafe t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {Pay : PayloadRel} {g : Nat} (hg6 : 6 ≤ g) (hg77 : g ≤ 77)
    (hP_lt : PayloadFacts t E₀ (truncPay Pay g))
    {x : _root_.Address} {c : Ixon.Constant}
    (hheld : recordOf (groupStore t E₀ Pay g) x = some c) :
    InLogic c ∧
      (IsProj c → ∃ cb, recordOf E₀ (Ix.Cert.ownerOf x c) = some cb ∧
        ConstAddrOf (Ix.Cert.ownerOf x c) cb x) := by
  have hval77 : ∀ k, k < 77 → ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r :=
    fun k _ => hvalAll k
  rw [← truncPay_groupStore_eq (n := g) (Nat.le_refl g)] at hheld
  obtain ⟨hsb, hE⟩ := (groupStore_recordOf hb hg6).mp hheld
  rcases hsb with hbas | ⟨k, hk6, hkg, hadd⟩
  · obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hbas
    obtain ⟨c₀, hmem, -⟩ := StoreInhabit.store_get?_inv hlc
    have hrecB : recordOf basisStore x = some c₀ := StoreInhabit.store_record_of_mem hmem
    have hrecE : recordOf E₀ x = some c₀ := by
      have h6 : recordOf (groupStore t E₀ (truncPay Pay g) 6) x = some c₀ := by
        rw [groupStore_six]; exact hrecB
      exact ((groupStore_recordOf hb (Nat.le_refl 6)).mp h6).2
    have ec : c₀ = c := Option.some.inj (hrecE.symm.trans hE)
    subst ec
    refine ⟨basisStore_inLogic hrecB, fun hp => ?_⟩
    obtain ⟨cb, hcbB, hca⟩ := basisStore_projMember hrecB hp
    have hcbE : recordOf E₀ (Ix.Cert.ownerOf x c₀) = some cb := by
      have h6 : recordOf (groupStore t E₀ (truncPay Pay g) 6) (Ix.Cert.ownerOf x c₀) = some cb := by
        rw [groupStore_six]; exact hcbB
      exact ((groupStore_recordOf hb (Nat.le_refl 6)).mp h6).2
    exact ⟨cb, hcbE, hca⟩
  · obtain ⟨recs, hw⟩ := hws k
    have hk77 : k < 77 := by omega
    rcases groupAdds_cases hC hax hw hadd with ⟨hr, r, -, hra⟩ |
        ⟨r, -, -, -, p, hp, hproj, hown, -, hca⟩ |
        ⟨ro, -, -, -, c₂, ax, hc₂, hi, hsafe⟩ | hpay
    · refine ⟨(groupReach_sourceSafe_of_run hC hval77 hroots hk77 hw x hr c hE).1, fun hp => ?_⟩
      have hrc := topRec_recordOf hC.hashedStored r
      rw [hra] at hrc
      have ec : c = r.c := Option.some.inj (hE.symm.trans hrc)
      have hpm := topRec_proj_member hC.runStore hC.hashedStored r (ec ▸ hp)
      rw [hra, ← ec] at hpm
      exact hpm
    · have ep : p = c := Option.some.inj (hp.symm.trans hE)
      subst ep
      refine ⟨?_, fun _ => ?_⟩
      · rcases hproj with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [InLogic, h]
      · rw [hown]
        exact ⟨r.c, topRec_recordOf hC.hashedStored r, hca⟩
    · have ec : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
      subst ec
      exact ⟨by simp [InLogic, hi, hsafe], fun hp => (proj_not_axiom hp hi).elim⟩
    · rcases payAdds_cases hP_lt hpay with ⟨hr, -⟩ |
          ⟨B, cB, -, hcB, -, p, hp, hproj, hown, -, hca⟩
      · exact ⟨hP_lt.logic k x c hr hE, fun hp => hP_lt.projMember k x c hr hE hp⟩
      · have ep : p = c := Option.some.inj (hp.symm.trans hE)
        subst ep
        refine ⟨?_, fun _ => ?_⟩
        · rcases hproj with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [InLogic, h]
        · rw [hown]
          exact ⟨cB, hcB, hca⟩

/-- A projection record is always in Lean's logic. -/
theorem isProj_inLogic {c : Ixon.Constant} (hp : IsProj c) : InLogic c := by
  rcases hp with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp [InLogic, h]

/-- A projection record is never an axiom or quotient record. -/
theorem isProj_not_axiomLike {c : Ixon.Constant} (hp : IsProj c) : ¬ IsAxiomLike c := by
  rintro (⟨ax, h⟩ | ⟨q, h⟩)
  · exact proj_not_axiom hp h
  · rcases hp with ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> (rw [h] at h'; cases h')

/-- A block record is never an axiom or quotient record. -/
theorem isBlock_not_axiomLike {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hms : c.info = .muts ms) : ¬ IsAxiomLike c := by
  rintro (⟨ax, h⟩ | ⟨q, h⟩) <;> (rw [hms] at h; cases h)

/-- A covered role address is `NeedOk`. -/
theorem covered_needOk (hC : CollisionFreeRun calls E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hroots : RootsSafe t E₀) {lim : Option Nat} {x : _root_.Address}
    (hcov : Claim.CoveredAt t lim x) : NeedOk E₀ x := by
  obtain ⟨r, had, hwr, -⟩ := hcov
  have hwb : RoleVal.roleWalksBound r = true := by
    rw [← Claim.walkedRole_eq_roleWalksBound]; exact hwr
  have hsafe := hroots.bound r (Or.inl hwb) x had
  obtain ⟨a', had', h₀, h₁, ap, ptr, v, cs, ha, ev, hsub, -, -⟩ :=
    RoleVal.ValidateRoleIn.bound_load_safe
      (show RoleVal.ValidateRoleIn calls bAddr t (Ix.SpecDigest.groupOf r) r from
        hvalAll _ r (role_mem_roleGroup r))
      (RoleVal.roleSpecKind_of_walked r (Or.inl hwb))
  have e : a' = x := Option.some.inj (had'.symm.trans had)
  rw [e] at ha
  obtain ⟨ab, hab, hab'⟩ := ha
  obtain ⟨raw, c', hsz, hh, hba, hx', -, hhead⟩ := Claim.get_ci_head hab ev
  have hcx : recordOf E₀ x = some c' := by
    rw [← hab', ← hba]
    exact Claim.recordOf_hashed hC.runStore hC.hashedStored (Core.hashed_mono hsub hh) hsz
      (L1.deConstant_of_deConstantExact hx') hx'
  exact ⟨c', hcx, fun ⟨ms, hms⟩ => hhead.notMuts ms hms, (hsafe c' hcx).1, (hsafe c' hcx).2⟩

/-- From `NotBlockIn`, `¬ CoveredAt → SourceSafe`, and a stored record in `E₀`, derive `NeedOk`. -/
theorem needOk_of_notBlock_sourceSafe (hC : CollisionFreeRun calls E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hroots : RootsSafe t E₀) {lim : Option Nat} {x : _root_.Address}
    (hnb : Claim.NotBlockIn calls x)
    (hsafe : ¬ Claim.CoveredAt t lim x → Claim.SourceSafe E₀ x)
    (hex : ∃ cx, recordOf E₀ x = some cx) : NeedOk E₀ x := by
  by_cases hcov : Claim.CoveredAt t lim x
  · exact covered_needOk hC hvalAll hroots hcov
  · obtain ⟨cx, hcx⟩ := hex
    obtain ⟨raw, c', hh, hbl, hde, hnotM⟩ := hnb
    have ec : c' = cx := by
      unfold recordOf at hcx
      cases hget : E₀.consts.get? x with
      | none => rw [hget] at hcx; cases hcx
      | some lc =>
        rw [hget] at hcx
        dsimp only [Option.bind] at hcx
        obtain ⟨hlcH, hlcB⟩ := hC.runStore.loaded.1 x lc hget
        have eraw : raw = lc.rawBytes := hC.runStore.hashed_inj hh hlcH (hbl.trans hlcB.symm)
        cases hdeE : Ixon.deConstantExact lc.rawBytes with
        | error _ => simp [hdeE, Except.toOption] at hcx
        | ok cx' =>
          simp only [hdeE, Except.toOption, Option.some.injEq] at hcx
          subst cx'
          have hde' := L1.deConstant_of_deConstantExact hdeE
          rw [← eraw, hde] at hde'
          exact Except.ok.inj hde'
    subst ec
    have hs := hsafe hcov c' hcx
    exact ⟨c', hcx, fun ⟨ms, hms⟩ => hnotM ms hms, hs.1, hs.2⟩

end Helpers

/-! ## The six-category classification of `PayReach` -/

/-- **Classification of every address reached through group `g`'s payload** relative to
`groupStore ... g` and `GroupReach ... g`. -/
inductive PayClass (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) : _root_.Address → Prop where
  | stored {x : _root_.Address} :
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x).isSome = true →
      PayClass calls bAddr t E₀ g x
  | walked {x : _root_.Address} :
      GroupReach t E₀ g x → PayClass calls bAddr t E₀ g x
  | famRec {B x : _root_.Address} {cs : List (Call F)} {advAs : List Bytes.Address} :
      (GroupReach t E₀ g B ∨
        (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) B).isSome = true) →
      ModeledRouteAt calls B →
      FamilyCallExact calls bAddr t B x (some (valLimit g)) cs advAs →
      PayClass calls bAddr t E₀ g x
  | directAdv {B rb x : _root_.Address} {cs : List (Call F)} {advAs : List Bytes.Address} :
      (GroupReach t E₀ g B ∨
        (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) B).isSome = true) →
      ModeledRouteAt calls B →
      FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs →
      AdviceListedIn advAs x →
      PayClass calls bAddr t E₀ g x
  | directCont {B rb x : _root_.Address} {cs : List (Call F)} {advAs : List Bytes.Address} :
      (GroupReach t E₀ g B ∨
        (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) B).isSome = true) →
      ModeledRouteAt calls B →
      FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs →
      DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs x →
      PayClass calls bAddr t E₀ g x
  | checkedProj {x : _root_.Address} {c cb : Ixon.Constant} :
      recordOf E₀ x = some c → IsProj c → usedRefIdxs c = [] →
      recordOf E₀ (Ix.Cert.ownerOf x c) = some cb → ConstAddrOf (Ix.Cert.ownerOf x c) cb x →
      ((recordOf (groupStore t E₀ (runPayload calls bAddr t) g)
          (Ix.Cert.ownerOf x c)).isSome = true ∨
        GroupReach t E₀ g (Ix.Cert.ownerOf x c) ∨
        ∃ B rb cs advAs,
          (GroupReach t E₀ g B ∨
            (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) B).isSome = true) ∧
          ModeledRouteAt calls B ∧
          FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs ∧
          AdviceListedIn advAs (Ix.Cert.ownerOf x c)) →
      PayClass calls bAddr t E₀ g x

section Classification

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- Helper: every witness classified by `outsClassified` lies in `PayClass`. -/
private theorem witness_in_payClass (hC : CollisionFreeRun calls E₀)
    {g : Nat} (hg6 : 6 ≤ g)
    (hcl_g : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) g))
    (halr_g : ∀ x, AlreadyStoredRole t g x →
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x).isSome = true)
    (hrec_g : ∀ x c, recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x = some c →
      recordOf E₀ x = some c)
    {B rb w : _root_.Address} {cs : List (Call F)} {advAs : List Bytes.Address}
    (hB : GroupReach t E₀ g B ∨
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) B).isSome = true)
    (hmodB : ModeledRouteAt calls B)
    (hex : FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs)
    (hw : (∃ ro : Ix.Kernel.Role, t.addressOf? ro = some w ∧
        Ix.SpecDigest.groupOf ro < 6 ∧
        (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
      (PathPos E₀ B w ∧ Claim.NotBlockIn calls w ∧
        ∃ c, recordOf E₀ w = some c ∧
          (IsProj c → usedRefIdxs c = [] ∧
            ∃ cb, recordOf E₀ (Ix.Cert.ownerOf w c) = some cb ∧
              ConstAddrOf (Ix.Cert.ownerOf w c) cb w)) ∨
      (DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs w ∧
        ∃ ib, PathPos E₀ B ib ∧
          ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
            Claim.RCLimRep t bAddr (some (valLimit g)) h₁ rc₁ ∧
            Core.S0.addr h₁ xx₁ w ∧ Core.S0.addr h₁ xib₁ ib ∧
            ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
            (∀ cl ∈ cs₁, cl ∈ calls) ∧ cs₁.length < cs.length) ∨
      (∃ ib c cib, PathPos E₀ B ib ∧ recordOf E₀ w = some c ∧ IsProj c ∧
        Ix.Cert.ownerOf w c = ib ∧ usedRefIdxs c = [] ∧
        recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib w)) :
    PayClass calls bAddr t E₀ g w := by
  rcases hw with ⟨ro, had, hlt, hk⟩ | ⟨hpos, -, -⟩ | ⟨hdc, -⟩ |
      ⟨ib, c, cib, hpos, hc, hp, hown, hnil, hcib, hca⟩
  · exact PayClass.stored (halr_g w (basisRole_alreadyStoredRole hg6 had hlt hk))
  · rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB hpos.toReach with hgr | hst
    · exact PayClass.walked hgr
    · exact PayClass.stored hst
  · exact PayClass.directCont hB hmodB hex hdc
  · rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB hpos.toReach with hgr | hst
    · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcib) (by rw [hown]; exact hca)
        (Or.inr (Or.inl (by rw [hown]; exact hgr)))
    · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcib) (by rw [hown]; exact hca)
        (Or.inl (by rw [hown]; exact hst))

/-- **Every address reached through group `g`'s payload lies in `PayClass`**, given `UsedClosed`
and `AlreadyStoredRole` completeness on `groupStore ... g`. -/
theorem payReach_in_payClass (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hstep : RunStepStores calls t E₀) {g : Nat} (hg6 : 6 ≤ g) (hg77 : g < 77)
    (hcl_g : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) g))
    (halr_g : ∀ x, AlreadyStoredRole t g x →
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x).isSome = true)
    {x : _root_.Address} (h : PayReach t E₀ (runPayload calls bAddr t) g x) :
    PayClass calls bAddr t E₀ g x := by
  have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
  have hrec_g : ∀ y c, recordOf (groupStore t E₀ (runPayload calls bAddr t) g) y = some c →
      recordOf E₀ y = some c :=
    fun y c hy => ((groupStore_recordOf hb hg6).mp hy).2
  induction h with
  | @payload B a hB hpay =>
    obtain ⟨-, hmod, rb, cs, advAs, hex, rfl | hadv | hdc⟩ := hpay
    · exact PayClass.famRec (Or.inl hB) hmod hex
    · exact PayClass.directAdv (Or.inl hB) hmod hex hadv
    · exact PayClass.directCont (Or.inl hB) hmod hex hdc
  | @payloadOf B a _ hpay ihB =>
    obtain ⟨-, hmod, rb, cs, advAs, hex, hcase⟩ := hpay
    have hfinish :
        (GroupReach t E₀ g B ∨
          (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) B).isSome = true) →
        PayClass calls bAddr t E₀ g a := fun hB => by
      rcases hcase with rfl | hadv | hdc
      · exact PayClass.famRec hB hmod hex
      · exact PayClass.directAdv hB hmod hex hadv
      · exact PayClass.directCont hB hmod hex hdc
    obtain ⟨cb, ms, hcb, hms, hpos, hallIndc⟩ :=
      familyCall_block_indc_nonempty hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
    cases ihB with
    | stored hst => exact hfinish (Or.inr hst)
    | walked hgr => exact hfinish (Or.inl hgr)
    | @famRec B' _ cs' advAs' _ _ hexB =>
      exfalso
      obtain ⟨c', rs, hc', -, hrs, -, hallRec, -⟩ :=
        familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hexB)
      have ec : c' = cb := Option.some.inj (hc'.symm.trans hcb)
      subst ec
      have ers : rs = ms := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hms)
      subst ers
      have hm0 : rs[0] ∈ rs.toList := Array.getElem_mem_toList hpos
      have hbi : Core.Specs.Callees.isIndc rs[0] = true :=
        (List.length_filter_eq_length_iff.mp (by simpa [Array.length_toList] using hallIndc)) _ hm0
      obtain ⟨r, hr⟩ := hallRec _ hm0
      rw [hr] at hbi
      simp [Core.Specs.Callees.isIndc, Core.isIndc] at hbi
    | @directAdv B' rb' _ cs' advAs' _ _ hexB hadvB =>
      exfalso
      obtain ⟨outs, hU⟩ := hexB.unpack hC hbd
      obtain ⟨ab, habMem, habEq⟩ := hadvB
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
      have ec : ca = cb := Option.some.inj (hca.symm.trans hcb)
      subst ec
      rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms', hms', -, -, hnat⟩ | ⟨hpr, -⟩
      · rw [hms] at hd; cases hd
      · rw [hms] at hrc; cases hrc
      · exact not_modeledRouteAt_of_nativeObs hnat hmod
      · exact proj_not_block hpr ⟨ms, hms⟩
    | @directCont B' rb' _ cs' advAs' _ _ hexB hdcB =>
      exact (containerRecIn_notBlock hC.runStore (FamilyCallExact.toCall hexB)
        (directContOwn_toContainerRecIn hdcB) hcb ms hms).elim
    | checkedProj hc' hpr _ _ _ _ =>
      have ec : _ = cb := Option.some.inj (hc'.symm.trans hcb)
      rw [ec] at hpr
      exact (proj_not_block hpr ⟨ms, hms⟩).elim
  | @ref a y _ hu hns ihA =>
    cases ihA with
    | stored hst =>
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp hst
      obtain ⟨c', i, hc', hi, hy⟩ := hu
      have ec : c' = ca := Option.some.inj (hc'.symm.trans (hrec_g a ca hca))
      subst ec
      exact PayClass.stored ((hcl_g.1 a c' hca).2 i hi y hy)
    | walked hgr =>
      exact PayClass.walked (GroupReach.ref hgr hu hns)
    | @famRec B _ cs advAs hB hmodB hex =>
      obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      obtain ⟨-, -, -, hcls⟩ := hU.famRefs y hu
      rcases hcls with huB | ⟨c, cb, hc, hp, hown, hnil, hcb, hca⟩ |
          ⟨blk, c, cb, hpos, hc, hp, hown, hnil, hcb, hca⟩ | hw
      · rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB
            (PathReach.single (Or.inl huB)) with hgr | hst
        · exact PayClass.walked hgr
        · exact PayClass.stored hst
      · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb) (by rw [hown]; exact hca)
          (by rw [hown]; rcases hB with h | h; exact Or.inr (Or.inl h); exact Or.inl h)
      · rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB hpos.toReach with hgr | hst
        · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb) (by rw [hown]; exact hca)
            (Or.inr (Or.inl (by rw [hown]; exact hgr)))
        · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb) (by rw [hown]; exact hca)
            (Or.inl (by rw [hown]; exact hst))
      · exact witness_in_payClass hC hg6 hcl_g halr_g hrec_g hB hmodB hex (hU.outsClassified y hw)
    | @directAdv B rb _ cs advAs hB hmodB hex hadv =>
      obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      obtain ⟨ab, habMem, habEq⟩ := hadv
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, -, -, -, -, hrefs⟩ := hfacts
      obtain ⟨-, -, -, hcls⟩ := hrefs y hu
      rcases hcls with hS | hW | ⟨blk, c, cb, hblkS, hc, hp, hown, hnil, hcb, hca⟩
      · have hyAdv : AdviceListedIn advAs y := by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hS
          exact ⟨b, List.mem_of_mem_take hb, rfl⟩
        exact PayClass.directAdv hB hmodB hex hyAdv
      · exact witness_in_payClass hC hg6 hcl_g halr_g hrec_g hB hmodB hex (hU.outsClassified y hW)
      · have hblkAdv : AdviceListedIn advAs blk := by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hblkS
          exact ⟨b, List.mem_of_mem_take hb, rfl⟩
        exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb) (by rw [hown]; exact hca)
          (Or.inr (Or.inr ⟨B, rb, cs, advAs, hB, hmodB, hex, by rw [hown]; exact hblkAdv⟩))
    | @directCont B rb _ cs advAs hB hmodB hex hdc =>
      obtain ⟨outs, -, -, hcrIn, ⟨ib, hposIb, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, -, hxx₁, hxib₁,
          evCr, hsubCr, -⟩, hcontRefs, -, houtsCls⟩ := hdc.unpack hC hbd
      obtain ⟨ca, i, hca, hi, hy⟩ := hu
      rcases check_container_rec_shape hC hbd hxx₁ hxib₁ evCr hsubCr hca with
        ⟨rc, hrc⟩ | ⟨rp, hrp⟩
      · obtain ⟨ib', ⟨h₃, h₄, xx', r', cs', b_ib', hxx', evRfb', hbRep', hbEq', hsubRfb'⟩, hrefs⟩ :=
          hcontRefs ca hca (Or.inl ⟨rc, hrc⟩)
        obtain ⟨v26, m29, cs37, evRfb1, hres1, hsub37⟩ :=
          check_container_rec_rec_family_block hC hbd hxx₁ hxib₁ evCr hsubCr
        have eib : ib' = ib := rec_family_block_det hC hbd hxx' hxx₁ evRfb' evRfb1
          hsubRfb' hsub37 ⟨b_ib', hbRep', hbEq'⟩ hres1
        subst eib
        have hownSelf : Ix.Cert.ownerOf a ca = a := by simp [Ix.Cert.ownerOf, hrc]
        have huOwn : UsedRef E₀ (Ix.Cert.ownerOf a ca) y := by rw [hownSelf]; exact ⟨ca, i, hca, hi, hy⟩
        obtain ⟨-, -, -, -, hcls⟩ := hrefs y huOwn
        rcases hcls with huIb | ⟨c, cb, hc, hp, hown, hnil, hcb, hca'⟩ |
            ⟨blk, c, cb, hposBlk, hc, hp, hown, hnil, hcb, hca'⟩ | ⟨hw, -⟩
        · rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB
              (hposIb.tail (Or.inl huIb)).toReach with hgr | hst
          · exact PayClass.walked hgr
          · exact PayClass.stored hst
        · rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB hposIb.toReach with hgr | hst
          · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb)
              (by rw [hown]; exact hca') (Or.inr (Or.inl (by rw [hown]; exact hgr)))
          · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb)
              (by rw [hown]; exact hca') (Or.inl (by rw [hown]; exact hst))
        · have hposB := hposIb.trans_reach hposBlk.toReach
          rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB hposB.toReach with hgr | hst
          · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb)
              (by rw [hown]; exact hca') (Or.inr (Or.inl (by rw [hown]; exact hgr)))
          · exact PayClass.checkedProj hc hp hnil (by rw [hown]; exact hcb)
              (by rw [hown]; exact hca') (Or.inl (by rw [hown]; exact hst))
        · exact witness_in_payClass hC hg6 hcl_g halr_g hrec_g hB hmodB hex (houtsCls y hw)
      · exfalso
        obtain ⟨h₀, h₀', ab, ap, ptr, cs', args, hab, rfl, evCi, hsubCi, -⟩ :=
          containerRecIn_load (FamilyCallExact.toCall hex) hcrIn
        have hnil := proj_usedRefIdxs_nil hC.runStore hab evCi hsubCi hca
          (Or.inr (Or.inr (Or.inr ⟨rp, hrp⟩)))
        rw [hnil] at hi
        cases hi
    | checkedProj hc' _ hnil _ _ _ =>
      exfalso
      obtain ⟨c', i, hc'', hi, -⟩ := hu
      have ec : c' = _ := Option.some.inj (hc''.symm.trans hc')
      rw [ec, hnil] at hi
      cases hi
  | @owner a c _ hc hp ihA =>
    cases ihA with
    | stored hst =>
      obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp hst
      have ec : ca = c := Option.some.inj ((hrec_g a ca hca).symm.trans hc)
      subst ec
      exact PayClass.stored (hcl_g.1 a ca hca).1
    | walked hgr =>
      exact PayClass.walked (GroupReach.owner hgr hc hp)
    | @famRec B _ cs advAs _ _ hex =>
      exfalso
      obtain ⟨c', rs, hc', -, hrs, -, -, -⟩ :=
        familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
      have ec : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst ec
      exact proj_not_block hp ⟨rs, hrs⟩
    | @directAdv B rb _ cs advAs hB hmodB hex hadv =>
      obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      obtain ⟨ab, habMem, habEq⟩ := hadv
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
      have ec : ca = c := Option.some.inj (hca.symm.trans hc)
      subst ec
      rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms, hms, -⟩ | ⟨-, -, hownS, -⟩
      · exact (standalone_not_proj (Or.inl ⟨d, hd⟩) hp).elim
      · exact (standalone_not_proj (Or.inr (Or.inl ⟨rc, hrc⟩)) hp).elim
      · exact (proj_not_block hp ⟨ms, hms⟩).elim
      · have hownAdv : AdviceListedIn advAs (Ix.Cert.ownerOf a ca) := by
          obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hownS
          exact ⟨b, List.mem_of_mem_take hb, hbe⟩
        exact PayClass.directAdv hB hmodB hex hownAdv
    | @directCont B rb _ cs advAs hB hmodB hex hdc =>
      obtain ⟨outs, -, -, -, ⟨ib, hposIb, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, hrc₁, hxx₁, hxib₁,
          evCr, hsubCr, -⟩, -, -, -⟩ := hdc.unpack hC hbd
      rcases check_container_rec_shape hC hbd hxx₁ hxib₁ evCr hsubCr hc with
        ⟨rc, hrc⟩ | ⟨rp, hrp⟩
      · exact (standalone_not_proj (Or.inr (Or.inl ⟨rc, hrc⟩)) hp).elim
      · have hchk := (Decl.containerRec_checked hC.runStore hrc₁ hxx₁ evCr hsubCr).1
        obtain ⟨family, cs', h_rf, m_rf, ap_rf, fb_rf, cs_rf, hmodF, hfcF, ha_rf, hfb_rf,
            ev_rf, hsub_rf⟩ := rprj_checked_modeled_family hC hstep hchk hc hrp
        obtain ⟨v26, m29, cs37, evRfb1, hres1, hsub37⟩ :=
          check_container_rec_rec_family_block hC hbd hxx₁ hxib₁ evCr hsubCr
        have efam : family = ib := rec_family_block_det hC hbd ha_rf hxx₁ ev_rf evRfb1
          hsub_rf hsub37 hfb_rf hres1
        subst efam
        obtain ⟨advAs', hex'⟩ := familyCallExact_of_call hfcF
        have hownEq : Ix.Cert.ownerOf a c = rp.block := by simp [Ix.Cert.ownerOf, hrp]
        rw [hownEq]
        exact PayClass.famRec (pathReach_closed_of_usedClosed hrec_g hcl_g halr_g hB hposIb.toReach)
          hmodF hex'
    | checkedProj hc' _ _ _ _ hown =>
      have ec : _ = c := Option.some.inj (hc'.symm.trans hc)
      subst ec
      rcases hown with hst | hgr | ⟨B, rb, cs, advAs, hB, hmodB, hex, hadv⟩
      · exact PayClass.stored hst
      · exact PayClass.walked hgr
      · exact PayClass.directAdv hB hmodB hex hadv

/-! ## Deriving `PayloadFactsAt` and `OpEarlier` at step `g` -/

/-- The step invariant proved by strong induction on `g` (`6 ≤ g < 77`). -/
def StoreStepInv (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) : Prop :=
  PayloadFactsAt t E₀ (runPayload calls bAddr t) g ∧
    (g < 33 → ∀ x, PayReach t E₀ (runPayload calls bAddr t) g x → OpEarlier t g x)

/-- Any record already stored in `groupStore ... g` for `6 ≤ g < 33` satisfies `OpEarlier t g`,
given the strong induction hypothesis below `g`. -/
private theorem storedOpEarlier (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hcheck : t.check = .ok ())
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) (hg33 : g < 33)
    (hih : ∀ k, 6 ≤ k → k < g → StoreStepInv calls bAddr t E₀ k)
    {x : _root_.Address}
    (hheld : (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x).isSome = true) :
    OpEarlier t g x := by
  have hP_lt : PayloadFacts t E₀ (truncPay (runPayload calls bAddr t) g) :=
    payloadFacts_truncPay (fun _ _ _ hp => hp.1) (fun k hk6 hkg => (hih k hk6 hkg).1)
  have hwf : t.wf = true := wf_of_check hcheck
  intro ro had hop
  obtain ⟨c, hcG⟩ := Option.isSome_iff_exists.mp hheld
  rw [← truncPay_groupStore_eq (n := g) (Nat.le_refl g)] at hcG
  obtain ⟨hsb, hE⟩ := (groupStore_recordOf hb hg6).mp hcG
  obtain ⟨a₁, c₁, d, had₁, hc₁, hd, -⟩ :=
    validate_role_op_obs hcheck hC.runStore hC.hashedStored
      (show RoleVal.ValidateRoleIn calls bAddr t _ ro from hvalAll _ ro (role_mem_roleGroup ro)) hop
  have ea : a₁ = x := Option.some.inj (had₁.symm.trans had)
  rw [ea, hE] at hc₁
  have hcd : c.info = .defn d := by rw [Option.some.inj hc₁]; exact hd
  rcases hsb with hbas | ⟨k, hk6, hkg, hadd⟩
  · exfalso
    obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hbas
    obtain ⟨c₀, hmem, -⟩ := StoreInhabit.store_get?_inv hlc
    have hrecE : recordOf E₀ x = some c₀ := by
      have h6 : recordOf (groupStore t E₀ (runPayload calls bAddr t) 6) x = some c₀ := by
        rw [groupStore_six]; exact StoreInhabit.store_record_of_mem hmem
      exact ((groupStore_recordOf hb (Nat.le_refl 6)).mp h6).2
    have ec : c₀ = c := Option.some.inj (hrecE.symm.trans hE)
    have hnd := List.all_eq_true.mp basisRows_no_defn (x, c₀) hmem
    rw [ec, hcd] at hnd
    cases hnd
  · obtain ⟨recs, hw⟩ := hws k
    rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ |
        ⟨-, -, -, -, p, hp, hproj, -⟩ | ⟨_, -, -, -, c₂, ax, hc₂, hi, -⟩ | hpay
    · have hsteps := walkStepsOrdered_of_run hC (hvalAll k) (Or.inl (by omega))
      rcases hra.root_or_earlier hsteps (axiomSteps_ordered hC (hvalAll k)) with
        ⟨r', hr', had'⟩ | hE' | ⟨y, cy, hy, hcy, hpy, hown⟩
      · have er : ro = r' := addressOf_role_inj hwf had had'
        rw [er, groupOf_of_mem_roleGroup hr']
        exact hkg
      · exact Nat.lt_trans (hE' ro had hop) hkg
      · exfalso
        obtain ⟨cb, hcb, ms, hms⟩ := hy.owner_block hC hw hcy hpy
        rw [hown, hE] at hcb
        rw [← Option.some.inj hcb, hcd] at hms
        cases hms
    · exfalso
      have ep : p = c := Option.some.inj (hp.symm.trans hE)
      rw [ep] at hproj
      exact standalone_not_proj (Or.inl ⟨d, hcd⟩) hproj
    · exfalso
      have ec : c₂ = c := Option.some.inj (hc₂.symm.trans hE)
      rw [ec, hcd] at hi
      cases hi
    · rcases payAdds_cases hP_lt hpay with ⟨hpr, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
      · have hpr' := (truncPay_payReach_iff hkg).mp hpr
        exact Nat.lt_trans ((hih k hk6 hkg).2 (by omega) x hpr' ro had hop) hkg
      · exfalso
        have ep : p = c := Option.some.inj (hp.symm.trans hE)
        rw [ep] at hproj
        exact standalone_not_proj (Or.inl ⟨d, hcd⟩) hproj

/-- **Strong induction establishing `StoreStepInv` for every group `6 ≤ g < 77`.** -/
theorem storeStepInv_all (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g < 77 → StoreStepInv calls bAddr t E₀ g := by
  have hval77 : ∀ k, k < 77 → ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r :=
    fun k _ => hvalAll k
  intro g
  induction g using Nat.strong_induction_on with
  | h g ih =>
    intro hg6 hg77
    have hP_lt : PayloadFacts t E₀ (truncPay (runPayload calls bAddr t) g) :=
      payloadFacts_truncPay (fun _ _ _ hp => hp.1) (fun k hk6 hkg => (ih k hkg hk6 (by omega)).1)
    have hcl_g : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) g) := by
      rw [← truncPay_groupStore_eq (n := g) (Nat.le_refl g)]
      exact groupStore_usedClosed_all hC hb hbr hax hP_lt hws g hg6
    have halr_g : ∀ x, AlreadyStoredRole t g x →
        (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x).isSome = true := by
      intro x hst
      rw [← truncPay_groupStore_eq (n := g) (Nat.le_refl g)]
      have hsb : StoredBelow t E₀ (truncPay (runPayload calls bAddr t) g) g x :=
        storedBelow_of_alreadyStored hbr hst
      obtain ⟨cx, hcx⟩ := storedBelow_record hC hb hax hP_lt hws hsb
      rw [(groupStore_recordOf hb hg6).mpr ⟨hsb, hcx⟩]
      rfl
    have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
    have hcls : ∀ x, PayReach t E₀ (runPayload calls bAddr t) g x →
        PayClass calls bAddr t E₀ g x :=
      fun x hx => payReach_in_payClass hC hbd hb hstep hg6 hg77 hcl_g halr_g hx
    obtain ⟨recs, hw⟩ := hws g
    have hPF : PayloadFactsAt t E₀ (runPayload calls bAddr t) g := by
      refine
        { record := fun a ha => ?_
          blockMembers := fun B c ms hB hE hms i m hm => ?_
          projMember := fun a c ha hE hp => ?_
          logic := fun a c ha hE => ?_
          notAxiomLike := fun a c ha hnew hE hk => ?_ }
      · cases hcls a ha with
        | stored hst =>
          obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hst
          exact ⟨c, ((groupStore_recordOf hb hg6).mp hc).2⟩
        | walked hgr =>
          obtain ⟨y, -, hya⟩ := hgr.listed hC.hashedStored hw
          exact ⟨y.c, by rw [← hya]; exact topRec_recordOf hC.hashedStored y⟩
        | famRec _ _ hex =>
          obtain ⟨c, hc, -⟩ :=
            familyCall_record_facts hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
          exact ⟨c, hc⟩
        | directAdv _ _ hex hadv =>
          exact adviceIn_record hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
            (adviceListedIn_toAdviceIn (FamilyCallExact.toOwn hex) hadv)
        | directCont _ _ hex hdc =>
          exact containerRecIn_record hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
            (directContOwn_toContainerRecIn hdc)
        | checkedProj hc _ _ _ _ _ => exact ⟨_, hc⟩
      · cases hcls B hB with
        | stored hst =>
          obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp hst
          have ec : c₀ = c := Option.some.inj (((groupStore_recordOf hb hg6).mp hc₀).2.symm.trans hE)
          subst ec
          obtain ⟨h1, h2⟩ := hcl_g.2 B c₀ ms hc₀ hms i m hm
          exact ⟨((groupStore_recordOf hb hg6).mp h1).2,
            fun ind j hind hj => ((groupStore_recordOf hb hg6).mp (h2 ind hind j hj)).2⟩
        | walked hgr =>
          obtain ⟨y, -, hya⟩ := hgr.listed hC.hashedStored hw
          have hyc := topRec_recordOf hC.hashedStored y
          rw [hya] at hyc
          have ec : c = y.c := Option.some.inj (hE.symm.trans hyc)
          rw [ec] at hms
          have hmem := topRec_block_members hC.runStore hC.hashedStored y hms hm
          rw [hya] at hmem
          exact hmem
        | famRec _ _ hex =>
          obtain ⟨c₀, hc₀, -, hshape⟩ :=
            familyCall_record_facts hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
          have ec : c₀ = c := Option.some.inj (hc₀.symm.trans hE)
          subst ec
          rcases hshape with ⟨rcr, hr⟩ | ⟨ms₀, hms₀, hall, hmem⟩
          · rw [hr] at hms; cases hms
          · have ems : ms₀ = ms := Ixon.ConstantInfo.muts.inj (hms₀.symm.trans hms)
            subst ems
            refine ⟨hmem i m hm, fun ind j hind _ => ?_⟩
            have hmL : ms₀.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
            obtain ⟨r, hr⟩ := hall m (List.mem_of_getElem? hmL)
            rw [hind] at hr; cases hr
        | directAdv _ _ hex hadv =>
          exact (adviceCheck_block t hC.runStore hC.hashedStored
            (adviceCheckObs_of_familyCall (FamilyCallExact.toCall hex)
              (adviceListedIn_toAdviceIn (FamilyCallExact.toOwn hex) hadv)) hE hms).2 i m hm
        | directCont _ _ hex hdc =>
          exact (containerRecIn_notBlock hC.runStore (FamilyCallExact.toCall hex)
            (directContOwn_toContainerRecIn hdc) hE ms hms).elim
        | checkedProj hc' hpr _ _ _ _ =>
          have ec : _ = c := Option.some.inj (hc'.symm.trans hE)
          rw [ec] at hpr
          exact (proj_not_block hpr ⟨ms, hms⟩).elim
      · cases hcls a ha with
        | stored hst =>
          obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp hst
          have ec : c₀ = c := Option.some.inj (((groupStore_recordOf hb hg6).mp hc₀).2.symm.trans hE)
          subst ec
          exact (stored_logic_and_projMember hC hb hax hroots hvalAll hws hg6 (by omega)
            hP_lt hc₀).2 hp
        | walked hgr =>
          obtain ⟨y, -, hya⟩ := hgr.listed hC.hashedStored hw
          have hyc := topRec_recordOf hC.hashedStored y
          rw [hya] at hyc
          have ec : c = y.c := Option.some.inj (hE.symm.trans hyc)
          have hpm := topRec_proj_member hC.runStore hC.hashedStored y (ec ▸ hp)
          rw [hya, ← ec] at hpm
          exact hpm
        | famRec _ _ hex =>
          obtain ⟨c₀, rs, hc₀, -, hrs, -, -, -⟩ :=
            familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
          have ec : c₀ = c := Option.some.inj (hc₀.symm.trans hE)
          subst ec
          exact (proj_not_block hp ⟨rs, hrs⟩).elim
        | directAdv _ _ hex hadv =>
          exact adviceCheck_projMember hC.runStore hC.hashedStored
            (adviceCheckObs_of_familyCall (FamilyCallExact.toCall hex)
              (adviceListedIn_toAdviceIn (FamilyCallExact.toOwn hex) hadv)) hE hp
        | directCont _ _ hex hdc =>
          exact containerRecIn_projMember hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
            (directContOwn_toContainerRecIn hdc) hE hp
        | checkedProj hc' _ _ hcb hca _ =>
          have ec : _ = c := Option.some.inj (hc'.symm.trans hE)
          subst ec
          exact ⟨_, hcb, hca⟩
      · cases hcls a ha with
        | stored hst =>
          obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp hst
          have ec : c₀ = c := Option.some.inj (((groupStore_recordOf hb hg6).mp hc₀).2.symm.trans hE)
          subst ec
          exact (stored_logic_and_projMember hC hb hax hroots hvalAll hws hg6 (by omega)
            hP_lt hc₀).1
        | walked hgr =>
          exact (groupReach_sourceSafe_of_run hC hval77 hroots hg77 hw a hgr c hE).1
        | famRec _ _ hex =>
          obtain ⟨c₀, hc₀, hlog, -⟩ :=
            familyCall_record_facts hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
          rw [← Option.some.inj (hc₀.symm.trans hE)]
          exact hlog
        | directAdv _ _ hex hadv =>
          exact adviceCheck_logic t hC.runStore hC.hashedStored
            (adviceCheckObs_of_familyCall (FamilyCallExact.toCall hex)
              (adviceListedIn_toAdviceIn (FamilyCallExact.toOwn hex) hadv)) hE
        | directCont _ _ hex hdc =>
          exact containerRecIn_logic hC.runStore (FamilyCallExact.toCall hex)
            (directContOwn_toContainerRecIn hdc) hE
        | checkedProj hc' hpr _ _ _ _ =>
          have ec : _ = c := Option.some.inj (hc'.symm.trans hE)
          rw [ec] at hpr
          exact isProj_inLogic hpr
      · cases hcls a ha with
        | stored hst =>
          rw [hnew.2] at hst; cases hst
        | walked hgr =>
          obtain ⟨-, -, -, -, hnot⟩ := new_groupStore hb hg6 hnew
          exact groupReach_new_not_axiomLike hC hax hpin (hvalAll g) hw
            (groupReach_sourceSafe_of_run hC hval77 hroots hg77 hw) hgr hnot hE hk
        | famRec _ _ hex =>
          obtain ⟨c₀, rs, hc₀, -, hrs, -, -, -⟩ :=
            familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
          have ec : c₀ = c := Option.some.inj (hc₀.symm.trans hE)
          subst ec
          exact isBlock_not_axiomLike hrs hk
        | directAdv _ _ hex hadv =>
          exact adviceIn_notAxiomLike hC.runStore (FamilyCallExact.toCall hex)
            (adviceListedIn_toAdviceIn (FamilyCallExact.toOwn hex) hadv) hE hk
        | directCont _ _ hex hdc =>
          exact containerRecIn_notAxiomLike hC.runStore (FamilyCallExact.toCall hex)
            (directContOwn_toContainerRecIn hdc) hE hk
        | checkedProj hc' hpr _ _ _ _ =>
          have ec : _ = c := Option.some.inj (hc'.symm.trans hE)
          rw [ec] at hpr
          exact isProj_not_axiomLike hpr hk
    refine ⟨hPF, fun hg33 x hx => ?_⟩
    have hstepsG := walkStepsOrdered_of_run hC (hvalAll g) (Or.inl hg33)
    have hpayOrd : ∀ B a, runPayload calls bAddr t g B a → OpEarlier t g a := by
      rintro B a ⟨-, -, rb, cs, advAs, hex, rfl | hadv | hdc⟩
      · obtain ⟨outs, hU⟩ := hex.unpack hC hbd
        exact opEarlier_of_ordered hg33 hU.rbOrdered
      · obtain ⟨outs, hU⟩ := hex.unpack hC hbd
        obtain ⟨ab, habMem, habEq⟩ := hadv
        obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
        have hfacts := hU.adviceFacts k hk
        rw [hgetk, habEq] at hfacts
        exact opEarlier_of_ordered hg33 hfacts.1
      · obtain ⟨-, -, hord, -⟩ := hdc.unpack hC hbd
        exact opEarlier_of_ordered hg33 hord
    induction hx with
    | payload _ hpay => exact hpayOrd _ _ hpay
    | payloadOf _ hpay _ => exact hpayOrd _ _ hpay
    | @ref a y ha hu hns _ =>
      cases hcls a ha with
      | stored hst =>
        obtain ⟨ca, hca⟩ := Option.isSome_iff_exists.mp hst
        obtain ⟨c', i, hc', hi, hy⟩ := hu
        have ec : c' = ca := Option.some.inj (hc'.symm.trans ((groupStore_recordOf hb hg6).mp hca).2)
        subst ec
        exact storedOpEarlier hC hb hax hcheck hvalAll hws hg6 hg33
          (fun k hk6 hkg => ih k hkg hk6 (by omega)) ((hcl_g.1 a c' hca).2 i hi y hy)
      | walked hgr =>
        exact hstepsG.refs a y hgr hu (AlreadyStoredRole.not_covered hns)
      | famRec _ _ hex =>
        obtain ⟨outs, hU⟩ := hex.unpack hC hbd
        exact opEarlier_of_ordered hg33 (hU.famRefs y hu).2.1
      | directAdv _ _ hex hadv =>
        obtain ⟨outs, hU⟩ := hex.unpack hC hbd
        obtain ⟨ab, habMem, habEq⟩ := hadv
        obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
        have hfacts := hU.adviceFacts k hk
        rw [hgetk, habEq] at hfacts
        exact opEarlier_of_ordered hg33 (hfacts.2.choose_spec.2.2.2 y hu).2.1
      | directCont _ _ hex hdc =>
        obtain ⟨outs, -, -, hcrIn, ⟨ib, -, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, -, hxx₁, hxib₁,
            evCr, hsubCr, -⟩, hcontRefs, -, -⟩ := hdc.unpack hC hbd
        obtain ⟨ca, i, hca, hi, hy⟩ := hu
        rcases check_container_rec_shape hC hbd hxx₁ hxib₁ evCr hsubCr hca with
          ⟨rc, hrc⟩ | ⟨rp, hrp⟩
        · obtain ⟨ib', -, hrefs⟩ := hcontRefs ca hca (Or.inl ⟨rc, hrc⟩)
          have hownSelf : Ix.Cert.ownerOf a ca = a := by simp [Ix.Cert.ownerOf, hrc]
          have huOwn : UsedRef E₀ (Ix.Cert.ownerOf a ca) y := by
            rw [hownSelf]; exact ⟨ca, i, hca, hi, hy⟩
          exact opEarlier_of_ordered hg33 (hrefs y huOwn).2.2.1
        · exfalso
          obtain ⟨h₀, h₀', ab, ap, ptr, cs', args, hab, rfl, evCi, hsubCi, -⟩ :=
            containerRecIn_load (FamilyCallExact.toCall hex) hcrIn
          have hnil := proj_usedRefIdxs_nil hC.runStore hab evCi hsubCi hca
            (Or.inr (Or.inr (Or.inr ⟨rp, hrp⟩)))
          rw [hnil] at hi
          cases hi
      | checkedProj hc' _ hnil _ _ _ =>
        exfalso
        obtain ⟨c', i, hc'', hi, -⟩ := hu
        have ec : c' = _ := Option.some.inj (hc''.symm.trans hc')
        rw [ec, hnil] at hi
        cases hi
    | @owner a c ha hc hp _ =>
      intro ro had hop
      exfalso
      obtain ⟨cb, hcb, hca⟩ := hPF.projMember a c ha hc hp
      obtain ⟨a₁, c₁, d, had₁, hc₁, hd, -⟩ :=
        validate_role_op_obs hcheck hC.runStore hC.hashedStored
          (show RoleVal.ValidateRoleIn calls bAddr t _ ro from hvalAll _ ro (role_mem_roleGroup ro))
          hop
      have ea : a₁ = Ix.Cert.ownerOf a c := Option.some.inj (had₁.symm.trans had)
      rw [ea, hcb] at hc₁
      have hcbd : cb.info = .defn d := by rw [Option.some.inj hc₁]; exact hd
      rcases hca with ⟨heq, hst⟩ | ⟨ms, _, _, hms, -, -⟩
      · rw [← heq, hc] at hcb
        have ec : c = cb := Option.some.inj hcb
        rw [ec] at hp
        exact standalone_not_proj hst hp
      · rw [hcbd] at hms; cases hms

/-! ## Global exports discharging all non-rank, non-family-flat/form obligations -/

/-- **Global `PayloadFacts` for the run's payload** (discharges `payloadSteps`). -/
theorem payloadFacts_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    PayloadFacts t E₀ (runPayload calls bAddr t) := by
  have hinv := storeStepInv_all hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hbounds : ∀ g a, PayReach t E₀ (runPayload calls bAddr t) g a → 6 ≤ g ∧ g < 77 := by
    intro g a h
    have h6 : 6 ≤ g := by
      induction h with
      | payload _ hp => exact hp.1
      | payloadOf _ hp _ => exact hp.1
      | ref _ _ _ ih => exact ih
      | owner _ _ _ ih => exact ih
    have h77 : g < 77 := by
      by_contra hge
      exact payReach_empty_of_ge (Nat.le_of_not_lt hge) h
    exact ⟨h6, h77⟩
  refine
    { record := fun g a h => by
        obtain ⟨h6, h77⟩ := hbounds g a h
        exact (hinv g h6 h77).1.record a h
      blockMembers := fun g B c ms h => by
        obtain ⟨h6, h77⟩ := hbounds g B h
        exact (hinv g h6 h77).1.blockMembers B c ms h
      projMember := fun g a c h => by
        obtain ⟨h6, h77⟩ := hbounds g a h
        exact (hinv g h6 h77).1.projMember a c h
      logic := fun g a c h => by
        obtain ⟨h6, h77⟩ := hbounds g a h
        exact (hinv g h6 h77).1.logic a c h
      notAxiomLike := fun g a c h => by
        obtain ⟨h6, h77⟩ := hbounds g a h
        exact (hinv g h6 h77).1.notAxiomLike a c h }

/-- **The payload's facts of a run** (`payloadFacts_of_run`), exported under
`RemainingFamilyClauses.payload`. -/
theorem RemainingFamilyClauses.payload (_hR : RemainingFamilyClauses calls bAddr t E₀)
    (hC : CollisionFreeRun calls E₀) (hbd : IxVM.Consistency.Bounded calls)
    (hb : BasisRowsLoaded E₀) (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ()) (hroots : RootsSafe t E₀)
    (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    PayloadFacts t E₀ (runPayload calls bAddr t) :=
  payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws

/-- **Global `payloadOps` below group 41**: groups 6..32 from `storeStepInv_all`, and groups
33..40 vacuous by `payReach_empty_wf`. -/
theorem payloadOps_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g < 41 → ∀ x, PayReach t E₀ (runPayload calls bAddr t) g x → OpEarlier t g x := by
  have hinv := storeStepInv_all hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  intro g hg6 hg41 x hx
  by_cases hg33 : g < 33
  · exact (hinv g hg6 (by omega)).2 hg33 x hx
  · exact (payReach_empty_wf hC hvalAll hws (by omega) (by omega) x hx).elim

/-- **Convenience `PayClass` corollary using global `payloadFacts_of_run`.** -/
theorem payReach_payClass_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) (hg77 : g < 77) {x : _root_.Address}
    (hx : PayReach t E₀ (runPayload calls bAddr t) g x) :
    PayClass calls bAddr t E₀ g x := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hcl_g := groupStore_usedClosed_all hC hb hbr hax hP hws g hg6
  have halr_g : ∀ y, AlreadyStoredRole t g y →
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) y).isSome = true := by
    intro y hst
    have hsb := storedBelow_of_alreadyStored (E₀ := E₀) (Pay := runPayload calls bAddr t) hbr hst
    obtain ⟨cy, hcy⟩ := storedBelow_record hC hb hax hP hws hsb
    rw [(groupStore_recordOf hb hg6).mpr ⟨hsb, hcy⟩]
    rfl
  exact payReach_in_payClass hC hbd hb hstep hg6 hg77 hcl_g halr_g hx

/-- **Discharges `claimed`**: every new non-empty block of recursors has an observed
`FamilyCallAtLim` at the group's validation limit. -/
theorem claimed_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g < 77 → ∀ (A : _root_.Address) (c : Ixon.Constant)
      (rs' : Array Ixon.MutConst),
      New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) A →
      recordOf E₀ A = some c → c.info = .muts rs' → 0 < rs'.size →
      (∀ m ∈ rs'.toList, ∃ r, m = Ixon.MutConst.recr r) →
      (∃ B, runFamOf calls bAddr t E₀ g B = some A) ∨
        ∃ B cs, FamilyCallAtLim calls bAddr t B A (some (valLimit g)) cs := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  intro g hg6 hg77 A c rs' hnew hE hms hpos hall
  obtain ⟨recs, hw⟩ := hws g
  have hfromWalk : GroupReach t E₀ g A →
      ∃ B cs, FamilyCallAtLim calls bAddr t B A (some (valLimit g)) cs := by
    intro hgr
    obtain ⟨y, -, hya⟩ := hgr.listed hC.hashedStored hw
    have hU := unitCheckedAt_of_topRec hC.hashedStored y
    rw [hya] at hU
    rcases hU with hchk | ⟨c', ms', hc', hms', hmem⟩
    · exact (Claim.checked_not_block hC.runStore hE hms hchk).elim
    · have ec : c' = c := Option.some.inj (hc'.symm.trans hE)
      subst ec
      have ems : ms' = rs' := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
      subst ms'
      obtain ⟨r, hr⟩ := hall rs'[0] (Array.getElem_mem_toList hpos)
      have hk0 : rs'.toList[((0 : Nat) : F).val]? = some (.recr r) := by
        simp [Array.getElem?_toList, Array.getElem?_eq_getElem hpos, hr]
      obtain ⟨B, cs, -, hfc⟩ :=
        recBlock_memberChecked_modeled_family hC hstep hE hms hk0 (hmem 0 hpos)
      exact ⟨B, cs, hfc⟩
  rcases new_reach_cases hC hb hax hP hg6 hw hnew hE
      (fun hp => proj_not_block hp ⟨rs', hms⟩) (fun ax h => by rw [hms] at h; cases h) with
    hgr | hpr
  · exact Or.inr (hfromWalk hgr)
  · cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws hg6 hg77 hpr with
    | stored hst => rw [hnew.2] at hst; cases hst
    | walked hgr => exact Or.inr (hfromWalk hgr)
    | famRec _ _ hex => exact Or.inr ⟨_, _, FamilyCallExact.toCall hex⟩
    | directAdv _ _ hex hadv =>
      exfalso
      obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      obtain ⟨ab, habMem, habEq⟩ := hadv
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
      have ec : ca = c := Option.some.inj (hca.symm.trans hE)
      subst ec
      rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms', hms', hallI, -, -⟩ | ⟨hp, -⟩
      · rw [hms] at hd; cases hd
      · rw [hms] at hrc; cases hrc
      · have ems : ms' = rs' := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
        subst ms'
        obtain ⟨ind, hind⟩ := hallI rs'[0] (Array.getElem_mem_toList hpos)
        obtain ⟨r, hr⟩ := hall rs'[0] (Array.getElem_mem_toList hpos)
        rw [hind] at hr; cases hr
      · exact proj_not_block hp ⟨rs', hms⟩
    | directCont _ _ hex hdc =>
      exact (containerRecIn_notBlock hC.runStore (FamilyCallExact.toCall hex)
        (directContOwn_toContainerRecIn hdc) hE rs' hms).elim
    | checkedProj hc' hpr _ _ _ _ =>
      have ec : _ = c := Option.some.inj (hc'.symm.trans hE)
      rw [ec] at hpr
      exact (proj_not_block hpr ⟨rs', hms⟩).elim

/-- **Discharges `payloadChecked`**: every new non-twin unit reached through group `g`'s payload
was checked at the group's validation limit (`UnitCheckedAt`). -/
theorem payloadChecked_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g < 77 → ∀ a c,
      PayReach t E₀ (runPayload calls bAddr t) g a →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
      recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c → UnitKind c →
      ¬ IsTwinShape c →
      UnitCheckedAt calls bAddr t E₀ a (some (valLimit g)) ∨
        ∃ B, runFamOf calls bAddr t E₀ g B = some a ∧
          New (groupStore t E₀ (runPayload calls bAddr t) g)
            (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B := by
  intro g hg6 hg77 a c hpr hnew hcR' hunit hntw
  have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
  obtain ⟨recs, hw⟩ := hws g
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcR').2
  cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws hg6 hg77 hpr with
  | stored hst => rw [hnew.2] at hst; cases hst
  | walked hgr =>
    left
    obtain ⟨y, -, hya⟩ := hgr.listed hC.hashedStored hw
    rw [← hya]
    exact unitCheckedAt_of_topRec hC.hashedStored y
  | famRec _ _ hex =>
    exfalso
    obtain ⟨c', rs, hc', -, hrs, hpos, hall, -⟩ :=
      familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
    have ec : c' = c := Option.some.inj (hc'.symm.trans hE)
    subst ec
    exact hntw ⟨rs, hrs, hpos, hall⟩
  | directAdv _ _ hex hadv =>
    left
    obtain ⟨outs, hU⟩ := hex.unpack hC hbd
    obtain ⟨ab, habMem, habEq⟩ := hadv
    obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
    have hfacts := hU.adviceFacts k hk
    rw [hgetk, habEq] at hfacts
    obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
    have ec : ca = c := Option.some.inj (hca.symm.trans hE)
    subst ec
    rcases hkind with ⟨_, _, hchk⟩ | ⟨_, _, hchk⟩ | ⟨ms, hms, -, hmem, -⟩ | ⟨hp, -⟩
    · exact Or.inl hchk
    · exact Or.inl hchk
    · exact Or.inr ⟨ca, ms, hE, hms, hmem⟩
    · exact (unitKind_not_proj hunit hp).elim
  | directCont _ _ hex hdc =>
    left
    obtain ⟨-, -, -, -, ⟨ib, -, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, hrc₁, hxx₁, -, evCr, hsubCr, -⟩,
        -, -, -⟩ := hdc.unpack hC hbd
    exact Or.inl (Decl.containerRec_checked hC.runStore hrc₁ hxx₁ evCr hsubCr).1
  | checkedProj hc' hpr _ _ _ _ =>
    have ec : _ = c := Option.some.inj (hc'.symm.trans hE)
    rw [ec] at hpr
    exact (unitKind_not_proj hunit hpr).elim

/-- **No inert axiom record is ever stored in `groupStore ... g` (`6 ≤ g ≤ 77`).** -/
theorem inert_not_in_groupStore (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∀ x, InertAt t x →
      recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x = none := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hval77 : ∀ k, k < 77 → ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r :=
    fun k _ => hvalAll k
  have hwf : t.wf = true := wf_of_check hcheck
  have hinertAx : ∀ x, InertAt t x → ∀ c, recordOf E₀ x = some c →
      ∃ ro ax, ro.inert = true ∧ t.addressOf? ro = some x ∧ c.info = .axio ax := by
    rintro x ⟨ro, hin, had⟩ c hc
    obtain ⟨a₁, raw, c₁, ax, had₁, hsz, hh, hbl, hde, hdeE, hinfo, -⟩ :=
      RoleVal.ValidateRoleIn.inert_record
        (show RoleVal.ValidateRoleIn calls bAddr t (Ix.SpecDigest.groupOf ro) ro from
          hvalAll _ ro (role_mem_roleGroup ro))
        (RoleVal.specKind_four_of_inert ro hin)
    have ea : a₁ = x := Option.some.inj (had₁.symm.trans had)
    have hc₁ : recordOf E₀ x = some c₁ := by
      rw [← ea, ← hbl]
      exact Claim.recordOf_hashed hC.runStore hC.hashedStored hh hsz hde hdeE
    have ec : c₁ = c := Option.some.inj (hc₁.symm.trans hc)
    exact ⟨ro, ax, hin, had, ec ▸ hinfo⟩
  intro g
  induction g with
  | zero => intro hg; omega
  | succ n ih =>
    intro hg6 hg77 x hin
    by_cases h6 : n + 1 = 6
    · rw [h6, groupStore_six]
      cases hrec : recordOf basisStore x with
      | none => rfl
      | some c =>
        exfalso
        have hmem := StoreInhabit.store_record_inv hrec
        have hE : recordOf E₀ x = some c := by
          have h6' : recordOf (groupStore t E₀ (runPayload calls bAddr t) 6) x = some c := by
            rw [groupStore_six]; exact hrec
          exact ((groupStore_recordOf hb (Nat.le_refl 6)).mp h6').2
        obtain ⟨ro, ax, hroIn, had, hinfo⟩ := hinertAx x hin c hE
        have hall := List.all_eq_true.mp basisRows_axiom_bound (x, c) hmem
        simp only [hinfo, List.any_eq_true, beq_iff_eq] at hall
        obtain ⟨r', hr', hb'⟩ := hall
        have had' : t.addressOf? r' = some x := by rw [addressOf_basis hpin hr']; exact hb'
        have er : ro = r' := addressOf_role_inj hwf had had'
        rw [er, basisRoles_not_inert r' hr'] at hroIn
        cases hroIn
    · have hn6 : 6 ≤ n := by omega
      have hn77 : n < 77 := by omega
      have hprev := ih hn6 (by omega) x hin
      cases hrec : recordOf (groupStore t E₀ (runPayload calls bAddr t) (n + 1)) x with
      | none => rfl
      | some c =>
        exfalso
        have hnew : New (groupStore t E₀ (runPayload calls bAddr t) n)
            (groupStore t E₀ (runPayload calls bAddr t) (n + 1)) x := ⟨by rw [hrec]; rfl, hprev⟩
        have hE : recordOf E₀ x = some c :=
          ((groupStore_recordOf hb (Nat.le_succ_of_le hn6)).mp hrec).2
        obtain ⟨ro, ax, hroIn, had, hinfo⟩ := hinertAx x hin c hE
        obtain ⟨r, -, hs, had'⟩ :=
          standing_of_rootsSafe hC hb hpin hP hval77 hroots n hn6 hn77 x c hnew hrec
            (Or.inl ⟨ax, hinfo⟩)
        have er : ro = r := addressOf_role_inj hwf had had'
        rw [er, stdAxiom_not_inert r hs] at hroIn
        cases hroIn

/-- **Discharges `RunFactsLeft`** at every group `6 ≤ g < 77`. -/
theorem runFactsLeft_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g < 77 → ∀ rk : Nat → _root_.Address → Nat,
      RunFactsLeft (observedRun calls bAddr t E₀ rk) t g
        (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g)
        (runAdv calls bAddr t g) (PayReach t E₀ (runPayload calls bAddr t) g) := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hval77 : ∀ k, k < 77 → ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r :=
    fun k _ => hvalAll k
  have hinert := inert_not_in_groupStore hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  intro g hg6 hg77 rk
  obtain ⟨recs, hw⟩ := hws g
  have hcl' := groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6)
  have husedStored : ∀ A x,
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) A).isSome = true →
      UsedRef E₀ A x →
      ∃ cx, recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) x = some cx := by
    intro A x hA hu
    obtain ⟨cA, hcA⟩ := Option.isSome_iff_exists.mp hA
    obtain ⟨c', i, hc', hi, hx⟩ := hu
    have ec : c' = cA := Option.some.inj
      (hc'.symm.trans ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcA).2)
    subst ec
    exact Option.isSome_iff_exists.mp ((hcl'.1 A c' hcA).2 i hi x hx)
  have hnotInert_of_held : ∀ A x,
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) A).isSome = true →
      UsedRef E₀ A x → ¬ InertAt t x := by
    intro A x hA hu hinx
    obtain ⟨cx, hcx⟩ := husedStored A x hA hu
    rw [hinert (g + 1) (by omega) (by omega) x hinx] at hcx
    cases hcx
  refine
    { notInert := fun A _ x hA _ hu => hnotInert_of_held A x hA.1.1 hu
      needOk := fun A c x hA hpay hu => ?_
      famNotInert := fun B _ x _ hnew _ hu => hnotInert_of_held B x hnew.1 hu
      famNeedOk := fun B rb x hfam hnew hpay hu => ?_ }
  · obtain ⟨hnew, hcR', hunit, -, -, -, hntw⟩ := hA
    have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
    have hE : recordOf E₀ A = some c :=
      ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcR').2
    have hxE : ∃ cx, recordOf E₀ x = some cx := by
      obtain ⟨cx, hcx⟩ := husedStored A x hnew.1 hu
      exact ⟨cx, ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcx).2⟩
    cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws hg6 hg77 hpay with
    | stored hst => rw [hnew.2] at hst; cases hst
    | walked hgr => exact walkedRef_needOk hC hb hpin hax hval77 hroots hg77 hw hgr hu
    | famRec _ _ hex =>
      exfalso
      obtain ⟨c', rs, hc', -, hrs, hpos, hall, -⟩ :=
        familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
      have ec : c' = c := Option.some.inj (hc'.symm.trans hE)
      subst ec
      exact hntw ⟨rs, hrs, hpos, hall⟩
    | directAdv _ _ hex hadv =>
      obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      obtain ⟨ab, habMem, habEq⟩ := hadv
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, -, -, -, -, hrefs⟩ := hfacts
      obtain ⟨hnb, -, hsafe, -⟩ := hrefs x hu
      exact needOk_of_notBlock_sourceSafe hC hvalAll hroots hnb hsafe hxE
    | directCont _ _ hex hdc =>
      obtain ⟨outs, -, -, -, ⟨ib, -, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, -, hxx₁, hxib₁,
          evCr, hsubCr, -⟩, hcontRefs, -, -⟩ := hdc.unpack hC hbd
      rcases check_container_rec_shape hC hbd hxx₁ hxib₁ evCr hsubCr hE with
        ⟨rc, hrc⟩ | ⟨rp, hrp⟩
      · obtain ⟨ib', -, hrefs⟩ := hcontRefs c hE (Or.inl ⟨rc, hrc⟩)
        have hownSelf : Ix.Cert.ownerOf A c = A := by simp [Ix.Cert.ownerOf, hrc]
        have huOwn : UsedRef E₀ (Ix.Cert.ownerOf A c) x := by rw [hownSelf]; exact hu
        obtain ⟨-, hnb, -, hsafe, -⟩ := hrefs x huOwn
        exact needOk_of_notBlock_sourceSafe hC hvalAll hroots hnb hsafe hxE
      · exact (unitKind_not_proj hunit (Or.inr (Or.inr (Or.inr ⟨rp, hrp⟩)))).elim
    | checkedProj hc' hpr _ _ _ _ =>
      have ec : _ = c := Option.some.inj (hc'.symm.trans hE)
      rw [ec] at hpr
      exact (unitKind_not_proj hunit hpr).elim
  · obtain ⟨-, hmod, cs, hfc⟩ := runFamOf_spec hfam
    have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
    obtain ⟨cb, ms, hcb, hms, hpos, hallIndc⟩ :=
      familyCall_block_indc_nonempty hC.runStore hC.hashedStored hfc
    cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws hg6 hg77 hpay with
    | stored hst => rw [hnew.2] at hst; cases hst
    | walked hgr => exact walkedRef_needOk hC hb hpin hax hval77 hroots hg77 hw hgr hu
    | famRec _ _ hex =>
      exfalso
      obtain ⟨c', rs, hc', -, hrs, -, hallRec, -⟩ :=
        familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
      have ec : c' = cb := Option.some.inj (hc'.symm.trans hcb)
      subst ec
      have ers : rs = ms := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hms)
      subst rs
      have hm0 : ms[0] ∈ ms.toList := Array.getElem_mem_toList hpos
      have hbi : Core.Specs.Callees.isIndc ms[0] = true :=
        (List.length_filter_eq_length_iff.mp (by simpa [Array.length_toList] using hallIndc)) _ hm0
      obtain ⟨r, hr⟩ := hallRec _ hm0
      rw [hr] at hbi
      simp [Core.Specs.Callees.isIndc, Core.isIndc] at hbi
    | directAdv _ _ hex hadv =>
      exfalso
      obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      obtain ⟨ab, habMem, habEq⟩ := hadv
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
      have ec : ca = cb := Option.some.inj (hca.symm.trans hcb)
      subst ec
      rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨_, _, -, -, hnat⟩ | ⟨hpr, -⟩
      · rw [hms] at hd; cases hd
      · rw [hms] at hrc; cases hrc
      · exact not_modeledRouteAt_of_nativeObs hnat hmod
      · exact proj_not_block hpr ⟨ms, hms⟩
    | directCont _ _ hex hdc =>
      exact (containerRecIn_notBlock hC.runStore (FamilyCallExact.toCall hex)
        (directContOwn_toContainerRecIn hdc) hcb ms hms).elim
    | checkedProj hc' hpr _ _ _ _ =>
      have ec : _ = cb := Option.some.inj (hc'.symm.trans hcb)
      rw [ec] at hpr
      exact (proj_not_block hpr ⟨ms, hms⟩).elim

end Classification

end IxVM.Refinement.Binding
