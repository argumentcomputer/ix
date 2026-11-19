import IxVMRefinement.Binding.FamilyOfCall
import IxVMRefinement.Binding.FamilyReconAnswers
import IxVMRefinement.Binding.GroupStores
import IxVMRefinement.Binding.BlockElimSpec
import IxVMRefinement.FamilyAlias.CallLists

/-! # The side premises of a run's family call

What the family clauses of a binding run (`RemainingFamilyClauses`) take of the block of a selected
family call and of the run's store, from the run itself.

* `member_ctor_addrs_hashed`, `block_ctor_addrs_hashed`, `familyCall_block_ctors`:
  `KernelModeled::block_ctor_addrs` hashes the projection record of every constructor of every
  inductive member of the block, so the block's constructor projection records are stored
  (`FamBlockRecord.ctors`).
* `selected_block_logic`, `famBlockRecord_of_selected`: the block of a selected family record is
  new in its group's admission, hence in Lean's logic (`logic_of_rootsSafe`); with the family
  check's own facts, `FamBlockRecord` of it.
* `storeNoCollision_of_binding`: a binding run that hashes no collision with a view hashes none
  with its store; `RemainingStoreClausesOfRunNC`, `groupStoresOfRun_of_remainingNC`: the remaining
  family clauses asked only under the run's step stores and that store-level no-collision, which
  give `GroupStoresOfRun` all the same.
* `check_const_defn_scope`, `check_const_induct_scope`, `LoadChecked`,
  `levelsDefinedAt_of_loadChecked`: `KernelCheck::check_const` scopes a definition's value and an
  inductive's type at the constant's level count, so the readings at a constant the run loaded and
  checked mention only its level parameters (`FamilyRecon.LevelsDefinedAt`).
* `UnitLevelsAt`, `unitLevelsAt_of_unitChecked`, `unitLevelsAt_of_added`,
  `unitLevelsAt_of_storedBelow`, `levelsDefinedAt_of_held`: the same of every unit a group's
  admission adds, and, given it of the basis rows, at every address a group's store holds.
* `loadedLevelsDefined_of_held`, `loadedLevelsDefined_of_run`: hence
  `FamilyRecon.LoadedLevelsDefined` of calls whose every loaded address with a record in the run's
  store is held by a group's store.
* `selected_members_levelsDefined`, `guardIndAnswersAt_of_selected`: at the members of a selected
  block, with no premise on the basis rows.
* `FamilyRecon.GuardIndAnswersAt`, `FamilyRecon.block_elim_resultSort_at`,
  `FamilyAlias.block_elim_blockElim_at`: `KernelModeled::block_elim` computes `BlockElim`'s offset
  from the inductive read at the block's first type alone, with the bounds a load gives (parameter
  and index counts below `2^56`). -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding.FamilyCallPremises

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Typing
open IxVM.Refinement (View)
open IxVM.Refinement.StoreInhabit (basisStore)

/-! ## The constructors' projection records -/

/-- **`KernelModeled::member_ctor_addrs` hashes the projection record of every constructor it
lists**: from position `j` on, the `cnt` constructors of the member at `p` of the block at `b`. -/
theorem member_ctor_addrs_hashed {b : Bytes.Address} {xb : SourceValue F} {p n : F} :
    ∀ (cnt j : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      j + cnt = ZMod.val n → Bytes.RepAddressRef addrTy h b xb →
      ObsFn Obs.W "KernelModeled::member_ctor_addrs" [xb, .field p, .field n, .field (j : F)] h r
        h' cs →
      ∀ k, j ≤ k → k < j + cnt →
        Hashed cs (Ixon.serConstant (constructorProjection (ixAddr b) (ZMod.val p) k))
  | 0, j, r, h, h', cs, hjn, hb, ev => fun k h1 h2 => by omega
  | cnt + 1, j, r, h, h', cs, hjn, hb, ev => by
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    have hlt := ZMod.val_lt n
    have hjv : ZMod.val (j : F) = j := SubstAux.val_natCast (by omega)
    rcases Obs.«KernelModeled::member_ctor_addrs».obs ev with
      ⟨op, hr, hh, -⟩ | ⟨v1, v45, v46, m48, cs56, m84, cs92, v98, op, hne, hr, hh, ev58, op133,
        ev94, hc⟩
    · exfalso
      have e := SubstAux.sub_ok op
      have hnj : n = (j : F) := sub_eq_zero.mp (Value.field.inj e).symm
      rw [hnj, hjv] at hjn
      omega
    · subst hr hh hc
      have hh0 := Core.projection_addr_ctor_hashed
        (ScopedCtx.unrestricted ⟨{}, .empty, default, none⟩) ev58 hb
      rw [hjv] at hh0
      have e98 : v98 = .field ((j + 1 : Nat) : F) := by
        rw [SubstAux.add_ok op133, Nat.cast_succ]
      subst e98
      have x1 := ev58.heap_extends
      have ih := member_ctor_addrs_hashed cnt (j + 1) (by omega)
        (Bytes.repAddressRef_heapMono₂ addrTy x1 hb) ev94
      intro k hk1 hk2
      rcases Nat.eq_or_lt_of_le hk1 with rfl | hlt'
      · exact Core.hashed_mono (fun x hx => by simp [hx]) hh0
      · exact Core.hashed_mono (fun x hx => by simp [hx]) (ih k hlt' (by omega))

private theorem repMutConst_heapMono : HeapMono₂ L1.RepMutConst :=
  fun _ _ _ _ ext r => L1.RepMutConst.mono ext r

/-- **`KernelModeled::block_ctor_addrs` hashes the projection record of every constructor of
every member it walks**: of the member at position `i` of the listed members, the block's member
`p + i`. -/
theorem block_ctor_addrs_hashed {b : Bytes.Address} {xb : SourceValue F} :
    ∀ (ms : List Ixon.MutConst) (p : Nat) {x_members r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      p + ms.length < 1099511627776 →
      (∀ ind, Ixon.MutConst.indc ind ∈ ms → ind.ctors.size < 1099511627776) →
      Bytes.RepAddressRef addrTy h b xb →
      RepList L1.mutConstListEnum L1.RepMutConst h ms x_members →
      ObsFn Obs.W "KernelModeled::block_ctor_addrs" [x_members, xb, .field (p : F)] h r h' cs →
      ∀ (i : Nat) (ind : Ixon.Inductive) (k : Nat), ms[i]? = some (.indc ind) →
        k < ind.ctors.size →
        Hashed cs (Ixon.serConstant (constructorProjection (ixAddr b) (p + i) k))
  | [], p, x_members, r, h, h', cs, hp, hsz, hb, hms, ev => by
    intro i ind k hi
    simp at hi
  | m :: rest, p, x_members, r, h, h', cs, hp, hsz, hb, hms, ev => by
    have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
    match Obs.«KernelModeled::block_ctor_addrs».obs ev with
    | .Nil (ld12 := ld) .. =>
      exact absurd (Lib.rep_nil_of_load hms ld) (List.cons_ne_nil _ _)
    | .Cons (x_ctors := x_ctors) (v124 := v124) (m127 := m127) (cs135 := cs135) (v140 := v140)
        (m157 := m157) (cs165 := cs165) (v196 := v196) (ld12 := ld)
        (ev167 := e1) (ev137 := e2) (op224 := op) (ev193 := e3) (ev123 := e4) (hc226 := hc) .. =>
      subst hc
      obtain ⟨m', rest', heq, hm, hrest⟩ := Lib.rep_cons_of_load hms ld
      injection heq with h1 h2
      subst h1 h2
      cases m with
      | defn d =>
        obtain ⟨dv, hv, -⟩ := hm
        simp at hv
      | recr r' =>
        obtain ⟨rv, hv, -⟩ := hm
        simp at hv
      | indc ind₀ =>
        obtain ⟨iv, hv, hind⟩ := hm
        injection hv with _ _ hargs
        injection hargs with hiv _
        subst hiv
        obtain ⟨typPtr, ctorsPtr, hv2, -, hctors⟩ := hind
        injection hv2 with _ _ hargs2
        have hx : x_ctors = ctorsPtr := by
          have e := congrArg (fun l : List (SourceValue F) => l.getD 5 (.field 0)) hargs2
          simpa using e
        subst hx
        have e1' : ObsFn Obs.W (Instance.mk "Lists::length" [.named "Ixon::Constructor" []]).symbol
            [x_ctors] h v140 m157 cs165 := by
          rw [Obs.Names.«Lists::length<Ixon::Constructor>».symbol]
          exact e1
        have hl' : RepList (Instance.mk "Lists::Node" [.named "Ixon::Constructor" []]).symbol
            L1.RepConstructor h ind₀.ctors.toList x_ctors := by
          rw [Obs.Names.«Lists::Node<Ixon::Constructor>».symbol]
          exact hctors
        obtain ⟨hv140, hm157⟩ := Lib.Lists.length_spec e1' hl'
        subst hv140
        subst m157
        have hsz0 : ind₀.ctors.size < 1099511627776 := hsz ind₀ (List.mem_cons_self ..)
        have hlen : ind₀.ctors.toList.length = ind₀.ctors.size := Array.length_toList
        have hpv : ZMod.val (p : F) = p := SubstAux.val_natCast (by simp at hp; omega)
        have e2' : ObsFn Obs.W "KernelModeled::member_ctor_addrs"
            [xb, .field (p : F), .field (ind₀.ctors.toList.length : F), .field ((0 : Nat) : F)]
            h v124 m127 cs135 := by
          rw [Nat.cast_zero]
          exact e2
        have x2 := e2.heap_extends
        have hmem := member_ctor_addrs_hashed ind₀.ctors.toList.length 0
          (by rw [SubstAux.val_natCast (n := ind₀.ctors.toList.length) (by omega)]; omega)
          hb e2'
        have e196 : v196 = .field ((p + 1 : Nat) : F) := by
          rw [SubstAux.add_ok op, Nat.cast_succ]
        subst e196
        have ih := block_ctor_addrs_hashed rest (p + 1)
          (by simp at hp; omega)
          (fun ind' hi => hsz ind' (List.mem_cons_of_mem _ hi))
          (Bytes.repAddressRef_heapMono₂ addrTy x2 hb)
          (RepLinkedList.mono repMutConst_heapMono x2 hrest) e3
        intro i ind k hi hk
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          obtain rfl : ind₀ = ind := Ixon.MutConst.indc.inj hi
          have h0 := hmem k (Nat.zero_le _) (by omega)
          rw [hpv] at h0
          exact Core.hashed_mono (fun x hx => by simp [hx]) h0
        | succ i =>
          have hi' : rest[i]? = some (.indc ind) := by simpa using hi
          have h0 := ih i ind k hi' hk
          rw [show p + 1 + i = p + (i + 1) by omega] at h0
          exact Core.hashed_mono (fun x hx => by simp [hx]) h0

/-- **The constructor projection records of the block of an observed family check are stored**
(`FamBlockRecord.ctors`): `KernelModeled::block_ctor_addrs` hashes each. -/
theorem familyCall_block_ctors {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hcb : recordOf E₀ B = some cb) (hms : cb.info = .muts ms) :
    ∀ i ind j, ms[i]? = some (Ixon.MutConst.indc ind) → j < ind.ctors.size →
      recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j) := by
  obtain ⟨h, h', rc, xb, xrb, r, -, ⟨bB, hbB, rfl⟩, -, ev, -, hsub⟩ := hfc
  obtain ⟨C⟩ := FamilyAlias.checkFamily_chain ev
  have ext_0_453 : Heap.Extends h C.m453 :=
    (check_family_seg1_extends C.sg112).trans C.ext_m105_m453
  have hsubLoad : ∀ cl ∈ C.evLoadBlk.cs, cl ∈ calls :=
    fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl)
  obtain ⟨cb', ms', hbl, hms_rep⟩ :=
    Claim.load_block_head (Bytes.repAddressRef_heapMono₂ addrTy ext_0_453 hbB) C.evLoadBlk.obs
  obtain ⟨hBrec, hBmuts⟩ := (hbl.mono hsubLoad).stored hH
  have e1 : cb' = cb := Option.some.inj (hBrec.symm.trans hcb)
  subst e1
  have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hBmuts.symm.trans hms)
  subst e2
  have hres : cb'.resourceSize < 8589934592 := ((hbl.mono hsubLoad).record hS hBrec).2
  have hsz : ms'.size ≤ cb'.resourceSize := Claim.muts_size_le hms
  have ext_501_704 : Heap.Extends C.m501 C.m704 :=
    C.evLenMem.extends.trans (C.evIndcCnt.extends.trans (C.evNParams.extends.trans
      (C.evTypes.extends.trans C.evTypeMods.extends)))
  have hb704 : Bytes.RepAddressRef addrTy C.m704 bB xb :=
    Bytes.repAddressRef_heapMono₂ addrTy
      (ext_0_453.trans (C.evLoadBlk.extends.trans ext_501_704)) hbB
  have evC : ObsFn Obs.W "KernelModeled::block_ctor_addrs"
      [C.members, xb, .field ((0 : Nat) : F)] C.m704 C.ctors C.m747 C.evCtors.cs := by
    rw [Nat.cast_zero]
    exact C.evCtors.obs
  have hhash := block_ctor_addrs_hashed ms'.toList 0
    (by rw [Array.length_toList]; omega)
    (fun ind hi => by
      obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.mp hi
      have := Claim.ctors_size_le hms hi'
      omega)
    hb704 (RepLinkedList.mono repMutConst_heapMono ext_501_704 hms_rep) evC
  intro i ind j hi hj
  have hiL : ms'.toList[i]? = some (.indc ind) := by rw [Array.getElem?_toList]; exact hi
  have hh := Core.hashed_mono (fun cl hcl => hsub cl (C.evCtors.sub cl hcl))
    (hhash i ind j hiL hj)
  rw [Nat.zero_add] at hh
  exact Claim.recordOf_of_hashed hH hh
    (Claim.serConstant_cprj_size_lt i.toUInt64 j.toUInt64 bB)
    (Ixon.Verify.deConstantExact_serConstant _
      (L1.projConstant_wireWF_cPrj i.toUInt64 j.toUInt64 bB))

/-! ## The block of a selected family call, in a run -/

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **The payload's facts of a run that validates every role of the 77 groups**
(`payloadFacts_of_run`, with the roots' safety, the axioms' records, the basis roles and the
walked records produced from the validations). -/
theorem payloadFacts_of_validated (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    PayloadFacts t E₀ (runPayload calls bAddr t) := by
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
      cases hr
  exact payloadFacts_of_run hC hbd hb (basisRolesStored_of_pinned hpin) (axiomRoles_of_run hC hval)
    hpin hcheck (RootsSafe.of_run hC hval (rootsAndTheoremsSafe_of_run hC hval)) hstep hvalAll
    (fun k => groupWalked_exists hC.hashedStored (hvalAll k))

/-- **The block of a selected family record is in Lean's logic** (`FamBlockRecord.logic`): it is
new in its group's admission (`runFamOf_spec`), and a record new in a group's admission is in
Lean's logic (`logic_of_rootsSafe`). -/
theorem selected_block_logic (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {B rb : _root_.Address}
    (hf : runFamOf calls bAddr t E₀ g B = some rb) {cb : Ixon.Constant}
    (hcb : recordOf E₀ B = some cb) : InLogic cb := by
  have hP := payloadFacts_of_validated hC hbd hb hpin hcheck hstep hval
  obtain ⟨hnew, -, -⟩ := runFamOf_spec hf
  obtain ⟨c, hE, hc, -, -⟩ := new_groupStore hb hg6 hnew
  have e : c = cb := Option.some.inj (hE.symm.trans hcb)
  subst e
  exact logic_of_rootsSafe hC hb hP hval
    (RootsSafe.of_run hC hval (rootsAndTheoremsSafe_of_run hC hval)) g hg6 hg B c hnew hc

/-- **The block's record facts of a selected family record** (`FamBlockRecord`), for a bounded
run with a collision-free store that validates every role of the 77 groups: the record, its
members and their projection records from the family check (`familyCall_block_members`), its
constructors' projection records from the family check's own address list
(`familyCall_block_ctors`), and that it is in Lean's logic from the group's admission
(`selected_block_logic`). -/
theorem famBlockRecord_of_selected (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {B rb : _root_.Address}
    (hf : runFamOf calls bAddr t E₀ g B = some rb) :
    ∃ cb ms, FamBlockRecord E₀ B cb ms := by
  obtain ⟨-, -, cs, hfc⟩ := runFamOf_spec hf
  obtain ⟨cb, ms, hcb, hms, -, -, -⟩ :=
    FamilyOfCall.familyCall_block_members hC.runStore hC.hashedStored hfc
  exact ⟨cb, ms, FamilyOfCall.famBlockRecord_of_call hC.runStore hC.hashedStored hfc hcb hms
    (selected_block_logic hC hbd hb hpin hcheck hstep hval hg6 hg hf hcb)
    (familyCall_block_ctors hC.runStore hC.hashedStored hfc hcb hms)⟩

end Run

/-! ## The store-level no-collision of a binding run -/

/-- **A binding run that hashes no collision with a view hashes none with its store**: the
store's records and blobs are byte strings the run hashed under their addresses, and its role
binding's bytes are the table bytes the run hashed, at the address the admission checks them
against (`Address.admissionHash` is the pure BLAKE3). -/
theorem storeNoCollision_of_binding {calls : List (Call F)} {V : View} {extra : List ByteArray}
    {a : _root_.Address} {tb : ByteArray} {t : Ix.Kernel.RoleTable}
    (htb : Hashed calls tb)
    (hadm : Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t)
    (hno : ¬ V.HashedCollision extra calls) :
    ¬ View.HashedCollision { env := Claim.runEnv ⟨a, tb⟩ (t := t) calls } [] calls := by
  refine FamilyRecon.storeNoCollision_of_view
    (Claim.envOfRecs_loadedBy (t := t) ⟨a, tb⟩ calls []) ?_ hno
  intro rb hrb
  have e : rb = { address := a, bytes := tb } := (Option.some.inj hrb).symm
  subst e
  have hauth := ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).authentic
  exact ⟨htb, hauth⟩

/-! ## The remaining family clauses, with the run's step stores and store-level no-collision -/

/-- **What is left of the store sequence's clauses, for a run** (`RemainingStoreClausesOfRun`),
asked only where the run has its step stores (`RunStepStores`) and hashes no collision with its
store: both hold in the alternative without a collision that `GroupStoresOfRun` is proved in
(`runStepStores_of_noCollision`, `storeNoCollision_of_binding`). `CollisionFreeRun` has no clause
for a collision of a hashed byte string with an unhashed projection image of a hashed block, which
the store-level no-collision excludes. -/
def RemainingStoreClausesOfRunNC (calls : List (Call F)) : Prop :=
  IxVM.Consistency.Bounded calls →
  ∀ (a : _root_.Address) (tb : ByteArray) (t : Ix.Kernel.RoleTable),
    Hashed calls tb →
    Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t →
    AllBound t → PreludePinned t →
    (∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r) →
    CollisionFreeRun calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) →
    RunStepStores calls t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) →
    ¬ View.HashedCollision { env := Claim.runEnv ⟨a, tb⟩ (t := t) calls } [] calls →
    RemainingFamilyClauses calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls)

/-- The clauses asked everywhere give the clauses asked under the two further facts. -/
theorem RemainingStoreClausesOfRunNC.of_remaining {calls : List (Call F)}
    (h : RemainingStoreClausesOfRun calls) : RemainingStoreClausesOfRunNC calls :=
  fun hbd a tb t htb hadm hall hpin hval hC _ _ => h hbd a tb t htb hadm hall hpin hval hC

/-- **The stores of a binding run, from what is left of its family clauses under the run's step
stores and store-level no-collision** (`groupStoresOfRun_of_remaining`, at
`RemainingStoreClausesOfRunNC`). -/
theorem groupStoresOfRun_of_remainingNC {calls : List (Call F)}
    (hrem : RemainingStoreClausesOfRunNC calls) :
    GroupStoresOfRun calls := by
  intro hbd V extra hextra a tb t htb hadm hall hpin hval
  by_cases hcol : V.HashedCollision extra calls
  · exact Or.inl hcol
  right
  have hnoColl : ∀ b₁ b₂ : ByteArray, Hashed calls b₁ → Hashed calls b₂ →
      Address.blake3Pure b₁ = Address.blake3Pure b₂ → b₁ = b₂ := by
    rcases Claim.noColl_or_hashedCollision V extra calls with h | h
    · exact absurd h hcol
    · exact h
  have hw0 : Claim.WalkedL6 calls t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) [] :=
    Claim.walkedL6_envOfRecs (seeds := []) hnoColl [] hadm (by simp)
      (by intro r hr; cases hr)
  have hload : LoadedBy calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    Claim.envOfRecs_loadedBy (t := t) ⟨a, tb⟩ calls []
  have hS := LoadedReads.RunStore.of_walkedL6 hload hw0
  have hH := LoadedReads.hashedRecordsStored_of_walkedL6 hw0
  have hC : CollisionFreeRun calls (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    collisionFreeRun_of_no_collision hextra hcol hS hH
  have hb := basisRows_of_run hC hpin hval
  have hax := axiomRoles_of_run hC hval
  have hbr : BasisRolesStored t := basisRolesStored_of_pinned hpin
  have hcheck : t.check = .ok () :=
    ((Ix.Kernel.Admission.admitBinding_ok_iff _ _ t).mp hadm).wellFormed
  have hroots : RootsSafe t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) :=
    RootsSafe.of_run hC hval (rootsAndTheoremsSafe_of_run hC hval)
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls a t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
      cases hr
  have hws : ∀ k, ∃ recs, GroupWalked calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) k recs :=
    fun k => groupWalked_exists hH (hvalAll k)
  have hstep := runStepStores_of_noCollision t hS hbd hextra hcol
  have hRF := hrem hbd a tb t htb hadm hall hpin hval hC hstep
    (storeNoCollision_of_binding htb hadm hcol)
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hblock := blockSteps_of_run hC hvalAll hws
  have hpayOps := payloadOps_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hclaimedAll := claimed_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hrunFactsAll := runFactsLeft_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hpayChkAll := payloadChecked_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hrankedAll := payloadRanked_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hrk : ∀ g, ∃ r : _root_.Address → Nat, 6 ≤ g → g < 77 →
      GroupRanked t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) (runPayload calls a t) g
        (runFamOf calls a t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) g) (runAdv calls a t g)
        (runCont calls a t g) r := by
    intro g
    by_cases hr : 6 ≤ g ∧ g < 77
    · obtain ⟨r, hr'⟩ := hrankedAll g hr.1 hr.2
      exact ⟨r, fun _ _ => hr'⟩
    · exact ⟨fun _ => 0, fun h6 h77 => absurd ⟨h6, h77⟩ hr⟩
  refine ⟨fun g => Classical.choose (hrk g),
    groupStore t (Claim.runEnv ⟨a, tb⟩ (t := t) calls) (runPayload calls a t),
    groupStore_basis_consts, groupStore_basis_blobs, fun g hg6 hg => ⟨?_, ?_, ?_⟩⟩
  · have hw := Classical.choose_spec (hws g)
    have hrank := Classical.choose_spec (hrk g) hg6 hg
    exact
      { mono := groupStore_mono hb hg6
        monoBlobs := groupStore_monoBlobs hg6
        loaded := groupStore_loaded hb (Nat.le_succ_of_le hg6)
        loadedBlobs := groupStore_loadedBlobs (Nat.lt_succ_of_le hg6)
        hashed := groupStore_hashed hS hb (Nat.lt_succ_of_le hg6)
        usedClosed :=
          groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6)
        committed := groupStore_committed hC hb (Nat.le_succ_of_le hg6)
        zeroFree := groupStore_zeroFree hC hb (Nat.lt_succ_of_le hg6)
        rankUsed := hrank.used
        rankOwner := hrank.owner
        projMember := groupStore_projMember hC hb hax hP hg6 hw
        standing := standing_of_rootsSafe hC hb hpin hP hval hroots
          g hg6 hg
        logic := logic_of_rootsSafe hC hb hP hval hroots g hg6 hg
        validated := fun _ _ => trivial
        kept := groupStore_kept hC hb hax hg6 hw
        opsOwn := groupStore_opsOwn hC hb hax hP hcheck hvalAll hg6 hw
          (walkStepsOrdered_all hC hvalAll hblock g)
          (payloadOpEarlier_all hpayOps g hg6)
        unitsLast := groupStore_unitsLast hC hb hax hP hpin hws hg6 (hvalAll g) hw
          (walkStepsOrdered_all hC hvalAll hblock g)
          (payloadOpEarlier_all hpayOps g hg6)
        evidenceRefs := groupStore_evidenceRefs hC hb hbr hax hP hws hg6 hw }
  · exact
      { blobs := groupStore_reads_blobs (Nat.lt_succ_of_le hg6)
        reads := groupStore_reads hcheck hC hb hbr hax hP hws hg6 }
  · exact ⟨_, _, _, families_of_remaining (rk := fun g => Classical.choose (hrk g)) hC hb hax hP hRF
      hcheck hroots hpin hg6 hg hvalAll (Classical.choose_spec (hws g))
      (Classical.choose_spec (hrk g) hg6 hg) (payloadOpEarlier_all hpayOps g hg6)
      (groupStore_usedClosed_all hC hb hbr hax hP hws g hg6)
      (groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6))
      hstep
      (groupStore_unitsLast hC hb hax hP hpin hws hg6 (hvalAll g) (Classical.choose_spec (hws g))
        (walkStepsOrdered_all hC hvalAll hblock g)
        (payloadOpEarlier_all hpayOps g hg6))
      (logic_of_rootsSafe hC hb hP hval hroots g hg6 hg)
      (hclaimedAll g hg6 hg)
      (hrunFactsAll g hg6 hg (fun g => Classical.choose (hrk g)))
      (hpayChkAll g hg6 hg)⟩

/-! ## Level parameters of the readings of a checked constant -/

/-- **`KernelCheck::check_const` on a definition scopes its value**: an observed
`KernelCheck::validate_expr_well_scoped` of the value at the definition's level count, at a heap
extending the check's and among the check's calls. -/
theorem check_const_defn_scope {rc xnl xty xval w1 w2 ap r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Defn" [xnl, xty, xval, w1, w2], ap] h r h'
      cs) :
    ∃ (m m' : Heap F) (v : SourceValue F) (cs' : List (Call F)), Heap.Extends h m ∧
      ObsFn Obs.W "KernelCheck::validate_expr_well_scoped" [xval, .field 0, xnl] m v m' cs' ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [xval, .field 0, xnl], m⟩ : Call F) ∈ cs := by
  cases Obs.«KernelCheck::check_const».obs ev with
  | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
  | Thm | Opaque | Quot
  | Induct_n0 | Induct_other_n0 | Induct_other_other
  | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
  | Rec_n0 | Rec_other =>
    simp_all
  | Defn v1 m2 cs12 x_nlvls x_ty x_val _ _ _ m299 cs309 _ m336 cs346 v372 m373 cs383 m404
      _ m417 cs427 _ m447 cs457 cs479 m508
      ev14 _ hv269 ev311 ev348 hm412 ev385 ev429 ev459 hm516 ev481 hc520 =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv269
    obtain ⟨rfl, rfl, rfl, -, -⟩ := hv269
    exact ⟨m299, m336, _, cs346, ev14.heap_extends.trans ev311.heap_extends, ev348,
      by rw [hc520]; simp⟩

/-- **`KernelCheck::check_const` on an inductive type scopes its type**: an observed
`KernelCheck::validate_expr_well_scoped` of the type at the inductive's level count, at a heap
extending the check's and among the check's calls. -/
theorem check_const_induct_scope {rc xnl xty xnp xni xnc xu xblk xidx ap r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelCheck::check_const"
      [rc, .construct "KernelTypes::KConstantInfo" "Induct"
        [xnl, xty, xnp, xni, xnc, xu, xblk, xidx], ap] h r h' cs) :
    ∃ (m m' : Heap F) (v : SourceValue F) (cs' : List (Call F)), Heap.Extends h m ∧
      ObsFn Obs.W "KernelCheck::validate_expr_well_scoped" [xty, .field 0, xnl] m v m' cs' ∧
      (⟨"KernelCheck::validate_expr_well_scoped", [xty, .field 0, xnl], m⟩ : Call F) ∈ cs := by
  cases Obs.«KernelCheck::check_const».obs ev with
  | Axiom_n1 | Axiom_other_n0 | Axiom_other_other
  | Defn | Thm | Opaque | Quot
  | Ctor_n0_n0 | Ctor_n0_other | Ctor_other_n0 | Ctor_other_other
  | Rec_n0 | Rec_other =>
    simp_all
  | Induct_n0 _ m2 _ x_nlvls x_ty _ _ _ _ _ _ v1282 m1283 cs1293 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ ev14 _ _ _ _ _ hv1240 ev1295 _ _ _ _ _ _ _ _ _ _ _ hc =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv1240
    obtain ⟨rfl, rfl, -⟩ := hv1240
    exact ⟨m2, m1283, _, cs1293, ev14.heap_extends, ev1295, by rw [hc]; simp⟩
  | Induct_other_n0 _ m2 _ x_nlvls x_ty _ _ _ _ _ v1282 m1283 cs1293 _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ hv1240 ev1295 _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv1240
    obtain ⟨rfl, rfl, -⟩ := hv1240
    exact ⟨m2, m1283, _, cs1293, ev14.heap_extends, ev1295, by rw [hc]; simp⟩
  | Induct_other_other _ m2 _ x_nlvls x_ty _ _ _ _ _ _ v1282 m1283 cs1293 _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev14 _ _ _ _ _ hv1240 ev1295 _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv1240
    obtain ⟨rfl, rfl, -⟩ := hv1240
    exact ⟨m2, m1283, _, cs1293, ev14.heap_extends, ev1295, by rw [hc]; simp⟩

/-- **A constant the run loaded and checked**: an observed `Ingress::get_ci` at the address `a`
and an observed `KernelCheck::check_const` of the value it loaded, at the heap the load left, both
with their calls among the run's. -/
def LoadChecked (calls : List (Call F)) (a : _root_.Address) : Prop :=
  ∃ (h m h' : Heap F) (xa p ci rc ap r : SourceValue F) (cs csc : List (Call F))
    (ab : Bytes.Address),
    ixAddr ab = a ∧ Bytes.RepAddressRef addrTy h ab xa ∧
    ObsFn Obs.W "Ingress::get_ci" [xa] h p m cs ∧ (∀ c ∈ cs, c ∈ calls) ∧
    loadValue m p = .ok ci ∧
    ObsFn Obs.W "KernelCheck::check_const" [rc, ci, ap] m r h' csc ∧ (∀ c ∈ csc, c ∈ calls)

/-- **The readings at a constant the run loaded and checked mention only their constant's level
parameters** (`FamilyRecon.LevelsDefinedAt`): `KernelCheck::check_const` scopes a definition's
value and an inductive's type at the constant's level count
(`KernelCheck::validate_expr_well_scoped`), on the pointers the load converted them to. -/
theorem levelsDefinedAt_of_loadChecked {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} (hS : LoadedReads.RunStore calls E₀) (hbd : Bounded calls)
    {a : _root_.Address} (hc : LoadChecked calls a) : FamilyRecon.LevelsDefinedAt t E₀ a := by
  obtain ⟨h, m, h', xa, p, ci, rc, ap, r, cs, csc, ab, rfl, ha, ev, hsub, hld, evc, hsubc⟩ := hc
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := L1.get_ci_trace_spec ha ev
  have hcc : ∀ c, recordOf E₀ (ixAddr ab) = some c → c' = c := fun c hc =>
    hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hc) (Core.hashed_mono hsub hh) haddr hex
  refine ⟨?_, ?_, ?_⟩
  · intro c d v hrec hinfo hk hread
    obtain rfl := hcc c hrec
    unfold L1.GetCITraceResult at hres
    rw [hinfo] at hres
    obtain ⟨blobs, tree, v', hhp, built, hld', rep⟩ := hres
    have hvci : v' = ci := Except.ok.inj (hld'.symm.trans hld)
    subst hvci
    obtain ⟨hnl, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, -, -, -, -⟩ := rep
    have hshape : v' = .construct "KernelTypes::KConstantInfo" "Defn"
        [.field (d.lvls.toNat : F), tyPtr, valPtr, L1.repDefSafetyVal d.safety, hint] := by
      rw [hv]
      simp [L1.defnValShape, hk, Core.kciEnum]
    rw [hshape] at evc
    obtain ⟨m1, m2, vv, cs', ext, evs, hmem⟩ := check_const_defn_scope evc
    exact (Assembly.validate_expr_well_scoped_spec hbd hnl rval ext hread evs
      (hsubc _ hmem)).2.2
  · intro c pr cb ms d v hrec hinfo hrecB hms hmem hk hread
    obtain rfl := hcc c hrec
    unfold L1.GetCITraceResult at hres
    rw [hinfo] at hres
    obtain ⟨hidx, blkBytes, cb', ms', d', blobs, tree, v', hhB, haddrB, hexB, hms', hm', hhp,
      built, hld', rep⟩ := hres
    have e1 : cb' = cb := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecB)
      (Core.hashed_mono hsub hhB) haddrB hexB
    subst e1
    have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
    subst e2
    have e3 : d' = d := by
      rw [Array.getElem?_toList, hmem] at hm'
      exact (Ixon.MutConst.defn.inj (Option.some.inj hm')).symm
    subst e3
    have hvci : v' = ci := Except.ok.inj (hld'.symm.trans hld)
    subst hvci
    obtain ⟨hnl, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, -, -, -, -⟩ := rep
    have hshape : v' = .construct "KernelTypes::KConstantInfo" "Defn"
        [.field (d'.lvls.toNat : F), tyPtr, valPtr, L1.repDefSafetyVal d'.safety, hint] := by
      rw [hv]
      simp [L1.defnValShape, hk, Core.kciEnum]
    rw [hshape] at evc
    obtain ⟨m1, m2, vv, cs', ext, evs, hmemc⟩ := check_const_defn_scope evc
    exact (Assembly.validate_expr_well_scoped_spec hbd hnl rval ext hread evs
      (hsubc _ hmemc)).2.2
  · intro c pr cb ms ind v hrec hinfo hrecB hms hmem hread
    obtain rfl := hcc c hrec
    obtain ⟨rawBytes₂, c₂, hh₂, haddr₂, hex₂, -, hres₂⟩ :=
      L1.get_ci_block_trace_spec (RomBound.bounded_mono hbd hsub) ha ev
    have hc₂ : c₂ = c' := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrec)
      (Core.hashed_mono hsub hh₂) haddr₂ hex₂
    subst hc₂
    unfold L1.GetCIBlockTraceResult at hres₂
    rw [hinfo] at hres₂
    obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v', hhB, haB, hexB, hcb, hm', hhp,
      built, planned, hld', hraw, hlev⟩ := hres₂
    have e1 : cb' = cb := hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hrecB)
      (Core.hashed_mono hsub hhB) haB hexB
    subst e1
    have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hms)
    subst e2
    have e3 : ind' = ind := by
      rw [Array.getElem?_toList, hmem] at hm'
      exact (Ixon.MutConst.indc.inj (Option.some.inj hm')).symm
    subst e3
    have hvci : v' = ci := Except.ok.inj (hld'.symm.trans hld)
    subst hvci
    obtain ⟨hl, hnp, hni, hnc, hii, tyPtr, blkPtr, b, hbaddr, hbrep, hv, rty⟩ := hraw
    have hshape : v' = .construct "KernelTypes::KConstantInfo" "Induct"
        [.field (ind'.lvls.toNat : F), tyPtr, .field (ind'.params.toNat : F),
          .field (ind'.indices.toNat : F), .field (ind'.ctors.size : F),
          L1.repBoolField ind'.isUnsafe, blkPtr, .field (pr.idx.toNat : F)] := hv
    rw [hshape] at evc
    obtain ⟨m1, m2, vv, cs', ext, evs, hmemc⟩ := check_const_induct_scope evc
    exact (Assembly.validate_expr_well_scoped_spec hbd hl rty ext hread evs
      (hsubc _ hmemc)).2.2

/-- A check at a context limit is a load and a check. -/
theorem LoadChecked.of_checkedLim {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {a : _root_.Address} {lim : Option Nat}
    (hc : Claim.CheckedLimAt calls bAddr t a lim) : LoadChecked calls a := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    -, -, ⟨ab, hab, hix⟩, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hc
  exact ⟨h_pre, m_chk, h'_chk, ap, ptr, v, rc, ap, r_chk, cs_load, cs_chk, ab, hix, hab, ev_ld,
    hsub_ld, hld, ev_chk, hsub_chk⟩

/-- The check of a block's member at a context limit is a load and a check at the member's
address. -/
theorem LoadChecked.of_memberCheckedLim {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B : _root_.Address} {ms : Array Ixon.MutConst} {k : Nat}
    {m : Ixon.MutConst} {lim : Option Nat} (hk : k < 288230376151711744)
    (hm : ms[k]? = some m)
    (hc : Claim.MemberCheckedLimAt calls bAddr t B ms k lim) :
    LoadChecked calls (memberAddr B k m) := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, ⟨b', hb', rfl⟩, ev_pa, -, hsub_pa,
    -, -, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hc
  obtain ⟨-, -, -, mc, a', hget', ha', hproj⟩ := L1.projection_addr_spec hmem hb' ev_pa
  rw [FamilyOfCall.val_cast_lt_u58 hk, Array.getElem?_toList, hm] at hget'
  obtain rfl : m = mc := Option.some.inj hget'
  rw [FamilyOfCall.val_cast_lt_u58 hk] at hproj
  exact ⟨h_pre, m_chk, h'_chk, ap, ptr, v, rc, ap, r_chk, cs_load, cs_chk, a',
    by rw [hproj, LoadedReads.memberAddr_eq_projAddr], ha', ev_ld, hsub_ld, hld, ev_chk,
    hsub_chk⟩


/-! ## Level parameters of the readings of every stored unit -/

/-- **The readings of the unit at `A` mention only their constants' level parameters**: the value
of a standalone definition at `A`, and of the block at `A` the value of every definition member
and the type of every inductive member. -/
structure UnitLevelsAt (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (A : _root_.Address) : Prop where
  solo : ∀ (c : Ixon.Constant) (d : Ixon.Definition) (v : Core.KExpr),
    recordOf E A = some c → c.info = .defn d → d.kind = .defn →
    (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t A)).read d.value = .ok v →
    v.allLevelParamsDefined (List.range d.lvls.toNat) = true
  defn : ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (k : Nat) (d : Ixon.Definition)
      (v : Core.KExpr),
    recordOf E A = some cb → cb.info = .muts ms → ms[k]? = some (.defn d) → d.kind = .defn →
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t A ms)).read d.value = .ok v →
    v.allLevelParamsDefined (List.range d.lvls.toNat) = true
  indc : ∀ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (k : Nat) (ind : Ixon.Inductive)
      (v : Core.KExpr),
    recordOf E A = some cb → cb.info = .muts ms → ms[k]? = some (.indc ind) →
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t A ms)).read ind.typ = .ok v →
    v.allLevelParamsDefined (List.range ind.lvls.toNat) = true

/-- **The readings at an address, from the readings of its unit**: the address's own for a
standalone definition, its block's for a projection record. -/
theorem levelsDefinedAt_of_unitLevels {t : Ix.Kernel.RoleTable} {E : Ixon.Env}
    {a : _root_.Address} (hsolo : UnitLevelsAt t E a)
    (hdprj : ∀ c p, recordOf E a = some c → c.info = .dPrj p → UnitLevelsAt t E p.block)
    (hiprj : ∀ c p, recordOf E a = some c → c.info = .iPrj p → UnitLevelsAt t E p.block) :
    FamilyRecon.LevelsDefinedAt t E a where
  solo := hsolo.solo
  member := fun c p cb ms d v hrec hinfo hrecB hms hmem hk hread =>
    (hdprj c p hrec hinfo).defn cb ms p.idx.toNat d v hrecB hms hmem hk hread
  ind := fun c p cb ms ind v hrec hinfo hrecB hms hmem hread =>
    (hiprj c p hrec hinfo).indc cb ms p.idx.toNat ind v hrecB hms hmem hread

/-- A record that is no definition and no block with a member other than a recursor has no
reading `UnitLevelsAt` speaks of. -/
theorem unitLevelsAt_of_no_reading {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {A : _root_.Address}
    (h : ∀ c, recordOf E A = some c → (∀ d, c.info ≠ .defn d) ∧
      ∀ ms, c.info = .muts ms → ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) :
    UnitLevelsAt t E A where
  solo := fun c d _ hrec hinfo _ _ => absurd hinfo ((h c hrec).1 d)
  defn := fun cb ms k d _ hrec hms hm _ _ => by
    have hmem : Ixon.MutConst.defn d ∈ ms.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm)
    obtain ⟨r, hr⟩ := (h cb hrec).2 ms hms _ hmem
    cases hr
  indc := fun cb ms k ind _ hrec hms hm _ => by
    have hmem : Ixon.MutConst.indc ind ∈ ms.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm)
    obtain ⟨r, hr⟩ := (h cb hrec).2 ms hms _ hmem
    cases hr

section Stored

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **The readings of a unit the run checked mention only their constants' level parameters**
(`UnitCheckedAt`, at any context limit): a standalone definition checked at its address, and
every member of a block checked member by member, each at its projection record's address. -/
theorem unitLevelsAt_of_unitChecked (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) (hbd : Bounded calls) {A : _root_.Address}
    {lim : Option Nat} (hu : UnitCheckedAt calls bAddr t E₀ A lim) : UnitLevelsAt t E₀ A := by
  have hblock : ∀ {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {k : Nat} {m : Ixon.MutConst},
      recordOf E₀ A = some cb → cb.info = .muts ms → ms[k]? = some m →
      FamilyRecon.LevelsDefinedAt t E₀ (memberAddr A k m) ∧
        recordOf E₀ (memberAddr A k m) = some (memberProjection A k m) ∧
        k.toUInt64.toNat = k := by
    intro cb ms k m hcb hms hm
    rcases hu with hc | ⟨cb', ms', hcb', hms', hall⟩
    · exact (Claim.checked_not_block hS hcb hms hc).elim
    · have e1 : cb' = cb := Option.some.inj (hcb'.symm.trans hcb)
      subst e1
      have e2 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
      subst e2
      have hklt : k < ms'.size := (Array.getElem?_eq_some_iff.mp hm).1
      obtain ⟨lc, hget, hx⟩ := recordOf_some hcb
      obtain ⟨cl, hcl, -, input, hargs, hrep⟩ := (hS.loaded.1 A lc hget).1
      have hlen : lc.rawBytes.data.toList.length < 2 ^ 39 :=
        RomBound.bounded_length_lt hbd hcl (by rw [hargs]; simp) hrep
      have hsize : lc.rawBytes.size = lc.rawBytes.data.toList.length := Array.length_toList.symm
      have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound lc.rawBytes cb' hx
      have hsz : ms'.size ≤ cb'.resourceSize := Claim.muts_size_le hms
      have hk58 : k < 288230376151711744 := by omega
      refine ⟨levelsDefinedAt_of_loadChecked hS hbd
          (LoadChecked.of_memberCheckedLim hk58 hm (hall k hklt)),
        (Claim.member_records hS hH hcb hms hm (hall k hklt)).1, ?_⟩
      change (UInt64.ofNat k).toNat = k
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.lt_trans hk58 (by decide))
  refine ⟨?_, ?_, ?_⟩
  · intro c d v hrec hinfo hk hread
    rcases hu with hc | ⟨cb', ms', hcb', hms', -⟩
    · exact (levelsDefinedAt_of_loadChecked hS hbd (LoadChecked.of_checkedLim hc)).solo c d v
        hrec hinfo hk hread
    · have e1 : cb' = c := Option.some.inj (hcb'.symm.trans hrec)
      rw [e1, hinfo] at hms'
      cases hms'
  · intro cb ms k d v hrec hms hm hk hread
    obtain ⟨hlv, hprec, hkk⟩ := hblock hrec hms hm
    exact hlv.member (memberProjection A k (.defn d)) ⟨k.toUInt64, A⟩ cb ms d v hprec rfl hrec
      hms (by rw [hkk]; exact hm) hk hread
  · intro cb ms k ind v hrec hms hm hread
    obtain ⟨hlv, hprec, hkk⟩ := hblock hrec hms hm
    exact hlv.ind (memberProjection A k (.indc ind)) ⟨k.toUInt64, A⟩ cb ms ind v hprec rfl hrec
      hms (by rw [hkk]; exact hm) hread

/-- **The readings of a unit a group's admission adds, not stored before it, mention only their
constants' level parameters**, for a bounded run with a collision-free store that validates every
role of the 77 groups: the unit is a record of the group's walk, checked at the group's
validation limit (`unitCheckedAt_of_topRec`), or a unit reached through its payload, checked
there (`payloadChecked_of_run`) or a selected family record, a block of recursors; a projection
record, an axiom and a block of recursors have no reading. -/
theorem unitLevelsAt_of_added (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {A : _root_.Address}
    (hadd : GroupAdds t E₀ (runPayload calls bAddr t) g A)
    (hsb : ¬ StoredBelow t E₀ (runPayload calls bAddr t) g A) : UnitLevelsAt t E₀ A := by
  have hS := hC.runStore
  have hH := hC.hashedStored
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
      cases hr
  have hbr := basisRolesStored_of_pinned hpin
  have hax := axiomRoles_of_run hC hval
  have hroots := RootsSafe.of_run hC hval (rootsAndTheoremsSafe_of_run hC hval)
  have hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs :=
    fun k => groupWalked_exists hH (hvalAll k)
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  cases hrec : recordOf E₀ A with
  | none =>
    exact unitLevelsAt_of_no_reading (fun c hc => by rw [hrec] at hc; cases hc)
  | some c =>
    have hproj : IsProj c → UnitLevelsAt t E₀ A := by
      intro hp
      refine unitLevelsAt_of_no_reading (fun c' hc' => ?_)
      have e : c' = c := Option.some.inj (hc'.symm.trans hrec)
      subst e
      refine ⟨fun d hd => ?_, fun ms hms => ?_⟩
      · rcases hp with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> (rw [hd] at hq; cases hq)
      · rcases hp with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩ <;> (rw [hms] at hq; cases hq)
    have hcR' : recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) A = some c :=
      (groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr ⟨storedBelow_of_adds hg6 hadd, hrec⟩
    have hnew : New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) A := by
      refine ⟨by rw [hcR']; rfl, ?_⟩
      cases hold : recordOf (groupStore t E₀ (runPayload calls bAddr t) g) A with
      | none => rfl
      | some c' => exact absurd ((groupStore_recordOf hb hg6).mp hold).1 hsb
    obtain ⟨recs, hw⟩ := hws g
    rcases groupAdds_cases hC hax hw hadd with ⟨-, r, hr, hra⟩ | ⟨r, hr, -, -, p, hp, hpr, -⟩ |
        ⟨ro, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpay
    · rw [← hra]
      exact unitLevelsAt_of_unitChecked hS hH hbd (unitCheckedAt_of_topRec hH r)
    · have e : p = c := Option.some.inj (hp.symm.trans hrec)
      exact hproj (e ▸ hpr)
    · refine unitLevelsAt_of_no_reading (fun c' hc' => ?_)
      have e : c' = c₂ := Option.some.inj (hc'.symm.trans hc₂)
      subst e
      exact ⟨fun d hd => (by rw [hd] at hinfo; cases hinfo),
        fun ms hms => (by rw [hms] at hinfo; cases hinfo)⟩
    · rcases payAdds_cases hP hpay with ⟨hreach, -⟩ | ⟨-, -, -, -, -, p, hp, hpr, -⟩
      · by_cases hunit : UnitKind c ∧ ¬ IsTwinShape c
        · rcases payloadChecked_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
            g hg6 hg A c hreach hnew hcR' hunit.1 hunit.2 with hu | ⟨B, hfam, -⟩
          · exact unitLevelsAt_of_unitChecked hS hH hbd hu
          · obtain ⟨-, -, cs, hfc⟩ := runFamOf_spec hfam
            obtain ⟨crb, rs, hcrb, -, hrs, hall, -⟩ := familyCall_record_block hS hH hfc
            refine unitLevelsAt_of_no_reading (fun c' hc' => ?_)
            have e : c' = crb := Option.some.inj (hc'.symm.trans hcrb)
            subst e
            refine ⟨fun d hd => (by rw [hd] at hrs; cases hrs), fun ms hms => ?_⟩
            have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrs)
            rw [e2]
            exact hall
        · refine unitLevelsAt_of_no_reading (fun c' hc' => ?_)
          have e : c' = c := Option.some.inj (hc'.symm.trans hrec)
          subst e
          refine ⟨fun d hd => hunit ⟨Or.inl ⟨d, hd⟩, ?_⟩, fun ms hms => ?_⟩
          · rintro ⟨rs, hrs, -⟩
            rw [hd] at hrs
            cases hrs
          · by_contra hcon
            refine hunit ⟨Or.inr (Or.inr ⟨ms, hms⟩), ?_⟩
            rintro ⟨rs, hrs, -, hall⟩
            have e2 : ms = rs := Ixon.ConstantInfo.muts.inj (hms.symm.trans hrs)
            exact hcon (e2 ▸ hall)
      · have e : p = c := Option.some.inj (hp.symm.trans hrec)
        exact hproj (e ▸ hpr)

/-- **The readings of every unit stored before a group mention only their constants' level
parameters**, for a bounded run with a collision-free store that validates every role of the 77
groups, given the same of the basis rows (`hbasis`): every other stored unit is one a group's
admission adds (`unitLevelsAt_of_added`). -/
theorem unitLevelsAt_of_storedBelow (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasis : ∀ A, (basisStore.consts.get? A).isSome = true → UnitLevelsAt t E₀ A) :
    ∀ g, 6 ≤ g → g ≤ 77 → ∀ A, StoredBelow t E₀ (runPayload calls bAddr t) g A →
      UnitLevelsAt t E₀ A := by
  intro g hg6
  induction g, hg6 using Nat.le_induction with
  | base =>
    intro _ A hA
    rcases hA with hbas | ⟨k, hk6, hk, -⟩
    · exact hbasis A hbas
    · omega
  | succ g hg6 ih =>
    intro hg77 A hA
    by_cases hsb : StoredBelow t E₀ (runPayload calls bAddr t) g A
    · exact ih (by omega) A hsb
    have hadd : GroupAdds t E₀ (runPayload calls bAddr t) g A := by
      rcases hA with hbas | ⟨k, hk6, hk, hadd⟩
      · exact absurd (Or.inl hbas) hsb
      · rcases Nat.lt_or_ge k g with hlt | hge
        · exact absurd (Or.inr ⟨k, hk6, hlt, hadd⟩) hsb
        · have e : k = g := by omega
          rw [← e]
          exact hadd
    exact unitLevelsAt_of_added hC hbd hb hpin hcheck hstep hval hg6 (by omega) hadd hsb

/-- **The readings at every address stored before a group mention only their constant's level
parameters** (`FamilyRecon.LevelsDefinedAt` on the addresses the store before group `g` holds,
which the store's own answers stay within: `FamilyRecon.reconOfStore_closedOn_sub`,
`groupStore_usedClosed_all`), under the hypotheses of `unitLevelsAt_of_storedBelow`: the store
holds the block of every projection record it holds. -/
theorem levelsDefinedAt_of_held (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasis : ∀ A, (basisStore.consts.get? A).isSome = true → UnitLevelsAt t E₀ A)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g ≤ 77) {a : _root_.Address}
    (ha : (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) a).isSome = true) :
    FamilyRecon.LevelsDefinedAt t E₀ a := by
  have hvalAll : ∀ g, ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r := by
    intro g r hr
    by_cases hg : g < 77
    · exact hval g hg r hr
    · rw [roleGroup_eq_nil (by rw [groups_length]; omega)] at hr
      cases hr
  have hP := payloadFacts_of_validated hC hbd hb hpin hcheck hstep hval
  have hcl := groupStore_usedClosed_all hC hb (basisRolesStored_of_pinned hpin)
    (axiomRoles_of_run hC hval) hP
    (fun k => groupWalked_exists hC.hashedStored (hvalAll k)) g hg6
  have hunit := unitLevelsAt_of_storedBelow hC hbd hb hpin hcheck hstep hval hbasis g hg6 hg
  obtain ⟨c₀, hc₀⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨hsb, hE⟩ := (groupStore_recordOf hb hg6).mp hc₀
  have howner : ∀ c, recordOf E₀ a = some c →
      StoredBelow t E₀ (runPayload calls bAddr t) g (Ix.Cert.ownerOf a c) := by
    intro c hc
    have e : c = c₀ := Option.some.inj (hc.symm.trans hE)
    subst e
    obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp (hcl.1 a c hc₀).1
    exact ((groupStore_recordOf hb hg6).mp hc₁).1
  refine levelsDefinedAt_of_unitLevels (hunit a hsb) (fun c p hrec hinfo => ?_)
    (fun c p hrec hinfo => ?_)
  · have h1 := howner c hrec
    simp only [Ix.Cert.ownerOf, hinfo] at h1
    exact hunit _ h1
  · have h1 := howner c hrec
    simp only [Ix.Cert.ownerOf, hinfo] at h1
    exact hunit _ h1

/-- **The readings at every address the calls `cs` load mention only their constant's level
parameters** (`FamilyRecon.LoadedLevelsDefined`), under the hypotheses of
`levelsDefinedAt_of_held`, when every address `cs` loads at which the run's store has a record is
held by the store before some group (`hheld`): an address with no record has no reading. The
run's store holds every record the run hashed, a group's store only those its admissions add, so
`hheld` is a fact of which loads `cs` makes. -/
theorem loadedLevelsDefined_of_held (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasis : ∀ A, (basisStore.consts.get? A).isSome = true → UnitLevelsAt t E₀ A)
    {cs : List (Call F)}
    (hheld : ∀ {xa : SourceValue F} {h : Heap F} {a : Bytes.Address},
      (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ cs → Bytes.RepAddressRef addrTy h a xa →
      (recordOf E₀ (ixAddr a)).isSome = true →
      ∃ g, 6 ≤ g ∧ g ≤ 77 ∧
        (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) (ixAddr a)).isSome = true) :
    FamilyRecon.LoadedLevelsDefined t E₀ cs := by
  intro xa h a hm ha
  cases hrec : recordOf E₀ (ixAddr a) with
  | none =>
    exact levelsDefinedAt_of_unitLevels
      (unitLevelsAt_of_no_reading (fun c hc => by rw [hrec] at hc; cases hc))
      (fun c p hc _ => by rw [hrec] at hc; cases hc)
      (fun c p hc _ => by rw [hrec] at hc; cases hc)
  | some c =>
    obtain ⟨g, hg6, hg, hs⟩ := hheld hm ha (by rw [hrec]; rfl)
    exact levelsDefinedAt_of_held hC hbd hb hpin hcheck hstep hval hbasis hg6 hg hs

/-- **`FamilyRecon.LoadedLevelsDefined` of a run** (`loadedLevelsDefined_of_held` at the run's
own calls): every address the run loads at which its store has a record is held by the store
before some group. -/
theorem loadedLevelsDefined_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    (hbasis : ∀ A, (basisStore.consts.get? A).isSome = true → UnitLevelsAt t E₀ A)
    (hheld : ∀ {xa : SourceValue F} {h : Heap F} {a : Bytes.Address},
      (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ calls → Bytes.RepAddressRef addrTy h a xa →
      (recordOf E₀ (ixAddr a)).isSome = true →
      ∃ g, 6 ≤ g ∧ g ≤ 77 ∧
        (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) (ixAddr a)).isSome = true) :
    FamilyRecon.LoadedLevelsDefined t E₀ calls :=
  loadedLevelsDefined_of_held hC hbd hb hpin hcheck hstep hval hbasis hheld

end Stored

end IxVM.Refinement.Binding.FamilyCallPremises

namespace IxVM.Refinement.Binding.FamilyRecon

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core (W KExpr KLevel KKey bmeta kexprEnum kexprListEnum klevelListEnum addrTy
  ixAddr addrListEnum)
open IxVM.Refinement.Decl (TmExact)
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Binding.FamilyFlat (GuardHead ResultSort BlockElim indTypeAt defnValAt
  membersAt indcAddrs keyAddr)
open IxVM.Consistency (Bounded)
open IxVM (F)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## `KernelModeled::block_elim`, with the bounds a load gives -/

/-- **`Ingress::get_ci` at the inductive type `a₀` answers the lookup `indTy`**
(`GuardIndAnswers`, at one address), with the bounds a load gives: the parameter and index counts
below `2^56`. `KernelModeled::block_elim` adds the two counts in the field and peels that many
binders, which asks no more of them. -/
def GuardIndAnswersAt (κ : _root_.Address → KKey)
    (indTy : _root_.Address → Option (Nat × KExpr × Nat × Nat)) (root : List (Call F))
    (a₀ : _root_.Address) : Prop :=
  ∀ {xa p xnl xty xnp xni xnc xrec xblk xidx : SourceValue F} {h m : Heap F}
    {cs : List (Call F)} {a : Bytes.Address},
    Bytes.RepAddressRef addrTy h a xa → ixAddr a = a₀ →
    ObsFn W "Ingress::get_ci" [xa] h p m cs →
    (⟨"Ingress::get_ci", [xa], h⟩ : Call F) ∈ root → (∀ c ∈ cs, c ∈ root) →
    loadValue m p = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
      [xnl, xty, xnp, xni, xnc, xrec, xblk, xidx]) →
    ∃ (nl np ni : Nat) (ty : KExpr),
      indTy (ixAddr a) = some (nl, ty, np, ni) ∧
      xnl = .field (nl : F) ∧ xnp = .field (np : F) ∧ xni = .field (ni : F) ∧
      np < 72057594037927936 ∧ ni < 72057594037927936 ∧ TmOExact κ m ty xty

/-- **`GuardIndAnswersAt` of a run**, at the store's inductive lookup: among the calls of a
bounded run with its store, at an address whose readings mention only their level parameters, a
load that returns an `Induct` gives the store's inductive at the address, its type represented
exactly. No bound on the counts is asked beyond the load's. -/
theorem guardIndAnswersAt_of_run {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hbd : Bounded calls) {a₀ : _root_.Address} (hlv : LevelsDefinedAt t E₀ a₀) :
    GuardIndAnswersAt (IxVM.Consistency.keyOf t) (indTypeAt t E₀) calls a₀ := by
  intro xa p xnl xty xnp xni xnc xrec xblk xidx h m cs a ha hix ev _ hsub hld
  subst hix
  obtain ⟨d, ba, hd, -, hnp, hni, -, -, e1, htm, e3, e4, -⟩ :=
    (indDataAt_of_load ht hS hH hbd hlv ha ev hsub hld).1 _ _ _ _ _ _ _ _ rfl
  exact ⟨d.nl, d.np, d.ni, d.ty, indTypeAt_of_indDataAt hd, e1, e3, e4, hnp, hni, htm⟩

/-- **`KernelModeled::block_elim` answers the never-zero test of the first type's result sort**
(`block_elim_resultSort`), the inductive read taken at the block's first type only and with the
bounds a load gives. -/
theorem block_elim_resultSort_at {κ : _root_.Address → KKey}
    {defVal : _root_.Address → Option (Nat × KExpr)}
    {indTy : _root_.Address → Option (Nat × KExpr × Nat × Nat)}
    {ka : KKey → Option _root_.Address} (hka : ∀ a, ka (κ a) = some a)
    {root : List (Call F)} (hD : GuardDefnAnswers κ defVal root)
    (bd : Bounded root) {typeAs : List Bytes.Address} {rc xtA bnl uo : SourceValue F}
    {h h' : Heap F}
    {cs : List (Call F)} (hroot : ∀ c ∈ cs, c ∈ root)
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA)
    (hI : ∀ a0 rest, typeAs = a0 :: rest → GuardIndAnswersAt κ indTy root (ixAddr a0))
    (ev : ObsFn W "KernelModeled::block_elim" [rc, xtA] h (.tuple [bnl, uo]) h' cs) :
    ∃ (a0 : Bytes.Address) (restAs : List Bytes.Address) (nl np ni : Nat) (ty : KExpr)
      (lvl : KLevel),
      typeAs = a0 :: restAs ∧
      indTy (ixAddr a0) = some (nl, ty, np, ni) ∧
      ResultSort defVal ka (np + ni) ty lvl ∧
      bnl = .field (nl : F) ∧
      uo = .field (((if lvl.isNeverZero then 1 else 0 : Nat) : Nat) : F) := by
  match Obs.«KernelModeled::block_elim».obs ev with
  | .run (m27 := m27) (m103 := m103) (v118 := v118) (ld11 := ld11) (ev43 := load) (ld37 := ld37)
      (op147 := op)
      (hm159 := hm) (ev115 := rsl) (ev176 := peers) (he213 := he) (ev232 := nz)
      (hc242 := hc) .. =>
    subst hm
    obtain ⟨a0, restAs, rfl, ha0, -⟩ := Lib.rep_cons_of_load htA ld11
    obtain ⟨nl, np, ni, ty, hind, rfl, rfl, rfl, hnp, hni, hty⟩ := hI a0 restAs rfl ha0 rfl load
      (hroot _ (by rw [hc]; simp)) (fun c hm => hroot c (by rw [hc]; simp [hm])) ld37
    have hv : v118 = .field ((np + ni : Nat) : F) := by
      simp only [evalBinOp] at op
      injection op with hv
      rw [← hv]
      congr 1
      push_cast
      rfl
    subst hv
    obtain ⟨lvl, hRS, rl⟩ := get_result_sort_level_spec hka hD bd (np + ni) (by omega)
      (fun c hc' => hroot c (by rw [hc]; simp [hc']))
      (hty.mono (Heap.Extends.snoc _ _)) rsl
    obtain ⟨hr, -⟩ := IxVM.Refinement.Levels.levelIsNotZero_step nz _ rfl lvl
      (rl.mono peers.heap_extends)
    injection he with htup
    injection htup with hbnl htup
    injection htup with huo _
    refine ⟨a0, restAs, nl, np, ni, ty, lvl, rfl, hind, hRS, hbnl, ?_⟩
    rw [huo, hr]
    split <;> simp

end IxVM.Refinement.Binding.FamilyRecon

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Binding.FamilyFlat (BlockElim indTypeAt defnValAt membersAt indcAddrs
  keyAddr)
open IxVM.Refinement.Binding.FamilyRecon (GuardDefnAnswers GuardIndAnswers IndAnswers ReconView
  block_elim_resultSort guardIndAnswers_of_indAnswers)
open IxVM.Refinement.Binding.FamilyRecon (GuardIndAnswersAt block_elim_resultSort_at)

set_option linter.unusedVariables false

/-- **`KernelModeled::block_elim` computes the block's elimination offset**
(`block_elim_blockElim`), the inductive read taken at the block's first type only and with the
bounds a load gives (`GuardIndAnswersAt`). -/
theorem block_elim_blockElim_at {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {κ : _root_.Address → KKey} (hka : ∀ a, keyAddr t (κ a) = some a)
    (hD : GuardDefnAnswers κ (defnValAt t E₀) calls)
    (hI : GuardIndAnswersAt κ (indTypeAt t E₀) calls (iprjAddr B 0))
    (hbd : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hms_u64 : ms.size < UInt64.size)
    {typeAs : List Bytes.Address} {rc xtA bnl uo : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (hsub : CallSub cs calls)
    (htypes : typeAs.map ixAddr =
      ms.toList.mapIdx fun i m => projAddr (Specs.Callees.memberProjInfo B i m))
    (htA : RepList addrListEnum (Bytes.RepAddressRef addrTy) h typeAs xtA)
    (ev : ObsFn Obs.W "KernelModeled::block_elim" [rc, xtA] h (.tuple [bnl, uo]) h' cs) :
    ∃ (a0 : Bytes.Address) (restAs : List Bytes.Address) (ind0 : Ixon.Inductive) (off : Nat),
      typeAs = a0 :: restAs ∧
      ixAddr a0 = iprjAddr B 0 ∧
      ms[0]? = some (.indc ind0) ∧
      ind0.lvls.toNat < 4294967296 ∧
      bnl = .field (ind0.lvls.toNat : F) ∧
      BlockElim t E₀ B off ∧
      uo = .field (off : F) := by
  obtain ⟨a0, restAs, ind0, htyAs, ha0, hms0, hlt, hbnl, -⟩ :=
    block_elim_spec hbd hS hB hms_u64 hsub htypes htA ev
  obtain ⟨a0', restAs', nl, np, ni, ty, lvl, htyAs', hind, hRS, -, huo⟩ :=
    block_elim_resultSort_at hka hD hbd hsub htA
      (fun a0' rest' h => by
        obtain ⟨rfl, -⟩ := List.cons.inj (htyAs.symm.trans h)
        rw [ha0]
        exact hI) ev
  obtain ⟨rfl, -⟩ := List.cons.inj (htyAs.symm.trans htyAs')
  obtain ⟨rest, hmem⟩ := membersAt_cons_of_block hB hms0
  rw [ha0] at hind
  exact ⟨a0, restAs, ind0, _, htyAs, ha0, hms0, hlt, hbnl,
    ⟨iprjAddr B 0, rest, nl, np, ni, ty, lvl, hmem, hind, hRS, rfl⟩, huo⟩

end IxVM.Refinement.Typing.FamilyAlias

namespace IxVM.Refinement.Binding.FamilyCallPremises

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Typing

/-! ## The readings of a selected block -/

section Selected

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **The readings at every member of a selected block mention only their constant's level
parameters**, with no premise on the basis rows: the block is new in its group's admission, so
its unit is one the admission adds (`unitLevelsAt_of_added`). -/
theorem selected_members_levelsDefined (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {B rb : _root_.Address}
    (hf : runFamOf calls bAddr t E₀ g B = some rb) {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms) :
    ∀ i m, ms[i]? = some m → FamilyRecon.LevelsDefinedAt t E₀ (memberAddr B i m) := by
  obtain ⟨hnew, -, -⟩ := runFamOf_spec hf
  obtain ⟨c, hE, -, hadd, hsb⟩ := new_groupStore hb hg6 hnew
  have hU := unitLevelsAt_of_added hC hbd hb hpin hcheck hstep hval hg6 hg hadd hsb
  intro i m hm
  have hprec := hB.members i m hm
  refine levelsDefinedAt_of_unitLevels (unitLevelsAt_of_no_reading (fun c' hc' => ?_))
    (fun c' p hc' hinfo => ?_) (fun c' p hc' hinfo => ?_)
  · have e : c' = memberProjection B i m := Option.some.inj (hc'.symm.trans hprec)
    subst e
    cases m <;> exact ⟨fun d hd => (by cases hd), fun ms' hms' => (by cases hms')⟩
  · have e : c' = memberProjection B i m := Option.some.inj (hc'.symm.trans hprec)
    subst e
    have hpb : p.block = B := by
      cases m with
      | defn d => injection hinfo with h1; rw [← h1]
      | indc _ => cases hinfo
      | recr _ => cases hinfo
    rw [hpb]
    exact hU
  · have e : c' = memberProjection B i m := Option.some.inj (hc'.symm.trans hprec)
    subst e
    have hpb : p.block = B := by
      cases m with
      | defn d => cases hinfo
      | indc _ => injection hinfo with h1; rw [← h1]
      | recr _ => cases hinfo
    rw [hpb]
    exact hU

/-- **The inductive read `KernelModeled::block_elim` makes of a selected block**
(`FamilyRecon.GuardIndAnswersAt` at the block's first type), from the run. -/
theorem guardIndAnswersAt_of_selected (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) (hstep : RunStepStores calls t E₀)
    (hval : ∀ g, g < 77 → ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77) {B rb : _root_.Address}
    (hf : runFamOf calls bAddr t E₀ g B = some rb) {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hB : FamBlockRecord E₀ B cb ms) {ind0 : Ixon.Inductive}
    (hms0 : ms[0]? = some (.indc ind0)) :
    FamilyRecon.GuardIndAnswersAt (IxVM.Consistency.keyOf t) (FamilyFlat.indTypeAt t E₀) calls
      (iprjAddr B 0) := by
  have hlv := selected_members_levelsDefined hC hbd hb hpin hcheck hstep hval hg6 hg hf hB 0 _
    hms0
  rw [LoadedReads.memberAddr_indc] at hlv
  intro xa p xnl xty xnp xni xnc xrec xblk xidx h m cs a ha hix ev hcl hsub hld
  exact FamilyRecon.guardIndAnswersAt_of_run hcheck hC.runStore hC.hashedStored hbd hlv ha hix ev
    hcl hsub hld

end Selected

end IxVM.Refinement.Binding.FamilyCallPremises
