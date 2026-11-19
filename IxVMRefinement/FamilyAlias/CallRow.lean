import IxVMRefinement.FamilyAlias.CallRecs
import IxVMRefinement.FamilyAlias.BlockRowCheck
import IxVMRefinement.FamilyAlias.ClosureFamilyStep
import IxVMRefinement.FamilyGraph.ProducersCallTree
import IxVMRefinement.StatementRel.ClosedFacts
import IxVMRefinement.StatementRel.StoreInhabit
import IxVMRefinement.Assembly.TypingStore

/-! # Discharging `FamilyBlockCheckRow` and `ClosureFamilyCheck` from `KernelModeled::check_family`

Wires the heap-chained check of a modeled family (`CheckFamilyChain`, `CallTables`, `CallAdvice`,
`CallRecRefs`, `CallMembers`, `CallRecs`) into both unconditional family check endpoints:

* `committedPrelude_inLogic`, `pinnedBasis_role_mem_prelude`, `coveredLogic_of_checked`:
  every covered `.iPrj` reference has its block in Lean's logic (`InLogic`);
* `basisPinHit_eq_none_of_fresh`: a fresh family block never hits any pinned basis package;
* `cidx_eq_of_modeled_checked`: every constructor of a checked modeled block has `ct.cidx = j`;
* `familyCall_checked_of_chain`: full Layer-2 assembly from `CheckFamilyChain` into
  `FamilyTysCanon`, `MajorRefs`, `recRefs`, `FamDeclReads`, `FamilyCheckFacts`, and
  `FamRecsCompanion`;
* `advAs_eq_of_familyOwnAdvice`: identifies the advice list `advAs` of a `FamilyOwnAdvice` witness
  with `C.advList` read off the same `check_family` call's `CheckFamilyChain`, via the payload
  stream anchor (`check_family_first_get_address`) and determinism of byte-stream deserialization;
* `closureFamilyCheck_of_run`: unconditional `ClosureFamilyCheck` at every group of every
  binding run;
* `familyBlockCheckRow_of_run`: unconditional `FamilyBlockCheckRow` at every typing walk. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.Decl.FamilyAlias (aliasMap FamilyAdvice FamilyCheckFacts MemberFacts
  MembersFacts RecsFacts RulesFacts nonrecsOf recsOf isTypeOrCtor typesScopedB)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Committed prelude logic, covered `.iPrj` safety, and basis-pin disjointness -/

private def inLogicMutB : Ixon.MutConst → Bool
  | .defn d => (Ix.Kernel.Reader.safetyDecline d).isNone
  | .indc i => !i.isUnsafe && i.ctors.toList.all (!·.isUnsafe)
  | .recr r => !r.isUnsafe

private def inLogicB (c : Ixon.Constant) : Bool :=
  match c.info with
  | .defn d => (Ix.Kernel.Reader.safetyDecline d).isNone
  | .recr r => !r.isUnsafe
  | .axio a => !a.isUnsafe
  | .muts ms => ms.toList.all inLogicMutB
  | _ => true

private theorem inLogicMut_of_bool {m : Ixon.MutConst} (h : inLogicMutB m = true) :
    InLogicMut m := by
  cases m with
  | defn d =>
    simp only [inLogicMutB, Option.isNone_iff_eq_none] at h
    exact h
  | indc i =>
    simp only [inLogicMutB, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    exact ⟨h.1, fun ct hct => h.2 ct hct⟩
  | recr r =>
    simp only [inLogicMutB, Bool.not_eq_true'] at h
    exact h

private theorem inLogic_of_bool {c : Ixon.Constant} (h : inLogicB c = true) : InLogic c := by
  unfold InLogic
  unfold inLogicB at h
  cases hinfo : c.info with
  | defn d =>
    rw [hinfo] at h
    simp only [Option.isNone_iff_eq_none] at h
    exact h
  | recr r =>
    rw [hinfo] at h
    simp only [Bool.not_eq_true'] at h
    exact h
  | axio a =>
    rw [hinfo] at h
    simp only [Bool.not_eq_true'] at h
    exact h
  | muts ms =>
    rw [hinfo] at h
    simp only [List.all_eq_true] at h
    exact fun m hm => inLogicMut_of_bool (h m hm)
  | quot _ | dPrj _ | iPrj _ | cPrj _ | rPrj _ => trivial

private theorem committedPrelude_inLogicB :
    RoleVal.committedPreludeList.all (fun q => inLogicB q.2) = true := by
  decide +kernel

/-- Every decoded committed prelude record is in Lean's logic. -/
theorem committedPrelude_inLogic : ∀ q ∈ RoleVal.committedPreludeList, InLogic q.2 := fun q hq =>
  inLogic_of_bool (List.all_eq_true.mp committedPrelude_inLogicB q hq)

private def isPreludeRoleKey : Ix.Kernel.Key .anon → Bool
  | .role r => preludeRoles.contains r
  | _ => false

private theorem basisKind_declsA_prelude (kind : Ix.Kernel.BasisKind) :
    (kind.declsA : List (ConstantInfo .anon)).all (fun ci => isPreludeRoleKey ci.name) = true := by
  cases kind <;> decide +kernel

/-- Every pinned basis constant is named by a prelude role. -/
theorem pinnedBasis_role_mem_prelude (kind : Ix.Kernel.BasisKind) (ci : ConstantInfo .anon)
    (hci : ci ∈ (kind.declsA : List (ConstantInfo .anon))) :
    ∃ r ∈ preludeRoles, ci.name = .role r := by
  have hb := List.all_eq_true.mp (basisKind_declsA_prelude kind) ci hci
  cases hn : ci.name with
  | role r =>
    rw [hn] at hb
    simp only [isPreludeRoleKey, List.contains_eq_mem, decide_eq_true_eq] at hb
    exact ⟨r, hb, rfl⟩
  | id _ | aux _ _ =>
    rw [hn] at hb
    cases hb

private theorem recordAt_of_committedPrelude {E : Ixon.Env} {R : Ixon.Env}
    (hRecs : RecordsFor R E) {q : _root_.Address × Ixon.Constant}
    (hq : q ∈ RoleVal.committedPreludeList) :
    Ix.Cert.recordAt E q.1 = some q.2 := by
  have hrow := ClosedFacts.committedPrelude_rows q hq
  obtain ⟨lc, hget, hbytes⟩ := hRecs.2.2.2 (q.1, Ixon.serConstant q.2) hrow.1
  rw [← recordOf_eq_recordAt_of_decoded hRecs.1 q.1]
  unfold recordOf
  rw [hget, Option.bind_some, hbytes, hrow.2]
  rfl

/-- **Any covered `.iPrj` reference has its parent block in Lean's logic.** -/
theorem coveredLogic_of_checked {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {G : Nat → Prop} {R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    {lim : Option Nat}
    (hshape : TableShape.{u} t G R envT)
    (hG : ∀ r : Ix.Kernel.Role, (∀ n, lim = some n → Ix.SpecDigest.groupOf r < n) →
      G (Ix.SpecDigest.groupOf r))
    (hRecs : RecordsFor R E)
    (hst : StepStore calls t E₀ E)
    {x : _root_.Address} {c : Ixon.Constant} {p : Ixon.InductiveProj} {cb : Ixon.Constant}
    (hcov : Claim.CoveredAt t lim x)
    (hrec : recordOf E₀ x = some c) (hinfo : c.info = .iPrj p)
    (hblk : recordOf E₀ p.block = some cb) : InLogic cb := by
  obtain ⟨r, ha, hw, hlt⟩ := hcov
  obtain ⟨ci, hfind, hpin | hkept⟩ :=
    hshape.kept (Ix.SpecDigest.groupOf r) r x (hG r hlt)
      (role_mem_roleGroup r) (Or.inl (Or.inl hw)) ha
  · -- Pinned basis constant: `r ∈ preludeRoles`, so both `x` and `p.block` are committed prelude rows.
    obtain ⟨kind, hci_mem⟩ := hpin
    obtain ⟨r', hr'_pre, hname'⟩ := pinnedBasis_role_mem_prelude kind ci hci_mem
    have hname := Ix.Kernel.Semantics.Env.find?_name hfind
    have hr_eq : r = r' := by
      have := hname.symm.trans hname'
      injection this
    subst hr_eq
    obtain ⟨a', bytes, ha', hrow⟩ := ClosedFacts.preludePinned_rows hshape.prelude r hr'_pre
    have hax : a' = x := Option.some.inj (ha'.symm.trans ha)
    subst hax
    rw [StoreInhabit.committedRows_eq] at hrow
    obtain ⟨e, he, hpe⟩ := List.mem_map.mp hrow
    have he1 : e.1 = a' := congrArg Prod.fst hpe
    have hrecE_e : Ix.Cert.recordAt E a' = some e.2 := by
      rw [← he1]; exact recordAt_of_committedPrelude hRecs he
    have hrecE_c : Ix.Cert.recordAt E a' = some c := hst.runRecord a' c hrec
    have hc_eq : c = e.2 := Option.some.inj (hrecE_c.symm.trans hrecE_e)
    obtain ⟨q, hq, hq1⟩ := ClosedFacts.committedPrelude_owner e he
    have hown_eq : Ix.Cert.ownerOf e.1 e.2 = p.block := by
      rw [← hc_eq]; simp [Ix.Cert.ownerOf, hinfo]
    have hq_blk : q.1 = p.block := hq1.trans hown_eq
    have hrecE_q : Ix.Cert.recordAt E p.block = some q.2 := by
      rw [← hq_blk]; exact recordAt_of_committedPrelude hRecs hq
    have hrecE_cb : Ix.Cert.recordAt E p.block = some cb := hst.runRecord p.block cb hblk
    have hcb_eq : cb = q.2 := Option.some.inj (hrecE_cb.symm.trans hrecE_q)
    rw [hcb_eq]
    exact committedPrelude_inLogic q hq
  · -- `KeptIn`: `ReadsIn` over `R` exposes `MemberAt` with `InLogic cbR`, and `cbR = cb`.
    obtain ⟨-, ci₀, ⟨cR, hrecR, hRR⟩, -⟩ := hkept
    have hcR_eq : cR = c :=
      Option.some.inj ((hRecs.2.1 x cR hrecR).symm.trans (hst.runRecord x c hrec))
    subst hcR_eq
    rw [hinfo] at hRR
    obtain ⟨cbR, msR, indR, ⟨hblkR, -, -, -, -, hlogR⟩, -⟩ := hRR
    have hcbR_eq : cbR = cb :=
      Option.some.inj ((hRecs.2.1 p.block cbR hblkR).symm.trans (hst.runRecord p.block cb hblk))
    rwa [← hcbR_eq]

private theorem basisKind_declsA_nonempty (k : Ix.Kernel.BasisKind) :
    ∃ ci, ci ∈ (k.declsA : List (ConstantInfo .anon)) := by
  cases k <;> exact ⟨_, List.mem_cons_self⟩

private theorem basisKind_declsA_names (k : Ix.Kernel.BasisKind) :
    (k.declsA : List (ConstantInfo .anon)).map (·.name) =
      (k.decls : List (ConstantInfo .anon)).map (·.name) := by
  cases k <;> decide

/-- **A fresh family block never hits any pinned basis package** (every pinned basis constant is
already stored in `env` via `TableShape.pins`). -/
theorem basisPinHit_eq_none_of_fresh {t : Ix.Kernel.RoleTable} {G : Nat → Prop}
    {R : Ixon.Env} {envT env : Ix.Kernel.Env .anon}
    (hshape : TableShape.{u} t G R envT)
    (hext : ∀ ci ∈ envT.consts, ci ∈ env.consts)
    {blk : List (ConstantInfo .anon)}
    (hfresh : ∀ ci ∈ blk, env.find? ci.name = none) :
    Ix.Kernel.basisPinHit blk = none := by
  cases h : Ix.Kernel.basisPinHit blk with
  | none => rfl
  | some k =>
    unfold Ix.Kernel.basisPinHit at h
    rw [Option.filter_eq_some_iff] at h
    obtain ⟨hfind, -⟩ := h
    have hname_eq : (k.decls : List (ConstantInfo .anon)).map (·.name) = blk.map (·.name) :=
      beq_iff_eq.mp (by simpa using List.find?_some hfind)
    obtain ⟨ci0, hci0⟩ := basisKind_declsA_nonempty k
    have hmem_env : ci0 ∈ env.consts := hext ci0 (hshape.pins k ci0 hci0)
    have hsome : (env.find? ci0.name).isSome = true := find?_isSome_of_mem hmem_env
    have hname_in : ci0.name ∈ blk.map (·.name) := by
      rw [← hname_eq, ← basisKind_declsA_names k]
      exact List.mem_map.mpr ⟨ci0, hci0, rfl⟩
    obtain ⟨ci1, hci1, hnm1⟩ := List.mem_map.mp hname_in
    have hnone := hfresh ci1 hci1
    rw [hnm1] at hnone
    rw [hnone] at hsome
    cases hsome

/-! ## `RCRep` from `RCLimRep`, and `ct.cidx = j` for checked modeled blocks -/

private theorem rcRep_of_rcLimRep {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address}
    {lim : Option Nat} {h : Heap F} {rc : SourceValue F}
    (hrc : Claim.RCLimRep t bAddr lim h rc) : RCRep t lim h rc := by
  obtain ⟨tbl, htbl, hnd⟩ := hrc.cases
  rcases hnd with ⟨n, rfl, hn, hl⟩ | ⟨rfl, hl⟩
  · exact ⟨tbl, .construct addrMapEnum "Nil" [], _, hl, .inl ⟨n, rfl, hn, rfl⟩, htbl.toTableRep⟩
  · exact ⟨tbl, .construct addrMapEnum "Nil" [], _, hl, .inr ⟨rfl, rfl⟩, htbl.toTableRep⟩

private theorem toNat_toUInt64_lt_cr {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- **Every constructor of a checked modeled block records its exact slot index `ct.cidx.toNat = j`**:
mirrors `UnitFree.modeledCtor_trees` for an arbitrary multi-inductive block `(ms, i)`. -/
theorem cidx_eq_of_modeled_checked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {lim : Option Nat}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms) (hst : StepStore calls t E₀ E)
    (hdec : L1.EnvDecoded E) (hmod : ModeledAt E B)
    (hms_lt : ms.size < 8589934592)
    (hmem : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim) :
    ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct → ct.cidx.toNat = j := by
  intro i ind j ct hmi hct
  have hi_lt : i < ms.size := (Array.getElem?_eq_some_iff.mp hmi).1
  have hj_lt : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  have hi_u64 : i < UInt64.size := by
    have : UInt64.size = 18446744073709551616 := rfl; omega
  have hval_i : ZMod.val ((i : Nat) : F) = i :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hchk := hmem i hi_lt
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmemRep, hblk, ev_pa, -, -, -, -, ev_ld, -, hsub_ld, hld,
    ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨b', hb', hb'B⟩ := hblk
  obtain ⟨-, -, -, mc, a, hget, ha, hax, -⟩ := L1.projection_addr_hashed_spec hmemRep hb' ev_pa
  rw [hval_i] at hget hax
  have hmc : mc = .indc ind := by
    rw [Array.getElem?_toList, hmi] at hget
    exact (Option.some.inj hget).symm
  subst hmc
  have hax' : Core.ixAddr a = Core.iprjAddr B i := by
    rw [← hb'B]
    exact hax.trans (LoadedReads.memberAddr_eq_projAddr _ i (.indc ind)).symm
  let c0 : Ctx := ⟨E, Ix.Kernel.Env.empty, t, lim⟩
  have hg : Core.Good c0 calls := hst.good Ix.Kernel.Env.empty lim
  have hg_ld : Core.Good c0 cs_load := hg.sub hsub_ld
  have hg_chk : Core.Good c0 cs_chk := hg.sub hsub_chk
  have hrecE_B : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hdec B).trans (hst.runRecord B cb hB.record)
  have hrecE_ip : recordOf E (Core.iprjAddr B i) = some (memberProjection B i (.indc ind)) := by
    rw [← LoadedReads.memberAddr_indc]
    exact (recordOf_eq_recordAt_of_decoded hdec _).trans
      (hst.runRecord _ _ (hB.members i (.indc ind) hmi))
  obtain ⟨rawBytes, c', hh, haddr, hex, -, hres⟩ := L1.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B i (.indc ind)) := by
    rw [hax']; exact hrecE_ip
  obtain ⟨lc, hgetA, hdecA⟩ := LoadedReads.recordOf_inv hrecA
  have hb0 : rawBytes = lc.rawBytes := Core.load_escape hgetA hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B i (.indc ind) := by
    rw [hb0, hdecA] at hex; exact (Except.ok.inj hex).symm
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B i (.indc ind)).info = .iPrj ⟨i.toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨-, blkBytes, cb', ms', ind', _, _, _, v₀, hhB, haB, hexB, hcb, hms,
    -, -, -, hld₀, hraw, -⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hrecE_B
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by rw [hbB, hdecB] at hexB; exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = ms := Ixon.ConstantInfo.muts.inj (hcb.symm.trans hB.muts)
  subst ms'
  have hi' : (⟨i.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = i := toNat_toUInt64_lt_cr hi_u64
  rw [hi'] at hms hraw
  have hiEq : ind' = ind := by
    rw [Array.getElem?_toList, hmi] at hms
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms)).symm
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨-, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, -⟩ := hraw
  subst hv
  rcases induct_native_or_ctors ev_chk with ⟨mb, ma, mcs, modeRun, hextN, hsubN⟩ |
      ⟨uarg, mcb, mca, mcr, mccs, hu, ctorsRun, hextC, hsubC⟩
  · have hgN : Core.Good c0 mcs := hg_chk.sub hsubN
    exact absurd (show NativeAt E B from ⟨blkPtr, mb, ma, mcs, b, modeRun, hgN.1, hgN.2,
      Bytes.repAddressRef_heapMono₂ Core.addrTy hextN hb_rep, hb_eq⟩) hmod
  obtain ⟨s, rfl⟩ : ∃ s : F, uarg = .field s := by
    rcases hu with rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨_, rfl⟩
  have hsubC' : ∀ cl ∈ mccs, cl ∈ calls := fun cl hcl => hsub_chk cl (hsubC cl hcl)
  obtain ⟨st⟩ := modeled_ctor_runs (b := b) (start := mcb) hc56 ind.ctors.size 0 (by omega)
    (Heap.Extends.refl _) hsubC' (Bytes.repAddressRef_heapMono₂ Core.addrTy hextC hb_rep)
    ctorsRun j (Nat.zero_le _) hj_lt
  have hval_j : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  have hgL : Core.Good c0 st.loadCalls := hg.sub st.loadSubset
  obtain ⟨-, -, -, blkBytes₂, cb₂, ms₂, ind₂, ct₂, _, v₂, hhB₂, haB₂, hexB₂, -, hcb₂, hms₂,
    hct₂, -, hldv₂, hraw₂⟩ := L1.get_ci_cprj_spec hgL.2 st.blockRep st.loaded
  have hbB₂ : blkBytes₂ = lcB.rawBytes :=
    Core.load_escape hgetB hgL.1 blkBytes₂ hhB₂ (haB₂.trans hb_eq)
  have hcB₂ : cb₂ = cb := by rw [hbB₂, hdecB] at hexB₂; exact (Except.ok.inj hexB₂).symm
  subst cb₂
  have hmsEq₂ : ms₂ = ms := Ixon.ConstantInfo.muts.inj (hcb₂.symm.trans hB.muts)
  subst ms₂
  rw [hval_i] at hms₂
  have hind₂ : ind₂ = ind := by
    rw [Array.getElem?_toList, hmi] at hms₂
    exact (Ixon.MutConst.indc.inj (Option.some.inj hms₂)).symm
  subst ind₂
  rw [hval_j] at hct₂
  have hct_eq : ct₂ = ct := by
    rw [Array.getElem?_toList, hct] at hct₂
    exact (Option.some.inj hct₂).symm
  subst ct₂
  have hvv₂ : v₂ = .construct Core.kciEnum "Ctor" [st.nl, st.ty, st.parent, st.member, st.slot,
      st.numParams, st.numFields, st.unsafeFlag] :=
    Except.ok.inj (hldv₂.symm.trans st.tag)
  obtain ⟨-, hccidx, -, -, -, _, _, _, -, -, hvC, -⟩ := hraw₂
  rw [hvC] at hvv₂
  injection hvv₂ with _ _ hargs
  injection hargs with _ hargs; injection hargs with _ hargs
  injection hargs with _ hargs; injection hargs with _ hargs
  injection hargs with hsl _
  exact Decl.nat_eq_of_field_eq_bounded (by omega) (by omega) (hsl.trans st.slotChecked)

/-! ## Indexing helpers for `ctorSlotsFrom`, `MembersFacts`, `RecsFacts`, `nonrecsOf`/`recsOf` -/

private theorem getElem?_finRange_eq {n k : Nat} (hk : k < n) :
    (List.finRange n)[k]? = some ⟨k, hk⟩ := by
  rw [List.getElem?_eq_getElem (by simp; exact hk), List.getElem_finRange]
  rfl

private theorem addrMapAll_imp {e : String} {P Q : Heap F → Bytes.Address → SourceValue F → Prop}
    (himp : ∀ h k v, P h k v → Q h k v) {h : Heap F} {p : SourceValue F}
    (hm : AddrMapAll e P h p) : AddrMapAll e Q h p := by
  induction hm with
  | nil => exact .nil
  | node hk hP hl hr _ _ ihl ihr => exact .node hk (himp _ _ _ hP) hl hr ihl ihr

private theorem repList_det {α : Type} {e n c : String} {R : Heap F → α → SourceValue F → Prop}
    (hdet : ∀ h a₁ a₂ p, R h a₁ p → R h a₂ p → a₁ = a₂) {h : Heap F} :
    ∀ {l₁ l₂ : List α} {p : SourceValue F},
      RepLinkedList e n c R h l₁ p → RepLinkedList e n c R h l₂ p → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, .nil c1, .cons c2 _ _ => by
    have hv := cell_eq c1 c2; simp at hv
  | _ :: _, [], _, .cons c1 _ _, .nil c2 => by
    have hv := cell_eq c1 c2; simp at hv
  | _ :: _, _ :: _, _, .cons c1 r1 t1, .cons c2 r2 t2 => by
    have hv := cell_eq c1 c2
    simp only [Value.construct.injEq, List.cons.injEq, and_true, true_and] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact congrArg₂ List.cons (hdet _ _ _ _ r1 r2) (repList_det hdet t1 t2)

private theorem ctorSlotsFrom_mem_of_getElem? :
    ∀ (ms : List Ixon.MutConst) (p i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
      (p + i, ind, j, ct) ∈ ctorSlotsFrom ms p
  | [], _, _, _, _, _, hi, _ => by simp at hi
  | m :: rest, p, 0, ind, j, ct, hi, hct => by
    have hm : m = .indc ind := by simpa using hi
    subst hm
    simp only [ctorSlotsFrom, Nat.add_zero, List.mem_append]
    left
    have hj_lt : j < ind.ctors.toList.length := by
      rw [Array.length_toList]; exact (Array.getElem?_eq_some_iff.mp hct).1
    refine List.mem_iff_getElem?.mpr ⟨j, ?_⟩
    rw [List.getElem?_mapIdx, Array.getElem?_toList, hct]
    rfl
  | m :: rest, p, i + 1, ind, j, ct, hi, hct => by
    have ih := ctorSlotsFrom_mem_of_getElem? rest (p + 1) i ind j ct (by simpa using hi) hct
    rw [show p + 1 + i = p + (i + 1) by omega] at ih
    cases m with
    | indc _ => exact List.mem_append_right _ ih
    | defn _ | recr _ => exact ih

private theorem membersFacts_append {env : Ix.Kernel.Env .anon} {g : KKey → KKey} :
    ∀ {b₁ b₂ : List (ConstantInfo .anon)} {t₁ t₂ : List KExpr},
      b₁.length = t₁.length →
      MembersFacts env g b₁ t₁ → MembersFacts env g b₂ t₂ →
      MembersFacts env g (b₁ ++ b₂) (t₁ ++ t₂)
  | [], _, [], _, _, _, h2 => h2
  | _ :: _, _, [], _, hlen, _, _ => by cases hlen
  | [], _, _ :: _, _, hlen, _, _ => by cases hlen
  | _ :: b₁, b₂, _ :: t₁, t₂, hlen, h1, h2 =>
    ⟨h1.1, membersFacts_append (Nat.succ.inj hlen) h1.2 h2⟩

private theorem membersFacts_of_getElem {env : Ix.Kernel.Env .anon} {g : KKey → KKey} :
    ∀ (bs : List (ConstantInfo .anon)) (ts : List KExpr) (hlen : bs.length = ts.length),
      (∀ idx (hi : idx < bs.length), MemberFacts env g bs[idx] (ts[idx]'(hlen ▸ hi))) →
      MembersFacts env g bs ts
  | [], [], _, _ => trivial
  | [], _ :: _, hlen, _ => by cases hlen
  | _ :: _, [], hlen, _ => by cases hlen
  | b :: bs, t :: ts, hlen, hall =>
    ⟨hall 0 (by simp),
     membersFacts_of_getElem bs ts (Nat.succ.inj hlen) fun idx hi => hall (idx + 1) (by simp; omega)⟩

private theorem recsFacts_of_getElem {env : Ix.Kernel.Env .anon} {g : KKey → KKey}
    {blk : List (ConstantInfo .anon)} {tys : List KExpr} :
    ∀ (recs : List (ConstantInfo .anon)) (tysR : List KExpr) (rhsss : List (List KExpr))
      (thss : List (List KKey))
      (hl1 : recs.length = tysR.length) (hl2 : recs.length = rhsss.length)
      (hl3 : recs.length = thss.length),
      (∀ idx (hi : idx < recs.length),
        ∃ cv mI rP rules,
          recs[idx] = .recInfo cv mI rP rules ∧
          RulesFacts env g blk tys cv.name cv.levelParams
            (tysR[idx]'(hl1 ▸ hi)) mI rP rules
            (rhsss[idx]'(hl2 ▸ hi)) (thss[idx]'(hl3 ▸ hi))) →
      RecsFacts env g blk tys recs tysR rhsss thss
  | [], [], [], [], _, _, _, _ => trivial
  | r :: rs, t :: ts, rh :: rhs, th :: ths, hl1, hl2, hl3, hall => by
    obtain ⟨cv, mI, rP, rules, hr_eq, hrf⟩ := hall 0 (by simp)
    simp only [List.getElem_cons_zero] at hr_eq hrf
    subst hr_eq
    exact ⟨hrf, recsFacts_of_getElem rs ts rhs ths
      (Nat.succ.inj hl1) (Nat.succ.inj hl2) (Nat.succ.inj hl3)
      fun idx hi => hall (idx + 1) (by simp; omega)⟩
  | [], _ :: _, _, _, hl1, _, _, _ | _ :: _, [], _, _, hl1, _, _, _ => by cases hl1
  | _ :: _, _ :: _, [], _, _, hl2, _, _ => by cases hl2
  | _ :: _, _ :: _, _ :: _, [], _, _, hl3, _ => by cases hl3

private theorem nonrecsOf_append_recs {nonrecs recs : List (ConstantInfo .anon)}
    (h1 : ∀ ci ∈ nonrecs, isTypeOrCtor ci = true)
    (h2 : ∀ ci ∈ recs, ∃ cv mI rP rules, ci = .recInfo cv mI rP rules) :
    nonrecsOf (nonrecs ++ recs) = nonrecs ∧ recsOf (nonrecs ++ recs) = recs := by
  have hf1 : ∀ l : List (ConstantInfo .anon), (∀ ci ∈ l, isTypeOrCtor ci = true) →
      nonrecsOf l = l ∧ recsOf l = [] := by
    intro l hl
    induction l with
    | nil => exact ⟨rfl, rfl⟩
    | cons ci rest ih =>
      obtain ⟨ih1, ih2⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      have hci := hl ci List.mem_cons_self
      cases ci with
      | indInfo _ _ | ctorInfo _ _ _ => simp [nonrecsOf, recsOf, ih1, ih2]
      | _ => simp [isTypeOrCtor] at hci
  have hf2 : ∀ l : List (ConstantInfo .anon),
      (∀ ci ∈ l, ∃ cv mI rP rules, ci = .recInfo cv mI rP rules) →
      nonrecsOf l = [] ∧ recsOf l = l := by
    intro l hl
    induction l with
    | nil => exact ⟨rfl, rfl⟩
    | cons ci rest ih =>
      obtain ⟨ih1, ih2⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      obtain ⟨_, _, _, _, rfl⟩ := hl ci List.mem_cons_self
      simp [nonrecsOf, recsOf, ih1, ih2]
  obtain ⟨hn1, hr1⟩ := hf1 nonrecs h1
  obtain ⟨hn2, hr2⟩ := hf2 recs h2
  simp [nonrecsOf, recsOf, List.filter_append, hn1, hr1, hn2, hr2]

/-! ## Core Layer-2 assembly from `CheckFamilyChain` -/

/-- **Full Layer-2 facts from one heap-chained `KernelModeled::check_family` run**:
builds `(blk, advM, tys, rhsss)` once from the check's payload, advice, tables, three
`members_val` loops, `block_elim`, `family_refs_ok`, and `check_recs`, yielding:
1. `FamilyTysCanon` (store-free canonical loads);
2. `MajorRefs` (major-premise heads are references of `rb`);
3. `recRefs` (`UsedRef E₀ rb x → CoveredAt t lim x ∨ NeedOk E₀ x`);
4. at any `FamilyStepEnv` (with covered `.iPrj` logic safety):
   `FamDeclReads`, `FamilyCheckFacts`, and `FamRecsCompanion E₀`. -/
theorem familyCall_checked_of_chain
    {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    {B rb : _root_.Address} {cb crb : Ixon.Constant} {ms rs : Array Ixon.MutConst}
    {adv : _root_.Address → Prop}
    {rc xb xrb : SourceValue F} {h h' : Heap F}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    (hrc : Claim.RCLimRep t bAddr lim h rc) (hxb : S0.addr h xb B) (hxrb : S0.addr h xrb rb)
    (hsub : CallSub csFam calls)
    (C : CheckFamilyChain rc xb xrb h h' csFam)
    (hadvHyp : (∀ a, AdviceIn csFam a → adv a) ∨
      ∀ (advAs : List Bytes.Address),
        RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m423 advAs C.advList →
        ∀ a, AdviceListedIn advAs a →
          adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x)
    (hcidx : ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct → ct.cidx.toNat = j) :
    ∃ (blk : List (ConstantInfo .anon)) (advM : FamilyAdvice)
      (tys : List KExpr) (rhsss : List (List KExpr)),
      FamilyTysCanon t E₀ B cb ms rb crb rs blk tys rhsss ∧
      MajorRefs t E₀ rb blk tys ∧
      (∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x) ∧
      ∀ (E : Ixon.Env) (env : Ix.Kernel.Env .anon),
        FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env →
        (∀ x c p cbM, Claim.CoveredAt t lim x → recordOf E₀ x = some c → c.info = .iPrj p →
          recordOf E₀ p.block = some cbM → InLogic cbM) →
        FamDeclReads t E₀ B cb rb crb blk ∧
        FamilyCheckFacts env blk advM tys rhsss ∧
        FamRecsCompanion E₀ t env blk tys := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  obtain ⟨bB, hbB_rep, hbB_eq⟩ := hxb
  obtain ⟨bR, hbR_rep, hbR_eq⟩ := hxrb
  have ext_h_105 : Heap.Extends h C.m105 := Decl.check_family_seg1_inv C.sg112
  have ext_h_423 : Heap.Extends h C.m423 :=
    ext_h_105.trans (C.evReadPayload.extends.trans (C.evGetRb.extends.trans (C.evRbEq.extends.trans
      (C.evInOrder.extends.trans (C.evCountAdv.extends.trans (C.evGetAdv.extends.trans
        (C.evCountWit.extends.trans (C.evCheckWit.extends.trans
          (C.evWset.extends.trans C.evContRefs.extends)))))))))
  have ext_h_453 : Heap.Extends h C.m453 := ext_h_105.trans C.ext_m105_m453
  have ext_h_978 : Heap.Extends h C.m978 := ext_h_453.trans C.ext_m453_m978
  have ext_h_1293 : Heap.Extends h C.m1293 := ext_h_978.trans C.ext_m978_m1293
  -- 1. Payload stream & `advAs` at `C.m423`
  obtain ⟨-, b0, hs0⟩ := read_payload_stream C.evReadPayload.obs
  obtain ⟨_, _, _, x_s1', -, htup1, -, hs1, -, -⟩ := Decl.get_address_spec hs0 C.evGetRb.obs
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup1
  rw [← htup1.2] at hs1
  obtain ⟨b2, hs2⟩ :=
    get_count_stream ((hs1.mono C.evRbEq.extends).mono C.evInOrder.extends) C.evCountAdv.obs
  obtain ⟨_, advAs, b3, -, -, hadv254, hs3, -⟩ := Decl.get_addrs_spec hs2 C.evGetAdv.obs
  obtain ⟨b4, hs4⟩ := get_count_stream hs3 C.evCountWit.obs
  obtain ⟨b5, hs5⟩ := check_witnesses_stream hs4 C.evCheckWit.obs
  have hadv423 : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m423 advAs C.advList :=
    RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
      (C.evCountWit.extends.trans (C.evCheckWit.extends.trans
        (C.evWset.extends.trans C.evContRefs.extends))) hadv254
  have hadvCase : (∀ a, AdviceIn csFam a → adv a) ∨
      ∀ a, AdviceListedIn advAs a →
        adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x := by
    rcases hadvHyp with hIn | hList
    · exact Or.inl hIn
    · exact Or.inr (hList advAs hadv423)
  -- 2. Advice set `C.aset` from `check_advice_records_checked`
  have hrc423 : Claim.RCLimRep t bAddr lim C.m423 rc := hrc.mono ext_h_423
  obtain ⟨haset453_raw, -⟩ :=
    check_advice_records_checked advAs (fun _ => False) hrc423 hadv423
      AddrMapAll.nil C.evCheckAdv.obs
      (fun cl hcl => hsub cl (C.evCheckAdv.sub cl hcl))
  have haset453 : AddrMapAll addrMapEnum
      (fun _ b _ => AdvChecked calls bAddr t lim csFam advAs b) C.m453 C.aset :=
    addrMapAll_imp
      (fun _ _ _ h => (h.resolve_left id).mono C.evCheckAdv.sub (fun _ hx => hx))
      haset453_raw
  have haset978 : AddrMapAll addrMapEnum
      (fun _ b _ => AdvChecked calls bAddr t lim csFam advAs b) C.m978 C.aset :=
    AddrMapAll.mono (fun _ _ _ _ _ hx => hx) C.ext_m453_m978 haset453
  -- 3. Tables (`typeAs, ctorAs, recAs, typeMs, ctorMs, recMs`) + size bounds
  have hB' : FamBlockRecord E₀ (ixAddr bB) cb ms := by rwa [hbB_eq]
  have hR' : FamRecRecord E₀ (ixAddr bR) crb rs := by rwa [hbR_eq]
  have hbB453 : Bytes.RepAddressRef addrTy C.m453 bB xb :=
    Bytes.repAddressRef_heapMono₂ addrTy ext_h_453 hbB_rep
  have hbR453 : Bytes.RepAddressRef addrTy C.m453 bR xrb :=
    Bytes.repAddressRef_heapMono₂ addrTy ext_h_453 hbR_rep
  have hs5_453 : L1.Stream C.m453 b5 C.s5 :=
    hs5.mono (C.evWset.extends.trans (C.evContRefs.extends.trans C.evCheckAdv.extends))
  obtain ⟨typeAs, ctorAs, recAs, typeMs, ctorMs, recMs, T_raw, hnRecs_eq, b8, hs8_978⟩ :=
    family_tables hS hH hB' hR' hbB453 hbR453 hs5_453
      C.evLoadBlk.obs C.evLenMem.obs C.evIndcCnt.obs C.evNParams.obs
      C.evTypes.obs C.evTypeMods.obs C.evCtors.obs C.evLenCtors.obs C.evCtorMods.obs
      C.evRecs.obs C.evNoRole.obs C.evNoTypeRole.obs C.evLenRecs.obs C.evRecMods.obs
      C.evSrcTail.obs C.evSrc.obs C.evDstTail.obs C.evDst.obs
      (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))
      (fun cl hcl => hsub cl (C.evRecs.sub cl hcl))
      (bounded_sub (fun cl hcl => hsub cl (C.evCtors.sub cl hcl)) hbd)
  have T : FamilyTables B rb ms rs C.m978 typeAs ctorAs recAs typeMs ctorMs recMs
      C.tys C.ctors C.recs C.tyM C.ctorM C.recM C.src C.dst := by
    rw [hbB_eq, hbR_eq] at T_raw; exact T_raw
  -- Size bounds for `ms`, `ind.ctors`, `rs`
  have hms_lt8 : ms.size < 8589934592 := by
    obtain ⟨cb', ms', hbl, -⟩ := Claim.load_block_head hbB453 C.evLoadBlk.obs
    obtain ⟨hrec', -⟩ := (hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).stored hH
    have e1 : cb = cb' := Option.some.inj (hB'.record.symm.trans hrec')
    subst e1
    have hres : cb.resourceSize < 8589934592 :=
      ((hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).record hS hB'.record).2
    have hsz : ms.size ≤ cb.resourceSize := Claim.muts_size_le hB.muts
    omega
  have hms_u64 : ms.size < UInt64.size := by
    have : UInt64.size = 18446744073709551616 := rfl; omega
  have hct_u64 : ∀ ind, Ixon.MutConst.indc ind ∈ ms.toList → ind.ctors.size < UInt64.size := by
    intro ind hind
    obtain ⟨cb', ms', hbl, -⟩ := Claim.load_block_head hbB453 C.evLoadBlk.obs
    obtain ⟨hrec', -⟩ := (hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).stored hH
    have e1 : cb = cb' := Option.some.inj (hB'.record.symm.trans hrec')
    subst e1
    have hres : cb.resourceSize < 8589934592 :=
      ((hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).record hS hB'.record).2
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hind
    have hle := Claim.ctors_size_le hB.muts hi
    have : UInt64.size = 18446744073709551616 := rfl; omega
  have hrs_u64 : rs.size < UInt64.size := by
    have ext_453_784 : Heap.Extends C.m453 C.m784 :=
      C.evLoadBlk.extends.trans (C.evLenMem.extends.trans (C.evIndcCnt.extends.trans
        (C.evNParams.extends.trans (C.evTypes.extends.trans (C.evTypeMods.extends.trans
          (C.evCtors.extends.trans (C.evLenCtors.extends.trans C.evCtorMods.extends)))))))
    have hlt := family_recs_bound hS hH
      (Bytes.repAddressRef_heapMono₂ addrTy ext_453_784 hbR453) C.evRecs.obs
      (fun cl hcl => hsub cl (C.evRecs.sub cl hcl)) hR'
    have : UInt64.size = 18446744073709551616 := rfl; omega
  -- 4. `family_recRefs` and `assert_no_role`
  have ext_h_refs : Heap.Extends h C.mRefs :=
    ext_h_978.trans (C.evTysVal.extends.trans (C.evLater.extends.trans (C.evCtorsVal.extends.trans
      (C.evRecsVal.extends.trans (C.evBlockElim.extends.trans C.extAfterElim)))))
  have hrecRefs : ∀ x, UsedRef E₀ rb x → Claim.CoveredAt t lim x ∨ NeedOk E₀ x :=
    family_recRefs hS hH hR (hrc.mono ext_h_refs)
      ⟨bR, Bytes.repAddressRef_heapMono₂ addrTy ext_h_refs hbR_rep, hbR_eq⟩
      C.evRefsOk.obs (fun cl hcl => hsub cl (C.evRefsOk.sub cl hcl))
  have hnoRoleRecs : ∀ a ∈ recAs, ∀ ro : Ix.Kernel.Role, Core.keyOf t (ixAddr a) ≠ .role ro := by
    have ext_h_840 : Heap.Extends h C.m840 :=
      ext_h_453.trans (C.evLoadBlk.extends.trans (C.evLenMem.extends.trans (C.evIndcCnt.extends.trans
        (C.evNParams.extends.trans (C.evTypes.extends.trans (C.evTypeMods.extends.trans
          (C.evCtors.extends.trans (C.evLenCtors.extends.trans (C.evCtorMods.extends.trans
            C.evRecs.extends)))))))))
    have hrA840 : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m840 recAs C.recs := by
      have ext_453_784 : Heap.Extends C.m453 C.m784 :=
        C.evLoadBlk.extends.trans (C.evLenMem.extends.trans (C.evIndcCnt.extends.trans
          (C.evNParams.extends.trans (C.evTypes.extends.trans (C.evTypeMods.extends.trans
            (C.evCtors.extends.trans (C.evLenCtors.extends.trans C.evCtorMods.extends)))))))
      obtain ⟨recAs', hrA', hrmap'⟩ := family_recs_list hH
        (Bytes.repAddressRef_heapMono₂ addrTy ext_453_784 hbR453) C.evRecs.obs
        (fun cl hcl => hsub cl (C.evRecs.sub cl hcl)) hR'
      have ext_840_978 : Heap.Extends C.m840 C.m978 :=
        C.evNoRole.extends.trans (C.evNoTypeRole.extends.trans (C.evLenRecs.extends.trans
          (C.evRecMods.extends.trans (C.evSrcTail.extends.trans (C.evSrc.extends.trans
            (C.evDstTail.extends.trans C.evDst.extends))))))
      have heq_recAs : recAs' = recAs := by
        have hrA978 := RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_840_978 hrA'
        exact repList_det (R := Bytes.RepAddressRef addrTy) (fun _ _ _ _ r1 r2 => addr_det r1 r2)
          hrA978 T.recsRep
      subst heq_recAs
      exact hrA'
    exact assert_no_role_spec recAs (hrc.mono ext_h_840) hrA840 C.evNoRole.obs
  -- 5. Table list associations (`srcAs`, `dstAs`, `srcKeys`, `dstKeys`, `Nodup`, `aliasMap`)
  let srcAs : List Bytes.Address := typeAs ++ ctorAs ++ recAs
  let dstAs : List Bytes.Address := typeMs ++ ctorMs ++ recMs
  let srcKeys : List KKey := srcAs.map fun b => Core.keyOf t (ixAddr b)
  let dstKeys : List KKey := dstAs.map fun b => Core.keyOf t (ixAddr b)
  let g : KKey → KKey := aliasMap (srcKeys.zip dstKeys)
  have hsrc_assoc : typeAs ++ (ctorAs ++ recAs) = srcAs := (List.append_assoc _ _ _).symm
  have hdst_assoc : typeMs ++ (ctorMs ++ recMs) = dstAs := (List.append_assoc _ _ _).symm
  have hsrcRep978 : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m978 srcAs C.src := by
    rw [← hsrc_assoc]; exact T.srcRep
  have hdstRep978 : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m978 dstAs C.dst := by
    rw [← hdst_assoc]; exact T.dstRep
  have hlenSD : srcAs.length = dstAs.length := by
    rw [← hsrc_assoc, ← hdst_assoc]; exact T.length_eq
  have hlenSD_keys : srcKeys.length = dstKeys.length := by
    simp only [srcKeys, dstKeys, List.length_map, hlenSD]
  have hsrc_nodup_addr : (srcAs.map ixAddr).Nodup := by
    rw [← hsrc_assoc]; exact srcAddrs_nodup hB hR hms_u64 hct_u64 hrs_u64 T
  have hsrcKeys_nodup : srcKeys.Nodup := by
    have hmap : srcKeys = (srcAs.map ixAddr).map (Core.keyOf t) := by
      simp [srcKeys, List.map_map, Function.comp_def]
    rw [hmap]
    exact hsrc_nodup_addr.map (fun _ _ h => Core.keyOf_inj htwf h)
  have hg_at : ∀ (pos : Nat) (hpos : pos < srcAs.length),
      g (Core.keyOf t (ixAddr srcAs[pos])) =
        Core.keyOf t (ixAddr (dstAs[pos]'(hlenSD ▸ hpos))) := by
    intro pos hpos
    have hposK : pos < srcKeys.length := by simpa [srcKeys] using hpos
    have h1 := aliasMap_zip_getElem hsrcKeys_nodup hlenSD_keys pos hposK
    simpa [g, srcKeys, dstKeys] using h1
  -- Length facts for `typeAs`, `ctorAs`, `recAs`
  have hlen_types : typeAs.length = ms.size := by
    have h := congrArg List.length T.types
    simpa only [List.length_map, List.length_mapIdx, Array.length_toList] using h
  let slots := ctorSlotsFrom ms.toList 0
  have hctors_slots : ctorAs.map ixAddr = slots.map (fun s => cprjAddr B s.1 s.2.2.1) := by
    rw [T.ctors, ctorSlotsFrom_addrs]
  have hlen_ctors : ctorAs.length = slots.length := by
    have h := congrArg List.length hctors_slots
    simpa only [List.length_map] using h
  have hlen_recs : recAs.length = rs.size := by
    have h := congrArg List.length T.recs
    simpa only [List.length_map, List.length_mapIdx, Array.length_toList] using h
  -- 6. Walk all three `members_val` loops (`evTysVal`, `evCtorsVal`, `evRecsVal`)
  have hTysItems :=
    membersVal_walk ht hbd hS hH typeAs typeMs T.typeModels.symm
      (fun cl hcl => hsub cl (C.evTysVal.sub cl hcl))
      T.typesRep T.typeModelsRep hsrcRep978 hdstRep978 haset978 hsrcRep978 C.evTysVal.obs
  have ext_978_later : Heap.Extends C.m978 C.mLater :=
    C.evTysVal.extends.trans C.evLater.extends
  have hLaterRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.mLater
      (ctorAs ++ recAs) C.later :=
    Decl.addrList_concat_spec
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) C.evTysVal.extends T.ctorsRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) C.evTysVal.extends T.recsRep)
      C.evLater.obs
  have hCtorsItems :=
    membersVal_walk ht hbd hS hH ctorAs ctorMs T.ctorModels.symm
      (fun cl hcl => hsub cl (C.evCtorsVal.sub cl hcl))
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_later T.ctorsRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_later T.ctorModelsRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_later hsrcRep978)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_later hdstRep978)
      (AddrMapAll.mono (fun _ _ _ _ _ hx => hx) ext_978_later haset978)
      hLaterRep C.evCtorsVal.obs
  have ext_978_ctorsV : Heap.Extends C.m978 C.mCtorsVal :=
    ext_978_later.trans C.evCtorsVal.extends
  have hRecsItems :=
    membersVal_walk ht hbd hS hH recAs recMs T.recModels.symm
      (fun cl hcl => hsub cl (C.evRecsVal.sub cl hcl))
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_ctorsV T.recsRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_ctorsV T.recModelsRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_ctorsV hsrcRep978)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_ctorsV hdstRep978)
      (AddrMapAll.mono (fun _ _ _ _ _ hx => hx) ext_978_ctorsV haset978)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_ctorsV T.recsRep)
      C.evRecsVal.obs
  -- 7. Extract concrete `IndMemberData` for each `i < ms.size` and `CtorMemberData` for each `idx < slots.length`
  have hIndAt : ∀ (i : Fin ms.size),
      ∃ ind : Ixon.Inductive, ms[i.val]? = some (.indc ind) := fun i => by
    have hm : ms[i.val]? = some ms[i.val] := Array.getElem?_eq_getElem i.isLt
    obtain ⟨ind, hind⟩ := hB.indcs ms[i.val] (Array.mem_toList_iff.mpr (Array.getElem_mem i.isLt))
    exact ⟨ind, by rwa [hind] at hm⟩
  let indOf (i : Fin ms.size) : Ixon.Inductive := (hIndAt i).choose
  have hms_indOf (i : Fin ms.size) : ms[i.val]? = some (.indc (indOf i)) := (hIndAt i).choose_spec
  have htypeAs_i : ∀ (i : Fin ms.size),
      ixAddr (typeAs[i.val]'(by omega)) = iprjAddr B i.val := fun i => by
    have hget : (typeAs.map ixAddr)[i.val]? = some (ixAddr (typeAs[i.val]'(by omega))) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]; rfl
    rw [T.types, List.getElem?_mapIdx, Array.getElem?_toList, hms_indOf i] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    rw [← hget, ← LoadedReads.memberAddr_eq_projAddr, LoadedReads.memberAddr_indc]
  have hgt_i : ∀ (i : Fin ms.size),
      g (Core.keyOf t (iprjAddr B i.val)) =
        Core.keyOf t (ixAddr (typeMs[i.val]'(by rw [T.typeModels, hlen_types]; exact i.isLt))) := fun i => by
    have hlt_src : i.val < srcAs.length := by simp only [srcAs, List.length_append]; omega
    have h1 := hg_at i.val hlt_src
    have hs_eq : srcAs[i.val]'hlt_src = typeAs[i.val]'(by omega) := by
      simp only [srcAs, List.append_assoc, List.getElem_append_left (show i.val < typeAs.length by omega)]
    have hd_eq : dstAs[i.val]'(by omega) =
        typeMs[i.val]'(by rw [T.typeModels, hlen_types]; exact i.isLt) := by
      simp only [dstAs, List.append_assoc,
        List.getElem_append_left (show i.val < typeMs.length by rw [T.typeModels, hlen_types]; exact i.isLt)]
    rw [hs_eq, htypeAs_i i, hd_eq] at h1
    exact h1
  let indData (i : Fin ms.size) :
      IndMemberData calls bAddr t E₀ lim csFam B cb ms advAs srcAs dstAs i.val (indOf i)
        (typeMs[i.val]'(by rw [T.typeModels, hlen_types]; exact i.isLt)) :=
    Classical.choice (indMember_of_item ht hbd hS hB hlenSD
      (Nat.lt_trans i.isLt hms_u64) (hms_indOf i) (htypeAs_i i) (hgt_i i)
      (Classical.choice (hTysItems i.val (by omega))))
  let indBlk : List (ConstantInfo .anon) :=
    (List.finRange ms.size).map fun i =>
      .indInfo ⟨Core.keyOf t (iprjAddr B i.val), List.range (indOf i).lvls.toNat, (indData i).ty₀⟩ {}
  let indTys : List KExpr := (List.finRange ms.size).map fun i => (indData i).tyA
  -- Constructors
  have hslot_ok : ∀ (p : Fin slots.length),
      let s := slots[p.val]
      ms[s.1]? = some (.indc s.2.1) ∧ s.2.1.ctors[s.2.2.1]? = some s.2.2.2 := fun p => by
    obtain ⟨k, hk, hmk, hct⟩ := ctorSlotsFrom_get 0 (List.getElem_mem p.isLt)
    rw [Nat.zero_add] at hk
    rw [← hk, Array.getElem?_toList] at hmk
    exact ⟨hmk, hct⟩
  have hctorAs_p : ∀ (p : Fin slots.length),
      ixAddr (ctorAs[p.val]'(by omega)) =
        cprjAddr B slots[p.val].1 slots[p.val].2.2.1 := fun p => by
    have hget : (ctorAs.map ixAddr)[p.val]? = some (ixAddr (ctorAs[p.val]'(by omega))) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hctors_slots, List.getElem?_map, List.getElem?_eq_getElem p.isLt] at hget
    exact (Option.some.inj hget).symm
  have hgc_p : ∀ (p : Fin slots.length),
      g (Core.keyOf t (cprjAddr B slots[p.val].1 slots[p.val].2.2.1)) =
        Core.keyOf t (ixAddr (ctorMs[p.val]'(by rw [T.ctorModels, hlen_ctors]; exact p.isLt))) := fun p => by
    have hpos_lt : typeAs.length + p.val < srcAs.length := by
      simp only [srcAs, List.length_append]; omega
    have h1 := hg_at (typeAs.length + p.val) hpos_lt
    have hs_eq : srcAs[typeAs.length + p.val]'hpos_lt = ctorAs[p.val]'(by omega) := by
      simp only [srcAs, List.append_assoc,
        List.getElem_append_right (Nat.le_add_right typeAs.length p.val),
        Nat.add_sub_cancel_left,
        List.getElem_append_left (show p.val < ctorAs.length by omega)]
    have hd_eq : dstAs[typeAs.length + p.val]'(by omega) =
        ctorMs[p.val]'(by rw [T.ctorModels, hlen_ctors]; exact p.isLt) := by
      have htm : typeMs.length = typeAs.length := T.typeModels
      simp only [dstAs, List.append_assoc,
        List.getElem_append_right (show typeMs.length ≤ typeAs.length + p.val by omega),
        show typeAs.length + p.val - typeMs.length = p.val by omega,
        List.getElem_append_left (show p.val < ctorMs.length by rw [T.ctorModels, hlen_ctors]; exact p.isLt)]
    rw [hs_eq, hctorAs_p p, hd_eq] at h1
    exact h1
  let ctorData (p : Fin slots.length) :
      CtorMemberData calls bAddr t E₀ lim csFam B cb ms advAs srcAs dstAs (ctorAs ++ recAs)
        slots[p.val].1 slots[p.val].2.1 slots[p.val].2.2.1 slots[p.val].2.2.2
        (ctorMs[p.val]'(by rw [T.ctorModels, hlen_ctors]; exact p.isLt)) :=
    Classical.choice (ctorMember_of_item ht hbd hS hB hlenSD
      (Nat.lt_trans (Array.getElem?_eq_some_iff.mp (hslot_ok p).1).1 hms_u64)
      (Nat.lt_trans (Array.getElem?_eq_some_iff.mp (hslot_ok p).2).1
        (hct_u64 slots[p.val].2.1
          (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact (hslot_ok p).1))))
      (hslot_ok p).1 (hslot_ok p).2 (hctorAs_p p) (hgc_p p)
      (Classical.choice (hCtorsItems p.val (by omega))))
  let ctorBlk : List (ConstantInfo .anon) :=
    (List.finRange slots.length).map fun p =>
      .ctorInfo ⟨Core.keyOf t (cprjAddr B slots[p.val].1 slots[p.val].2.2.1),
          List.range slots[p.val].2.2.2.lvls.toNat, (ctorData p).ty₀⟩
        slots[p.val].2.2.2.params.toNat slots[p.val].2.2.2.fields.toNat
  let ctorTys : List KExpr := (List.finRange slots.length).map fun p => (ctorData p).tyA
  let nonrecsBlk : List (ConstantInfo .anon) := indBlk ++ ctorBlk
  let nonrecsTys : List KExpr := indTys ++ ctorTys
  have hlen_indB : indBlk.length = ms.size := by simp [indBlk]
  have hlen_indT : indTys.length = ms.size := by simp [indTys]
  have hlen_ctorB : ctorBlk.length = slots.length := by simp [ctorBlk]
  have hlen_ctorT : ctorTys.length = slots.length := by simp [ctorTys]
  have hlenNR : nonrecsBlk.length = nonrecsTys.length := by
    simp only [nonrecsBlk, nonrecsTys, List.length_append, hlen_indB, hlen_indT,
      hlen_ctorB, hlen_ctorT]
  -- 8. `CtorLookupFn` on `(nonrecsBlk, nonrecsTys)`
  have hctorLookup : CtorLookupFn calls bAddr t E₀ lim csFam B rb cb crb ms advAs srcAs dstAs
      nonrecsBlk nonrecsTys := by
    intro im j ind ct hmi hct
    have hmem_slot : (im, ind, j, ct) ∈ slots := by
      have h1 := ctorSlotsFrom_mem_of_getElem? ms.toList 0 im ind j ct
        (by rw [Array.getElem?_toList]; exact hmi) hct
      simpa using h1
    obtain ⟨p_nat, hp_get⟩ := List.mem_iff_getElem?.mp hmem_slot
    have hp_lt : p_nat < slots.length := (List.getElem?_eq_some_iff.mp hp_get).1
    let p : Fin slots.length := ⟨p_nat, hp_lt⟩
    have hsp_eq : slots[p.val] = (im, ind, j, ct) :=
      Option.some.inj ((List.getElem?_eq_getElem hp_lt).symm.trans hp_get)
    have him_eq : slots[p.val].1 = im := congrArg Prod.fst hsp_eq
    have hind_eq : slots[p.val].2.1 = ind := congrArg (fun x => x.2.1) hsp_eq
    have hj_eq : slots[p.val].2.2.1 = j := congrArg (fun x => x.2.2.1) hsp_eq
    have hct_eq : slots[p.val].2.2.2 = ct := congrArg (fun x => x.2.2.2) hsp_eq
    refine ⟨indBlk.length + p.val, (ctorData p).ty₀, (ctorData p).tyA,
      by simp only [nonrecsBlk, List.length_append, hlen_ctorB]; omega, ?_, ?_,
      by rw [← hct_eq]; exact (ctorData p).hread,
      (ctorData p).hlbb,
      by rw [← hct_eq]; exact (ctorData p).hdef,
      by rw [← him_eq, ← hj_eq, ← hct_eq]; exact (ctorData p).hcanon,
      by rw [← hct_eq]; exact (ctorData p).hA_def, ?_⟩
    · simp only [nonrecsBlk]
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      simp only [ctorBlk, List.getElem?_map, getElem?_finRange_eq p.isLt, Option.map_some,
        him_eq, hj_eq, hct_eq]
    · simp only [nonrecsTys]
      rw [List.getElem?_append_right (by omega),
        show indBlk.length + p.val - indTys.length = p.val by omega]
      simp only [ctorTys, List.getElem?_map, getElem?_finRange_eq p.isLt, Option.map_some]
    · intro L' adv' E' env' hSE' hadvH' hdefSrc'
      have haMd_adv : adv' (ixAddr (ctorMs[p.val]'(by rw [T.ctorModels, hlen_ctors]; exact p.isLt))) :=
        adv_of_advChecked (ctorData p).hitem.hAdv (ctorData p).hitem.hrecM
          (ctorData p).hitem.hcaM hadvH'
      obtain ⟨hnp, hmf⟩ := (ctorData p).hfacts hSE' haMd_adv hdefSrc'
      refine ⟨hnp, fun ci_gc hfind_gc => ?_⟩
      obtain ⟨cvm, mval, hint, hfind_m, hperm_m, -⟩ := hmf.model
      have hfind_m' : env'.find? (g (Core.keyOf t (cprjAddr B im j))) =
          some (.defnInfo cvm mval hint) := by
        simpa [g, srcKeys, dstKeys, him_eq, hj_eq, ConstantInfo.name, ConstantInfo.toConstantVal] using hfind_m
      have hci_eq : ci_gc = .defnInfo cvm mval hint :=
        Option.some.inj (hfind_gc.symm.trans hfind_m')
      have hlen_p := hperm_m.length_eq
      simp only [ConstantInfo.toConstantVal, List.length_range] at hlen_p
      rw [hci_eq, ConstantInfo.toConstantVal, hlen_p, hct_eq]
  -- 9. `block_elim_spec` and `checkRecs_walk`
  have ext_978_recsV : Heap.Extends C.m978 C.mRecsVal :=
    ext_978_ctorsV.trans C.evRecsVal.extends
  obtain ⟨a0, restTypeAs, ind0, htypeAs_cons, ha0_eq, hms0, hind0_lvls_lt, hbnl_eq, huo⟩ :=
    block_elim_spec hbd hS hB hms_u64 (fun cl hcl => hsub cl (C.evBlockElim.sub cl hcl))
      T.types (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext_978_recsV T.typesRep)
      C.evBlockElim.obs
  have hrecItems_f2 : List.Forall₂ (fun aM aMd =>
      Nonempty (MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs recAs aM aMd))
      recAs recMs :=
    List.forall₂_iff_get.mpr ⟨T.recModels.symm, fun idx h1 _ => hRecsItems idx h1⟩
  have hrecAs_k : ∀ idx (hi : idx < recAs.length), ixAddr recAs[idx] = rprjAddr rb (0 + idx) := by
    intro idx hi
    have hget : (recAs.map ixAddr)[idx]? = some (ixAddr recAs[idx]) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
    have hr_lt : idx < rs.size := hlen_recs ▸ hi
    have hget_rs : rs[idx]? = some rs[idx] := Array.getElem?_eq_getElem hr_lt
    obtain ⟨rc_i, hrc_i⟩ := hR.recrs rs[idx] (Array.mem_toList_iff.mpr (Array.getElem_mem hr_lt))
    rw [T.recs, List.getElem?_mapIdx, Array.getElem?_toList, hget_rs, hrc_i] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    rw [← hget, ← LoadedReads.memberAddr_eq_projAddr, LoadedReads.memberAddr_recr, Nat.zero_add]
  have hgr_k : ∀ idx (hi : idx < recAs.length),
      g (Core.keyOf t (rprjAddr rb (0 + idx))) =
        Core.keyOf t (ixAddr (recMs[idx]'(by rw [T.recModels]; exact hi))) := by
    intro idx hi
    have hpos_lt : (typeAs.length + ctorAs.length) + idx < srcAs.length := by
      simp only [srcAs, List.length_append]; omega
    have h1 := hg_at ((typeAs.length + ctorAs.length) + idx) hpos_lt
    have hs_eq : srcAs[(typeAs.length + ctorAs.length) + idx]'hpos_lt = recAs[idx]'hi := by
      have hle : (typeAs ++ ctorAs).length ≤ (typeAs.length + ctorAs.length) + idx := by
        simp only [List.length_append]; omega
      have hsub : (typeAs.length + ctorAs.length) + idx - (typeAs ++ ctorAs).length = idx := by
        simp only [List.length_append]; omega
      simp only [srcAs, List.getElem_append_right hle, hsub]
    have hd_eq : dstAs[(typeAs.length + ctorAs.length) + idx]'(by omega) =
        recMs[idx]'(by rw [T.recModels]; exact hi) := by
      have hlen_tc : (typeMs ++ ctorMs).length = typeAs.length + ctorAs.length := by
        simp only [List.length_append, T.typeModels, T.ctorModels]
      have hle : (typeMs ++ ctorMs).length ≤ (typeAs.length + ctorAs.length) + idx := by omega
      have hsub : (typeAs.length + ctorAs.length) + idx - (typeMs ++ ctorMs).length = idx := by omega
      simp only [dstAs, List.getElem_append_right hle, hsub]
    rw [hs_eq, hrecAs_k idx hi, hd_eq] at h1
    exact h1
  have hrecMs_sub : ∀ b ∈ recMs, b ∈ dstAs := fun b hb => by
    simp only [dstAs, List.mem_append]; exact Or.inr hb
  have evCheckRecs' : ObsFn Obs.W "KernelModeled::check_recs"
      [rc, C.tys, C.recs, C.recM, C.src, C.dst, C.aset, C.s8, C.nRecs, .field ((0 : Nat) : F),
        C.np, C.uo, C.bnl, C.recs, .field 0] C.m1293 C.s9 h' C.evCheckRecs.cs := by
    rw [Nat.cast_zero]; exact C.evCheckRecs.obs
  obtain ⟨recsBlk, recsTys, rhsss, thmsList, hlen_rB, hlen_rT, hlen_rh, hlen_th, hRecAt0⟩ :=
    checkRecs_walk ht hbd hS hH hB hR T.types T.ctors T.recs hlenSD hlenNR hctorLookup hrecRefs
      htypeAs_cons ha0_eq hms0 hind0_lvls_lt hrs_u64 hbnl_eq huo
      0 recAs recMs (by omega) T.recModels.symm hrecAs_k hgr_k hrecMs_sub hrecItems_f2
      (fun cl hcl => hsub cl (C.evCheckRecs.sub cl hcl))
      (rcRep_of_rcLimRep (hrc.mono ext_h_1293))
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) C.ext_m978_m1293 T.typesRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) C.ext_m978_m1293 T.recsRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) C.ext_m978_m1293 T.recModelsRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) C.ext_m978_m1293 hsrcRep978)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) C.ext_m978_m1293 hdstRep978)
      (AddrMapAll.mono (fun _ _ _ _ _ hx => hx) C.ext_m978_m1293 haset978)
      (hs8_978.mono C.ext_m978_m1293) evCheckRecs'
  have hRecAt : ∀ idx (hi : idx < recAs.length),
      ∃ (rc : Ixon.Recursor)
        (D : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
          srcAs dstAs recAs nonrecsBlk nonrecsTys idx rc recAs[idx]
          (recMs[idx]'(by rw [T.recModels]; exact hi))),
        rs[idx]? = some (.recr rc) ∧
        recsBlk[idx]? = some D.recInfo ∧
        recsTys[idx]? = some D.tyA ∧
        rhsss[idx]? = some D.rhss ∧
        thmsList[idx]? = some D.thms := by
    intro idx hi
    obtain ⟨rc, D0, hrk, hb, ht', hrh, hth⟩ := hRecAt0 idx hi
    have hcast : ∀ {k1 k2 : Nat}, k1 = k2 →
        ∀ {nb nt} (D1 : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
            srcAs dstAs recAs nb nt k1 rc recAs[idx] (recMs[idx]'(by rw [T.recModels]; exact hi))),
          rs[k1]? = some (.recr rc) → recsBlk[idx]? = some D1.recInfo →
          recsTys[idx]? = some D1.tyA → rhsss[idx]? = some D1.rhss → thmsList[idx]? = some D1.thms →
          ∃ (D2 : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
              srcAs dstAs recAs nb nt k2 rc recAs[idx] (recMs[idx]'(by rw [T.recModels]; exact hi))),
            rs[k2]? = some (.recr rc) ∧ recsBlk[idx]? = some D2.recInfo ∧
            recsTys[idx]? = some D2.tyA ∧ rhsss[idx]? = some D2.rhss ∧ thmsList[idx]? = some D2.thms := by
      rintro k1 _ rfl nb nt D1 h1 h2 h3 h4 h5; exact ⟨D1, h1, h2, h3, h4, h5⟩
    obtain ⟨D, h1, h2, h3, h4, h5⟩ := hcast (Nat.zero_add idx) D0 hrk hb ht' hrh hth
    exact ⟨rc, D, h1, h2, h3, h4, h5⟩
  -- 10. Assemble `blk`, `advM`, `tys`, `rhsss` and their structural identities
  let blk : List (ConstantInfo .anon) := nonrecsBlk ++ recsBlk
  let tys : List KExpr := nonrecsTys ++ recsTys
  let advM : FamilyAdvice := ⟨srcKeys.zip dstKeys, thmsList⟩
  have hindBlk_names : indBlk.map (·.name) = typeAs.map (fun b => Core.keyOf t (ixAddr b)) := by
    apply List.ext_getElem (by simp [indBlk, hlen_types])
    intro idx h1 h2
    simp only [indBlk, List.getElem_map, List.getElem_finRange]
    exact congrArg (Core.keyOf t) (htypeAs_i ⟨idx, by simpa [indBlk] using h1⟩).symm
  have hctorBlk_names : ctorBlk.map (·.name) = ctorAs.map (fun b => Core.keyOf t (ixAddr b)) := by
    apply List.ext_getElem (by simp [ctorBlk, hlen_ctors])
    intro idx h1 h2
    simp only [ctorBlk, List.getElem_map, List.getElem_finRange]
    exact congrArg (Core.keyOf t) (hctorAs_p ⟨idx, by simpa [ctorBlk] using h1⟩).symm
  have hrecsBlk_names : recsBlk.map (·.name) = recAs.map (fun b => Core.keyOf t (ixAddr b)) := by
    apply List.ext_getElem (by simp [hlen_rB])
    intro idx h1 h2
    have hi : idx < recAs.length := by simpa [hlen_rB] using h1
    obtain ⟨rc_i, D_i, -, hb_i, -, -, -⟩ := hRecAt idx hi
    have hget : recsBlk[idx]'(by omega) = D_i.recInfo :=
      Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hb_i)
    simp only [List.getElem_map, hget, RecMemberData.recInfo, ConstantInfo.name,
      ConstantInfo.toConstantVal]
    have ha := hrecAs_k idx hi
    rw [Nat.zero_add] at ha
    rw [ha]
  have hblk_names : blk.map (·.name) = srcKeys := by
    simp only [blk, nonrecsBlk, srcKeys, srcAs, List.map_append,
      hindBlk_names, hctorBlk_names, hrecsBlk_names]
  have hblk_nodup : (blk.map (·.name)).Nodup := by rw [hblk_names]; exact hsrcKeys_nodup
  have hnonrecs_kind : ∀ ci ∈ nonrecsBlk, isTypeOrCtor ci = true := by
    intro ci hci
    rcases List.mem_append.mp hci with h1 | h2
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h1; rfl
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp h2; rfl
  have hrecs_kind : ∀ ci ∈ recsBlk, ∃ cv mI rP rules, ci = .recInfo cv mI rP rules := by
    intro ci hci
    obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hci
    have hi : idx < recAs.length := by
      have := (List.getElem?_eq_some_iff.mp hidx).1; omega
    obtain ⟨rc_i, D_i, -, hb_i, -, -, -⟩ := hRecAt idx hi
    have hci_eq : ci = D_i.recInfo := Option.some.inj (hidx.symm.trans hb_i)
    rw [hci_eq]
    exact ⟨_, _, _, _, rfl⟩
  obtain ⟨hnonrecs_eq, hrecs_eq⟩ := nonrecsOf_append_recs hnonrecs_kind hrecs_kind
  -- 11. `FamilyTysCanon` (store-free)
  have hcanon : FamilyTysCanon t E₀ B cb ms rb crb rs blk tys rhsss := by
    refine ⟨?_, ?_, ?_⟩
    · -- `.ind`
      intro k ci tyA hk htyA i ind ty₀ hi_u64 hmi hname hread
      rw [hnonrecs_eq] at hk
      have hkt_lt : k < nonrecsBlk.length := (List.getElem?_eq_some_iff.mp hk).1
      rcases Nat.lt_or_ge k indBlk.length with hlt | hge
      · rw [List.getElem?_append_left hlt] at hk
        rw [List.getElem?_append_left (by simp only [nonrecsTys, List.length_append]; omega),
          List.getElem?_append_left (by omega)] at htyA
        have hk_ms : k < ms.size := by omega
        let kf : Fin ms.size := ⟨k, hk_ms⟩
        simp only [indBlk, List.getElem?_map, getElem?_finRange_eq hk_ms, Option.map_some,
          Option.some.injEq] at hk
        simp only [indTys, List.getElem?_map, getElem?_finRange_eq hk_ms, Option.map_some,
          Option.some.injEq] at htyA
        subst hk; subst htyA
        have haddr_eq : iprjAddr B k = iprjAddr B i := Core.keyOf_inj htwf hname
        have hrec_k : recordOf E₀ (iprjAddr B k) = some (memberProjection B k (.indc (indOf kf))) := by
          rw [← LoadedReads.memberAddr_indc]; exact hB.members k (.indc (indOf kf)) (hms_indOf kf)
        have hrec_i : recordOf E₀ (iprjAddr B i) = some (memberProjection B i (.indc ind)) := by
          rw [← LoadedReads.memberAddr_indc]; exact hB.members i (.indc ind) hmi
        rw [haddr_eq] at hrec_k
        have hinfo_eq := congrArg Ixon.Constant.info (Option.some.inj (hrec_k.symm.trans hrec_i))
        simp only [memberProjection, Ixon.ConstantInfo.iPrj.injEq,
          Ixon.InductiveProj.mk.injEq] at hinfo_eq
        have hk_eq_i : k = i := by
          rw [← toNat_toUInt64_lt_cr (Nat.lt_trans hk_ms hms_u64),
            ← toNat_toUInt64_lt_cr hi_u64, hinfo_eq.1]
        subst hk_eq_i
        have hind_eq : indOf kf = ind :=
          Ixon.MutConst.indc.inj (Option.some.inj ((hms_indOf kf).symm.trans hmi))
        subst hind_eq
        have hty0_eq : ty₀ = (indData kf).ty₀ :=
          Except.ok.inj (hread.symm.trans (indData kf).hread)
        subst hty0_eq
        exact ⟨(indData kf).hlbb, (indData kf).hdef, (indData kf).hcanon⟩
      · -- `k ≥ indBlk.length` means `ci` is a constructor (`.cPrj`), contradicting `ci.name = keyOf t (iprjAddr B i)`.
        rw [List.getElem?_append_right hge] at hk
        have hp_lt : k - indBlk.length < slots.length := by
          have := (List.getElem?_eq_some_iff.mp hk).1; omega
        let pf : Fin slots.length := ⟨k - indBlk.length, hp_lt⟩
        simp only [ctorBlk, List.getElem?_map, getElem?_finRange_eq hp_lt, Option.map_some,
          Option.some.injEq] at hk
        subst hk
        have haddr_eq : cprjAddr B slots[pf.val].1 slots[pf.val].2.2.1 = iprjAddr B i :=
          Core.keyOf_inj htwf hname
        have hrec_c : recordOf E₀ (cprjAddr B slots[pf.val].1 slots[pf.val].2.2.1) =
            some (constructorProjection B slots[pf.val].1 slots[pf.val].2.2.1) := by
          rw [← LoadedReads.ctorAddr_eq_cprjAddr]
          exact hB.ctors _ _ _ (hslot_ok pf).1 (Array.getElem?_eq_some_iff.mp (hslot_ok pf).2).1
        have hrec_i : recordOf E₀ (iprjAddr B i) = some (memberProjection B i (.indc ind)) := by
          rw [← LoadedReads.memberAddr_indc]; exact hB.members i (.indc ind) hmi
        rw [haddr_eq] at hrec_c
        have hinfo_eq := congrArg Ixon.Constant.info (Option.some.inj (hrec_c.symm.trans hrec_i))
        cases hinfo_eq
    · -- `.ctor`
      intro k ci tyA hk htyA i ind j ct ty₀ hi_u64 hj_u64 hmi hct hname hread
      rw [hnonrecs_eq] at hk
      rcases Nat.lt_or_ge k indBlk.length with hlt | hge
      · rw [List.getElem?_append_left hlt] at hk
        have hk_ms : k < ms.size := by omega
        let kf : Fin ms.size := ⟨k, hk_ms⟩
        simp only [indBlk, List.getElem?_map, getElem?_finRange_eq hk_ms, Option.map_some,
          Option.some.injEq] at hk
        subst hk
        have haddr_eq : iprjAddr B k = cprjAddr B i j := Core.keyOf_inj htwf hname
        have hrec_i : recordOf E₀ (iprjAddr B k) = some (memberProjection B k (.indc (indOf kf))) := by
          rw [← LoadedReads.memberAddr_indc]; exact hB.members k (.indc (indOf kf)) (hms_indOf kf)
        have hrec_c : recordOf E₀ (cprjAddr B i j) = some (constructorProjection B i j) := by
          rw [← LoadedReads.ctorAddr_eq_cprjAddr]
          exact hB.ctors i ind j hmi (Array.getElem?_eq_some_iff.mp hct).1
        rw [haddr_eq] at hrec_i
        have hinfo_eq := congrArg Ixon.Constant.info (Option.some.inj (hrec_i.symm.trans hrec_c))
        cases hinfo_eq
      · rw [List.getElem?_append_right hge] at hk
        have hp_lt : k - indBlk.length < slots.length := by
          have := (List.getElem?_eq_some_iff.mp hk).1; omega
        let pf : Fin slots.length := ⟨k - indBlk.length, hp_lt⟩
        rw [List.getElem?_append_left (by simp only [nonrecsTys, List.length_append]; omega)] at htyA
        rw [List.getElem?_append_right (by omega)] at htyA
        have hsub_eq : k - indTys.length = k - indBlk.length := by omega
        rw [hsub_eq] at htyA
        simp only [ctorBlk, List.getElem?_map, getElem?_finRange_eq hp_lt, Option.map_some,
          Option.some.injEq] at hk
        simp only [ctorTys, List.getElem?_map, getElem?_finRange_eq hp_lt, Option.map_some,
          Option.some.injEq] at htyA
        subst hk; subst htyA
        have haddr_eq : cprjAddr B slots[pf.val].1 slots[pf.val].2.2.1 = cprjAddr B i j :=
          Core.keyOf_inj htwf hname
        have hrec_p : recordOf E₀ (cprjAddr B slots[pf.val].1 slots[pf.val].2.2.1) =
            some (constructorProjection B slots[pf.val].1 slots[pf.val].2.2.1) := by
          rw [← LoadedReads.ctorAddr_eq_cprjAddr]
          exact hB.ctors _ _ _ (hslot_ok pf).1 (Array.getElem?_eq_some_iff.mp (hslot_ok pf).2).1
        have hrec_c : recordOf E₀ (cprjAddr B i j) = some (constructorProjection B i j) := by
          rw [← LoadedReads.ctorAddr_eq_cprjAddr]
          exact hB.ctors i ind j hmi (Array.getElem?_eq_some_iff.mp hct).1
        rw [haddr_eq] at hrec_p
        have hinfo_eq := congrArg Ixon.Constant.info (Option.some.inj (hrec_p.symm.trans hrec_c))
        simp only [constructorProjection, Ixon.ConstantInfo.cPrj.injEq,
          Ixon.ConstructorProj.mk.injEq] at hinfo_eq
        have hi_eq : slots[pf.val].1 = i := by
          rw [← toNat_toUInt64_lt_cr (Nat.lt_trans (Array.getElem?_eq_some_iff.mp (hslot_ok pf).1).1 hms_u64),
            ← toNat_toUInt64_lt_cr hi_u64, hinfo_eq.1]
        have hj_eq : slots[pf.val].2.2.1 = j := by
          have hj_pf_u64 : slots[pf.val].2.2.1 < UInt64.size :=
            Nat.lt_trans (Array.getElem?_eq_some_iff.mp (hslot_ok pf).2).1
              (hct_u64 slots[pf.val].2.1
                (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact (hslot_ok pf).1)))
          rw [← toNat_toUInt64_lt_cr hj_pf_u64, ← toNat_toUInt64_lt_cr hj_u64, hinfo_eq.2.1]
        have hind_eq : slots[pf.val].2.1 = ind := by
          have h1 := (hslot_ok pf).1; rw [hi_eq] at h1
          exact Ixon.MutConst.indc.inj (Option.some.inj (h1.symm.trans hmi))
        have hct_eq : slots[pf.val].2.2.2 = ct := by
          have h2 := (hslot_ok pf).2; rw [hind_eq, hj_eq] at h2
          exact Option.some.inj (h2.symm.trans hct)
        have hty0_eq : ty₀ = (ctorData pf).ty₀ := by
          have hr1 := (ctorData pf).hread
          have hct_typ : slots[pf.val].2.2.2.typ = ct.typ := congrArg Ixon.Constructor.typ hct_eq
          rw [hct_typ] at hr1
          exact Except.ok.inj (hread.symm.trans hr1)
        subst hty0_eq
        have hct_lvls : slots[pf.val].2.2.2.lvls = ct.lvls := congrArg Ixon.Constructor.lvls hct_eq
        have hct_typ : slots[pf.val].2.2.2.typ = ct.typ := congrArg Ixon.Constructor.typ hct_eq
        refine ⟨(ctorData pf).hlbb, by rw [← hct_lvls]; exact (ctorData pf).hdef, ?_⟩
        rw [← hi_eq, ← hj_eq, ← hct_lvls, ← hct_typ]
        exact (ctorData pf).hcanon
    · -- `.recr`
      intro k cv mI rP rules₀ tyA rhss hk htyA hrhss p rc hpb hrp hname _
      rw [hrecs_eq] at hk
      rw [hnonrecs_eq] at htyA
      have hk_lt : k < recAs.length := by
        have := (List.getElem?_eq_some_iff.mp hk).1; omega
      obtain ⟨rc_k, D_k, hrk, hb_k, ht_k, hrh_k, -⟩ := hRecAt k hk_lt
      have hinfo_k : ConstantInfo.recInfo cv mI rP rules₀ = D_k.recInfo :=
        Option.some.inj (hk.symm.trans hb_k)
      unfold RecMemberData.recInfo at hinfo_k
      injection hinfo_k with hcv_eq hmI_eq hrP_eq hrules_eq
      subst hcv_eq; subst hmI_eq; subst hrP_eq; subst hrules_eq
      rw [List.getElem?_append_right (by omega),
        show nonrecsBlk.length + k - nonrecsTys.length = k by omega] at htyA
      have htyA_eq : tyA = D_k.tyA := Option.some.inj (htyA.symm.trans ht_k)
      have hrhss_eq : rhss = D_k.rhss := Option.some.inj (hrhss.symm.trans hrh_k)
      subst htyA_eq; subst hrhss_eq
      have haddr_eq : rprjAddr rb k = memberAddr rb p.idx.toNat (.recr rc) :=
        Core.keyOf_inj htwf hname
      have hrec_k : recordOf E₀ (rprjAddr rb k) = some (memberProjection rb k (.recr rc_k)) := by
        rw [← LoadedReads.memberAddr_recr]; exact hR.members k (.recr rc_k) hrk
      have hrec_p : recordOf E₀ (memberAddr rb p.idx.toNat (.recr rc)) =
          some (memberProjection rb p.idx.toNat (.recr rc)) :=
        hR.members p.idx.toNat (.recr rc) hrp
      rw [haddr_eq] at hrec_k
      have hp_eq := congrArg Ixon.Constant.info (Option.some.inj (hrec_k.symm.trans hrec_p))
      simp only [memberProjection, Ixon.ConstantInfo.rPrj.injEq,
        Ixon.RecursorProj.mk.injEq] at hp_eq
      have hk_eq_p : p.idx.toNat = k := by
        have hk_u64 : k < UInt64.size := Nat.lt_trans (by omega) hrs_u64
        have hp_u64 : p.idx.toNat < UInt64.size := p.idx.toNat_lt_size
        rw [← toNat_toUInt64_lt_cr hk_u64, ← toNat_toUInt64_lt_cr hp_u64, hp_eq.1]
      have hrc_eq : rc = rc_k := by
        rw [hk_eq_p] at hrp
        exact Ixon.MutConst.recr.inj (Option.some.inj (hrp.symm.trans hrk))
      subst hrc_eq
      exact
        { lvls := D_k.hps_len
          tyBounded := D_k.hty_lbb
          tyLevels := D_k.hty_def
          rulesScoped := D_k.hrules_sc
          notK := D_k.hnotK
          ty := by rw [hk_eq_p]; exact D_k.hcanon_ty
          rules := by rw [hk_eq_p]; exact D_k.hcanon_rules }
  -- 12. `MajorRefs`
  have hmajorRefs : MajorRefs t E₀ rb blk tys := by
    intro k cv mI rP rules₀ tyA p us hk htyA _ hhd
    rw [hrecs_eq] at hk
    rw [hnonrecs_eq] at htyA
    have hk_lt : k < recAs.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1; omega
    obtain ⟨rc_k, D_k, -, hb_k, ht_k, -, -⟩ := hRecAt k hk_lt
    have hinfo_k : ConstantInfo.recInfo cv mI rP rules₀ = D_k.recInfo :=
      Option.some.inj (hk.symm.trans hb_k)
    unfold RecMemberData.recInfo at hinfo_k
    injection hinfo_k with _ hmI_eq _ _
    subst hmI_eq
    rw [List.getElem?_append_right (by omega),
      show nonrecsBlk.length + k - nonrecsTys.length = k by omega] at htyA
    have htyA_eq : tyA = D_k.tyA := Option.some.inj (htyA.symm.trans ht_k)
    subst htyA_eq
    obtain ⟨DM, lvlsM, pinsM, hpiM, hfnM, -⟩ := D_k.hhead
    rw [hpiM, Option.map_some, hfnM] at hhd
    injection hhd with hce; injection hce with hk_eq _
    have hp_eq : p = ixAddr D_k.aIndM := (Core.keyOf_inj htwf hk_eq).symm
    rw [hp_eq]
    exact D_k.husedIndM
  -- 13. `typesScopedB (blk.map (·.name)) tys = true` (store-free!)
  have htypesScoped : typesScopedB (blk.map (·.name)) tys = true := by
    let tKs := typeAs.map (fun b => Core.keyOf t (ixAddr b))
    let cKs := ctorAs.map (fun b => Core.keyOf t (ixAddr b))
    let rKs := recAs.map (fun b => Core.keyOf t (ixAddr b))
    have hnames_split : blk.map (·.name) = tKs ++ (cKs ++ rKs) := by
      rw [hblk_names]; simp only [srcKeys, srcAs, tKs, cKs, rKs, List.map_append, List.append_assoc]
    have htys_split : tys = indTys ++ (ctorTys ++ recsTys) := by
      simp only [tys, nonrecsTys, List.append_assoc]
    rw [hnames_split, htys_split]
    refine typesScopedB_of_blocks
      (by simp [tKs, hlen_indT, hlen_types])
      (by simp [cKs, hlen_ctorT, hlen_ctors])
      (by simp [rKs, hlen_rT]) ?_ ?_ ?_
    · intro ty hty k hk
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hty
      have hk_src : k ∈ srcAs.map (fun b => Core.keyOf t (ixAddr b)) := by
        simpa only [srcAs, tKs, cKs, rKs, List.map_append, List.append_assoc] using hk
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk_src
      exact (indData i).hment b hb
    · intro ty hty k hk
      obtain ⟨p, -, rfl⟩ := List.mem_map.mp hty
      have hk_cr : k ∈ (ctorAs ++ recAs).map (fun b => Core.keyOf t (ixAddr b)) := by
        simpa only [cKs, rKs, List.map_append] using hk
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk_cr
      exact (ctorData p).hment b hb
    · intro ty hty k hk
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hty
      have hi : idx < recAs.length := by
        have := (List.getElem?_eq_some_iff.mp hidx).1; omega
      obtain ⟨rc_i, D_i, -, -, ht_i, -, -⟩ := hRecAt idx hi
      have hty_eq : ty = D_i.tyA := Option.some.inj (hidx.symm.trans ht_i)
      subst hty_eq
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
      exact D_i.hment b hb
  -- 14. Step-environment conclusions: `FamDeclReads`, `FamilyCheckFacts`, `FamRecsCompanion`
  refine ⟨blk, advM, tys, rhsss, hcanon, hmajorRefs, hrecRefs, fun E env hSE hcovLogic => ?_⟩
  -- Every `k' ∈ srcKeys` maps under `g` to a stored `.defnInfo` in `env`
  have hdefSrc : ∀ k' ∈ srcKeys, ∃ cvm mval hint, env.find? (g k') = some (.defnInfo cvm mval hint) := by
    intro k' hk'
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk'
    obtain ⟨pos, hpos⟩ := List.mem_iff_getElem?.mp hb
    have hpos_lt : pos < srcAs.length := (List.getElem?_eq_some_iff.mp hpos).1
    have hb_eq : srcAs[pos]'hpos_lt = b :=
      Option.some.inj ((List.getElem?_eq_getElem hpos_lt).symm.trans hpos)
    have hgk := hg_at pos hpos_lt
    rw [hb_eq] at hgk
    rw [hgk]
    rcases Nat.lt_or_ge pos typeAs.length with h1 | h1
    · let pf : Fin ms.size := ⟨pos, by omega⟩
      have hd_eq : dstAs[pos]'(by omega) =
          typeMs[pos]'(by rw [T.typeModels]; exact h1) := by
        simp only [dstAs, List.append_assoc,
          List.getElem_append_left (show pos < typeMs.length by rw [T.typeModels]; exact h1)]
      rw [hd_eq]
      have hadvM := adv_of_advChecked (indData pf).hitem.hAdv (indData pf).hitem.hrecM
        (indData pf).hitem.hcaM hadvCase
      obtain ⟨cvm, mval, hint, hfind, -⟩ := (indData pf).hitem.stored_defn hSE hadvM
      exact ⟨cvm, mval, hint, hfind⟩
    · rcases Nat.lt_or_ge pos (typeAs.length + ctorAs.length) with h2 | h2
      · have hp_lt : pos - typeAs.length < slots.length := by omega
        let pf : Fin slots.length := ⟨pos - typeAs.length, hp_lt⟩
        have hd_eq : dstAs[pos]'(by omega) =
            ctorMs[pf.val]'(by rw [T.ctorModels, hlen_ctors]; exact hp_lt) := by
          have h1lt : pos < (typeMs ++ ctorMs).length := by
            simp only [List.length_append, T.typeModels, T.ctorModels]; omega
          have h2le : typeMs.length ≤ pos := by rw [T.typeModels]; omega
          simp only [dstAs, List.getElem_append_left h1lt, List.getElem_append_right h2le]
          congr 1; simp [pf, T.typeModels]
        rw [hd_eq]
        have hadvM := adv_of_advChecked (ctorData pf).hitem.hAdv (ctorData pf).hitem.hrecM
          (ctorData pf).hitem.hcaM hadvCase
        obtain ⟨cvm, mval, hint, hfind, -⟩ := (ctorData pf).hitem.stored_defn hSE hadvM
        exact ⟨cvm, mval, hint, hfind⟩
      · have hr_lt : pos - (typeAs.length + ctorAs.length) < recAs.length := by
          simp only [srcAs, List.length_append] at hpos_lt; omega
        have hd_eq : dstAs[pos]'(by omega) =
            recMs[pos - (typeAs.length + ctorAs.length)]'(by rw [T.recModels]; exact hr_lt) := by
          have hlen_tc : (typeMs ++ ctorMs).length = typeAs.length + ctorAs.length := by
            simp only [List.length_append, T.typeModels, T.ctorModels]
          have hle : (typeMs ++ ctorMs).length ≤ pos := by omega
          have hsub : pos - (typeMs ++ ctorMs).length = pos - (typeAs.length + ctorAs.length) := by omega
          simp only [dstAs, List.getElem_append_right hle, hsub]
        rw [hd_eq]
        let itemR := Classical.choice (hRecsItems (pos - (typeAs.length + ctorAs.length)) hr_lt)
        have hadvM := adv_of_advChecked itemR.hAdv itemR.hrecM itemR.hcaM hadvCase
        obtain ⟨cvm, mval, hint, hfind, -⟩ := itemR.stored_defn hSE hadvM
        exact ⟨cvm, mval, hint, hfind⟩
  have hdst_stored : ∀ b ∈ dstAs, ∃ ci, env.find? (Core.keyOf t (ixAddr b)) = some ci := by
    intro b hb
    obtain ⟨pos, hpos⟩ := List.mem_iff_getElem?.mp hb
    have hpos_lt : pos < dstAs.length := (List.getElem?_eq_some_iff.mp hpos).1
    have hb_eq : dstAs[pos]'hpos_lt = b :=
      Option.some.inj ((List.getElem?_eq_getElem hpos_lt).symm.trans hpos)
    have hpos_s : pos < srcAs.length := by omega
    have hgk := hg_at pos hpos_s
    rw [hb_eq] at hgk
    obtain ⟨cvm, mval, hint, hfind⟩ :=
      hdefSrc _ (List.mem_map.mpr ⟨srcAs[pos]'hpos_s, List.getElem_mem hpos_s, rfl⟩)
    rw [hgk] at hfind
    exact ⟨.defnInfo cvm mval hint, hfind⟩
  -- 14a. `FamDeclReads t E₀ B cb rb crb blk`
  have hblk_fresh : ∀ ci ∈ blk, env.find? ci.name = none := by
    intro ci hci
    have hmem_srcK : ci.name ∈ srcKeys := by rw [← hblk_names]; exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    obtain ⟨b, hb, hkeq⟩ := List.mem_map.mp hmem_srcK
    rw [← hkeq]
    have hfam_b : FamAddr B cb rb crb (ixAddr b) := by
      have hmem_src : ixAddr b ∈ (typeAs ++ ctorAs ++ recAs).map ixAddr :=
        List.mem_map.mpr ⟨b, hb, rfl⟩
      simp only [List.map_append, List.mem_append] at hmem_src
      rcases hmem_src with (ht_m | hc_m) | hr_m
      · rw [T.types] at ht_m
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ht_m
        rw [List.getElem?_mapIdx] at hi
        cases hmi : ms.toList[i]? with
        | none => rw [hmi] at hi; cases hi
        | some m =>
          rw [hmi] at hi; simp only [Option.map_some, Option.some.injEq] at hi
          exact Or.inl (Or.inr ⟨ms, i, m, hB.muts, by rwa [← Array.getElem?_toList],
            Or.inl (by rw [← hi, LoadedReads.memberAddr_eq_projAddr])⟩)
      · rw [hctors_slots] at hc_m
        obtain ⟨s, hs, hseq⟩ := List.mem_map.mp hc_m
        obtain ⟨k, hk, hmk, hct⟩ := ctorSlotsFrom_get 0 hs
        rw [Nat.zero_add] at hk
        have hmkA : ms[s.1]? = some (.indc s.2.1) := by rw [hk, ← Array.getElem?_toList]; exact hmk
        exact Or.inl (Or.inr ⟨ms, s.1, .indc s.2.1, hB.muts, hmkA,
          Or.inr ⟨s.2.1, s.2.2.1, rfl, (Array.getElem?_eq_some_iff.mp hct).1,
            by rw [← hseq, LoadedReads.ctorAddr_eq_cprjAddr]⟩⟩)
      · rw [T.recs] at hr_m
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr_m
        rw [List.getElem?_mapIdx] at hk
        cases hrk : rs.toList[k]? with
        | none => rw [hrk] at hk; cases hk
        | some m =>
          rw [hrk] at hk; simp only [Option.map_some, Option.some.injEq] at hk
          exact Or.inr (Or.inr ⟨rs, k, m, hR.muts, by rwa [← Array.getElem?_toList],
            Or.inl (by rw [← hk, LoadedReads.memberAddr_eq_projAddr])⟩)
    exact hSE.fresh (ixAddr b) hfam_b
  have hpinNone : Ix.Kernel.basisPinHit blk = none := by
    obtain ⟨G, R, envT, hshape, hext⟩ := hSE.shape
    exact basisPinHit_eq_none_of_fresh hshape hext hblk_fresh
  have hreads : FamDeclReads t E₀ B cb rb crb blk := by
    refine ⟨hblk_nodup, ?_, ?_, hpinNone⟩
    · intro ci hci
      rcases List.mem_append.mp hci with hnr | hr
      · rcases List.mem_append.mp hnr with hi | hc
        · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hi
          refine ⟨iprjAddr B i.val,
            Or.inl (Or.inr ⟨ms, i.val, .indc (indOf i), hB.muts, hms_indOf i,
              Or.inl (by rw [LoadedReads.memberAddr_indc])⟩), rfl, ?_⟩
          have hi_toNat : i.val.toUInt64.toNat = i.val := toNat_toUInt64_lt_cr (Nat.lt_trans i.isLt hms_u64)
          refine ⟨memberProjection B i.val (.indc (indOf i)),
            by rw [← LoadedReads.memberAddr_indc]; exact hB.members i.val (.indc (indOf i)) (hms_indOf i), ?_⟩
          show ∃ cb' ms' ind',
            MemberAt (recordOf E₀) (iprjAddr B i.val) (memberProjection B i.val (.indc (indOf i)))
              B cb' ms' i.val.toUInt64.toNat (.indc ind') ∧
            IndReads (exprReader t (fun x => E₀.blobs.get? x) cb' id (blockSelf t B ms'))
              (Consistency.keyOf t (iprjAddr B i.val)) ind' _
          rw [hi_toNat]
          exact ⟨cb, ms, indOf i,
            ⟨hB.record, hB.muts, hms_indOf i, rfl, by rw [LoadedReads.memberAddr_indc], hB.logic⟩,
            (indData i).ty₀, {}, (indData i).hread, rfl⟩
        · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hc
          let s := slots[p.val]
          have hmi := (hslot_ok p).1
          have hct := (hslot_ok p).2
          have hj_lt : s.2.2.1 < s.2.1.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
          have hi_toNat : s.1.toUInt64.toNat = s.1 :=
            toNat_toUInt64_lt_cr (Nat.lt_trans (Array.getElem?_eq_some_iff.mp hmi).1 hms_u64)
          have hj_toNat : s.2.2.1.toUInt64.toNat = s.2.2.1 :=
            toNat_toUInt64_lt_cr (Nat.lt_trans hj_lt (hct_u64 s.2.1
              (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmi))))
          refine ⟨cprjAddr B s.1 s.2.2.1,
            Or.inl (Or.inr ⟨ms, s.1, .indc s.2.1, hB.muts, hmi,
              Or.inr ⟨s.2.1, s.2.2.1, rfl, hj_lt, by rw [LoadedReads.ctorAddr_eq_cprjAddr]⟩⟩), rfl, ?_⟩
          refine ⟨constructorProjection B s.1 s.2.2.1,
            by rw [← LoadedReads.ctorAddr_eq_cprjAddr]; exact hB.ctors s.1 s.2.1 s.2.2.1 hmi hj_lt, ?_⟩
          show ∃ cb' ms' ind' ct',
            recordOf E₀ B = some cb' ∧ cb'.info = .muts ms' ∧
            ms'[s.1.toUInt64.toNat]? = some (.indc ind') ∧
            ind'.ctors[s.2.2.1.toUInt64.toNat]? = some ct' ∧
            ct'.cidx.toNat = s.2.2.1.toUInt64.toNat ∧
            constructorProjection B s.1 s.2.2.1 =
              constructorProjection B s.1.toUInt64.toNat s.2.2.1.toUInt64.toNat ∧
            cprjAddr B s.1 s.2.2.1 = ctorAddr B s.1.toUInt64.toNat s.2.2.1.toUInt64.toNat ∧
            InLogic cb' ∧
            CtorReads (exprReader t (fun x => E₀.blobs.get? x) cb' id (blockSelf t B ms'))
              (Consistency.keyOf t (cprjAddr B s.1 s.2.2.1)) ct' _
          rw [hi_toNat, hj_toNat]
          exact ⟨cb, ms, s.2.1, s.2.2.2, hB.record, hB.muts, hmi, hct,
            hcidx s.1 s.2.1 s.2.2.1 s.2.2.2 hmi hct, rfl,
            by rw [LoadedReads.ctorAddr_eq_cprjAddr], hB.logic,
            (ctorData p).ty₀, (ctorData p).hread, rfl⟩
      · obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.mp hr
        have hi : idx < recAs.length := by
          have := (List.getElem?_eq_some_iff.mp hidx).1; omega
        obtain ⟨rc_i, D_i, hrk, hb_i, -, -, -⟩ := hRecAt idx hi
        have hci_eq : ci = D_i.recInfo := Option.some.inj (hidx.symm.trans hb_i)
        subst hci_eq
        have hlogM : InLogic D_i.cbM := by
          rcases hrecRefs (ixAddr D_i.aIndM) D_i.husedIndM with hcovM | hneedM
          · exact hcovLogic _ _ _ _ hcovM D_i.hrecM D_i.hinfoM D_i.hrecBM
          · obtain ⟨c', hrec', -, -, hown'⟩ := hneedM
            have hc'_eq : c' = D_i.cmM := Option.some.inj (hrec'.symm.trans D_i.hrecM)
            subst hc'_eq
            have hown_eq : Ix.Cert.ownerOf (ixAddr D_i.aIndM) D_i.cmM = D_i.ipM.block := by
              simp [Ix.Cert.ownerOf, D_i.hinfoM]
            rw [hown_eq] at hown'
            exact hown' D_i.cbM D_i.hrecBM
        refine ⟨rprjAddr rb idx,
          Or.inr (Or.inr ⟨rs, idx, .recr rc_i, hR.muts, hrk,
            Or.inl (by rw [LoadedReads.memberAddr_recr])⟩), rfl, ?_⟩
        rw [← LoadedReads.memberAddr_recr (rc := rc_i)]
        exact D_i.hreads hlogM
    · intro x hx
      have hmem : x ∈ srcAs.map ixAddr := by
        rw [← hsrc_assoc]; exact famAddr_mem_src hB hR T hx
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hmem
      have hk : Core.keyOf t (ixAddr b) ∈ blk.map (·.name) := by
        rw [hblk_names]; exact List.mem_map.mpr ⟨b, hb, rfl⟩
      obtain ⟨ci, hci, hnm⟩ := List.mem_map.mp hk
      exact ⟨ci, hci, hnm⟩
  -- 14b. `FamilyCheckFacts env blk advM tys rhsss`
  have hrec_rulesFacts : ∀ idx (hi : idx < recAs.length),
      ∀ (rc_i : Ixon.Recursor)
        (D_i : RecMemberData.{u} calls bAddr t E₀ lim csFam B rb cb crb ms rs advAs
          srcAs dstAs recAs nonrecsBlk nonrecsTys idx rc_i recAs[idx]
          (recMs[idx]'(by rw [T.recModels]; exact hi))),
        RulesFacts env g blk tys (Core.keyOf t (rprjAddr rb idx)) D_i.ps D_i.tyA
          (rc_i.params.toNat + rc_i.motives.toNat + rc_i.minors.toNat + rc_i.indices.toNat)
          (rc_i.params.toNat + rc_i.motives.toNat + rc_i.minors.toNat)
          D_i.rules₀ D_i.rhss D_i.thms := by
    intro idx hi rc_i D_i
    let itemR := Classical.choice (hRecsItems idx hi)
    have hadvM := adv_of_advChecked itemR.hAdv itemR.hrecM itemR.hcaM hadvCase
    exact D_i.hrulesFacts recsBlk recsTys hSE hadvM hadvCase hdefSrc hdst_stored
  have hcheckFacts : FamilyCheckFacts env blk advM tys rhsss := by
    refine
      { split := by rw [hnonrecs_eq, hrecs_eq]
        kinds := by rw [hnonrecs_eq]; exact List.all_eq_true.mpr hnonrecs_kind
        table := by
          simp only [advM, List.map_fst_zip (Nat.le_of_eq hlenSD_keys), hblk_names]
        members := ?_
        typesScoped := htypesScoped
        recs := ?_ }
    · -- `MembersFacts`
      have hren_eq : advM.ren = g := rfl
      rw [hren_eq]
      refine membersFacts_append hlenNR (membersFacts_append (by omega) ?_ ?_) ?_
      · refine membersFacts_of_getElem indBlk indTys (by omega) fun idx hi => ?_
        simp only [indBlk, indTys, List.getElem_map]
        let kf : Fin ms.size := (List.finRange ms.size)[idx]'(by simp; omega)
        have hadvM := adv_of_advChecked (indData kf).hitem.hAdv (indData kf).hitem.hrecM
          (indData kf).hitem.hcaM hadvCase
        exact ((indData kf).hfacts hSE hadvM hdefSrc).2
      · refine membersFacts_of_getElem ctorBlk ctorTys (by omega) fun idx hi => ?_
        simp only [ctorBlk, ctorTys, List.getElem_map]
        let pf : Fin slots.length := (List.finRange slots.length)[idx]'(by simp; omega)
        have hadvM := adv_of_advChecked (ctorData pf).hitem.hAdv (ctorData pf).hitem.hrecM
          (ctorData pf).hitem.hcaM hadvCase
        exact ((ctorData pf).hfacts hSE hadvM hdefSrc).2
      · refine membersFacts_of_getElem recsBlk recsTys (by omega) fun idx hi => ?_
        have hi_r : idx < recAs.length := by omega
        obtain ⟨rc_i, D_i, -, hb_i, ht_i, -, -⟩ := hRecAt idx hi_r
        have hbi_eq : recsBlk[idx]'hi = D_i.recInfo :=
          Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hb_i)
        have hti_eq : recsTys[idx]'(by omega) = D_i.tyA :=
          Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans ht_i)
        rw [hbi_eq, hti_eq]
        let itemR := Classical.choice (hRecsItems idx hi_r)
        have hadvM := adv_of_advChecked itemR.hAdv itemR.hrecM itemR.hcaM hadvCase
        exact D_i.hmemFacts hSE hadvM hdefSrc
    · -- `RecsFacts`
      have hren_eq : advM.ren = g := rfl
      rw [hren_eq, hrecs_eq, hnonrecs_eq]
      have hdrop : tys.drop nonrecsBlk.length = recsTys := by
        simp only [tys, List.drop_left' hlenNR.symm]
      rw [hdrop]
      refine recsFacts_of_getElem recsBlk recsTys rhsss thmsList
        (by omega) (by omega) (by omega) fun idx hi => ?_
      have hi_r : idx < recAs.length := by omega
      obtain ⟨rc_i, D_i, -, hb_i, ht_i, hrh_i, hth_i⟩ := hRecAt idx hi_r
      have hbi_eq : recsBlk[idx]'hi = D_i.recInfo :=
        Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hb_i)
      have hti_eq : recsTys[idx]'(by omega) = D_i.tyA :=
        Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans ht_i)
      have hrhi_eq : rhsss[idx]'(by omega) = D_i.rhss :=
        Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hrh_i)
      have hthi_eq : thmsList[idx]'(by omega) = D_i.thms :=
        Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hth_i)
      rw [hbi_eq, hti_eq, hrhi_eq, hthi_eq]
      exact ⟨_, _, _, _, rfl, hrec_rulesFacts idx hi_r rc_i D_i⟩
  -- 14c. `FamRecsCompanion E₀ t env blk tys`
  have hcompanions : FamRecsCompanion E₀ t env blk tys := by
    intro k cv mI rP rules₀ tyA hk htyA
    rw [hrecs_eq] at hk
    rw [hnonrecs_eq] at htyA
    have hk_lt : k < recAs.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1; omega
    obtain ⟨rc_k, D_k, -, hb_k, ht_k, -, -⟩ := hRecAt k hk_lt
    have hinfo_k : ConstantInfo.recInfo cv mI rP rules₀ = D_k.recInfo :=
      Option.some.inj (hk.symm.trans hb_k)
    unfold RecMemberData.recInfo at hinfo_k
    injection hinfo_k with hcv_eq hmI_eq hrP_eq hrules_eq
    subst hcv_eq; subst hmI_eq; subst hrP_eq; subst hrules_eq
    rw [List.getElem?_append_right (by omega),
      show nonrecsBlk.length + k - nonrecsTys.length = k by omega] at htyA
    have htyA_eq : tyA = D_k.tyA := Option.some.inj (htyA.symm.trans ht_k)
    subst htyA_eq
    refine ⟨famRecCompanion_of_data ht hS D_k hblk_nodup hblk_fresh
      (hrec_rulesFacts k hk_lt rc_k D_k), fun ro => ?_⟩
    have hmem_k := hnoRoleRecs recAs[k] (List.getElem_mem hk_lt) ro
    have ha_k := hrecAs_k k hk_lt
    rw [Nat.zero_add] at ha_k
    rwa [ha_k] at hmem_k
  exact ⟨hreads, hcheckFacts, hcompanions⟩

/-! ## Payload-stream determinism: identifying `FamilyOwnAdvice`'s advice list with `C.advList` -/

private theorem get_count_spec_bytes {s x_n x_s2 : SourceValue F} {bytes : List UInt8}
    {h h' : Heap F} {cs : List (Call F)} (hs : L1.Stream h bytes s)
    (ev : ObsFn Obs.W "KernelModeled::get_count" [s] h (.tuple [x_n, x_s2]) h' cs) :
    ∃ (tg : Ixon.TagN) (k : Nat),
      Ixon.getTagN 0 (TagN.start bytes) = .ok tg { idx := k, bytes := ⟨bytes.toArray⟩ } ∧
      x_n = .field (tg.value.toNat : F) ∧
      L1.Stream h' (bytes.drop k) x_s2 := by
  match Obs.«KernelModeled::get_count».obs ev with
  | .run (m2 := m2) (x_n := x_w) (x_s2 := y) (v38 := v38) (ev14 := e1) (he40 := hr)
      (ev52 := e2) (he68 := hh) .. =>
    obtain ⟨hm2, tg, k, restPtr, htag, -, hrest, htup⟩ := TagN.getTagN0_refines hs e1.erase
    subst hm2
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup hr
    obtain ⟨rfl, rfl⟩ := htup
    obtain ⟨rfl, rfl⟩ := hr
    obtain ⟨-, hv38, hm42⟩ := Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 tg.value) e2
    rw [hh, hm42]
    exact ⟨tg, k, htag, hv38, hrest⟩

private theorem get_addrs_bytes_go :
    ∀ (cnt : Nat) {n_f : F} {x_s r : SourceValue F} {bytes_in : List UInt8}
      {h h' : Heap F} {cs : List (Call F)},
      ZMod.val n_f = cnt →
      L1.Stream h bytes_in x_s →
      ObsFn Obs.W "KernelModeled::get_addrs" [x_s, .field n_f] h r h' cs →
      ∃ (as_ : List Bytes.Address) (bytes_out : List UInt8) (x_as x_s' : SourceValue F),
        r = .tuple [x_as, x_s'] ∧
        as_.length = cnt ∧
        bytes_in = as_.flatMap (·.toList) ++ bytes_out ∧
        RepList addrListEnum (Bytes.RepAddressRef addrTy) h' as_ x_as ∧
        L1.Stream h' bytes_out x_s'
  | 0, n_f, x_s, r, bytes_in, h, h', cs, hcnt, hs, ev => by
    cases Obs.«KernelModeled::get_addrs».obs ev with
    | n0 m21 _ he19 hm29 he40 _ =>
      have ext : Heap.Extends h h' := ⟨_, by rw [he40, hm29]⟩
      refine ⟨[], bytes_in, .ptr (.enum addrListEnum) h.length, x_s, he19, rfl, rfl, ?_, hs.mono ext⟩
      rw [he40, hm29]
      exact Lib.rep_store_nil h
    | other _ _ _ _ _ _ _ _ _ _ hne42 _ _ _ _ _ _ _ =>
      have hn0 : n_f = 0 := by rwa [ZMod.val_eq_zero] at hcnt
      exact absurd (congrArg Value.field hn0) hne42
  | cnt + 1, n_f, x_s, r, bytes_in, h, h', cs, hcnt, hs, ev => by
    cases Obs.«KernelModeled::get_addrs».obs ev with
    | n0 _ hv14 _ _ _ _ =>
      injection hv14 with hn0
      subst hn0
      simp at hcnt
    | other m47 cs57 x_a x_s2 m82 cs92 v96 x_rest x_s3 m138
        hne42 ev59 op117 ev94 he136 hm146 he173 _ =>
      have hn_ne : n_f ≠ 0 := fun e => hne42 (congrArg Value.field e)
      obtain rfl := Lib.sub_one_inv op117
      have hpred : ZMod.val (n_f - 1) = cnt := by
        have hv := Lib.val_sub_one hn_ne
        omega
      obtain ⟨a, rem, x_t, x_s2', hbytes1, htup1, ha_rep, hs_rem, _, _⟩ :=
        Decl.get_address_spec hs ev59
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup1
      obtain ⟨rfl, rfl⟩ := htup1
      obtain ⟨as_rest, bytes_out, x_as_rest, x_s_out, htup2, hlen_rest, hbytes2, hrest_rep, hs_out⟩ :=
        get_addrs_bytes_go cnt hpred hs_rem ev94
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup2
      obtain ⟨rfl, rfl⟩ := htup2
      have ext2 : Heap.Extends m47 m82 := ev94.heap_extends
      have ext3 : Heap.Extends m82 h' := ⟨_, by rw [he173, hm146]⟩
      refine ⟨a :: as_rest, bytes_out, .ptr (.enum addrListEnum) m82.length, x_s3,
        he136, by simp [hlen_rest], ?_, ?_, hs_out.mono ext3⟩
      · rw [hbytes1, hbytes2, List.flatMap_cons, List.append_assoc]
      · rw [he173, hm146]
        exact Lib.rep_store_cons (Bytes.repAddressRef_heapMono₂ addrTy)
          (Bytes.repAddressRef_heapMono₂ addrTy ext2 ha_rep) hrest_rep

private theorem addrs_eq_of_flatMap_eq :
    ∀ {l₁ l₂ : List Bytes.Address} {r₁ r₂ : List UInt8},
      l₁.length = l₂.length →
      l₁.flatMap (·.toList) ++ r₁ = l₂.flatMap (·.toList) ++ r₂ →
      l₁ = l₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => by cases hlen
  | _ :: _, [], _, _, hlen, _ => by cases hlen
  | a₁ :: t₁, a₂ :: t₂, r₁, r₂, hlen, hbytes => by
    simp only [List.flatMap_cons, List.append_assoc] at hbytes
    have hlen32 : a₁.toList.length = a₂.toList.length := by simp only [Vector.length_toList]
    obtain ⟨ha, ht⟩ := List.append_inj hbytes hlen32
    exact congrArg₂ List.cons (Vector.toList_inj.mp ha)
      (addrs_eq_of_flatMap_eq (by simpa using hlen) ht)

/-- **The advice list `advAs` of a `FamilyOwnAdvice` witness equals the advice list `C.advList`
read off the same `check_family` call's `CheckFamilyChain`**, via the payload-stream anchor
(`check_family_first_get_address`) and determinism of byte-stream deserialization. -/
theorem advAs_eq_of_familyOwnAdvice {rc xb xrb r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {advAs advAs' : List Bytes.Address}
    (w : FamilyOwnAdvice rc xb xrb h r h' cs advAs)
    (C : CheckFamilyChain rc xb xrb h h' cs)
    (hrep' : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m423 advAs' C.advList) :
    advAs' = advAs := by
  match w with
  | .mk (m_adv := m_adv) (x_advice := x_advice) (advRep := advRep)
      (v_pl := v_pl) (m_pl := m_pl) (bytes_pl := bytes_pl)
      (pl_stream := pl_stream) (pl_first := pl_first)
      (x_s1 := x_s1_w) (ev_rb := ev_rb)
      (m_na := m_na_w) (x_na := x_na_w) (x_s2 := x_s2_w)
      (ext_s1_na := ext_s1_na) (ev_na := ev_na)
      (ev_ga := ev_ga) (ext_s3_adv := ext_s3_adv) .. =>
    have hfirst_C := check_family_first_get_address C.sg112 C.evReadPayload.obs C.callsPrefix
    have hcall_eq : (⟨"IxonDeserialize::get_address", [v_pl], m_pl⟩ : Call F) =
        ⟨"IxonDeserialize::get_address", [C.payload], C.m114⟩ :=
      Option.some.inj (pl_first.symm.trans hfirst_C)
    have hvpl : v_pl = C.payload := (List.cons.inj (congrArg Call.args hcall_eq)).1
    have hmpl : m_pl = C.m114 := congrArg Call.heap hcall_eq
    subst hvpl hmpl
    have hs_pl : L1.Stream C.m114 bytes_pl C.payload := pl_stream
    obtain ⟨a_rb_w, rem1_w, x_t_w, x_s1_w', hbytes_rb_w, htup_rb_w, -, hs_rem1_w, -, -⟩ :=
      Decl.get_address_spec hs_pl ev_rb
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_rb_w
    obtain ⟨-, rfl⟩ := htup_rb_w
    obtain ⟨a_rb_C, rem1_C, x_t_C, x_s1_C', hbytes_rb_C, htup_rb_C, -, hs_rem1_C, -, -⟩ :=
      Decl.get_address_spec hs_pl C.evGetRb.obs
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_rb_C
    obtain ⟨-, hxs1_C⟩ := htup_rb_C
    have hrem1_eq : rem1_w = rem1_C := by
      have h12 : a_rb_w.toList ++ rem1_w = a_rb_C.toList ++ rem1_C :=
        hbytes_rb_w.symm.trans hbytes_rb_C
      exact (List.append_inj h12 (by simp only [Vector.length_toList])).2
    subst hrem1_eq
    have hs_s1_w : L1.Stream m_na_w rem1_w x_s1_w := hs_rem1_w.mono ext_s1_na
    have ext_136_ord : Heap.Extends C.m136 C.mOrd := C.evRbEq.extends.trans C.evInOrder.extends
    have hs_s1_C : L1.Stream C.mOrd rem1_w C.s1 := by
      rw [hxs1_C]; exact hs_rem1_C.mono ext_136_ord
    obtain ⟨tg_w, k_w, htag_w, hxna_w, hs_s2_w⟩ := get_count_spec_bytes hs_s1_w ev_na
    obtain ⟨tg_C, k_C, htag_C, hxna_C, hs_s2_C⟩ := get_count_spec_bytes hs_s1_C C.evCountAdv.obs
    have htag_eq := htag_w.symm.trans htag_C
    injection htag_eq with htg_eq hst_eq
    have hk_eq : k_w = k_C := congrArg Ixon.GetState.idx hst_eq
    subst htg_eq hk_eq
    rw [hxna_w] at ev_ga
    have ev_ga_C : ObsFn Obs.W "KernelModeled::get_addrs" [C.s2, .field (tg_w.value.toNat : F)]
        C.m219 (.tuple [C.advList, C.s3]) C.m254 C.evGetAdv.cs := by
      rw [← hxna_C]; exact C.evGetAdv.obs
    obtain ⟨as_w, out_w, x_as_w, x_s3_w', htup_ga_w, hlen_w, hbytes_ga_w, hrep_ga_w, -⟩ :=
      get_addrs_bytes_go (ZMod.val (tg_w.value.toNat : F)) rfl hs_s2_w ev_ga
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ga_w
    obtain ⟨hxa_w, -⟩ := htup_ga_w
    obtain ⟨as_C, out_C, x_as_C, x_s3_C', htup_ga_C, hlen_C, hbytes_ga_C, hrep_ga_C, -⟩ :=
      get_addrs_bytes_go (ZMod.val (tg_w.value.toNat : F)) rfl hs_s2_C ev_ga_C
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup_ga_C
    obtain ⟨hxa_C, -⟩ := htup_ga_C
    have has_eq : as_C = as_w :=
      addrs_eq_of_flatMap_eq (hlen_C.trans hlen_w.symm) (hbytes_ga_C.symm.trans hbytes_ga_w)
    have hrep_w_adv : RepList addrListEnum (Bytes.RepAddressRef addrTy) m_adv as_w x_advice := by
      rw [hxa_w]
      exact repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext_s3_adv hrep_ga_w
    have ext_254_423 : Heap.Extends C.m254 C.m423 :=
      C.evCountWit.extends.trans (C.evCheckWit.extends.trans (C.evWset.extends.trans C.evContRefs.extends))
    have hrep_C_423 : RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m423 as_C C.advList := by
      rw [hxa_C]
      exact repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) ext_254_423 hrep_ga_C
    have h1 : advAs' = as_C := repList_det (fun _ _ _ _ r1 r2 => Core.addr_det r1 r2) hrep' hrep_C_423
    have h2 : as_w = advAs := repList_det (fun _ _ _ _ r1 r2 => Core.addr_det r1 r2) hrep_w_adv advRep
    exact h1.trans (has_eq.trans h2)

/-! ## Endpoint 1 (unconditional): `ClosureFamilyCheck` at every group of every binding run -/

/-- **Unconditional `ClosureFamilyCheck` at every group of every binding run**, polymorphic in any
link predicate `L` (in particular `FormerOpenTraceAt`). -/
theorem closureFamilyCheck_of_run {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} :
    ∀ calls, Binding.AtGroups (Binding.BindingRun calls) (ClosureFamilyCheck.{u} L calls) := by
  intro calls t ρ Rs hrun hall ht g hg6 hg R R' R₁ env₀ envT famOf₀ famOf adv cont bAddr B rb cb
    crb hC hextT hndT hnB hcb hunc hfam hcrb hfrT
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hS : LoadedReads.RunStore calls ρ.E₀ := hrun.runStore
  have hH : LoadedReads.HashedRecordsStored calls ρ.E₀ := hrun.hashedStored
  have hloaded : ∀ a lr, R₁.consts.get? a = some lr → ρ.E₀.consts.get? a = some lr :=
    fun a lr h => hC.admits.loaded a lr (hC.store.le₂.1 a lr h)
  have hcb₀ : recordOf ρ.E₀ B = some cb := Binding.recordOf_of_loaded hloaded hcb
  have hcrb₀ : recordOf ρ.E₀ rb = some crb := Binding.recordOf_of_loaded hloaded hcrb
  obtain ⟨-, hroute, cs, advAs, hown, hadvIn, -⟩ := hC.checks.famCall B rb hfam
  obtain ⟨cb', ms, crb', rs, flat, hFB⟩ := hC.checks.family B rb hfam
  have e1 : cb' = cb := Option.some.inj (hFB.block.record.symm.trans hcb₀)
  subst cb'
  have e2 : crb' = crb := Option.some.inj (hFB.record.record.symm.trans hcrb₀)
  subst crb'
  have hcb' : recordOf R' B = some cb := Binding.recordOf_of_loaded hC.store.le₂.1 hcb
  have hnB' : Binding.New R R' B := ⟨by rw [hcb']; rfl, hnB.2⟩
  -- Unpack `FamilyCallOwn` into `CheckFamilyChain`
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, w, -, hsub⟩ := hown
  obtain ⟨C⟩ := checkFamily_chain ev
  -- Bounded calls + `ms.size < 2^33` + checked members at `valLimit g`
  have hzc : R₁.consts.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h0 : R₁.consts.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some lc =>
      have h' := hC.store.le₂.1 _ lc h0; rw [hC.admits.zeroFree.1] at h'; cases h'
  have hzb : R₁.blobs.get? Ix.HostAdmission.Merkle.padding = none := by
    cases h0 : R₁.blobs.get? Ix.HostAdmission.Merkle.padding with
    | none => rfl
    | some b =>
      have h' := hC.store.le₂.2 _ b h0; rw [hC.admits.zeroFree.2] at h'; cases h'
  obtain ⟨Ec0, hRc0, hst0⟩ := hrun.stepStores R₁ hloaded
    (fun a b h => hC.admits.loadedBlobs a b (hC.store.le₂.2 a b h))
    (fun p hp lc h => hC.admits.committed p hp lc (hC.store.le₂.1 _ lc h)) ⟨hzc, hzb⟩
  have hbd : Bounded calls := (hst0.good Ix.Kernel.Env.empty none).2
  -- Extract `ct.cidx.toNat = j` from checked members + modeled route
  have hkind : UnitKind cb := Or.inr (Or.inr ⟨ms, hFB.block.muts⟩)
  have hntw : ¬ (∃ rs' : Array Ixon.MutConst, cb.info = .muts rs' ∧ 0 < rs'.size ∧
      ∀ m ∈ rs'.toList, ∃ r, m = Ixon.MutConst.recr r) := by
    rintro ⟨rs', hrs', hpos', hrecs'⟩
    have e : rs' = ms := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hFB.block.muts)
    subst e
    obtain ⟨m, hm⟩ : ∃ m, m ∈ rs'.toList := by
      cases hl : rs'.toList with
      | nil =>
        have h0 : rs'.size = 0 := by rw [← Array.length_toList, hl]; rfl
        exact absurd hpos' (by omega)
      | cons m _ => exact ⟨m, by simp⟩
    obtain ⟨r, hr⟩ := hrecs' m hm
    obtain ⟨ind, hind⟩ := hFB.block.indcs m hm
    rw [hr] at hind; cases hind
  have hchkB : ρ.checked B (Binding.valLimit g) := by
    rcases hC.famAdmits.checked B cb hnB' hcb' hkind hntw with hchk | ⟨B', hB', -⟩
    · exact hchk
    · exact (hunc B' hB').elim
  obtain ⟨bAddr', hiff⟩ := hrun.checked_iff
  have hU : Binding.UnitCheckedAt calls bAddr' t ρ.E₀ B (some (Binding.valLimit g)) :=
    (hiff B _).mp hchkB
  have hmem : ∀ k, k < ms.size →
      Claim.MemberCheckedLimAt calls bAddr' t B ms k (some (Binding.valLimit g)) := by
    rcases hU with h1 | ⟨c', ms', hc'', hms', hk'⟩
    · exact (Claim.checked_not_block hS hcb₀ hFB.block.muts h1).elim
    · rw [Option.some.inj (hc''.symm.trans hcb₀), hFB.block.muts] at hms'
      have e : ms' = ms := (Ixon.ConstantInfo.muts.inj hms').symm
      rw [e] at hk'; exact hk'
  have hpos : 0 < ms.size := by
    obtain ⟨cb₂, ms₂, hcb₂, hms₂, hpos₂⟩ := hC.run.famNonempty B rb hfam
    have e : cb₂ = cb := Option.some.inj (hcb₂.symm.trans hcb₀)
    rw [e, hFB.block.muts] at hms₂
    rw [Ixon.ConstantInfo.muts.inj hms₂]; exact hpos₂
  have hcanon₀ : L1.CanonicalHashCoverage ρ.E₀ calls := by
    intro bytes value hashed size exactRead
    obtain ⟨entry, stored, bytesEq, cached⟩ := hH bytes value hashed size
      (L1.deConstant_of_deConstantExact exactRead) exactRead
    refine ⟨⟨entry, value, stored, cached, ?_⟩, rfl⟩
    rw [bytesEq]; exact exactRead
  have hcanon0 : L1.CanonicalHashCoverage Ec0 calls :=
    Assembly.canonicalHashCoverage_frame hcanon₀ hst0.decoded
      (fun a v h => hst0.runRecord a v ((hS.recordOf_eq_recordAt a).trans h))
  have hmod0 : ModeledAt Ec0 B :=
    modeledAt_of_modeledRoute (c := ⟨Ec0, Ix.Kernel.Env.empty, t, none⟩)
      (hst0.good Ix.Kernel.Env.empty none) hcanon0 hroute
      (Claim.MemberCheckedLimAt.dispatch hS hFB.block.indcs (hmem 0 hpos))
  have hms_lt8 : ms.size < 8589934592 := by
    obtain ⟨bB, hbB_rep, hbB_eq⟩ := hxb
    have ext_h_453 : Heap.Extends h C.m453 := (Decl.check_family_seg1_inv C.sg112).trans C.ext_m105_m453
    obtain ⟨cb', ms', hbl, -⟩ :=
      Claim.load_block_head (Bytes.repAddressRef_heapMono₂ addrTy ext_h_453 hbB_rep) C.evLoadBlk.obs
    have hB' : FamBlockRecord ρ.E₀ (ixAddr bB) cb ms := by rw [hbB_eq]; exact hFB.block
    obtain ⟨hrec', -⟩ := (hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).stored hH
    have e : cb = cb' := Option.some.inj (hB'.record.symm.trans hrec')
    subst e
    have hres : cb.resourceSize < 8589934592 :=
      ((hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).record hS hB'.record).2
    have hsz : ms.size ≤ cb.resourceSize := Claim.muts_size_le hFB.block.muts
    omega
  have hcidx : ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct → ct.cidx.toNat = j :=
    cidx_eq_of_modeled_checked hFB.block hst0 hRc0.1 hmod0 hms_lt8 hmem
  have hadvHyp : ∀ (advAs' : List Bytes.Address),
      RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m423 advAs' C.advList →
      ∀ a, AdviceListedIn advAs' a →
        adv B a ∨ ∀ ca x, recordOf ρ.E₀ a = some ca → ¬ ConstAddrOf a ca x := by
    intro advAs' hrep' a ha'
    rw [advAs_eq_of_familyOwnAdvice w C hrep'] at ha'
    exact Or.inl (hadvIn a ha')
  obtain ⟨blk, advM, tys, rhsss, hcanon, hmajorRefs, hrecRefs, hstep⟩ :=
    familyCall_checked_of_chain (L := L) ht hbd hS hH hFB.block hFB.record hrc hxb hxrb hsub C
      (Or.inr hadvHyp) hcidx
  refine ⟨fun Ec hRc hst env hext hnd hinv hX hinert hrefs hadv1 hadv2 hfresh => ?_, hrecRefs⟩
  have hSE : FamilyStepEnv.{u} L calls t ρ.E₀ (some (Binding.valLimit g)) B cb rb crb (adv B)
      Ec env :=
    { store := hst
      shape := ⟨(· < g), R, env₀, hC.bnd.shape, fun ci hci => hext ci (hextT ci hci)⟩
      nodup := hnd
      prefixInv := hinv
      extra := hX
      inert := hinert
      refs := hrefs
      advStored := hadv1
      advRefs := hadv2
      fresh := hfresh
      covered := fun x hx => by
        obtain ⟨ci, hci, hname⟩ := coveredAt_stored hC.bnd.shape hinv.tableWf
          (fun r hr => Nat.lt_of_lt_of_le (hr _ rfl) (Binding.valLimit_le g)) hx
        exact find_isSome_of_storedAt ⟨ci, hext ci (hextT ci hci), hname⟩
      blockRefs := fun x hu => Or.inr (hC.run.famNeedOk B rb x hfam hnB' hu) }
  have hRecsR : RecordsFor R Ec :=
    ⟨hRc.1,
     fun a c hc => hRc.2.1 a c (Binding.recordOf_of_loaded hC.store.le₁.1 hc),
     fun x b hb => hRc.2.2.1 x b (hC.store.le₁.2 x b hb),
     hRc.2.2.2⟩
  have hcovLogic : ∀ x c p cbM, Claim.CoveredAt t (some (Binding.valLimit g)) x →
      recordOf ρ.E₀ x = some c → c.info = .iPrj p → recordOf ρ.E₀ p.block = some cbM →
      InLogic cbM := fun x c p cbM hcov hrec hinfo hblk =>
    coveredLogic_of_checked hC.bnd.shape
      (fun r hr => Nat.lt_of_lt_of_le (hr _ rfl) (Binding.valLimit_le g))
      hRecsR hst hcov hrec hinfo hblk
  obtain ⟨hreads, hcheckFacts, hcompanions⟩ := hstep Ec env hSE hcovLogic
  refine ⟨blk, advM, tys, rhsss, hreads, hcheckFacts,
    fun ms' rs' hms' hrs' => ?_, fun E hE => ?_⟩
  · have e3 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hFB.block.muts)
    have e4 : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hFB.record.muts)
    subst e3 e4; exact hcanon
  · refine famRecsCompanion_carry hS.recordOf_eq_recordAt (fun p hp c' hc' => ?_) hmajorRefs
      hcompanions
    obtain ⟨c₁, i, hc₁, hi, hx⟩ := hp
    have e5 : c₁ = crb := Option.some.inj (hc₁.symm.trans hcrb₀)
    subst e5
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp ((hC.closed.1 rb c₁ hcrb).2 i hi p hx)
    have e6 : P = c' := Option.some.inj ((Binding.recordOf_of_loaded hloaded hP).symm.trans hc')
    subst e6
    exact hE.2.1 p P hP

/-! ## Endpoint 2 (unconditional): `FamilyBlockCheckRow` at every typing walk -/

/-- **Unconditional `FamilyBlockCheckRow`**, polymorphic in any link predicate `L`
(in particular `FormerOpenTraceAt`). -/
theorem familyBlockCheckRow_of_run {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} :
    FamilyBlockCheckRow.{u} L := by
  intro calls t seeds E₀ lim Top rank hTW R envT E fam twin adv Inner hrun hctx A c rb crb rs
    hTop hc hlog hkind hfam hrb
  obtain ⟨ms, hB⟩ := famBlockRecord_of_run hTW hrun hTop hc hlog hfam
  have hneed := Claim.TopWalk.need hTW hTop hc hkind hlog
  have hmod : ModeledAt E A := famModeledAt_of_run hTW hrun hctx hTop hc hfam
  obtain ⟨bAddr, hW, -⟩ := hTW
  have hinert : InertClause t c := hW.inertClause hTop hc
  have hS : LoadedReads.RunStore calls E₀ := hW.runStore
  have hH : LoadedReads.HashedRecordsStored calls E₀ := hW.hashedStored
  obtain ⟨bAddr', hC⟩ := hrun.checks
  obtain ⟨hroute, cs, advAs, hown, hlist⟩ := hC.famCall A rb hfam
  obtain ⟨h, h', rc, xb, xrb, r, hrc, hxb, hxrb, ev, w, -, hsub⟩ := hown
  obtain ⟨C⟩ := checkFamily_chain ev
  have ht : t.check = .ok () := by
    obtain ⟨_, ⟨hwf, -⟩, -⟩ := hrc.cases
    exact Core.RoleClosure.check_ok_of_wf hwf
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  have hbd : Bounded calls := (hctx.good Ix.Kernel.Env.empty lim).2
  have hms_lt8 : ms.size < 8589934592 := by
    obtain ⟨bB, hbB_rep, hbB_eq⟩ := hxb
    have ext_h_453 : Heap.Extends h C.m453 := (Decl.check_family_seg1_inv C.sg112).trans C.ext_m105_m453
    obtain ⟨cb', ms', hbl, -⟩ :=
      Claim.load_block_head (Bytes.repAddressRef_heapMono₂ addrTy ext_h_453 hbB_rep) C.evLoadBlk.obs
    have hB' : FamBlockRecord E₀ (ixAddr bB) c ms := by rwa [hbB_eq]
    obtain ⟨hrec', -⟩ := (hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).stored hH
    have e : c = cb' := Option.some.inj (hB'.record.symm.trans hrec')
    subst e
    have hres : c.resourceSize < 8589934592 :=
      ((hbl.mono (fun cl hcl => hsub cl (C.evLoadBlk.sub cl hcl))).record hS hB'.record).2
    have hsz : ms.size ≤ c.resourceSize := Claim.muts_size_le hB.muts
    omega
  have hchk : (∃ ms', c.info = .muts ms' ∧
        ∀ k, k < ms'.size → Claim.MemberCheckedLimAt calls bAddr t A ms' k lim) ∨
      Claim.CheckedLimAt calls bAddr t A lim := by
    obtain ⟨c', hc', hchk'⟩ := hW.checked A hTop
    have e : c' = c := Option.some.inj (hc'.symm.trans hc)
    rw [e] at hchk'; exact hchk'
  have hmem : ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t A ms k lim :=
    fun k hk => Claim.membersChecked_of_block hS hc hB.muts hchk k hk
  have hcidx : ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
      ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct → ct.cidx.toNat = j :=
    cidx_eq_of_modeled_checked hB hctx.toStepStore hctx.recordsFor.1 hmod hms_lt8 hmem
  have hadvHyp : ∀ (advAs' : List Bytes.Address),
      RepList addrListEnum (Bytes.RepAddressRef addrTy) C.m423 advAs' C.advList →
      ∀ a, AdviceListedIn advAs' a →
        adv A a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x := by
    intro advAs' hrep' a ha'
    rw [advAs_eq_of_familyOwnAdvice w C hrep'] at ha'
    exact hlist a ha'
  obtain ⟨blk, advM, tys, rhsss, hcanon, hmajorRefs, hrecRefs, hstep⟩ :=
    familyCall_checked_of_chain (L := L) ht hbd hS hH hB hrb hrc hxb hxrb hsub C
      (Or.inr hadvHyp) hcidx
  refine ⟨fun env hextT hnd hinv hX hrefs hadv1 hadv2 hfresh => ?_, hrecRefs⟩
  have hSE : FamilyStepEnv.{u} L calls t E₀ lim A c rb crb (adv A) E env :=
    { store := hctx.toStepStore
      shape := ⟨fun _ => True, R, envT, hctx.shape, hextT⟩
      nodup := hnd
      prefixInv := hinv
      extra := hX.1
      inert := hinert
      refs := hrefs
      advStored := hadv1
      advRefs := hadv2
      fresh := hfresh
      covered := fun x hx => by
        obtain ⟨ci, hci, hname⟩ :=
          coveredAt_stored hctx.shape hinv.tableWf (fun _ _ => trivial) hx
        exact find_isSome_of_storedAt ⟨ci, hextT ci hci, hname⟩
      blockRefs := fun x hu => by
        by_cases hcov : Covered t x
        · obtain ⟨ci, hci, hname⟩ := covered_stored hctx.shape hinv.tableWf hcov
          exact Or.inl (find_isSome_of_storedAt ⟨ci, hextT ci hci, hname⟩)
        · obtain ⟨c', i, hc', hi, hx⟩ := hu
          have e : c' = c := Option.some.inj (hc'.symm.trans hc)
          rw [e] at hi hx
          have hx' : c.refs.toList[i]? = some x := by rw [Array.getElem?_toList]; exact hx
          exact Or.inr (hneed i hi x hx' (hinert i hi x hx') hcov) }
  have hcovLogic : ∀ x cx p cbM, Claim.CoveredAt t lim x →
      recordOf E₀ x = some cx → cx.info = .iPrj p → recordOf E₀ p.block = some cbM →
      InLogic cbM := fun x cx p cbM hcov hrec hinfo hblk =>
    coveredLogic_of_checked hctx.shape (fun _ _ => trivial) hctx.recordsFor hctx.toStepStore
      hcov hrec hinfo hblk
  obtain ⟨hreads, hcheckFacts, hcompanions⟩ := hstep E env hSE hcovLogic
  refine ⟨blk, advM, tys, rhsss, hreads, hcheckFacts, ?_⟩
  unfold SelectedForms
  refine ⟨fun ms' rs' hms' hrs' => ?_, ?_⟩
  · have e1 : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hB.muts)
    have e2 : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hrb.muts)
    subst e1 e2; exact hcanon
  · exact famRecsCompanion_carry hS.recordOf_eq_recordAt
      (fun p _ c' hc' => hctx.runRecord p c' hc') hmajorRefs hcompanions

end IxVM.Refinement.Typing.FamilyAlias
